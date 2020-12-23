%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:11 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 221 expanded)
%              Number of leaves         :   23 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :  339 ( 790 expanded)
%              Number of equality atoms :   17 (  35 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f655,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f345,f362,f632,f636,f654])).

fof(f654,plain,
    ( spl6_6
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f653])).

fof(f653,plain,
    ( $false
    | spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f652,f47])).

fof(f47,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3))
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(X1))
          & r1_tarski(sK2,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(X1))
        & r1_tarski(sK2,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3))
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f652,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f649,f353])).

fof(f353,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK3))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl6_8
  <=> r1_tarski(k2_relat_1(sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f649,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl6_6 ),
    inference(resolution,[],[f344,f88])).

fof(f88,plain,(
    ! [X2,X3] :
      ( r1_tarski(X3,k3_relat_1(X2))
      | ~ r1_tarski(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f62,f50])).

fof(f50,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f344,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl6_6
  <=> r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f636,plain,(
    spl6_14 ),
    inference(avatar_contradiction_clause,[],[f635])).

fof(f635,plain,
    ( $false
    | spl6_14 ),
    inference(subsumption_resolution,[],[f634,f47])).

fof(f634,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_14 ),
    inference(subsumption_resolution,[],[f633,f48])).

fof(f48,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f633,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ v1_relat_1(sK3)
    | spl6_14 ),
    inference(resolution,[],[f613,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f51,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f53,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f613,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | spl6_14 ),
    inference(avatar_component_clause,[],[f611])).

fof(f611,plain,
    ( spl6_14
  <=> r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f632,plain,
    ( ~ spl6_14
    | spl6_5 ),
    inference(avatar_split_clause,[],[f607,f338,f611])).

fof(f338,plain,
    ( spl6_5
  <=> r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f607,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | spl6_5 ),
    inference(subsumption_resolution,[],[f605,f47])).

fof(f605,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl6_5 ),
    inference(resolution,[],[f559,f340])).

fof(f340,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f338])).

fof(f559,plain,(
    ! [X6,X7] :
      ( r1_tarski(X6,k3_relat_1(X7))
      | ~ r1_tarski(X6,k1_relat_1(X7))
      | ~ v1_relat_1(X7) ) ),
    inference(resolution,[],[f547,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X1,k1_relat_1(X0)),k2_relat_1(X0))
      | r1_tarski(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f63,f50])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f547,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f114,f243])).

fof(f243,plain,(
    ! [X4,X5,X3] :
      ( ~ sP0(X5,X3,X4)
      | ~ r1_tarski(X4,X5) ) ),
    inference(subsumption_resolution,[],[f238,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f238,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ r1_tarski(X4,X5)
      | ~ sP0(X5,X3,X4) ) ),
    inference(resolution,[],[f236,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k4_xboole_0(X2,X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f66,f76])).

fof(f76,plain,(
    ! [X0,X1] : sP1(X0,X1,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f28,f27])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sP0(X1,sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sP0(X1,sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f236,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X6,k4_xboole_0(X4,X5))
      | ~ r2_hidden(X6,X4)
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f221,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f221,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f109,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f109,plain,(
    ! [X4,X5,X3] :
      ( sP0(k4_xboole_0(X4,X5),X3,X4)
      | ~ r2_hidden(X3,k1_setfam_1(k2_tarski(X4,X5))) ) ),
    inference(resolution,[],[f65,f97])).

fof(f97,plain,(
    ! [X4,X3] : sP1(X3,k4_xboole_0(X3,X4),k1_setfam_1(k2_tarski(X3,X4))) ),
    inference(superposition,[],[f76,f74])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f55,f54])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,sK4(k4_xboole_0(X1,X0),X2),X1)
      | r1_tarski(k4_xboole_0(X1,X0),X2) ) ),
    inference(resolution,[],[f108,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | sP0(X2,X0,X1) ) ),
    inference(resolution,[],[f65,f76])).

fof(f362,plain,(
    spl6_8 ),
    inference(avatar_contradiction_clause,[],[f361])).

fof(f361,plain,
    ( $false
    | spl6_8 ),
    inference(subsumption_resolution,[],[f360,f47])).

fof(f360,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_8 ),
    inference(subsumption_resolution,[],[f359,f48])).

fof(f359,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ v1_relat_1(sK3)
    | spl6_8 ),
    inference(resolution,[],[f354,f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f52,f78])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f354,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK3))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f352])).

fof(f345,plain,
    ( ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f336,f342,f338])).

fof(f336,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f328,f46])).

fof(f46,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f328,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f107,f49])).

fof(f49,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),X1)
      | ~ r1_tarski(k2_relat_1(X0),X1)
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f64,f50])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:39:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (29510)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (29526)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (29511)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (29519)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (29526)Refutation not found, incomplete strategy% (29526)------------------------------
% 0.20/0.53  % (29526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (29527)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.54  % (29507)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.27/0.54  % (29526)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (29526)Memory used [KB]: 10618
% 1.27/0.54  % (29526)Time elapsed: 0.111 s
% 1.27/0.54  % (29526)------------------------------
% 1.27/0.54  % (29526)------------------------------
% 1.27/0.54  % (29504)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.27/0.54  % (29518)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.55  % (29513)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.27/0.55  % (29523)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.27/0.55  % (29532)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.27/0.55  % (29508)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.55  % (29517)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.27/0.55  % (29522)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.27/0.55  % (29515)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.27/0.55  % (29509)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.27/0.55  % (29515)Refutation not found, incomplete strategy% (29515)------------------------------
% 1.27/0.55  % (29515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.55  % (29515)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.55  
% 1.27/0.55  % (29515)Memory used [KB]: 10618
% 1.27/0.55  % (29515)Time elapsed: 0.137 s
% 1.27/0.55  % (29515)------------------------------
% 1.27/0.55  % (29515)------------------------------
% 1.27/0.55  % (29528)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.27/0.55  % (29521)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.27/0.55  % (29514)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.27/0.55  % (29520)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.44/0.56  % (29505)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.44/0.56  % (29530)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.44/0.56  % (29524)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.44/0.56  % (29521)Refutation not found, incomplete strategy% (29521)------------------------------
% 1.44/0.56  % (29521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (29506)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.44/0.56  % (29525)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.44/0.56  % (29529)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.44/0.56  % (29531)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.44/0.56  % (29533)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.44/0.56  % (29514)Refutation not found, incomplete strategy% (29514)------------------------------
% 1.44/0.56  % (29514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (29516)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.57  % (29514)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.57  % (29521)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.57  
% 1.44/0.57  
% 1.44/0.57  % (29514)Memory used [KB]: 10618
% 1.44/0.57  % (29521)Memory used [KB]: 10618
% 1.44/0.57  % (29514)Time elapsed: 0.158 s
% 1.44/0.57  % (29521)Time elapsed: 0.105 s
% 1.44/0.57  % (29514)------------------------------
% 1.44/0.57  % (29514)------------------------------
% 1.44/0.57  % (29521)------------------------------
% 1.44/0.57  % (29521)------------------------------
% 1.44/0.58  % (29512)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.44/0.61  % (29531)Refutation found. Thanks to Tanya!
% 1.44/0.61  % SZS status Theorem for theBenchmark
% 1.93/0.63  % SZS output start Proof for theBenchmark
% 1.93/0.63  fof(f655,plain,(
% 1.93/0.63    $false),
% 1.93/0.63    inference(avatar_sat_refutation,[],[f345,f362,f632,f636,f654])).
% 1.93/0.63  fof(f654,plain,(
% 1.93/0.63    spl6_6 | ~spl6_8),
% 1.93/0.63    inference(avatar_contradiction_clause,[],[f653])).
% 1.93/0.63  fof(f653,plain,(
% 1.93/0.63    $false | (spl6_6 | ~spl6_8)),
% 1.93/0.63    inference(subsumption_resolution,[],[f652,f47])).
% 1.93/0.63  fof(f47,plain,(
% 1.93/0.63    v1_relat_1(sK3)),
% 1.93/0.63    inference(cnf_transformation,[],[f32])).
% 1.93/0.63  fof(f32,plain,(
% 1.93/0.63    (~r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 1.93/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f31,f30])).
% 1.93/0.63  fof(f30,plain,(
% 1.93/0.63    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK2),k3_relat_1(X1)) & r1_tarski(sK2,X1) & v1_relat_1(X1)) & v1_relat_1(sK2))),
% 1.93/0.63    introduced(choice_axiom,[])).
% 1.93/0.63  fof(f31,plain,(
% 1.93/0.63    ? [X1] : (~r1_tarski(k3_relat_1(sK2),k3_relat_1(X1)) & r1_tarski(sK2,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 1.93/0.63    introduced(choice_axiom,[])).
% 1.93/0.63  fof(f16,plain,(
% 1.93/0.63    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.93/0.63    inference(flattening,[],[f15])).
% 1.93/0.63  fof(f15,plain,(
% 1.93/0.63    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.93/0.63    inference(ennf_transformation,[],[f14])).
% 1.93/0.63  fof(f14,negated_conjecture,(
% 1.93/0.63    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.93/0.63    inference(negated_conjecture,[],[f13])).
% 1.93/0.63  fof(f13,conjecture,(
% 1.93/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 1.93/0.63  fof(f652,plain,(
% 1.93/0.63    ~v1_relat_1(sK3) | (spl6_6 | ~spl6_8)),
% 1.93/0.63    inference(subsumption_resolution,[],[f649,f353])).
% 1.93/0.63  fof(f353,plain,(
% 1.93/0.63    r1_tarski(k2_relat_1(sK2),k2_relat_1(sK3)) | ~spl6_8),
% 1.93/0.63    inference(avatar_component_clause,[],[f352])).
% 1.93/0.63  fof(f352,plain,(
% 1.93/0.63    spl6_8 <=> r1_tarski(k2_relat_1(sK2),k2_relat_1(sK3))),
% 1.93/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.93/0.63  fof(f649,plain,(
% 1.93/0.63    ~r1_tarski(k2_relat_1(sK2),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | spl6_6),
% 1.93/0.63    inference(resolution,[],[f344,f88])).
% 1.93/0.63  fof(f88,plain,(
% 1.93/0.63    ( ! [X2,X3] : (r1_tarski(X3,k3_relat_1(X2)) | ~r1_tarski(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.93/0.63    inference(superposition,[],[f62,f50])).
% 1.93/0.63  fof(f50,plain,(
% 1.93/0.63    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f17])).
% 1.93/0.63  fof(f17,plain,(
% 1.93/0.63    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.93/0.63    inference(ennf_transformation,[],[f11])).
% 1.93/0.63  fof(f11,axiom,(
% 1.93/0.63    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 1.93/0.63  fof(f62,plain,(
% 1.93/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f23])).
% 1.93/0.63  fof(f23,plain,(
% 1.93/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.93/0.63    inference(ennf_transformation,[],[f3])).
% 1.93/0.63  fof(f3,axiom,(
% 1.93/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.93/0.63  fof(f344,plain,(
% 1.93/0.63    ~r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3)) | spl6_6),
% 1.93/0.63    inference(avatar_component_clause,[],[f342])).
% 1.93/0.63  fof(f342,plain,(
% 1.93/0.63    spl6_6 <=> r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3))),
% 1.93/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.93/0.63  fof(f636,plain,(
% 1.93/0.63    spl6_14),
% 1.93/0.63    inference(avatar_contradiction_clause,[],[f635])).
% 1.93/0.63  fof(f635,plain,(
% 1.93/0.63    $false | spl6_14),
% 1.93/0.63    inference(subsumption_resolution,[],[f634,f47])).
% 1.93/0.63  fof(f634,plain,(
% 1.93/0.63    ~v1_relat_1(sK3) | spl6_14),
% 1.93/0.63    inference(subsumption_resolution,[],[f633,f48])).
% 1.93/0.63  fof(f48,plain,(
% 1.93/0.63    r1_tarski(sK2,sK3)),
% 1.93/0.63    inference(cnf_transformation,[],[f32])).
% 1.93/0.63  fof(f633,plain,(
% 1.93/0.63    ~r1_tarski(sK2,sK3) | ~v1_relat_1(sK3) | spl6_14),
% 1.93/0.63    inference(resolution,[],[f613,f137])).
% 1.93/0.63  fof(f137,plain,(
% 1.93/0.63    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) )),
% 1.93/0.63    inference(subsumption_resolution,[],[f51,f78])).
% 1.93/0.63  fof(f78,plain,(
% 1.93/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 1.93/0.63    inference(resolution,[],[f53,f61])).
% 1.93/0.63  fof(f61,plain,(
% 1.93/0.63    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f37])).
% 1.93/0.63  fof(f37,plain,(
% 1.93/0.63    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.93/0.63    inference(nnf_transformation,[],[f9])).
% 1.93/0.63  fof(f9,axiom,(
% 1.93/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.93/0.63  fof(f53,plain,(
% 1.93/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f20])).
% 1.93/0.63  fof(f20,plain,(
% 1.93/0.63    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.93/0.63    inference(ennf_transformation,[],[f10])).
% 1.93/0.63  fof(f10,axiom,(
% 1.93/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.93/0.63  fof(f51,plain,(
% 1.93/0.63    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f19])).
% 1.93/0.63  fof(f19,plain,(
% 1.93/0.63    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.93/0.63    inference(flattening,[],[f18])).
% 1.93/0.63  fof(f18,plain,(
% 1.93/0.63    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.93/0.63    inference(ennf_transformation,[],[f12])).
% 1.93/0.63  fof(f12,axiom,(
% 1.93/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 1.93/0.63  fof(f613,plain,(
% 1.93/0.63    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | spl6_14),
% 1.93/0.63    inference(avatar_component_clause,[],[f611])).
% 1.93/0.63  fof(f611,plain,(
% 1.93/0.63    spl6_14 <=> r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3))),
% 1.93/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.93/0.63  fof(f632,plain,(
% 1.93/0.63    ~spl6_14 | spl6_5),
% 1.93/0.63    inference(avatar_split_clause,[],[f607,f338,f611])).
% 1.93/0.63  fof(f338,plain,(
% 1.93/0.63    spl6_5 <=> r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3))),
% 1.93/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.93/0.63  fof(f607,plain,(
% 1.93/0.63    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | spl6_5),
% 1.93/0.63    inference(subsumption_resolution,[],[f605,f47])).
% 1.93/0.63  fof(f605,plain,(
% 1.93/0.63    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl6_5),
% 1.93/0.63    inference(resolution,[],[f559,f340])).
% 1.93/0.63  fof(f340,plain,(
% 1.93/0.63    ~r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3)) | spl6_5),
% 1.93/0.63    inference(avatar_component_clause,[],[f338])).
% 1.93/0.63  fof(f559,plain,(
% 1.93/0.63    ( ! [X6,X7] : (r1_tarski(X6,k3_relat_1(X7)) | ~r1_tarski(X6,k1_relat_1(X7)) | ~v1_relat_1(X7)) )),
% 1.93/0.63    inference(resolution,[],[f547,f90])).
% 1.93/0.63  fof(f90,plain,(
% 1.93/0.63    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X1,k1_relat_1(X0)),k2_relat_1(X0)) | r1_tarski(X1,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.93/0.63    inference(superposition,[],[f63,f50])).
% 1.93/0.63  fof(f63,plain,(
% 1.93/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f24])).
% 1.93/0.63  fof(f24,plain,(
% 1.93/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.93/0.63    inference(ennf_transformation,[],[f5])).
% 1.93/0.63  fof(f5,axiom,(
% 1.93/0.63    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 1.93/0.63  fof(f547,plain,(
% 1.93/0.63    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,X1)) )),
% 1.93/0.63    inference(resolution,[],[f114,f243])).
% 1.93/0.63  fof(f243,plain,(
% 1.93/0.63    ( ! [X4,X5,X3] : (~sP0(X5,X3,X4) | ~r1_tarski(X4,X5)) )),
% 1.93/0.63    inference(subsumption_resolution,[],[f238,f69])).
% 1.93/0.63  fof(f69,plain,(
% 1.93/0.63    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f44])).
% 1.93/0.63  fof(f44,plain,(
% 1.93/0.63    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 1.93/0.63    inference(rectify,[],[f43])).
% 1.93/0.63  fof(f43,plain,(
% 1.93/0.63    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.93/0.63    inference(flattening,[],[f42])).
% 1.93/0.63  fof(f42,plain,(
% 1.93/0.63    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.93/0.63    inference(nnf_transformation,[],[f27])).
% 1.93/0.63  fof(f27,plain,(
% 1.93/0.63    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 1.93/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.93/0.63  fof(f238,plain,(
% 1.93/0.63    ( ! [X4,X5,X3] : (~r2_hidden(X3,X4) | ~r1_tarski(X4,X5) | ~sP0(X5,X3,X4)) )),
% 1.93/0.63    inference(resolution,[],[f236,f111])).
% 1.93/0.63  fof(f111,plain,(
% 1.93/0.63    ( ! [X2,X0,X1] : (r2_hidden(X1,k4_xboole_0(X2,X0)) | ~sP0(X0,X1,X2)) )),
% 1.93/0.63    inference(resolution,[],[f66,f76])).
% 1.93/0.63  fof(f76,plain,(
% 1.93/0.63    ( ! [X0,X1] : (sP1(X0,X1,k4_xboole_0(X0,X1))) )),
% 1.93/0.63    inference(equality_resolution,[],[f72])).
% 1.93/0.63  fof(f72,plain,(
% 1.93/0.63    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.93/0.63    inference(cnf_transformation,[],[f45])).
% 1.93/0.63  fof(f45,plain,(
% 1.93/0.63    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.93/0.63    inference(nnf_transformation,[],[f29])).
% 1.93/0.63  fof(f29,plain,(
% 1.93/0.63    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 1.93/0.63    inference(definition_folding,[],[f2,f28,f27])).
% 1.93/0.63  fof(f28,plain,(
% 1.93/0.63    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 1.93/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.93/0.63  fof(f2,axiom,(
% 1.93/0.63    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.93/0.63  fof(f66,plain,(
% 1.93/0.63    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f41])).
% 1.93/0.63  fof(f41,plain,(
% 1.93/0.63    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(X1,sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.93/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f39,f40])).
% 1.93/0.63  fof(f40,plain,(
% 1.93/0.63    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(X1,sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.93/0.63    introduced(choice_axiom,[])).
% 1.93/0.63  fof(f39,plain,(
% 1.93/0.63    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.93/0.63    inference(rectify,[],[f38])).
% 1.93/0.63  fof(f38,plain,(
% 1.93/0.63    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 1.93/0.63    inference(nnf_transformation,[],[f28])).
% 1.93/0.63  fof(f236,plain,(
% 1.93/0.63    ( ! [X6,X4,X5] : (~r2_hidden(X6,k4_xboole_0(X4,X5)) | ~r2_hidden(X6,X4) | ~r1_tarski(X4,X5)) )),
% 1.93/0.63    inference(superposition,[],[f221,f75])).
% 1.93/0.63  fof(f75,plain,(
% 1.93/0.63    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.93/0.63    inference(definition_unfolding,[],[f56,f54])).
% 1.93/0.63  fof(f54,plain,(
% 1.93/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.93/0.63    inference(cnf_transformation,[],[f8])).
% 1.93/0.63  fof(f8,axiom,(
% 1.93/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.93/0.63  fof(f56,plain,(
% 1.93/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f21])).
% 1.93/0.63  fof(f21,plain,(
% 1.93/0.63    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.93/0.63    inference(ennf_transformation,[],[f4])).
% 1.93/0.63  fof(f4,axiom,(
% 1.93/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.93/0.63  fof(f221,plain,(
% 1.93/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_setfam_1(k2_tarski(X1,X2))) | ~r2_hidden(X0,k4_xboole_0(X1,X2))) )),
% 1.93/0.63    inference(resolution,[],[f109,f70])).
% 1.93/0.63  fof(f70,plain,(
% 1.93/0.63    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f44])).
% 1.93/0.63  fof(f109,plain,(
% 1.93/0.63    ( ! [X4,X5,X3] : (sP0(k4_xboole_0(X4,X5),X3,X4) | ~r2_hidden(X3,k1_setfam_1(k2_tarski(X4,X5)))) )),
% 1.93/0.63    inference(resolution,[],[f65,f97])).
% 1.93/0.63  fof(f97,plain,(
% 1.93/0.63    ( ! [X4,X3] : (sP1(X3,k4_xboole_0(X3,X4),k1_setfam_1(k2_tarski(X3,X4)))) )),
% 1.93/0.63    inference(superposition,[],[f76,f74])).
% 1.93/0.63  fof(f74,plain,(
% 1.93/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.93/0.63    inference(definition_unfolding,[],[f55,f54])).
% 1.93/0.63  fof(f55,plain,(
% 1.93/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.93/0.63    inference(cnf_transformation,[],[f6])).
% 1.93/0.63  fof(f6,axiom,(
% 1.93/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.93/0.63  fof(f65,plain,(
% 1.93/0.63    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X1,X4,X0)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f41])).
% 1.93/0.63  fof(f114,plain,(
% 1.93/0.63    ( ! [X2,X0,X1] : (sP0(X0,sK4(k4_xboole_0(X1,X0),X2),X1) | r1_tarski(k4_xboole_0(X1,X0),X2)) )),
% 1.93/0.63    inference(resolution,[],[f108,f58])).
% 1.93/0.63  fof(f58,plain,(
% 1.93/0.63    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f36])).
% 1.93/0.63  fof(f36,plain,(
% 1.93/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.93/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 1.93/0.63  fof(f35,plain,(
% 1.93/0.63    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.93/0.63    introduced(choice_axiom,[])).
% 1.93/0.63  fof(f34,plain,(
% 1.93/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.93/0.63    inference(rectify,[],[f33])).
% 1.93/0.63  fof(f33,plain,(
% 1.93/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.93/0.63    inference(nnf_transformation,[],[f22])).
% 1.93/0.63  fof(f22,plain,(
% 1.93/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.93/0.63    inference(ennf_transformation,[],[f1])).
% 1.93/0.63  fof(f1,axiom,(
% 1.93/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.93/0.63  fof(f108,plain,(
% 1.93/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | sP0(X2,X0,X1)) )),
% 1.93/0.63    inference(resolution,[],[f65,f76])).
% 1.93/0.63  fof(f362,plain,(
% 1.93/0.63    spl6_8),
% 1.93/0.63    inference(avatar_contradiction_clause,[],[f361])).
% 1.93/0.63  fof(f361,plain,(
% 1.93/0.63    $false | spl6_8),
% 1.93/0.63    inference(subsumption_resolution,[],[f360,f47])).
% 1.93/0.63  fof(f360,plain,(
% 1.93/0.63    ~v1_relat_1(sK3) | spl6_8),
% 1.93/0.63    inference(subsumption_resolution,[],[f359,f48])).
% 1.93/0.63  fof(f359,plain,(
% 1.93/0.63    ~r1_tarski(sK2,sK3) | ~v1_relat_1(sK3) | spl6_8),
% 1.93/0.63    inference(resolution,[],[f354,f149])).
% 1.93/0.63  fof(f149,plain,(
% 1.93/0.63    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) )),
% 1.93/0.63    inference(subsumption_resolution,[],[f52,f78])).
% 1.93/0.63  fof(f52,plain,(
% 1.93/0.63    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f19])).
% 1.93/0.63  fof(f354,plain,(
% 1.93/0.63    ~r1_tarski(k2_relat_1(sK2),k2_relat_1(sK3)) | spl6_8),
% 1.93/0.63    inference(avatar_component_clause,[],[f352])).
% 1.93/0.63  fof(f345,plain,(
% 1.93/0.63    ~spl6_5 | ~spl6_6),
% 1.93/0.63    inference(avatar_split_clause,[],[f336,f342,f338])).
% 1.93/0.63  fof(f336,plain,(
% 1.93/0.63    ~r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3)) | ~r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3))),
% 1.93/0.63    inference(subsumption_resolution,[],[f328,f46])).
% 1.93/0.63  fof(f46,plain,(
% 1.93/0.63    v1_relat_1(sK2)),
% 1.93/0.63    inference(cnf_transformation,[],[f32])).
% 1.93/0.63  fof(f328,plain,(
% 1.93/0.63    ~r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3)) | ~r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3)) | ~v1_relat_1(sK2)),
% 1.93/0.63    inference(resolution,[],[f107,f49])).
% 1.93/0.63  fof(f49,plain,(
% 1.93/0.63    ~r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3))),
% 1.93/0.63    inference(cnf_transformation,[],[f32])).
% 1.93/0.63  fof(f107,plain,(
% 1.93/0.63    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),X1) | ~r1_tarski(k2_relat_1(X0),X1) | ~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 1.93/0.63    inference(superposition,[],[f64,f50])).
% 1.93/0.63  fof(f64,plain,(
% 1.93/0.63    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f26])).
% 1.93/0.63  fof(f26,plain,(
% 1.93/0.63    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.93/0.63    inference(flattening,[],[f25])).
% 1.93/0.63  fof(f25,plain,(
% 1.93/0.63    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.93/0.63    inference(ennf_transformation,[],[f7])).
% 1.93/0.63  fof(f7,axiom,(
% 1.93/0.63    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.93/0.63  % SZS output end Proof for theBenchmark
% 1.93/0.63  % (29531)------------------------------
% 1.93/0.63  % (29531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.63  % (29531)Termination reason: Refutation
% 1.93/0.63  
% 1.93/0.63  % (29531)Memory used [KB]: 6524
% 1.93/0.63  % (29531)Time elapsed: 0.204 s
% 1.93/0.63  % (29531)------------------------------
% 1.93/0.63  % (29531)------------------------------
% 1.93/0.63  % (29503)Success in time 0.261 s
%------------------------------------------------------------------------------
