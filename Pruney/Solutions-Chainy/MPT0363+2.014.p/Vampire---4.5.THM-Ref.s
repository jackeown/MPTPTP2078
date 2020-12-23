%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 138 expanded)
%              Number of leaves         :   19 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :  254 ( 504 expanded)
%              Number of equality atoms :   19 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f123,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f67,f79,f88,f115,f120,f122])).

fof(f122,plain,
    ( ~ spl4_4
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | ~ spl4_4
    | spl4_6 ),
    inference(subsumption_resolution,[],[f90,f119])).

fof(f119,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl4_6
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f90,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f78,f57])).

fof(f57,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f78,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_4
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f120,plain,
    ( ~ spl4_6
    | ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f116,f62,f59,f118])).

fof(f59,plain,
    ( spl4_1
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f62,plain,
    ( spl4_2
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f116,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ r1_tarski(sK1,sK0)
    | spl4_2 ),
    inference(resolution,[],[f63,f96])).

fof(f96,plain,(
    ! [X0] :
      ( r1_tarski(X0,k3_subset_1(sK0,sK2))
      | ~ r1_xboole_0(X0,sK2)
      | ~ r1_tarski(X0,sK0) ) ),
    inference(superposition,[],[f55,f80])).

fof(f80,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f32,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
      | ~ r1_xboole_0(sK1,sK2) )
    & ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
      | r1_xboole_0(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | r1_xboole_0(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,X2))
            | ~ r1_xboole_0(sK1,X2) )
          & ( r1_tarski(sK1,k3_subset_1(sK0,X2))
            | r1_xboole_0(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,X2))
          | ~ r1_xboole_0(sK1,X2) )
        & ( r1_tarski(sK1,k3_subset_1(sK0,X2))
          | r1_xboole_0(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
        | ~ r1_xboole_0(sK1,sK2) )
      & ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
        | r1_xboole_0(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,X2)
          <~> r1_tarski(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,X2)
            <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f37])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f63,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f115,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f68,f113])).

fof(f113,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f102,f97])).

fof(f97,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK2),sK2) ),
    inference(superposition,[],[f53,f80])).

fof(f53,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f36,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f102,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(k3_subset_1(sK0,sK2),X1)
        | r1_xboole_0(X1,sK1) )
    | ~ spl4_2 ),
    inference(resolution,[],[f99,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f99,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,k3_subset_1(sK0,sK2))
        | r1_xboole_0(X1,sK1) )
    | ~ spl4_2 ),
    inference(superposition,[],[f50,f89])).

fof(f89,plain,
    ( k3_subset_1(sK0,sK2) = k2_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl4_2 ),
    inference(resolution,[],[f66,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f66,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f68,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl4_1 ),
    inference(resolution,[],[f60,f43])).

fof(f60,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f88,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | ~ spl4_3 ),
    inference(resolution,[],[f75,f35])).

fof(f35,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f75,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl4_3
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f79,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f71,f77,f74])).

fof(f71,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f31,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f33,f62,f59])).

fof(f33,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f34,f62,f59])).

fof(f34,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n010.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 12:40:14 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.20/0.49  % (10216)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (10219)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (10241)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.50  % (10237)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (10229)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (10235)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.50  % (10233)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.50  % (10216)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f64,f67,f79,f88,f115,f120,f122])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    ~spl4_4 | spl4_6),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f121])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    $false | (~spl4_4 | spl4_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f90,f119])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    ~r1_tarski(sK1,sK0) | spl4_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f118])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    spl4_6 <=> r1_tarski(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    r1_tarski(sK1,sK0) | ~spl4_4),
% 0.20/0.50    inference(resolution,[],[f78,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.50    inference(rectify,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f77])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    spl4_4 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    ~spl4_6 | ~spl4_1 | spl4_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f116,f62,f59,f118])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    spl4_1 <=> r1_xboole_0(sK1,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    spl4_2 <=> r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    ~r1_xboole_0(sK1,sK2) | ~r1_tarski(sK1,sK0) | spl4_2),
% 0.20/0.50    inference(resolution,[],[f63,f96])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(X0,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(X0,sK2) | ~r1_tarski(X0,sK0)) )),
% 0.20/0.50    inference(superposition,[],[f55,f80])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 0.20/0.50    inference(resolution,[],[f32,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f44,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ((~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)) & (r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f24,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK1,k3_subset_1(sK0,X2)) | ~r1_xboole_0(sK1,X2)) & (r1_tarski(sK1,k3_subset_1(sK0,X2)) | r1_xboole_0(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ? [X2] : ((~r1_tarski(sK1,k3_subset_1(sK0,X2)) | ~r1_xboole_0(sK1,X2)) & (r1_tarski(sK1,k3_subset_1(sK0,X2)) | r1_xboole_0(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)) & (r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(nnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,X2) <~> r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.20/0.50    inference(negated_conjecture,[],[f11])).
% 0.20/0.50  fof(f11,conjecture,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f52,f37])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | spl4_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f62])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    spl4_1 | ~spl4_2),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f114])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    $false | (spl4_1 | ~spl4_2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f68,f113])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    r1_xboole_0(sK2,sK1) | ~spl4_2),
% 0.20/0.50    inference(resolution,[],[f102,f97])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    r1_xboole_0(k3_subset_1(sK0,sK2),sK2)),
% 0.20/0.50    inference(superposition,[],[f53,f80])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f36,f37])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    ( ! [X1] : (~r1_xboole_0(k3_subset_1(sK0,sK2),X1) | r1_xboole_0(X1,sK1)) ) | ~spl4_2),
% 0.20/0.50    inference(resolution,[],[f99,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    ( ! [X1] : (~r1_xboole_0(X1,k3_subset_1(sK0,sK2)) | r1_xboole_0(X1,sK1)) ) | ~spl4_2),
% 0.20/0.50    inference(superposition,[],[f50,f89])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    k3_subset_1(sK0,sK2) = k2_xboole_0(sK1,k3_subset_1(sK0,sK2)) | ~spl4_2),
% 0.20/0.50    inference(resolution,[],[f66,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~spl4_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f62])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ~r1_xboole_0(sK2,sK1) | spl4_1),
% 0.20/0.50    inference(resolution,[],[f60,f43])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ~r1_xboole_0(sK1,sK2) | spl4_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f59])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ~spl4_3),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f87])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    $false | ~spl4_3),
% 0.20/0.50    inference(resolution,[],[f75,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl4_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    spl4_3 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    spl4_3 | spl4_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f71,f77,f74])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(resolution,[],[f31,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.50    inference(nnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    spl4_1 | spl4_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f33,f62,f59])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ~spl4_1 | ~spl4_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f34,f62,f59])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (10216)------------------------------
% 0.20/0.50  % (10216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (10216)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (10216)Memory used [KB]: 10746
% 0.20/0.50  % (10216)Time elapsed: 0.113 s
% 0.20/0.50  % (10216)------------------------------
% 0.20/0.50  % (10216)------------------------------
% 0.20/0.50  % (10222)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (10213)Success in time 0.157 s
%------------------------------------------------------------------------------
