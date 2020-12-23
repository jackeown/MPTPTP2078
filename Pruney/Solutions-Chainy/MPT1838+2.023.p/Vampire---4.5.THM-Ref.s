%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:57 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 228 expanded)
%              Number of leaves         :   24 (  71 expanded)
%              Depth                    :   14
%              Number of atoms          :  315 ( 929 expanded)
%              Number of equality atoms :   74 ( 205 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f296,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f187,f222,f228,f292,f295])).

fof(f295,plain,(
    ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | ~ spl6_7 ),
    inference(trivial_inequality_removal,[],[f293])).

fof(f293,plain,
    ( sK1 != sK1
    | ~ spl6_7 ),
    inference(superposition,[],[f185,f118])).

fof(f118,plain,(
    sK1 = k1_tarski(sK2(sK1)) ),
    inference(forward_demodulation,[],[f117,f106])).

fof(f106,plain,(
    sK1 = k6_domain_1(sK1,sK2(sK1)) ),
    inference(subsumption_resolution,[],[f104,f64])).

fof(f64,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( sK0 != sK1
    & r1_tarski(sK0,sK1)
    & v1_zfmisc_1(sK1)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & r1_tarski(sK0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( sK0 != X1
        & r1_tarski(sK0,X1)
        & v1_zfmisc_1(X1)
        & ~ v1_xboole_0(X1) )
   => ( sK0 != sK1
      & r1_tarski(sK0,sK1)
      & v1_zfmisc_1(sK1)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f104,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f65,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f65,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f117,plain,(
    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) ),
    inference(subsumption_resolution,[],[f116,f64])).

fof(f116,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f105,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f105,plain,(
    m1_subset_1(sK2(sK1),sK1) ),
    inference(subsumption_resolution,[],[f103,f64])).

fof(f103,plain,
    ( m1_subset_1(sK2(sK1),sK1)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f65,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f185,plain,
    ( ! [X0] : k1_tarski(X0) != sK1
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl6_7
  <=> ! [X0] : k1_tarski(X0) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f292,plain,(
    ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f290,f63])).

fof(f63,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f290,plain,
    ( v1_xboole_0(sK0)
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f287,f100])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f287,plain,
    ( ~ r1_tarski(sK0,sK0)
    | v1_xboole_0(sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f283,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f283,plain,
    ( r1_xboole_0(sK0,sK0)
    | ~ spl6_6 ),
    inference(superposition,[],[f75,f182])).

fof(f182,plain,
    ( sK0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl6_6
  <=> sK0 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f75,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f228,plain,(
    ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f226,f67])).

fof(f67,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f226,plain,
    ( sK0 = sK1
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f224,f68])).

fof(f68,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f224,plain,
    ( sK1 = k2_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f111,f178])).

fof(f178,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl6_5
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f111,plain,(
    sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f66,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f66,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f222,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f196,f159])).

fof(f159,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(global_subsumption,[],[f109,f141,f149])).

fof(f149,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f123,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f123,plain,(
    r1_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[],[f75,f108])).

fof(f108,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f66,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f141,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f122,f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f59,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f122,plain,(
    r1_tarski(k1_xboole_0,sK0) ),
    inference(superposition,[],[f77,f108])).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f109,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f66,f90])).

fof(f196,plain,
    ( r2_hidden(sK3(k1_xboole_0),k1_xboole_0)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f101,f132])).

fof(f132,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f101,plain,(
    r2_hidden(sK3(sK0),sK0) ),
    inference(resolution,[],[f63,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f50,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f187,plain,
    ( spl6_5
    | spl6_6
    | spl6_2
    | spl6_7 ),
    inference(avatar_split_clause,[],[f172,f184,f131,f180,f176])).

fof(f172,plain,(
    ! [X0] :
      ( k1_tarski(X0) != sK1
      | k1_xboole_0 = sK0
      | sK0 = k4_xboole_0(sK1,sK0)
      | k1_xboole_0 = k4_xboole_0(sK1,sK0) ) ),
    inference(superposition,[],[f98,f111])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) != k1_tarski(X0)
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:49:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.51  % (2468)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.52  % (2461)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.18/0.53  % (2469)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.18/0.53  % (2484)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.18/0.54  % (2460)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.18/0.54  % (2466)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.18/0.55  % (2476)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.18/0.55  % (2475)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.18/0.55  % (2457)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.18/0.55  % (2464)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.18/0.55  % (2458)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.18/0.55  % (2459)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.18/0.56  % (2465)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.18/0.56  % (2477)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.18/0.56  % (2483)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.18/0.56  % (2464)Refutation found. Thanks to Tanya!
% 0.18/0.56  % SZS status Theorem for theBenchmark
% 0.18/0.56  % SZS output start Proof for theBenchmark
% 0.18/0.56  fof(f296,plain,(
% 0.18/0.56    $false),
% 0.18/0.56    inference(avatar_sat_refutation,[],[f187,f222,f228,f292,f295])).
% 0.18/0.56  fof(f295,plain,(
% 0.18/0.56    ~spl6_7),
% 0.18/0.56    inference(avatar_contradiction_clause,[],[f294])).
% 0.18/0.56  fof(f294,plain,(
% 0.18/0.56    $false | ~spl6_7),
% 0.18/0.56    inference(trivial_inequality_removal,[],[f293])).
% 0.18/0.56  fof(f293,plain,(
% 0.18/0.56    sK1 != sK1 | ~spl6_7),
% 0.18/0.56    inference(superposition,[],[f185,f118])).
% 0.18/0.56  fof(f118,plain,(
% 0.18/0.56    sK1 = k1_tarski(sK2(sK1))),
% 0.18/0.56    inference(forward_demodulation,[],[f117,f106])).
% 0.18/0.56  fof(f106,plain,(
% 0.18/0.56    sK1 = k6_domain_1(sK1,sK2(sK1))),
% 0.18/0.56    inference(subsumption_resolution,[],[f104,f64])).
% 0.18/0.56  fof(f64,plain,(
% 0.18/0.56    ~v1_xboole_0(sK1)),
% 0.18/0.56    inference(cnf_transformation,[],[f44])).
% 0.18/0.56  fof(f44,plain,(
% 0.18/0.56    (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.18/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f43,f42])).
% 0.18/0.56  fof(f42,plain,(
% 0.18/0.56    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.18/0.56    introduced(choice_axiom,[])).
% 0.18/0.56  fof(f43,plain,(
% 0.18/0.56    ? [X1] : (sK0 != X1 & r1_tarski(sK0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK0 != sK1 & r1_tarski(sK0,sK1) & v1_zfmisc_1(sK1) & ~v1_xboole_0(sK1))),
% 0.18/0.56    introduced(choice_axiom,[])).
% 0.18/0.56  fof(f25,plain,(
% 0.18/0.56    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.18/0.56    inference(flattening,[],[f24])).
% 0.18/0.56  fof(f24,plain,(
% 0.18/0.56    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 0.18/0.56    inference(ennf_transformation,[],[f22])).
% 0.18/0.56  fof(f22,negated_conjecture,(
% 0.18/0.56    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.18/0.56    inference(negated_conjecture,[],[f21])).
% 0.18/0.56  fof(f21,conjecture,(
% 0.18/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.18/0.56  fof(f104,plain,(
% 0.18/0.56    sK1 = k6_domain_1(sK1,sK2(sK1)) | v1_xboole_0(sK1)),
% 0.18/0.56    inference(resolution,[],[f65,f70])).
% 0.18/0.56  fof(f70,plain,(
% 0.18/0.56    ( ! [X0] : (~v1_zfmisc_1(X0) | k6_domain_1(X0,sK2(X0)) = X0 | v1_xboole_0(X0)) )),
% 0.18/0.56    inference(cnf_transformation,[],[f48])).
% 0.18/0.56  fof(f48,plain,(
% 0.18/0.56    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.18/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).
% 0.18/0.56  fof(f47,plain,(
% 0.18/0.56    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK2(X0)) = X0 & m1_subset_1(sK2(X0),X0)))),
% 0.18/0.56    introduced(choice_axiom,[])).
% 0.18/0.56  fof(f46,plain,(
% 0.18/0.56    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.18/0.56    inference(rectify,[],[f45])).
% 0.18/0.56  fof(f45,plain,(
% 0.18/0.56    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.18/0.56    inference(nnf_transformation,[],[f26])).
% 0.18/0.56  fof(f26,plain,(
% 0.18/0.56    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.18/0.56    inference(ennf_transformation,[],[f20])).
% 0.18/0.56  fof(f20,axiom,(
% 0.18/0.56    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
% 0.18/0.56  fof(f65,plain,(
% 0.18/0.56    v1_zfmisc_1(sK1)),
% 0.18/0.56    inference(cnf_transformation,[],[f44])).
% 0.18/0.56  fof(f117,plain,(
% 0.18/0.56    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))),
% 0.18/0.56    inference(subsumption_resolution,[],[f116,f64])).
% 0.18/0.56  fof(f116,plain,(
% 0.18/0.56    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | v1_xboole_0(sK1)),
% 0.18/0.56    inference(resolution,[],[f105,f84])).
% 0.18/0.56  fof(f84,plain,(
% 0.18/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 0.18/0.56    inference(cnf_transformation,[],[f34])).
% 0.18/0.56  fof(f34,plain,(
% 0.18/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.18/0.56    inference(flattening,[],[f33])).
% 0.18/0.56  fof(f33,plain,(
% 0.18/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.18/0.56    inference(ennf_transformation,[],[f19])).
% 0.18/0.56  fof(f19,axiom,(
% 0.18/0.56    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.18/0.56  fof(f105,plain,(
% 0.18/0.56    m1_subset_1(sK2(sK1),sK1)),
% 0.18/0.56    inference(subsumption_resolution,[],[f103,f64])).
% 0.18/0.56  fof(f103,plain,(
% 0.18/0.56    m1_subset_1(sK2(sK1),sK1) | v1_xboole_0(sK1)),
% 0.18/0.56    inference(resolution,[],[f65,f69])).
% 0.18/0.56  fof(f69,plain,(
% 0.18/0.56    ( ! [X0] : (~v1_zfmisc_1(X0) | m1_subset_1(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.18/0.56    inference(cnf_transformation,[],[f48])).
% 0.18/0.56  fof(f185,plain,(
% 0.18/0.56    ( ! [X0] : (k1_tarski(X0) != sK1) ) | ~spl6_7),
% 0.18/0.56    inference(avatar_component_clause,[],[f184])).
% 0.18/0.56  fof(f184,plain,(
% 0.18/0.56    spl6_7 <=> ! [X0] : k1_tarski(X0) != sK1),
% 0.18/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.18/0.56  fof(f292,plain,(
% 0.18/0.56    ~spl6_6),
% 0.18/0.56    inference(avatar_contradiction_clause,[],[f291])).
% 0.18/0.56  fof(f291,plain,(
% 0.18/0.56    $false | ~spl6_6),
% 0.18/0.56    inference(subsumption_resolution,[],[f290,f63])).
% 0.18/0.56  fof(f63,plain,(
% 0.18/0.56    ~v1_xboole_0(sK0)),
% 0.18/0.56    inference(cnf_transformation,[],[f44])).
% 0.18/0.56  fof(f290,plain,(
% 0.18/0.56    v1_xboole_0(sK0) | ~spl6_6),
% 0.18/0.56    inference(subsumption_resolution,[],[f287,f100])).
% 0.18/0.56  fof(f100,plain,(
% 0.18/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.18/0.56    inference(equality_resolution,[],[f85])).
% 0.18/0.56  fof(f85,plain,(
% 0.18/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.18/0.56    inference(cnf_transformation,[],[f56])).
% 0.18/0.56  fof(f56,plain,(
% 0.18/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.18/0.56    inference(flattening,[],[f55])).
% 0.18/0.56  fof(f55,plain,(
% 0.18/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.18/0.56    inference(nnf_transformation,[],[f6])).
% 0.18/0.56  fof(f6,axiom,(
% 0.18/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.18/0.56  fof(f287,plain,(
% 0.18/0.56    ~r1_tarski(sK0,sK0) | v1_xboole_0(sK0) | ~spl6_6),
% 0.18/0.56    inference(resolution,[],[f283,f81])).
% 0.18/0.56  fof(f81,plain,(
% 0.18/0.56    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.18/0.56    inference(cnf_transformation,[],[f30])).
% 0.18/0.56  fof(f30,plain,(
% 0.18/0.56    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.18/0.56    inference(flattening,[],[f29])).
% 0.18/0.56  fof(f29,plain,(
% 0.18/0.56    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.18/0.56    inference(ennf_transformation,[],[f14])).
% 0.18/0.56  fof(f14,axiom,(
% 0.18/0.56    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.18/0.56  fof(f283,plain,(
% 0.18/0.56    r1_xboole_0(sK0,sK0) | ~spl6_6),
% 0.18/0.56    inference(superposition,[],[f75,f182])).
% 0.18/0.56  fof(f182,plain,(
% 0.18/0.56    sK0 = k4_xboole_0(sK1,sK0) | ~spl6_6),
% 0.18/0.56    inference(avatar_component_clause,[],[f180])).
% 0.18/0.56  fof(f180,plain,(
% 0.18/0.56    spl6_6 <=> sK0 = k4_xboole_0(sK1,sK0)),
% 0.18/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.18/0.56  fof(f75,plain,(
% 0.18/0.56    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.18/0.56    inference(cnf_transformation,[],[f15])).
% 0.18/0.56  fof(f15,axiom,(
% 0.18/0.56    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.18/0.56  fof(f228,plain,(
% 0.18/0.56    ~spl6_5),
% 0.18/0.56    inference(avatar_contradiction_clause,[],[f227])).
% 0.18/0.56  fof(f227,plain,(
% 0.18/0.56    $false | ~spl6_5),
% 0.18/0.56    inference(subsumption_resolution,[],[f226,f67])).
% 0.18/0.56  fof(f67,plain,(
% 0.18/0.56    sK0 != sK1),
% 0.18/0.56    inference(cnf_transformation,[],[f44])).
% 0.18/0.56  fof(f226,plain,(
% 0.18/0.56    sK0 = sK1 | ~spl6_5),
% 0.18/0.56    inference(forward_demodulation,[],[f224,f68])).
% 0.18/0.56  fof(f68,plain,(
% 0.18/0.56    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.18/0.56    inference(cnf_transformation,[],[f8])).
% 0.18/0.56  fof(f8,axiom,(
% 0.18/0.56    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.18/0.56  fof(f224,plain,(
% 0.18/0.56    sK1 = k2_xboole_0(sK0,k1_xboole_0) | ~spl6_5),
% 0.18/0.56    inference(backward_demodulation,[],[f111,f178])).
% 0.18/0.56  fof(f178,plain,(
% 0.18/0.56    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl6_5),
% 0.18/0.56    inference(avatar_component_clause,[],[f176])).
% 0.18/0.56  fof(f176,plain,(
% 0.18/0.56    spl6_5 <=> k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.18/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.18/0.56  fof(f111,plain,(
% 0.18/0.56    sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.18/0.56    inference(resolution,[],[f66,f83])).
% 0.18/0.56  fof(f83,plain,(
% 0.18/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 0.18/0.56    inference(cnf_transformation,[],[f32])).
% 0.18/0.56  fof(f32,plain,(
% 0.18/0.56    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.18/0.56    inference(ennf_transformation,[],[f12])).
% 0.18/0.56  fof(f12,axiom,(
% 0.18/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.18/0.56  fof(f66,plain,(
% 0.18/0.56    r1_tarski(sK0,sK1)),
% 0.18/0.56    inference(cnf_transformation,[],[f44])).
% 0.18/0.56  fof(f222,plain,(
% 0.18/0.56    ~spl6_2),
% 0.18/0.56    inference(avatar_contradiction_clause,[],[f221])).
% 0.18/0.56  fof(f221,plain,(
% 0.18/0.56    $false | ~spl6_2),
% 0.18/0.56    inference(subsumption_resolution,[],[f196,f159])).
% 0.18/0.56  fof(f159,plain,(
% 0.18/0.56    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.18/0.56    inference(global_subsumption,[],[f109,f141,f149])).
% 0.18/0.56  fof(f149,plain,(
% 0.18/0.56    ( ! [X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.18/0.56    inference(resolution,[],[f123,f80])).
% 0.18/0.56  fof(f80,plain,(
% 0.18/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.18/0.56    inference(cnf_transformation,[],[f54])).
% 0.18/0.56  fof(f54,plain,(
% 0.18/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.18/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f53])).
% 0.18/0.56  fof(f53,plain,(
% 0.18/0.56    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.18/0.56    introduced(choice_axiom,[])).
% 0.18/0.56  fof(f28,plain,(
% 0.18/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.18/0.56    inference(ennf_transformation,[],[f23])).
% 0.18/0.56  fof(f23,plain,(
% 0.18/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.18/0.56    inference(rectify,[],[f5])).
% 0.18/0.56  fof(f5,axiom,(
% 0.18/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.18/0.56  fof(f123,plain,(
% 0.18/0.56    r1_xboole_0(k1_xboole_0,sK1)),
% 0.18/0.56    inference(superposition,[],[f75,f108])).
% 0.18/0.56  fof(f108,plain,(
% 0.18/0.56    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.18/0.56    inference(resolution,[],[f66,f94])).
% 0.18/0.56  fof(f94,plain,(
% 0.18/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.18/0.56    inference(cnf_transformation,[],[f62])).
% 0.18/0.56  fof(f62,plain,(
% 0.18/0.56    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.18/0.56    inference(nnf_transformation,[],[f7])).
% 0.18/0.56  fof(f7,axiom,(
% 0.18/0.56    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.18/0.56  fof(f141,plain,(
% 0.18/0.56    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,sK0)) )),
% 0.18/0.56    inference(resolution,[],[f122,f90])).
% 0.18/0.56  fof(f90,plain,(
% 0.18/0.56    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.18/0.56    inference(cnf_transformation,[],[f61])).
% 0.18/0.56  fof(f61,plain,(
% 0.18/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.18/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f59,f60])).
% 0.18/0.56  fof(f60,plain,(
% 0.18/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.18/0.56    introduced(choice_axiom,[])).
% 0.18/0.56  fof(f59,plain,(
% 0.18/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.18/0.56    inference(rectify,[],[f58])).
% 0.18/0.56  fof(f58,plain,(
% 0.18/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.18/0.56    inference(nnf_transformation,[],[f35])).
% 0.18/0.56  fof(f35,plain,(
% 0.18/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.18/0.56    inference(ennf_transformation,[],[f2])).
% 0.18/0.56  fof(f2,axiom,(
% 0.18/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.18/0.56  fof(f122,plain,(
% 0.18/0.56    r1_tarski(k1_xboole_0,sK0)),
% 0.18/0.56    inference(superposition,[],[f77,f108])).
% 0.18/0.56  fof(f77,plain,(
% 0.18/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.18/0.56    inference(cnf_transformation,[],[f10])).
% 0.18/0.56  fof(f10,axiom,(
% 0.18/0.56    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.18/0.56  fof(f109,plain,(
% 0.18/0.56    ( ! [X1] : (r2_hidden(X1,sK1) | ~r2_hidden(X1,sK0)) )),
% 0.18/0.56    inference(resolution,[],[f66,f90])).
% 0.18/0.56  fof(f196,plain,(
% 0.18/0.56    r2_hidden(sK3(k1_xboole_0),k1_xboole_0) | ~spl6_2),
% 0.18/0.56    inference(backward_demodulation,[],[f101,f132])).
% 0.18/0.56  fof(f132,plain,(
% 0.18/0.56    k1_xboole_0 = sK0 | ~spl6_2),
% 0.18/0.56    inference(avatar_component_clause,[],[f131])).
% 0.18/0.56  fof(f131,plain,(
% 0.18/0.56    spl6_2 <=> k1_xboole_0 = sK0),
% 0.18/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.18/0.56  fof(f101,plain,(
% 0.18/0.56    r2_hidden(sK3(sK0),sK0)),
% 0.18/0.56    inference(resolution,[],[f63,f74])).
% 0.18/0.56  fof(f74,plain,(
% 0.18/0.56    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 0.18/0.56    inference(cnf_transformation,[],[f52])).
% 0.18/0.56  fof(f52,plain,(
% 0.18/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.18/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f50,f51])).
% 0.18/0.56  fof(f51,plain,(
% 0.18/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.18/0.56    introduced(choice_axiom,[])).
% 0.18/0.56  fof(f50,plain,(
% 0.18/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.18/0.56    inference(rectify,[],[f49])).
% 0.18/0.56  fof(f49,plain,(
% 0.18/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.18/0.56    inference(nnf_transformation,[],[f1])).
% 0.18/0.56  fof(f1,axiom,(
% 0.18/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.18/0.56  fof(f187,plain,(
% 0.18/0.56    spl6_5 | spl6_6 | spl6_2 | spl6_7),
% 0.18/0.56    inference(avatar_split_clause,[],[f172,f184,f131,f180,f176])).
% 0.18/0.56  fof(f172,plain,(
% 0.18/0.56    ( ! [X0] : (k1_tarski(X0) != sK1 | k1_xboole_0 = sK0 | sK0 = k4_xboole_0(sK1,sK0) | k1_xboole_0 = k4_xboole_0(sK1,sK0)) )),
% 0.18/0.56    inference(superposition,[],[f98,f111])).
% 0.18/0.56  fof(f98,plain,(
% 0.18/0.56    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) != k1_tarski(X0) | k1_xboole_0 = X1 | X1 = X2 | k1_xboole_0 = X2) )),
% 0.18/0.56    inference(cnf_transformation,[],[f41])).
% 0.18/0.56  fof(f41,plain,(
% 0.18/0.56    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k2_xboole_0(X1,X2) != k1_tarski(X0))),
% 0.18/0.56    inference(ennf_transformation,[],[f18])).
% 0.18/0.56  fof(f18,axiom,(
% 0.18/0.56    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 0.18/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.18/0.56  % SZS output end Proof for theBenchmark
% 0.18/0.56  % (2464)------------------------------
% 0.18/0.56  % (2464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.56  % (2464)Termination reason: Refutation
% 0.18/0.56  
% 0.18/0.56  % (2464)Memory used [KB]: 10746
% 0.18/0.56  % (2464)Time elapsed: 0.142 s
% 0.18/0.56  % (2464)------------------------------
% 0.18/0.56  % (2464)------------------------------
% 0.18/0.57  % (2485)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.18/0.57  % (2481)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.18/0.57  % (2472)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.18/0.57  % (2474)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.18/0.57  % (2467)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.18/0.57  % (2473)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.18/0.58  % (2455)Success in time 0.231 s
%------------------------------------------------------------------------------
