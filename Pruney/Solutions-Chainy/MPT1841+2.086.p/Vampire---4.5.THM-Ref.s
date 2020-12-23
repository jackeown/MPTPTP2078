%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 130 expanded)
%              Number of leaves         :   22 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  402 ( 578 expanded)
%              Number of equality atoms :  240 ( 240 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f177,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f127,f176])).

fof(f176,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f160,f105])).

fof(f105,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f48,f86])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f48,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f160,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl3_1 ),
    inference(superposition,[],[f103,f152])).

fof(f152,plain,
    ( k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f130,f131])).

fof(f131,plain,
    ( k1_xboole_0 = k6_domain_1(sK0,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f118,f107])).

fof(f107,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f55,f44])).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f118,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl3_1
  <=> v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f130,plain,(
    k6_domain_1(sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f128,f40])).

fof(f40,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f128,plain,
    ( k6_domain_1(sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f85,f41])).

fof(f41,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f50,f84])).

fof(f84,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f83])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f57,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f58,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f103,plain,(
    ! [X6,X4,X2,X10,X7,X5,X3,X1] : r2_hidden(X10,k6_enumset1(X10,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X6,X4,X2,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | k6_enumset1(X10,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | X0 != X10
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ( ( ( sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7
              & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6
              & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5
              & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4
              & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3
              & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2
              & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1
              & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7
            | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6
            | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5
            | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4
            | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3
            | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2
            | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1
            | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0
            | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ( X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 ) )
            & ( X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | ~ r2_hidden(X10,X8) ) )
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

% (19646)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f38,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 )
            | ~ r2_hidden(X9,X8) )
          & ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9
            | r2_hidden(X9,X8) ) )
     => ( ( ( sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7
            & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6
            & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5
            & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4
            & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3
            & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2
            & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1
            & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7
          | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6
          | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5
          | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4
          | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3
          | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2
          | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1
          | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0
          | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ( X7 != X10
                & X6 != X10
                & X5 != X10
                & X4 != X10
                & X3 != X10
                & X2 != X10
                & X1 != X10
                & X0 != X10 ) )
            & ( X7 = X10
              | X6 = X10
              | X5 = X10
              | X4 = X10
              | X3 = X10
              | X2 = X10
              | X1 = X10
              | X0 = X10
              | ~ r2_hidden(X10,X8) ) )
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X8) ) )
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X8) ) )
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f29])).

% (19621)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

fof(f127,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f125,f40])).

fof(f125,plain,
    ( v1_xboole_0(sK0)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f124,f41])).

fof(f124,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | spl3_2 ),
    inference(resolution,[],[f122,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f122,plain,
    ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl3_2
  <=> m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f123,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f114,f120,f116])).

fof(f114,plain,
    ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    inference(resolution,[],[f113,f42])).

fof(f42,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f113,plain,(
    ! [X0] :
      ( ~ v1_subset_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f112,f43])).

fof(f43,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f47,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:01:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.50  % (19619)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (19629)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (19633)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (19629)Refutation not found, incomplete strategy% (19629)------------------------------
% 0.20/0.53  % (19629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (19629)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (19629)Memory used [KB]: 10618
% 0.20/0.53  % (19629)Time elapsed: 0.113 s
% 0.20/0.53  % (19629)------------------------------
% 0.20/0.53  % (19629)------------------------------
% 0.20/0.53  % (19622)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (19622)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f177,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f123,f127,f176])).
% 0.20/0.54  fof(f176,plain,(
% 0.20/0.54    ~spl3_1),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f175])).
% 0.20/0.54  fof(f175,plain,(
% 0.20/0.54    $false | ~spl3_1),
% 0.20/0.54    inference(subsumption_resolution,[],[f160,f105])).
% 0.20/0.54  fof(f105,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.54    inference(superposition,[],[f48,f86])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.54    inference(equality_resolution,[],[f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.54    inference(flattening,[],[f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.54    inference(nnf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.20/0.54  fof(f160,plain,(
% 0.20/0.54    r2_hidden(sK1,k1_xboole_0) | ~spl3_1),
% 0.20/0.54    inference(superposition,[],[f103,f152])).
% 0.20/0.54  fof(f152,plain,(
% 0.20/0.54    k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl3_1),
% 0.20/0.54    inference(forward_demodulation,[],[f130,f131])).
% 0.20/0.54  fof(f131,plain,(
% 0.20/0.54    k1_xboole_0 = k6_domain_1(sK0,sK1) | ~spl3_1),
% 0.20/0.54    inference(resolution,[],[f118,f107])).
% 0.20/0.54  fof(f107,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(resolution,[],[f55,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    v1_xboole_0(k1_xboole_0)),
% 0.20/0.54    inference(cnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    v1_xboole_0(k1_xboole_0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.20/0.54  fof(f118,plain,(
% 0.20/0.54    v1_xboole_0(k6_domain_1(sK0,sK1)) | ~spl3_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f116])).
% 0.20/0.54  fof(f116,plain,(
% 0.20/0.54    spl3_1 <=> v1_xboole_0(k6_domain_1(sK0,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.54  fof(f130,plain,(
% 0.20/0.54    k6_domain_1(sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 0.20/0.54    inference(subsumption_resolution,[],[f128,f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ~v1_xboole_0(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f31,f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.54    inference(flattening,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,negated_conjecture,(
% 0.20/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.54    inference(negated_conjecture,[],[f17])).
% 0.20/0.54  fof(f17,conjecture,(
% 0.20/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.20/0.54  fof(f128,plain,(
% 0.20/0.54    k6_domain_1(sK0,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | v1_xboole_0(sK0)),
% 0.20/0.54    inference(resolution,[],[f85,f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    m1_subset_1(sK1,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f50,f84])).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f45,f83])).
% 0.20/0.54  fof(f83,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f49,f82])).
% 0.20/0.54  fof(f82,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f56,f81])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f57,f80])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f58,f79])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f59,f60])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.54    inference(flattening,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.54  fof(f103,plain,(
% 0.20/0.54    ( ! [X6,X4,X2,X10,X7,X5,X3,X1] : (r2_hidden(X10,k6_enumset1(X10,X1,X2,X3,X4,X5,X6,X7))) )),
% 0.20/0.54    inference(equality_resolution,[],[f102])).
% 0.20/0.54  fof(f102,plain,(
% 0.20/0.54    ( ! [X6,X4,X2,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | k6_enumset1(X10,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 0.20/0.54    inference(equality_resolution,[],[f62])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | X0 != X10 | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 0.20/0.54    inference(cnf_transformation,[],[f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | (((sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0 | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | (X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~r2_hidden(X10,X8))) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 0.20/0.54  % (19646)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | r2_hidden(X9,X8))) => (((sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1 & sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1 | sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0 | r2_hidden(sK2(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | (X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)) & (X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10 | ~r2_hidden(X10,X8))) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 0.20/0.54    inference(rectify,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~r2_hidden(X9,X8))) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 0.20/0.54    inference(flattening,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~r2_hidden(X9,X8))) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 0.20/0.54    inference(nnf_transformation,[],[f29])).
% 0.20/0.54  % (19621)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).
% 0.20/0.54  fof(f127,plain,(
% 0.20/0.54    spl3_2),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f126])).
% 0.20/0.54  fof(f126,plain,(
% 0.20/0.54    $false | spl3_2),
% 0.20/0.54    inference(subsumption_resolution,[],[f125,f40])).
% 0.20/0.54  fof(f125,plain,(
% 0.20/0.54    v1_xboole_0(sK0) | spl3_2),
% 0.20/0.54    inference(subsumption_resolution,[],[f124,f41])).
% 0.20/0.54  fof(f124,plain,(
% 0.20/0.54    ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0) | spl3_2),
% 0.20/0.54    inference(resolution,[],[f122,f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.54    inference(flattening,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,axiom,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.54  fof(f122,plain,(
% 0.20/0.54    ~m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | spl3_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f120])).
% 0.20/0.54  fof(f120,plain,(
% 0.20/0.54    spl3_2 <=> m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.54  fof(f123,plain,(
% 0.20/0.54    spl3_1 | ~spl3_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f114,f120,f116])).
% 0.20/0.54  fof(f114,plain,(
% 0.20/0.54    ~m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k6_domain_1(sK0,sK1))),
% 0.20/0.54    inference(resolution,[],[f113,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  fof(f113,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_subset_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(resolution,[],[f112,f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    v1_zfmisc_1(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  fof(f112,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f47,f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.54    inference(flattening,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,axiom,(
% 0.20/0.54    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (19622)------------------------------
% 0.20/0.54  % (19622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (19622)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (19622)Memory used [KB]: 10746
% 0.20/0.54  % (19622)Time elapsed: 0.130 s
% 0.20/0.54  % (19622)------------------------------
% 0.20/0.54  % (19622)------------------------------
% 0.20/0.55  % (19618)Success in time 0.197 s
%------------------------------------------------------------------------------
