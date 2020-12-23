%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:55 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 128 expanded)
%              Number of leaves         :   14 (  38 expanded)
%              Depth                    :   16
%              Number of atoms          :  192 ( 364 expanded)
%              Number of equality atoms :  115 ( 232 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f26,f101,f58])).

fof(f58,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f101,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f100,f51])).

fof(f51,plain,(
    k1_zfmisc_1(k1_xboole_0) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f25,f50])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f34,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f41,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f25,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(flattening,[],[f13])).

fof(f13,negated_conjecture,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f100,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(trivial_inequality_removal,[],[f97])).

fof(f97,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f53,f90])).

fof(f90,plain,(
    k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(trivial_inequality_removal,[],[f89])).

fof(f89,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f51,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(k1_xboole_0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)
      | sK1(X0,X1,k1_zfmisc_1(k1_xboole_0)) = X0
      | sK1(X0,X1,k1_zfmisc_1(k1_xboole_0)) = X1
      | k1_xboole_0 = sK1(X0,X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f82,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK1(X0,X1,k1_zfmisc_1(X2)),X2)
      | sK1(X0,X1,k1_zfmisc_1(X2)) = X0
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k1_zfmisc_1(X2)
      | sK1(X0,X1,k1_zfmisc_1(X2)) = X1 ) ),
    inference(resolution,[],[f54,f59])).

fof(f59,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X2)
      | sK1(X0,X1,X2) = X1
      | sK1(X0,X1,X2) = X0
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2 ) ),
    inference(definition_unfolding,[],[f38,f49])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK1(X0,X1,X2) = X1
      | sK1(X0,X1,X2) = X0
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sK1(X0,X1,X2) != X0
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f39,f49])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK1(X0,X1,X2) != X0
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f26,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n024.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 10:55:06 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.42  % (1404)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.18/0.45  % (1421)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.18/0.47  % (1412)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.18/0.47  % (1421)Refutation found. Thanks to Tanya!
% 0.18/0.47  % SZS status Theorem for theBenchmark
% 0.18/0.47  % SZS output start Proof for theBenchmark
% 0.18/0.47  fof(f102,plain,(
% 0.18/0.47    $false),
% 0.18/0.47    inference(unit_resulting_resolution,[],[f26,f101,f58])).
% 0.18/0.47  fof(f58,plain,(
% 0.18/0.47    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.18/0.47    inference(equality_resolution,[],[f31])).
% 0.18/0.47  fof(f31,plain,(
% 0.18/0.47    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.18/0.47    inference(cnf_transformation,[],[f19])).
% 0.18/0.47  fof(f19,plain,(
% 0.18/0.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.18/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 0.18/0.47  fof(f18,plain,(
% 0.18/0.47    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 0.18/0.47    introduced(choice_axiom,[])).
% 0.18/0.47  fof(f17,plain,(
% 0.18/0.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.18/0.47    inference(rectify,[],[f16])).
% 0.18/0.47  fof(f16,plain,(
% 0.18/0.47    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.18/0.47    inference(nnf_transformation,[],[f11])).
% 0.18/0.47  fof(f11,axiom,(
% 0.18/0.47    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.18/0.47  fof(f101,plain,(
% 0.18/0.47    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.18/0.47    inference(subsumption_resolution,[],[f100,f51])).
% 0.18/0.47  fof(f51,plain,(
% 0.18/0.47    k1_zfmisc_1(k1_xboole_0) != k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.18/0.47    inference(definition_unfolding,[],[f25,f50])).
% 0.18/0.47  fof(f50,plain,(
% 0.18/0.47    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.18/0.47    inference(definition_unfolding,[],[f27,f49])).
% 0.18/0.47  fof(f49,plain,(
% 0.18/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.18/0.47    inference(definition_unfolding,[],[f29,f48])).
% 0.18/0.47  fof(f48,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.18/0.47    inference(definition_unfolding,[],[f34,f47])).
% 0.18/0.47  fof(f47,plain,(
% 0.18/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.18/0.47    inference(definition_unfolding,[],[f41,f46])).
% 0.18/0.47  fof(f46,plain,(
% 0.18/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.18/0.47    inference(definition_unfolding,[],[f42,f45])).
% 0.18/0.47  fof(f45,plain,(
% 0.18/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.18/0.47    inference(definition_unfolding,[],[f43,f44])).
% 0.18/0.47  fof(f44,plain,(
% 0.18/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f10])).
% 0.18/0.47  fof(f10,axiom,(
% 0.18/0.47    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.18/0.47  fof(f43,plain,(
% 0.18/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f9])).
% 0.18/0.47  fof(f9,axiom,(
% 0.18/0.47    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.18/0.47  fof(f42,plain,(
% 0.18/0.47    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f8])).
% 0.18/0.47  fof(f8,axiom,(
% 0.18/0.47    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.18/0.47  fof(f41,plain,(
% 0.18/0.47    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f7])).
% 0.18/0.47  fof(f7,axiom,(
% 0.18/0.47    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.18/0.47  fof(f34,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f6])).
% 0.18/0.47  fof(f6,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.18/0.47  fof(f29,plain,(
% 0.18/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f5])).
% 0.18/0.47  fof(f5,axiom,(
% 0.18/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.18/0.47  fof(f27,plain,(
% 0.18/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f4])).
% 0.18/0.47  fof(f4,axiom,(
% 0.18/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.18/0.47  fof(f25,plain,(
% 0.18/0.47    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0)),
% 0.18/0.47    inference(cnf_transformation,[],[f14])).
% 0.18/0.47  fof(f14,plain,(
% 0.18/0.47    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0)),
% 0.18/0.47    inference(flattening,[],[f13])).
% 0.18/0.47  fof(f13,negated_conjecture,(
% 0.18/0.47    ~k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.18/0.47    inference(negated_conjecture,[],[f12])).
% 0.18/0.47  fof(f12,conjecture,(
% 0.18/0.47    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.18/0.47  fof(f100,plain,(
% 0.18/0.47    k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.18/0.47    inference(trivial_inequality_removal,[],[f97])).
% 0.18/0.47  fof(f97,plain,(
% 0.18/0.47    k1_xboole_0 != k1_xboole_0 | k1_zfmisc_1(k1_xboole_0) = k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.18/0.47    inference(superposition,[],[f53,f90])).
% 0.18/0.47  fof(f90,plain,(
% 0.18/0.47    k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.18/0.47    inference(trivial_inequality_removal,[],[f89])).
% 0.18/0.47  fof(f89,plain,(
% 0.18/0.47    k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.18/0.47    inference(duplicate_literal_removal,[],[f85])).
% 0.18/0.47  fof(f85,plain,(
% 0.18/0.47    k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1(k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.18/0.47    inference(superposition,[],[f51,f84])).
% 0.18/0.47  fof(f84,plain,(
% 0.18/0.47    ( ! [X0,X1] : (k1_zfmisc_1(k1_xboole_0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) | sK1(X0,X1,k1_zfmisc_1(k1_xboole_0)) = X0 | sK1(X0,X1,k1_zfmisc_1(k1_xboole_0)) = X1 | k1_xboole_0 = sK1(X0,X1,k1_zfmisc_1(k1_xboole_0))) )),
% 0.18/0.47    inference(resolution,[],[f82,f28])).
% 0.18/0.47  fof(f28,plain,(
% 0.18/0.47    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.18/0.47    inference(cnf_transformation,[],[f15])).
% 0.18/0.47  fof(f15,plain,(
% 0.18/0.47    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.18/0.47    inference(ennf_transformation,[],[f2])).
% 0.18/0.47  fof(f2,axiom,(
% 0.18/0.47    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.18/0.47  fof(f82,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (r1_tarski(sK1(X0,X1,k1_zfmisc_1(X2)),X2) | sK1(X0,X1,k1_zfmisc_1(X2)) = X0 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k1_zfmisc_1(X2) | sK1(X0,X1,k1_zfmisc_1(X2)) = X1) )),
% 0.18/0.47    inference(resolution,[],[f54,f59])).
% 0.18/0.47  fof(f59,plain,(
% 0.18/0.47    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 0.18/0.47    inference(equality_resolution,[],[f30])).
% 0.18/0.47  fof(f30,plain,(
% 0.18/0.47    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.18/0.47    inference(cnf_transformation,[],[f19])).
% 0.18/0.48  fof(f54,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X2) | sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2) )),
% 0.18/0.48    inference(definition_unfolding,[],[f38,f49])).
% 0.18/0.48  fof(f38,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f24])).
% 0.18/0.48  fof(f24,plain,(
% 0.18/0.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.18/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).
% 0.18/0.48  fof(f23,plain,(
% 0.18/0.48    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 0.18/0.48    introduced(choice_axiom,[])).
% 0.18/0.48  fof(f22,plain,(
% 0.18/0.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.18/0.48    inference(rectify,[],[f21])).
% 0.18/0.48  fof(f21,plain,(
% 0.18/0.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.18/0.48    inference(flattening,[],[f20])).
% 0.18/0.48  fof(f20,plain,(
% 0.18/0.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.18/0.48    inference(nnf_transformation,[],[f3])).
% 0.18/0.48  fof(f3,axiom,(
% 0.18/0.48    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.18/0.48  fof(f53,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (sK1(X0,X1,X2) != X0 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 0.18/0.48    inference(definition_unfolding,[],[f39,f49])).
% 0.18/0.48  fof(f39,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK1(X0,X1,X2) != X0 | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f24])).
% 0.18/0.48  fof(f26,plain,(
% 0.18/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f1])).
% 0.18/0.48  fof(f1,axiom,(
% 0.18/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.18/0.48  % SZS output end Proof for theBenchmark
% 0.18/0.48  % (1421)------------------------------
% 0.18/0.48  % (1421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (1421)Termination reason: Refutation
% 0.18/0.48  
% 0.18/0.48  % (1421)Memory used [KB]: 6268
% 0.18/0.48  % (1421)Time elapsed: 0.103 s
% 0.18/0.48  % (1421)------------------------------
% 0.18/0.48  % (1421)------------------------------
% 0.18/0.48  % (1398)Success in time 0.142 s
%------------------------------------------------------------------------------
