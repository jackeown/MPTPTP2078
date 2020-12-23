%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:21 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 100 expanded)
%              Number of leaves         :   13 (  27 expanded)
%              Depth                    :   14
%              Number of atoms          :  192 ( 315 expanded)
%              Number of equality atoms :   47 (  81 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f268,plain,(
    $false ),
    inference(global_subsumption,[],[f31,f264])).

fof(f264,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f121,f62])).

fof(f62,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k1_relat_1(sK1))) ),
    inference(superposition,[],[f56,f50])).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f32,f34,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f56,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0)) ),
    inference(resolution,[],[f29,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f39,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK0 != k1_relat_1(k7_relat_1(sK1,sK0))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( sK0 != k1_relat_1(k7_relat_1(sK1,sK0))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f121,plain,(
    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1))) ),
    inference(superposition,[],[f80,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f49])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f80,plain,(
    ! [X3] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X3,k1_relat_1(sK1))) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X3] :
      ( sK0 = k4_xboole_0(sK0,k4_xboole_0(X3,k1_relat_1(sK1)))
      | sK0 = k4_xboole_0(sK0,k4_xboole_0(X3,k1_relat_1(sK1))) ) ),
    inference(resolution,[],[f69,f64])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_relat_1(sK1),X0),k1_relat_1(sK1))
      | sK0 = k4_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f58,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f58,plain,(
    ! [X0] :
      ( r1_xboole_0(sK0,X0)
      | r2_hidden(sK2(k1_relat_1(sK1),X0),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f57,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f57,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_relat_1(sK1),X0)
      | r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f30,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f30,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK2(k1_relat_1(sK1),k4_xboole_0(X2,X3)),X3)
      | sK0 = k4_xboole_0(sK0,k4_xboole_0(X2,X3)) ) ),
    inference(resolution,[],[f60,f54])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_relat_1(sK1),X0),X0)
      | sK0 = k4_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f59,f40])).

fof(f59,plain,(
    ! [X1] :
      ( r1_xboole_0(sK0,X1)
      | r2_hidden(sK2(k1_relat_1(sK1),X1),X1) ) ),
    inference(resolution,[],[f57,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f31,plain,(
    sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:57:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (32336)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (32328)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (32324)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (32323)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (32327)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (32344)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (32351)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (32326)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (32325)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (32322)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (32343)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (32344)Refutation not found, incomplete strategy% (32344)------------------------------
% 0.22/0.55  % (32344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32344)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32344)Memory used [KB]: 10618
% 0.22/0.55  % (32344)Time elapsed: 0.128 s
% 0.22/0.55  % (32344)------------------------------
% 0.22/0.55  % (32344)------------------------------
% 0.22/0.55  % (32341)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (32342)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (32345)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (32342)Refutation not found, incomplete strategy% (32342)------------------------------
% 0.22/0.55  % (32342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32342)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32342)Memory used [KB]: 10746
% 0.22/0.55  % (32342)Time elapsed: 0.136 s
% 0.22/0.55  % (32342)------------------------------
% 0.22/0.55  % (32342)------------------------------
% 1.42/0.55  % (32330)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.42/0.55  % (32332)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.42/0.55  % (32335)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.42/0.56  % (32333)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.42/0.56  % (32334)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.56  % (32337)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.42/0.56  % (32333)Refutation not found, incomplete strategy% (32333)------------------------------
% 1.42/0.56  % (32333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (32333)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (32333)Memory used [KB]: 10618
% 1.42/0.56  % (32333)Time elapsed: 0.147 s
% 1.42/0.56  % (32333)------------------------------
% 1.42/0.56  % (32333)------------------------------
% 1.42/0.56  % (32324)Refutation found. Thanks to Tanya!
% 1.42/0.56  % SZS status Theorem for theBenchmark
% 1.42/0.56  % SZS output start Proof for theBenchmark
% 1.42/0.56  fof(f268,plain,(
% 1.42/0.56    $false),
% 1.42/0.56    inference(global_subsumption,[],[f31,f264])).
% 1.42/0.56  fof(f264,plain,(
% 1.42/0.56    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.42/0.56    inference(superposition,[],[f121,f62])).
% 1.42/0.56  fof(f62,plain,(
% 1.42/0.56    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k1_relat_1(sK1)))) )),
% 1.42/0.56    inference(superposition,[],[f56,f50])).
% 1.42/0.56  fof(f50,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.42/0.56    inference(definition_unfolding,[],[f32,f34,f34])).
% 1.42/0.56  fof(f34,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f7])).
% 1.42/0.56  fof(f7,axiom,(
% 1.42/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.42/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.42/0.56  fof(f32,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f6])).
% 1.42/0.56  fof(f6,axiom,(
% 1.42/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.42/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.42/0.56  fof(f56,plain,(
% 1.42/0.56    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),X0))) )),
% 1.42/0.56    inference(resolution,[],[f29,f52])).
% 1.42/0.56  fof(f52,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 1.42/0.56    inference(definition_unfolding,[],[f39,f49])).
% 1.42/0.56  fof(f49,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.42/0.56    inference(definition_unfolding,[],[f33,f34])).
% 1.42/0.56  fof(f33,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.42/0.56    inference(cnf_transformation,[],[f8])).
% 1.42/0.56  fof(f8,axiom,(
% 1.42/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.42/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.42/0.56  fof(f39,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f16])).
% 1.42/0.56  fof(f16,plain,(
% 1.42/0.56    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.42/0.56    inference(ennf_transformation,[],[f9])).
% 1.42/0.56  fof(f9,axiom,(
% 1.42/0.56    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.42/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 1.42/0.56  fof(f29,plain,(
% 1.42/0.56    v1_relat_1(sK1)),
% 1.42/0.56    inference(cnf_transformation,[],[f20])).
% 1.42/0.56  fof(f20,plain,(
% 1.42/0.56    sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.42/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f19])).
% 1.42/0.56  fof(f19,plain,(
% 1.42/0.56    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f14,plain,(
% 1.42/0.56    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.42/0.56    inference(flattening,[],[f13])).
% 1.42/0.56  fof(f13,plain,(
% 1.42/0.56    ? [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.42/0.56    inference(ennf_transformation,[],[f11])).
% 1.42/0.56  fof(f11,negated_conjecture,(
% 1.42/0.56    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.42/0.56    inference(negated_conjecture,[],[f10])).
% 1.42/0.56  fof(f10,conjecture,(
% 1.42/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.42/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.42/0.56  fof(f121,plain,(
% 1.42/0.56    sK0 = k1_setfam_1(k1_enumset1(sK0,sK0,k1_relat_1(sK1)))),
% 1.42/0.56    inference(superposition,[],[f80,f51])).
% 1.42/0.56  fof(f51,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.42/0.56    inference(definition_unfolding,[],[f35,f49])).
% 1.42/0.56  fof(f35,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f3])).
% 1.42/0.56  fof(f3,axiom,(
% 1.42/0.56    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.42/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.42/0.56  fof(f80,plain,(
% 1.42/0.56    ( ! [X3] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X3,k1_relat_1(sK1)))) )),
% 1.42/0.56    inference(duplicate_literal_removal,[],[f77])).
% 1.42/0.56  fof(f77,plain,(
% 1.42/0.56    ( ! [X3] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X3,k1_relat_1(sK1))) | sK0 = k4_xboole_0(sK0,k4_xboole_0(X3,k1_relat_1(sK1)))) )),
% 1.42/0.56    inference(resolution,[],[f69,f64])).
% 1.42/0.56  fof(f64,plain,(
% 1.42/0.56    ( ! [X0] : (r2_hidden(sK2(k1_relat_1(sK1),X0),k1_relat_1(sK1)) | sK0 = k4_xboole_0(sK0,X0)) )),
% 1.42/0.56    inference(resolution,[],[f58,f40])).
% 1.42/0.56  fof(f40,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.42/0.56    inference(cnf_transformation,[],[f23])).
% 1.42/0.56  fof(f23,plain,(
% 1.42/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.42/0.56    inference(nnf_transformation,[],[f5])).
% 1.42/0.56  fof(f5,axiom,(
% 1.42/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.42/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.42/0.56  fof(f58,plain,(
% 1.42/0.56    ( ! [X0] : (r1_xboole_0(sK0,X0) | r2_hidden(sK2(k1_relat_1(sK1),X0),k1_relat_1(sK1))) )),
% 1.42/0.56    inference(resolution,[],[f57,f36])).
% 1.42/0.56  fof(f36,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f22])).
% 1.42/0.56  fof(f22,plain,(
% 1.42/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.42/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f21])).
% 1.42/0.56  fof(f21,plain,(
% 1.42/0.56    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f15,plain,(
% 1.42/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.42/0.56    inference(ennf_transformation,[],[f12])).
% 1.42/0.56  fof(f12,plain,(
% 1.42/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.42/0.56    inference(rectify,[],[f2])).
% 1.42/0.56  fof(f2,axiom,(
% 1.42/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.42/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.42/0.56  fof(f57,plain,(
% 1.42/0.56    ( ! [X0] : (~r1_xboole_0(k1_relat_1(sK1),X0) | r1_xboole_0(sK0,X0)) )),
% 1.42/0.56    inference(resolution,[],[f30,f42])).
% 1.42/0.56  fof(f42,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f18])).
% 1.42/0.56  fof(f18,plain,(
% 1.42/0.56    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.42/0.56    inference(flattening,[],[f17])).
% 1.42/0.56  fof(f17,plain,(
% 1.42/0.56    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.42/0.56    inference(ennf_transformation,[],[f4])).
% 1.42/0.56  fof(f4,axiom,(
% 1.42/0.56    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.42/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.42/0.56  fof(f30,plain,(
% 1.42/0.56    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.42/0.56    inference(cnf_transformation,[],[f20])).
% 1.42/0.56  fof(f69,plain,(
% 1.42/0.56    ( ! [X2,X3] : (~r2_hidden(sK2(k1_relat_1(sK1),k4_xboole_0(X2,X3)),X3) | sK0 = k4_xboole_0(sK0,k4_xboole_0(X2,X3))) )),
% 1.42/0.56    inference(resolution,[],[f60,f54])).
% 1.42/0.56  fof(f54,plain,(
% 1.42/0.56    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.42/0.56    inference(equality_resolution,[],[f44])).
% 1.42/0.56  fof(f44,plain,(
% 1.42/0.56    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.42/0.56    inference(cnf_transformation,[],[f28])).
% 1.42/0.56  fof(f28,plain,(
% 1.42/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.42/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 1.42/0.56  fof(f27,plain,(
% 1.42/0.56    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f26,plain,(
% 1.42/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.42/0.56    inference(rectify,[],[f25])).
% 1.42/0.56  fof(f25,plain,(
% 1.42/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.42/0.56    inference(flattening,[],[f24])).
% 1.42/0.56  fof(f24,plain,(
% 1.42/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.42/0.56    inference(nnf_transformation,[],[f1])).
% 1.42/0.56  fof(f1,axiom,(
% 1.42/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.42/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.42/0.56  fof(f60,plain,(
% 1.42/0.56    ( ! [X0] : (r2_hidden(sK2(k1_relat_1(sK1),X0),X0) | sK0 = k4_xboole_0(sK0,X0)) )),
% 1.42/0.56    inference(resolution,[],[f59,f40])).
% 1.42/0.56  fof(f59,plain,(
% 1.42/0.56    ( ! [X1] : (r1_xboole_0(sK0,X1) | r2_hidden(sK2(k1_relat_1(sK1),X1),X1)) )),
% 1.42/0.56    inference(resolution,[],[f57,f37])).
% 1.42/0.56  fof(f37,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X1)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f22])).
% 1.42/0.56  fof(f31,plain,(
% 1.42/0.56    sK0 != k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.42/0.56    inference(cnf_transformation,[],[f20])).
% 1.42/0.56  % SZS output end Proof for theBenchmark
% 1.42/0.56  % (32324)------------------------------
% 1.42/0.56  % (32324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (32324)Termination reason: Refutation
% 1.42/0.56  
% 1.42/0.56  % (32324)Memory used [KB]: 10874
% 1.42/0.56  % (32324)Time elapsed: 0.145 s
% 1.42/0.56  % (32324)------------------------------
% 1.42/0.56  % (32324)------------------------------
% 1.42/0.56  % (32321)Success in time 0.195 s
%------------------------------------------------------------------------------
