%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:40 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 449 expanded)
%              Number of leaves         :   17 ( 136 expanded)
%              Depth                    :   19
%              Number of atoms          :  190 ( 831 expanded)
%              Number of equality atoms :   43 ( 334 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(resolution,[],[f186,f67])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f38,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

% (1603)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (1599)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (1612)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (1608)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (1608)Refutation not found, incomplete strategy% (1608)------------------------------
% (1608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1608)Termination reason: Refutation not found, incomplete strategy

% (1608)Memory used [KB]: 10746
% (1608)Time elapsed: 0.207 s
% (1608)------------------------------
% (1608)------------------------------
% (1615)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (1604)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f186,plain,(
    ~ r1_tarski(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(global_subsumption,[],[f76,f184])).

fof(f184,plain,
    ( sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | ~ r1_tarski(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(resolution,[],[f182,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f182,plain,(
    r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,
    ( r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)
    | r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(resolution,[],[f133,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f133,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0),sK1)
      | r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0) ) ),
    inference(resolution,[],[f124,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f124,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
      | r2_hidden(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f91,f122])).

fof(f122,plain,(
    ! [X3] : ~ r2_hidden(X3,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(global_subsumption,[],[f101,f100,f92,f120,f119,f94])).

fof(f94,plain,(
    ! [X3] :
      ( r2_hidden(X3,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
      | r2_hidden(X3,sK1)
      | ~ r2_hidden(X3,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ) ),
    inference(superposition,[],[f59,f89])).

fof(f89,plain,(
    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f70,f80])).

fof(f80,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f77,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f77,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f34,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f54,f64])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f62])).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f34,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f70,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f44,f63,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f119,plain,(
    ! [X2] :
      ( r2_hidden(X2,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
      | ~ r2_hidden(X2,sK1)
      | ~ r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X2] :
      ( r2_hidden(X2,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
      | ~ r2_hidden(X2,sK1)
      | ~ r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ) ),
    inference(resolution,[],[f93,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f93,plain,(
    ! [X2] :
      ( r2_hidden(X2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
      | r2_hidden(X2,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
      | ~ r2_hidden(X2,sK1) ) ),
    inference(superposition,[],[f58,f89])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f120,plain,(
    ! [X1] :
      ( r2_hidden(X1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,(
    ! [X1] :
      ( r2_hidden(X1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
      | ~ r2_hidden(X1,sK1)
      | r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ) ),
    inference(resolution,[],[f93,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
      | ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ) ),
    inference(superposition,[],[f57,f89])).

fof(f100,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
      | r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
      | ~ r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ) ),
    inference(resolution,[],[f91,f57])).

fof(f101,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
      | r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))
      | r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ) ),
    inference(resolution,[],[f91,f56])).

fof(f91,plain,(
    ! [X0] :
      ( r2_hidden(X0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ) ),
    inference(superposition,[],[f56,f89])).

fof(f76,plain,(
    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f65,f68])).

fof(f68,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f39,f62,f62])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f65,plain,(
    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f35,f63,f64])).

fof(f35,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:31:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.56  % (1585)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.23/0.56  % (1613)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.23/0.56  % (1600)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.58  % (1587)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.58  % (1605)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.23/0.59  % (1602)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.23/0.59  % (1592)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.59  % (1598)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.59  % (1591)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.60  % (1595)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.60  % (1601)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.60  % (1610)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.60  % (1594)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.61  % (1609)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.23/0.61  % (1589)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.61  % (1597)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.23/0.61  % (1596)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.23/0.61  % (1596)Refutation not found, incomplete strategy% (1596)------------------------------
% 0.23/0.61  % (1596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.61  % (1596)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.61  
% 0.23/0.61  % (1596)Memory used [KB]: 10618
% 0.23/0.61  % (1596)Time elapsed: 0.176 s
% 0.23/0.61  % (1596)------------------------------
% 0.23/0.61  % (1596)------------------------------
% 1.84/0.62  % (1590)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.84/0.62  % (1607)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.84/0.62  % (1588)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.84/0.62  % (1611)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.84/0.63  % (1614)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.84/0.63  % (1588)Refutation found. Thanks to Tanya!
% 1.84/0.63  % SZS status Theorem for theBenchmark
% 1.84/0.63  % SZS output start Proof for theBenchmark
% 1.84/0.63  fof(f187,plain,(
% 1.84/0.63    $false),
% 1.84/0.63    inference(resolution,[],[f186,f67])).
% 1.84/0.63  fof(f67,plain,(
% 1.84/0.63    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.84/0.63    inference(definition_unfolding,[],[f38,f63])).
% 1.84/0.63  fof(f63,plain,(
% 1.84/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.84/0.63    inference(definition_unfolding,[],[f42,f62])).
% 1.84/0.63  fof(f62,plain,(
% 1.84/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.84/0.63    inference(definition_unfolding,[],[f41,f61])).
% 1.84/0.63  fof(f61,plain,(
% 1.84/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.84/0.63    inference(definition_unfolding,[],[f55,f60])).
% 1.84/0.63  fof(f60,plain,(
% 1.84/0.63    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.84/0.63    inference(cnf_transformation,[],[f15])).
% 1.84/0.63  fof(f15,axiom,(
% 1.84/0.63    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.84/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.84/0.63  fof(f55,plain,(
% 1.84/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.84/0.63    inference(cnf_transformation,[],[f14])).
% 1.84/0.63  fof(f14,axiom,(
% 1.84/0.63    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.84/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.84/0.63  fof(f41,plain,(
% 1.84/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.84/0.63    inference(cnf_transformation,[],[f13])).
% 1.84/0.63  fof(f13,axiom,(
% 1.84/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.84/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.84/0.63  fof(f42,plain,(
% 1.84/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.84/0.63    inference(cnf_transformation,[],[f17])).
% 1.84/0.63  fof(f17,axiom,(
% 1.84/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.84/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.84/0.63  fof(f38,plain,(
% 1.84/0.63    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.84/0.63    inference(cnf_transformation,[],[f9])).
% 1.84/0.63  fof(f9,axiom,(
% 1.84/0.63    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.84/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.84/0.63  % (1603)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.84/0.63  % (1599)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.84/0.63  % (1612)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.84/0.64  % (1608)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.84/0.64  % (1608)Refutation not found, incomplete strategy% (1608)------------------------------
% 1.84/0.64  % (1608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.64  % (1608)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.64  
% 1.84/0.64  % (1608)Memory used [KB]: 10746
% 1.84/0.64  % (1608)Time elapsed: 0.207 s
% 1.84/0.64  % (1608)------------------------------
% 1.84/0.64  % (1608)------------------------------
% 2.11/0.64  % (1615)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.11/0.65  % (1604)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 2.11/0.65  fof(f186,plain,(
% 2.11/0.65    ~r1_tarski(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 2.11/0.65    inference(global_subsumption,[],[f76,f184])).
% 2.11/0.65  fof(f184,plain,(
% 2.11/0.65    sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | ~r1_tarski(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 2.11/0.65    inference(resolution,[],[f182,f49])).
% 2.11/0.65  fof(f49,plain,(
% 2.11/0.65    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f27])).
% 2.11/0.65  fof(f27,plain,(
% 2.11/0.65    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.11/0.65    inference(flattening,[],[f26])).
% 2.11/0.65  fof(f26,plain,(
% 2.11/0.65    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.11/0.65    inference(nnf_transformation,[],[f3])).
% 2.11/0.65  fof(f3,axiom,(
% 2.11/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.11/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.11/0.65  fof(f182,plain,(
% 2.11/0.65    r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)),
% 2.11/0.65    inference(duplicate_literal_removal,[],[f180])).
% 2.11/0.65  fof(f180,plain,(
% 2.11/0.65    r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1) | r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)),
% 2.11/0.65    inference(resolution,[],[f133,f52])).
% 2.11/0.65  fof(f52,plain,(
% 2.11/0.65    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f31])).
% 2.11/0.65  fof(f31,plain,(
% 2.11/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.11/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 2.11/0.65  fof(f30,plain,(
% 2.11/0.65    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 2.11/0.65    introduced(choice_axiom,[])).
% 2.11/0.65  fof(f29,plain,(
% 2.11/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.11/0.65    inference(rectify,[],[f28])).
% 2.11/0.65  fof(f28,plain,(
% 2.11/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.11/0.65    inference(nnf_transformation,[],[f22])).
% 2.11/0.65  fof(f22,plain,(
% 2.11/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.11/0.65    inference(ennf_transformation,[],[f1])).
% 2.11/0.65  fof(f1,axiom,(
% 2.11/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.11/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.11/0.65  fof(f133,plain,(
% 2.11/0.65    ( ! [X0] : (r2_hidden(sK2(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0),sK1) | r1_tarski(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),X0)) )),
% 2.11/0.65    inference(resolution,[],[f124,f51])).
% 2.11/0.65  fof(f51,plain,(
% 2.11/0.65    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f31])).
% 2.11/0.65  fof(f124,plain,(
% 2.11/0.65    ( ! [X0] : (~r2_hidden(X0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | r2_hidden(X0,sK1)) )),
% 2.11/0.65    inference(subsumption_resolution,[],[f91,f122])).
% 2.11/0.65  fof(f122,plain,(
% 2.11/0.65    ( ! [X3] : (~r2_hidden(X3,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) )),
% 2.11/0.65    inference(global_subsumption,[],[f101,f100,f92,f120,f119,f94])).
% 2.11/0.65  fof(f94,plain,(
% 2.11/0.65    ( ! [X3] : (r2_hidden(X3,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | r2_hidden(X3,sK1) | ~r2_hidden(X3,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) )),
% 2.11/0.65    inference(superposition,[],[f59,f89])).
% 2.11/0.65  fof(f89,plain,(
% 2.11/0.65    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 2.11/0.65    inference(superposition,[],[f70,f80])).
% 2.11/0.65  fof(f80,plain,(
% 2.11/0.65    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 2.11/0.65    inference(resolution,[],[f77,f46])).
% 2.11/0.65  fof(f46,plain,(
% 2.11/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.11/0.65    inference(cnf_transformation,[],[f21])).
% 2.11/0.65  fof(f21,plain,(
% 2.11/0.65    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.11/0.65    inference(ennf_transformation,[],[f7])).
% 2.11/0.65  fof(f7,axiom,(
% 2.11/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.11/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.11/0.65  fof(f77,plain,(
% 2.11/0.65    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 2.11/0.65    inference(resolution,[],[f34,f72])).
% 2.11/0.65  fof(f72,plain,(
% 2.11/0.65    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 2.11/0.65    inference(definition_unfolding,[],[f54,f64])).
% 2.11/0.65  fof(f64,plain,(
% 2.11/0.65    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.11/0.65    inference(definition_unfolding,[],[f37,f62])).
% 2.11/0.65  fof(f37,plain,(
% 2.11/0.65    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f12])).
% 2.11/0.65  fof(f12,axiom,(
% 2.11/0.65    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.11/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.11/0.65  fof(f54,plain,(
% 2.11/0.65    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f32])).
% 2.11/0.65  fof(f32,plain,(
% 2.11/0.65    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.11/0.65    inference(nnf_transformation,[],[f16])).
% 2.11/0.65  fof(f16,axiom,(
% 2.11/0.65    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.11/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.11/0.65  fof(f34,plain,(
% 2.11/0.65    r2_hidden(sK0,sK1)),
% 2.11/0.65    inference(cnf_transformation,[],[f25])).
% 2.11/0.65  fof(f25,plain,(
% 2.11/0.65    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 2.11/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f24])).
% 2.11/0.65  fof(f24,plain,(
% 2.11/0.65    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 2.11/0.65    introduced(choice_axiom,[])).
% 2.11/0.65  fof(f20,plain,(
% 2.11/0.65    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 2.11/0.65    inference(ennf_transformation,[],[f19])).
% 2.11/0.65  fof(f19,negated_conjecture,(
% 2.11/0.65    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 2.11/0.65    inference(negated_conjecture,[],[f18])).
% 2.11/0.65  fof(f18,conjecture,(
% 2.11/0.65    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 2.11/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 2.11/0.65  fof(f70,plain,(
% 2.11/0.65    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.11/0.65    inference(definition_unfolding,[],[f44,f63,f43])).
% 2.11/0.65  fof(f43,plain,(
% 2.11/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.11/0.65    inference(cnf_transformation,[],[f4])).
% 2.11/0.65  fof(f4,axiom,(
% 2.11/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.11/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.11/0.65  fof(f44,plain,(
% 2.11/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.11/0.65    inference(cnf_transformation,[],[f10])).
% 2.11/0.65  fof(f10,axiom,(
% 2.11/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.11/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.11/0.65  fof(f59,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f33])).
% 2.11/0.65  fof(f33,plain,(
% 2.11/0.65    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 2.11/0.65    inference(nnf_transformation,[],[f23])).
% 2.11/0.65  fof(f23,plain,(
% 2.11/0.65    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.11/0.65    inference(ennf_transformation,[],[f2])).
% 2.11/0.65  fof(f2,axiom,(
% 2.11/0.65    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.11/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 2.11/0.65  fof(f119,plain,(
% 2.11/0.65    ( ! [X2] : (r2_hidden(X2,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | ~r2_hidden(X2,sK1) | ~r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) )),
% 2.11/0.65    inference(duplicate_literal_removal,[],[f116])).
% 2.11/0.65  fof(f116,plain,(
% 2.11/0.65    ( ! [X2] : (r2_hidden(X2,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | ~r2_hidden(X2,sK1) | ~r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) )),
% 2.11/0.65    inference(resolution,[],[f93,f57])).
% 2.11/0.65  fof(f57,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f33])).
% 2.11/0.65  fof(f93,plain,(
% 2.11/0.65    ( ! [X2] : (r2_hidden(X2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | r2_hidden(X2,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | ~r2_hidden(X2,sK1)) )),
% 2.11/0.65    inference(superposition,[],[f58,f89])).
% 2.11/0.65  fof(f58,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f33])).
% 2.11/0.65  fof(f120,plain,(
% 2.11/0.65    ( ! [X1] : (r2_hidden(X1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | ~r2_hidden(X1,sK1) | r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) )),
% 2.11/0.65    inference(duplicate_literal_removal,[],[f115])).
% 2.11/0.65  fof(f115,plain,(
% 2.11/0.65    ( ! [X1] : (r2_hidden(X1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | ~r2_hidden(X1,sK1) | r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) )),
% 2.11/0.65    inference(resolution,[],[f93,f56])).
% 2.11/0.65  fof(f56,plain,(
% 2.11/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f33])).
% 2.11/0.65  fof(f92,plain,(
% 2.11/0.65    ( ! [X1] : (~r2_hidden(X1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | ~r2_hidden(X1,sK1) | ~r2_hidden(X1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) )),
% 2.11/0.65    inference(superposition,[],[f57,f89])).
% 2.11/0.65  fof(f100,plain,(
% 2.11/0.65    ( ! [X1] : (~r2_hidden(X1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | r2_hidden(X1,sK1) | ~r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) )),
% 2.11/0.65    inference(duplicate_literal_removal,[],[f97])).
% 2.11/0.65  fof(f97,plain,(
% 2.11/0.65    ( ! [X1] : (r2_hidden(X1,sK1) | ~r2_hidden(X1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | ~r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) )),
% 2.11/0.65    inference(resolution,[],[f91,f57])).
% 2.11/0.65  fof(f101,plain,(
% 2.11/0.65    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) )),
% 2.11/0.65    inference(duplicate_literal_removal,[],[f96])).
% 2.11/0.65  fof(f96,plain,(
% 2.11/0.65    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) | r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) )),
% 2.11/0.65    inference(resolution,[],[f91,f56])).
% 2.11/0.65  fof(f91,plain,(
% 2.11/0.65    ( ! [X0] : (r2_hidden(X0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | r2_hidden(X0,sK1) | ~r2_hidden(X0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) )),
% 2.11/0.65    inference(superposition,[],[f56,f89])).
% 2.11/0.65  fof(f76,plain,(
% 2.11/0.65    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 2.11/0.65    inference(forward_demodulation,[],[f65,f68])).
% 2.11/0.65  fof(f68,plain,(
% 2.11/0.65    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 2.11/0.65    inference(definition_unfolding,[],[f39,f62,f62])).
% 2.11/0.65  fof(f39,plain,(
% 2.11/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.11/0.65    inference(cnf_transformation,[],[f11])).
% 2.11/0.65  fof(f11,axiom,(
% 2.11/0.65    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.11/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.11/0.65  fof(f65,plain,(
% 2.11/0.65    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 2.11/0.65    inference(definition_unfolding,[],[f35,f63,f64])).
% 2.11/0.65  fof(f35,plain,(
% 2.11/0.65    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 2.11/0.65    inference(cnf_transformation,[],[f25])).
% 2.11/0.65  % SZS output end Proof for theBenchmark
% 2.11/0.65  % (1588)------------------------------
% 2.11/0.65  % (1588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.65  % (1588)Termination reason: Refutation
% 2.11/0.65  
% 2.11/0.65  % (1588)Memory used [KB]: 10874
% 2.11/0.65  % (1588)Time elapsed: 0.194 s
% 2.11/0.65  % (1588)------------------------------
% 2.11/0.65  % (1588)------------------------------
% 2.11/0.65  % (1584)Success in time 0.281 s
%------------------------------------------------------------------------------
