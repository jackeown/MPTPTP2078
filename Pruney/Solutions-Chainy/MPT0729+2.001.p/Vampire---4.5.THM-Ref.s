%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 325 expanded)
%              Number of leaves         :   17 ( 103 expanded)
%              Depth                    :   13
%              Number of atoms          :  178 ( 535 expanded)
%              Number of equality atoms :   78 ( 362 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1517,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1516,f155])).

fof(f155,plain,(
    ~ r2_hidden(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(extensionality_resolution,[],[f124,f52])).

fof(f52,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( sK1 != sK2
    & k1_ordinal1(sK1) = k1_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_ordinal1(X0) = k1_ordinal1(X1) )
   => ( sK1 != sK2
      & k1_ordinal1(sK1) = k1_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_ordinal1(X0) = k1_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_ordinal1(X0) = k1_ordinal1(X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( k1_ordinal1(X0) = k1_ordinal1(X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).

fof(f124,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f70,f98])).

fof(f98,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f95])).

fof(f95,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f79,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f79,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f1516,plain,(
    r2_hidden(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(subsumption_resolution,[],[f1508,f586])).

fof(f586,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f585,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f585,plain,(
    r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f584,f210])).

fof(f210,plain,(
    ! [X4] : r1_xboole_0(X4,k3_enumset1(X4,X4,X4,X4,X4)) ),
    inference(trivial_inequality_removal,[],[f208])).

fof(f208,plain,(
    ! [X4] :
      ( X4 != X4
      | r1_xboole_0(X4,k3_enumset1(X4,X4,X4,X4,X4)) ) ),
    inference(superposition,[],[f69,f195])).

fof(f195,plain,(
    ! [X0] : k4_xboole_0(X0,k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(resolution,[],[f113,f127])).

fof(f127,plain,(
    ! [X0] : ~ r2_hidden(X0,X0) ),
    inference(resolution,[],[f78,f120])).

fof(f120,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f113,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f77,f98])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f584,plain,
    ( r2_hidden(sK2,sK1)
    | ~ r1_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f581,f154])).

fof(f154,plain,(
    ~ r2_hidden(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(extensionality_resolution,[],[f124,f52])).

fof(f581,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ r1_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f479,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f89,f96])).

fof(f96,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f95])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

fof(f479,plain,(
    r2_hidden(sK2,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f101,f100])).

fof(f100,plain,(
    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    inference(definition_unfolding,[],[f51,f99,f99])).

fof(f99,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f55,f96,f98])).

fof(f55,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f51,plain,(
    k1_ordinal1(sK1) = k1_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f101,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f53,f99])).

fof(f53,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f1508,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(resolution,[],[f487,f101])).

fof(f487,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))
      | r2_hidden(X2,sK2)
      | r2_hidden(X2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ) ),
    inference(subsumption_resolution,[],[f483,f210])).

fof(f483,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))
      | r2_hidden(X2,sK2)
      | r2_hidden(X2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
      | ~ r1_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ) ),
    inference(superposition,[],[f119,f100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n012.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:52:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.46  % (27280)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.48  % (27305)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.48  % (27296)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.49  % (27288)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.50  % (27284)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (27281)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (27278)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (27283)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (27286)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (27300)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (27292)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (27282)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (27289)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (27287)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (27299)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (27301)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (27293)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (27277)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (27291)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (27297)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (27308)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (27285)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (27290)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (27308)Refutation not found, incomplete strategy% (27308)------------------------------
% 0.21/0.53  % (27308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27308)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27308)Memory used [KB]: 1663
% 0.21/0.53  % (27308)Time elapsed: 0.133 s
% 0.21/0.53  % (27308)------------------------------
% 0.21/0.53  % (27308)------------------------------
% 0.21/0.54  % (27304)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (27294)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (27307)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (27294)Refutation not found, incomplete strategy% (27294)------------------------------
% 0.21/0.54  % (27294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27294)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27294)Memory used [KB]: 10618
% 0.21/0.54  % (27294)Time elapsed: 0.139 s
% 0.21/0.54  % (27294)------------------------------
% 0.21/0.54  % (27294)------------------------------
% 0.21/0.55  % (27303)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (27295)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (27298)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (27306)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.57  % (27284)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f1517,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(subsumption_resolution,[],[f1516,f155])).
% 0.21/0.58  fof(f155,plain,(
% 0.21/0.58    ~r2_hidden(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 0.21/0.58    inference(extensionality_resolution,[],[f124,f52])).
% 1.73/0.59  fof(f52,plain,(
% 1.73/0.59    sK1 != sK2),
% 1.73/0.59    inference(cnf_transformation,[],[f35])).
% 1.73/0.59  fof(f35,plain,(
% 1.73/0.59    sK1 != sK2 & k1_ordinal1(sK1) = k1_ordinal1(sK2)),
% 1.73/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f34])).
% 1.73/0.59  fof(f34,plain,(
% 1.73/0.59    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1)) => (sK1 != sK2 & k1_ordinal1(sK1) = k1_ordinal1(sK2))),
% 1.73/0.59    introduced(choice_axiom,[])).
% 1.73/0.59  fof(f26,plain,(
% 1.73/0.59    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1))),
% 1.73/0.59    inference(ennf_transformation,[],[f25])).
% 1.73/0.59  fof(f25,negated_conjecture,(
% 1.73/0.59    ~! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 1.73/0.59    inference(negated_conjecture,[],[f24])).
% 1.73/0.59  fof(f24,conjecture,(
% 1.73/0.59    ! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).
% 1.73/0.59  fof(f124,plain,(
% 1.73/0.59    ( ! [X0,X3] : (~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.73/0.59    inference(equality_resolution,[],[f110])).
% 1.73/0.59  fof(f110,plain,(
% 1.73/0.59    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.73/0.59    inference(definition_unfolding,[],[f70,f98])).
% 1.73/0.59  fof(f98,plain,(
% 1.73/0.59    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f54,f95])).
% 1.73/0.59  fof(f95,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f60,f94])).
% 1.73/0.59  fof(f94,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f79,f93])).
% 1.73/0.59  fof(f93,plain,(
% 1.73/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f16])).
% 1.73/0.59  fof(f16,axiom,(
% 1.73/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.73/0.59  fof(f79,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f15])).
% 1.73/0.59  fof(f15,axiom,(
% 1.73/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.73/0.59  fof(f60,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f14])).
% 1.73/0.59  fof(f14,axiom,(
% 1.73/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.73/0.59  fof(f54,plain,(
% 1.73/0.59    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f13])).
% 1.73/0.59  fof(f13,axiom,(
% 1.73/0.59    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.73/0.59  fof(f70,plain,(
% 1.73/0.59    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.73/0.59    inference(cnf_transformation,[],[f42])).
% 1.73/0.59  fof(f42,plain,(
% 1.73/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.73/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 1.73/0.59  fof(f41,plain,(
% 1.73/0.59    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.73/0.59    introduced(choice_axiom,[])).
% 1.73/0.59  fof(f40,plain,(
% 1.73/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.73/0.59    inference(rectify,[],[f39])).
% 1.73/0.59  fof(f39,plain,(
% 1.73/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.73/0.59    inference(nnf_transformation,[],[f12])).
% 1.73/0.59  fof(f12,axiom,(
% 1.73/0.59    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.73/0.59  fof(f1516,plain,(
% 1.73/0.59    r2_hidden(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 1.73/0.59    inference(subsumption_resolution,[],[f1508,f586])).
% 1.73/0.59  fof(f586,plain,(
% 1.73/0.59    ~r2_hidden(sK1,sK2)),
% 1.73/0.59    inference(resolution,[],[f585,f64])).
% 1.73/0.59  fof(f64,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f28])).
% 1.73/0.59  fof(f28,plain,(
% 1.73/0.59    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.73/0.59    inference(ennf_transformation,[],[f1])).
% 1.73/0.59  fof(f1,axiom,(
% 1.73/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.73/0.59  fof(f585,plain,(
% 1.73/0.59    r2_hidden(sK2,sK1)),
% 1.73/0.59    inference(subsumption_resolution,[],[f584,f210])).
% 1.73/0.59  fof(f210,plain,(
% 1.73/0.59    ( ! [X4] : (r1_xboole_0(X4,k3_enumset1(X4,X4,X4,X4,X4))) )),
% 1.73/0.59    inference(trivial_inequality_removal,[],[f208])).
% 1.73/0.59  fof(f208,plain,(
% 1.73/0.59    ( ! [X4] : (X4 != X4 | r1_xboole_0(X4,k3_enumset1(X4,X4,X4,X4,X4))) )),
% 1.73/0.59    inference(superposition,[],[f69,f195])).
% 1.73/0.59  fof(f195,plain,(
% 1.73/0.59    ( ! [X0] : (k4_xboole_0(X0,k3_enumset1(X0,X0,X0,X0,X0)) = X0) )),
% 1.73/0.59    inference(resolution,[],[f113,f127])).
% 1.73/0.59  fof(f127,plain,(
% 1.73/0.59    ( ! [X0] : (~r2_hidden(X0,X0)) )),
% 1.73/0.59    inference(resolution,[],[f78,f120])).
% 1.73/0.59  fof(f120,plain,(
% 1.73/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.73/0.59    inference(equality_resolution,[],[f66])).
% 1.73/0.59  fof(f66,plain,(
% 1.73/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.73/0.59    inference(cnf_transformation,[],[f37])).
% 1.73/0.59  fof(f37,plain,(
% 1.73/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.73/0.59    inference(flattening,[],[f36])).
% 1.73/0.59  fof(f36,plain,(
% 1.73/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.73/0.59    inference(nnf_transformation,[],[f4])).
% 1.73/0.59  fof(f4,axiom,(
% 1.73/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.73/0.59  fof(f78,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f29])).
% 1.73/0.59  fof(f29,plain,(
% 1.73/0.59    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.73/0.59    inference(ennf_transformation,[],[f23])).
% 1.73/0.59  fof(f23,axiom,(
% 1.73/0.59    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.73/0.59  fof(f113,plain,(
% 1.73/0.59    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k3_enumset1(X1,X1,X1,X1,X1)) = X0) )),
% 1.73/0.59    inference(definition_unfolding,[],[f77,f98])).
% 1.73/0.59  fof(f77,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f44])).
% 1.73/0.59  fof(f44,plain,(
% 1.73/0.59    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.73/0.59    inference(nnf_transformation,[],[f19])).
% 1.73/0.59  fof(f19,axiom,(
% 1.73/0.59    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.73/0.59  fof(f69,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f38])).
% 1.73/0.59  fof(f38,plain,(
% 1.73/0.59    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.73/0.59    inference(nnf_transformation,[],[f10])).
% 1.73/0.59  fof(f10,axiom,(
% 1.73/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.73/0.59  fof(f584,plain,(
% 1.73/0.59    r2_hidden(sK2,sK1) | ~r1_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 1.73/0.59    inference(subsumption_resolution,[],[f581,f154])).
% 1.73/0.59  fof(f154,plain,(
% 1.73/0.59    ~r2_hidden(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 1.73/0.59    inference(extensionality_resolution,[],[f124,f52])).
% 1.73/0.59  fof(f581,plain,(
% 1.73/0.59    r2_hidden(sK2,sK1) | r2_hidden(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~r1_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 1.73/0.59    inference(resolution,[],[f479,f119])).
% 1.73/0.59  fof(f119,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f89,f96])).
% 1.73/0.59  fof(f96,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.73/0.59    inference(definition_unfolding,[],[f59,f95])).
% 1.73/0.59  fof(f59,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.73/0.59    inference(cnf_transformation,[],[f18])).
% 1.73/0.59  fof(f18,axiom,(
% 1.73/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.73/0.59  fof(f89,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f31])).
% 1.73/0.59  fof(f31,plain,(
% 1.73/0.59    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 1.73/0.59    inference(ennf_transformation,[],[f3])).
% 1.73/0.59  fof(f3,axiom,(
% 1.73/0.59    ! [X0,X1,X2] : ~(~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & ~(~r2_hidden(X2,X1) & r2_hidden(X2,X0)) & r2_hidden(X2,k2_xboole_0(X0,X1)) & r1_xboole_0(X0,X1))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).
% 1.73/0.59  fof(f479,plain,(
% 1.73/0.59    r2_hidden(sK2,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))),
% 1.73/0.59    inference(superposition,[],[f101,f100])).
% 1.73/0.59  fof(f100,plain,(
% 1.73/0.59    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))),
% 1.73/0.59    inference(definition_unfolding,[],[f51,f99,f99])).
% 1.73/0.59  fof(f99,plain,(
% 1.73/0.59    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0)))) )),
% 1.73/0.59    inference(definition_unfolding,[],[f55,f96,f98])).
% 1.73/0.59  fof(f55,plain,(
% 1.73/0.59    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.73/0.59    inference(cnf_transformation,[],[f21])).
% 1.73/0.59  fof(f21,axiom,(
% 1.73/0.59    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.73/0.59  fof(f51,plain,(
% 1.73/0.59    k1_ordinal1(sK1) = k1_ordinal1(sK2)),
% 1.73/0.59    inference(cnf_transformation,[],[f35])).
% 1.73/0.59  fof(f101,plain,(
% 1.73/0.59    ( ! [X0] : (r2_hidden(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0))))) )),
% 1.73/0.59    inference(definition_unfolding,[],[f53,f99])).
% 1.73/0.59  fof(f53,plain,(
% 1.73/0.59    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 1.73/0.59    inference(cnf_transformation,[],[f22])).
% 1.73/0.59  fof(f22,axiom,(
% 1.73/0.59    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 1.73/0.59  fof(f1508,plain,(
% 1.73/0.59    r2_hidden(sK1,sK2) | r2_hidden(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 1.73/0.59    inference(resolution,[],[f487,f101])).
% 1.73/0.59  fof(f487,plain,(
% 1.73/0.59    ( ! [X2] : (~r2_hidden(X2,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) | r2_hidden(X2,sK2) | r2_hidden(X2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f483,f210])).
% 1.73/0.59  fof(f483,plain,(
% 1.73/0.59    ( ! [X2] : (~r2_hidden(X2,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) | r2_hidden(X2,sK2) | r2_hidden(X2,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | ~r1_xboole_0(sK2,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) )),
% 1.73/0.59    inference(superposition,[],[f119,f100])).
% 1.73/0.59  % SZS output end Proof for theBenchmark
% 1.73/0.59  % (27284)------------------------------
% 1.73/0.59  % (27284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.59  % (27284)Termination reason: Refutation
% 1.73/0.59  
% 1.73/0.59  % (27284)Memory used [KB]: 11641
% 1.73/0.59  % (27284)Time elapsed: 0.143 s
% 1.73/0.59  % (27284)------------------------------
% 1.73/0.59  % (27284)------------------------------
% 1.73/0.59  % (27274)Success in time 0.227 s
%------------------------------------------------------------------------------
