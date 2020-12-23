%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:55 EST 2020

% Result     : Theorem 6.90s
% Output     : Refutation 6.90s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 165 expanded)
%              Number of leaves         :    8 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 307 expanded)
%              Number of equality atoms :   62 ( 177 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2894,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f310,f2883,f28])).

fof(f28,plain,(
    ! [X2,X0] :
      ( ~ sP7(X2,X0)
      | r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f2883,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(k4_tarski(sK5(sK0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))),X0),k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,X1),X2),k4_tarski(k4_tarski(sK0,X1),X2),k4_tarski(k4_tarski(sK0,X1),X2)))) ),
    inference(unit_resulting_resolution,[],[f2865,f56])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | sP7(X2,X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( sP7(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f2865,plain,(
    ! [X2,X0,X1] : ~ sP7(k4_tarski(sK5(sK0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))),X0),k1_enumset1(k4_tarski(k4_tarski(sK0,X1),X2),k4_tarski(k4_tarski(sK0,X1),X2),k4_tarski(k4_tarski(sK0,X1),X2))) ),
    inference(unit_resulting_resolution,[],[f308,f28])).

fof(f308,plain,(
    ! [X2,X0,X3,X1] : ~ r2_hidden(k4_tarski(k4_tarski(sK5(sK0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))),X0),X1),k1_enumset1(k4_tarski(k4_tarski(sK0,X2),X3),k4_tarski(k4_tarski(sK0,X2),X3),k4_tarski(k4_tarski(sK0,X2),X3))) ),
    inference(unit_resulting_resolution,[],[f201,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_enumset1(X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f24,f36])).

fof(f36,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f201,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(sK5(sK0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))),X0),X1) != k4_tarski(k4_tarski(sK0,X2),X3) ),
    inference(unit_resulting_resolution,[],[f149,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_tarski(k4_tarski(X0,X1),X2) != k4_tarski(k4_tarski(X3,X4),X5)
      | X0 = X3 ) ),
    inference(definition_unfolding,[],[f13,f34,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f13,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
     => ( X2 = X5
        & X1 = X4
        & X0 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_mcart_1)).

fof(f149,plain,(
    sK0 != sK5(sK0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))) ),
    inference(unit_resulting_resolution,[],[f123,f37,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X0
      | ~ r2_hidden(X0,X1)
      | k1_enumset1(X0,X0,X0) = X1 ) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) = X1
      | ~ r2_hidden(X0,X1)
      | sK5(X0,X1) != X0
      | k1_enumset1(X0,X0,X0) = X1 ) ),
    inference(resolution,[],[f121,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | sK5(X0,X1) != X0
      | k1_enumset1(X0,X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f26,f36])).

fof(f26,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X0
      | ~ r2_hidden(sK5(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f121,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | k1_enumset1(X0,X0,X0) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(trivial_inequality_removal,[],[f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X0
      | k1_enumset1(X0,X0,X0) = X1
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X0
      | k1_enumset1(X0,X0,X0) = X1
      | r2_hidden(sK5(X0,X1),X1)
      | k1_enumset1(X0,X0,X0) = X1 ) ),
    inference(superposition,[],[f45,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) = X0
      | r2_hidden(sK5(X0,X1),X1)
      | k1_enumset1(X0,X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f25,f36])).

fof(f25,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) = X0
      | r2_hidden(sK5(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f37,plain,(
    k1_enumset1(sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)))) ),
    inference(definition_unfolding,[],[f12,f36,f36,f34])).

fof(f12,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).

fof(f123,plain,(
    ! [X2,X0,X3,X1] : r2_hidden(X0,k1_relat_1(k1_relat_1(k1_enumset1(X1,X1,k4_tarski(k4_tarski(X0,X2),X3))))) ),
    inference(unit_resulting_resolution,[],[f102,f57])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ sP7(X2,X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X2,X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] : sP7(X0,k1_relat_1(k1_enumset1(X1,X1,k4_tarski(k4_tarski(X0,X2),X3)))) ),
    inference(unit_resulting_resolution,[],[f95,f29])).

fof(f29,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | sP7(X2,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f95,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_relat_1(k1_enumset1(X1,X1,k4_tarski(X0,X2)))) ),
    inference(unit_resulting_resolution,[],[f72,f57])).

fof(f72,plain,(
    ! [X2,X0,X1] : sP7(X0,k1_enumset1(X1,X1,k4_tarski(X0,X2))) ),
    inference(unit_resulting_resolution,[],[f66,f29])).

fof(f66,plain,(
    ! [X0,X1] : r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
    inference(unit_resulting_resolution,[],[f51,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,k1_enumset1(X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f19,f35])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f51,plain,(
    ! [X0,X3] : sP4(X3,X3,X0) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X0,X3,X1] :
      ( X1 != X3
      | sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f310,plain,(
    sP7(sK5(sK0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))),k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)))) ),
    inference(unit_resulting_resolution,[],[f123,f37,f134])).

fof(f134,plain,(
    ! [X2,X3] :
      ( sP7(sK5(X2,k1_relat_1(X3)),X3)
      | ~ r2_hidden(X2,k1_relat_1(X3))
      | k1_enumset1(X2,X2,X2) = k1_relat_1(X3) ) ),
    inference(resolution,[],[f121,f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n021.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:11:49 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.56  % (23915)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.56  % (23914)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (23916)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.57  % (23922)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.57  % (23930)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.57  % (23923)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.57  % (23931)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.57  % (23924)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.57  % (23922)Refutation not found, incomplete strategy% (23922)------------------------------
% 0.22/0.57  % (23922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (23932)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.57  % (23922)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (23922)Memory used [KB]: 1663
% 0.22/0.57  % (23922)Time elapsed: 0.127 s
% 0.22/0.57  % (23922)------------------------------
% 0.22/0.57  % (23922)------------------------------
% 0.22/0.57  % (23924)Refutation not found, incomplete strategy% (23924)------------------------------
% 0.22/0.57  % (23924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (23924)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (23924)Memory used [KB]: 10618
% 0.22/0.57  % (23924)Time elapsed: 0.139 s
% 0.22/0.57  % (23924)------------------------------
% 0.22/0.57  % (23924)------------------------------
% 0.22/0.59  % (23932)Refutation not found, incomplete strategy% (23932)------------------------------
% 0.22/0.59  % (23932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (23932)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (23932)Memory used [KB]: 10618
% 0.22/0.59  % (23932)Time elapsed: 0.156 s
% 0.22/0.59  % (23932)------------------------------
% 0.22/0.59  % (23932)------------------------------
% 0.22/0.60  % (23913)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.60  % (23912)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.61  % (23909)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.85/0.61  % (23917)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.85/0.61  % (23919)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.85/0.62  % (23911)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.85/0.62  % (23937)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.85/0.62  % (23925)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.85/0.62  % (23925)Refutation not found, incomplete strategy% (23925)------------------------------
% 1.85/0.62  % (23925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.62  % (23925)Termination reason: Refutation not found, incomplete strategy
% 1.85/0.62  
% 1.85/0.62  % (23925)Memory used [KB]: 1663
% 1.85/0.62  % (23925)Time elapsed: 0.142 s
% 1.85/0.62  % (23925)------------------------------
% 1.85/0.62  % (23925)------------------------------
% 1.85/0.62  % (23920)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.85/0.62  % (23935)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.85/0.63  % (23935)Refutation not found, incomplete strategy% (23935)------------------------------
% 1.85/0.63  % (23935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.63  % (23935)Termination reason: Refutation not found, incomplete strategy
% 1.85/0.63  
% 1.85/0.63  % (23935)Memory used [KB]: 6140
% 1.85/0.63  % (23935)Time elapsed: 0.187 s
% 1.85/0.63  % (23935)------------------------------
% 1.85/0.63  % (23935)------------------------------
% 1.85/0.63  % (23921)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.85/0.63  % (23936)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.85/0.63  % (23933)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.85/0.63  % (23927)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.95/0.64  % (23909)Refutation not found, incomplete strategy% (23909)------------------------------
% 1.95/0.64  % (23909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.64  % (23909)Termination reason: Refutation not found, incomplete strategy
% 1.95/0.64  
% 1.95/0.64  % (23909)Memory used [KB]: 1663
% 1.95/0.64  % (23909)Time elapsed: 0.157 s
% 1.95/0.64  % (23909)------------------------------
% 1.95/0.64  % (23909)------------------------------
% 1.95/0.64  % (23929)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.95/0.64  % (23928)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 2.17/0.67  % (23910)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 2.17/0.68  % (23908)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 2.17/0.69  % (23934)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.17/0.69  % (23934)Refutation not found, incomplete strategy% (23934)------------------------------
% 2.17/0.69  % (23934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.69  % (23934)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.69  
% 2.17/0.69  % (23934)Memory used [KB]: 6140
% 2.17/0.69  % (23934)Time elapsed: 0.245 s
% 2.17/0.69  % (23934)------------------------------
% 2.17/0.69  % (23934)------------------------------
% 2.17/0.69  % (23926)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.17/0.69  % (23926)Refutation not found, incomplete strategy% (23926)------------------------------
% 2.17/0.69  % (23926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.69  % (23926)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.69  
% 2.17/0.69  % (23926)Memory used [KB]: 1663
% 2.17/0.69  % (23926)Time elapsed: 0.256 s
% 2.17/0.69  % (23926)------------------------------
% 2.17/0.69  % (23926)------------------------------
% 2.17/0.70  % (23918)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 2.66/0.74  % (23944)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.98/0.81  % (23943)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.98/0.84  % (23945)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.98/0.84  % (23911)Refutation not found, incomplete strategy% (23911)------------------------------
% 2.98/0.84  % (23911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.98/0.84  % (23911)Termination reason: Refutation not found, incomplete strategy
% 2.98/0.84  
% 2.98/0.84  % (23911)Memory used [KB]: 6140
% 2.98/0.84  % (23911)Time elapsed: 0.407 s
% 2.98/0.84  % (23911)------------------------------
% 2.98/0.84  % (23911)------------------------------
% 3.50/0.85  % (23949)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 3.50/0.86  % (23947)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.50/0.87  % (23948)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 3.50/0.87  % (23948)Refutation not found, incomplete strategy% (23948)------------------------------
% 3.50/0.87  % (23948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.68/0.88  % (23950)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 3.68/0.89  % (23948)Termination reason: Refutation not found, incomplete strategy
% 3.68/0.89  
% 3.68/0.89  % (23948)Memory used [KB]: 10618
% 3.68/0.89  % (23948)Time elapsed: 0.186 s
% 3.68/0.89  % (23948)------------------------------
% 3.68/0.89  % (23948)------------------------------
% 3.68/0.92  % (23910)Time limit reached!
% 3.68/0.92  % (23910)------------------------------
% 3.68/0.92  % (23910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.68/0.92  % (23910)Termination reason: Time limit
% 3.68/0.92  % (23910)Termination phase: Saturation
% 3.68/0.92  
% 3.68/0.92  % (23910)Memory used [KB]: 6268
% 3.68/0.92  % (23910)Time elapsed: 0.469 s
% 3.68/0.92  % (23910)------------------------------
% 3.68/0.92  % (23910)------------------------------
% 4.05/0.93  % (23951)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 4.18/0.95  % (23937)Time limit reached!
% 4.18/0.95  % (23937)------------------------------
% 4.18/0.95  % (23937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/0.95  % (23937)Termination reason: Time limit
% 4.18/0.95  
% 4.18/0.95  % (23937)Memory used [KB]: 5500
% 4.18/0.95  % (23937)Time elapsed: 0.521 s
% 4.18/0.95  % (23937)------------------------------
% 4.18/0.95  % (23937)------------------------------
% 4.18/0.99  % (23914)Time limit reached!
% 4.18/0.99  % (23914)------------------------------
% 4.18/0.99  % (23914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/0.99  % (23914)Termination reason: Time limit
% 4.18/0.99  % (23914)Termination phase: Saturation
% 4.18/0.99  
% 4.18/0.99  % (23914)Memory used [KB]: 13816
% 4.18/0.99  % (23914)Time elapsed: 0.543 s
% 4.18/0.99  % (23914)------------------------------
% 4.18/0.99  % (23914)------------------------------
% 4.58/1.05  % (23955)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 4.58/1.06  % (23955)Refutation not found, incomplete strategy% (23955)------------------------------
% 4.58/1.06  % (23955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.58/1.06  % (23955)Termination reason: Refutation not found, incomplete strategy
% 4.58/1.06  
% 4.58/1.06  % (23955)Memory used [KB]: 10746
% 4.58/1.06  % (23955)Time elapsed: 0.075 s
% 4.58/1.06  % (23955)------------------------------
% 4.58/1.06  % (23955)------------------------------
% 4.58/1.06  % (23915)Time limit reached!
% 4.58/1.06  % (23915)------------------------------
% 4.58/1.06  % (23915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.58/1.06  % (23915)Termination reason: Time limit
% 4.58/1.06  
% 4.58/1.06  % (23915)Memory used [KB]: 4989
% 4.58/1.06  % (23915)Time elapsed: 0.620 s
% 4.58/1.06  % (23915)------------------------------
% 4.58/1.06  % (23915)------------------------------
% 4.90/1.11  % (23954)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 6.26/1.18  % (23959)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 6.49/1.21  % (23958)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 6.49/1.21  % (23962)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 6.90/1.25  % (23967)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 6.90/1.28  % (23927)Refutation found. Thanks to Tanya!
% 6.90/1.28  % SZS status Theorem for theBenchmark
% 6.90/1.28  % SZS output start Proof for theBenchmark
% 6.90/1.28  fof(f2894,plain,(
% 6.90/1.28    $false),
% 6.90/1.28    inference(unit_resulting_resolution,[],[f310,f2883,f28])).
% 6.90/1.28  fof(f28,plain,(
% 6.90/1.28    ( ! [X2,X0] : (~sP7(X2,X0) | r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0)) )),
% 6.90/1.28    inference(cnf_transformation,[],[f5])).
% 6.90/1.28  fof(f5,axiom,(
% 6.90/1.28    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 6.90/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 6.90/1.28  fof(f2883,plain,(
% 6.90/1.28    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(sK5(sK0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))),X0),k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,X1),X2),k4_tarski(k4_tarski(sK0,X1),X2),k4_tarski(k4_tarski(sK0,X1),X2))))) )),
% 6.90/1.28    inference(unit_resulting_resolution,[],[f2865,f56])).
% 6.90/1.28  fof(f56,plain,(
% 6.90/1.28    ( ! [X2,X0] : (~r2_hidden(X2,k1_relat_1(X0)) | sP7(X2,X0)) )),
% 6.90/1.28    inference(equality_resolution,[],[f31])).
% 6.90/1.28  fof(f31,plain,(
% 6.90/1.28    ( ! [X2,X0,X1] : (sP7(X2,X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 6.90/1.28    inference(cnf_transformation,[],[f5])).
% 6.90/1.28  fof(f2865,plain,(
% 6.90/1.28    ( ! [X2,X0,X1] : (~sP7(k4_tarski(sK5(sK0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))),X0),k1_enumset1(k4_tarski(k4_tarski(sK0,X1),X2),k4_tarski(k4_tarski(sK0,X1),X2),k4_tarski(k4_tarski(sK0,X1),X2)))) )),
% 6.90/1.28    inference(unit_resulting_resolution,[],[f308,f28])).
% 6.90/1.28  fof(f308,plain,(
% 6.90/1.28    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(k4_tarski(sK5(sK0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))),X0),X1),k1_enumset1(k4_tarski(k4_tarski(sK0,X2),X3),k4_tarski(k4_tarski(sK0,X2),X3),k4_tarski(k4_tarski(sK0,X2),X3)))) )),
% 6.90/1.28    inference(unit_resulting_resolution,[],[f201,f53])).
% 6.90/1.28  fof(f53,plain,(
% 6.90/1.28    ( ! [X2,X0] : (~r2_hidden(X2,k1_enumset1(X0,X0,X0)) | X0 = X2) )),
% 6.90/1.28    inference(equality_resolution,[],[f47])).
% 6.90/1.28  fof(f47,plain,(
% 6.90/1.28    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 6.90/1.28    inference(definition_unfolding,[],[f24,f36])).
% 6.90/1.28  fof(f36,plain,(
% 6.90/1.28    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 6.90/1.28    inference(definition_unfolding,[],[f27,f35])).
% 6.90/1.28  fof(f35,plain,(
% 6.90/1.28    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.90/1.28    inference(cnf_transformation,[],[f4])).
% 6.90/1.28  fof(f4,axiom,(
% 6.90/1.28    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.90/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 6.90/1.28  fof(f27,plain,(
% 6.90/1.28    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 6.90/1.28    inference(cnf_transformation,[],[f3])).
% 6.90/1.28  fof(f3,axiom,(
% 6.90/1.28    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 6.90/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 6.90/1.28  fof(f24,plain,(
% 6.90/1.28    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 6.90/1.28    inference(cnf_transformation,[],[f1])).
% 6.90/1.28  fof(f1,axiom,(
% 6.90/1.28    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 6.90/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 6.90/1.28  fof(f201,plain,(
% 6.90/1.28    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(sK5(sK0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))),X0),X1) != k4_tarski(k4_tarski(sK0,X2),X3)) )),
% 6.90/1.28    inference(unit_resulting_resolution,[],[f149,f40])).
% 6.90/1.28  fof(f40,plain,(
% 6.90/1.28    ( ! [X4,X2,X0,X5,X3,X1] : (k4_tarski(k4_tarski(X0,X1),X2) != k4_tarski(k4_tarski(X3,X4),X5) | X0 = X3) )),
% 6.90/1.28    inference(definition_unfolding,[],[f13,f34,f34])).
% 6.90/1.28  fof(f34,plain,(
% 6.90/1.28    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 6.90/1.28    inference(cnf_transformation,[],[f6])).
% 6.90/1.28  fof(f6,axiom,(
% 6.90/1.28    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 6.90/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 6.90/1.28  fof(f13,plain,(
% 6.90/1.28    ( ! [X4,X2,X0,X5,X3,X1] : (k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) | X0 = X3) )),
% 6.90/1.28    inference(cnf_transformation,[],[f11])).
% 6.90/1.28  fof(f11,plain,(
% 6.90/1.28    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5))),
% 6.90/1.28    inference(ennf_transformation,[],[f7])).
% 6.90/1.28  fof(f7,axiom,(
% 6.90/1.28    ! [X0,X1,X2,X3,X4,X5] : (k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) => (X2 = X5 & X1 = X4 & X0 = X3))),
% 6.90/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_mcart_1)).
% 6.90/1.28  fof(f149,plain,(
% 6.90/1.28    sK0 != sK5(sK0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)))))),
% 6.90/1.28    inference(unit_resulting_resolution,[],[f123,f37,f139])).
% 6.90/1.28  fof(f139,plain,(
% 6.90/1.28    ( ! [X0,X1] : (sK5(X0,X1) != X0 | ~r2_hidden(X0,X1) | k1_enumset1(X0,X0,X0) = X1) )),
% 6.90/1.28    inference(duplicate_literal_removal,[],[f133])).
% 6.90/1.28  fof(f133,plain,(
% 6.90/1.28    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = X1 | ~r2_hidden(X0,X1) | sK5(X0,X1) != X0 | k1_enumset1(X0,X0,X0) = X1) )),
% 6.90/1.28    inference(resolution,[],[f121,f45])).
% 6.90/1.28  fof(f45,plain,(
% 6.90/1.28    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | sK5(X0,X1) != X0 | k1_enumset1(X0,X0,X0) = X1) )),
% 6.90/1.28    inference(definition_unfolding,[],[f26,f36])).
% 6.90/1.28  fof(f26,plain,(
% 6.90/1.28    ( ! [X0,X1] : (sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 6.90/1.28    inference(cnf_transformation,[],[f1])).
% 6.90/1.28  fof(f121,plain,(
% 6.90/1.28    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | k1_enumset1(X0,X0,X0) = X1 | ~r2_hidden(X0,X1)) )),
% 6.90/1.28    inference(trivial_inequality_removal,[],[f120])).
% 6.90/1.28  fof(f120,plain,(
% 6.90/1.28    ( ! [X0,X1] : (~r2_hidden(X0,X1) | X0 != X0 | k1_enumset1(X0,X0,X0) = X1 | r2_hidden(sK5(X0,X1),X1)) )),
% 6.90/1.28    inference(duplicate_literal_removal,[],[f119])).
% 6.90/1.28  fof(f119,plain,(
% 6.90/1.28    ( ! [X0,X1] : (~r2_hidden(X0,X1) | X0 != X0 | k1_enumset1(X0,X0,X0) = X1 | r2_hidden(sK5(X0,X1),X1) | k1_enumset1(X0,X0,X0) = X1) )),
% 6.90/1.28    inference(superposition,[],[f45,f46])).
% 6.90/1.28  fof(f46,plain,(
% 6.90/1.28    ( ! [X0,X1] : (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1) | k1_enumset1(X0,X0,X0) = X1) )),
% 6.90/1.28    inference(definition_unfolding,[],[f25,f36])).
% 6.90/1.28  fof(f25,plain,(
% 6.90/1.28    ( ! [X0,X1] : (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 6.90/1.28    inference(cnf_transformation,[],[f1])).
% 6.90/1.28  fof(f37,plain,(
% 6.90/1.28    k1_enumset1(sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))),
% 6.90/1.28    inference(definition_unfolding,[],[f12,f36,f36,f34])).
% 6.90/1.28  fof(f12,plain,(
% 6.90/1.28    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 6.90/1.28    inference(cnf_transformation,[],[f10])).
% 6.90/1.28  fof(f10,plain,(
% 6.90/1.28    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 6.90/1.28    inference(ennf_transformation,[],[f9])).
% 6.90/1.28  fof(f9,negated_conjecture,(
% 6.90/1.28    ~! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 6.90/1.28    inference(negated_conjecture,[],[f8])).
% 6.90/1.28  fof(f8,conjecture,(
% 6.90/1.28    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 6.90/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).
% 6.90/1.28  fof(f123,plain,(
% 6.90/1.28    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k1_relat_1(k1_relat_1(k1_enumset1(X1,X1,k4_tarski(k4_tarski(X0,X2),X3)))))) )),
% 6.90/1.28    inference(unit_resulting_resolution,[],[f102,f57])).
% 6.90/1.28  fof(f57,plain,(
% 6.90/1.28    ( ! [X2,X0] : (~sP7(X2,X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 6.90/1.28    inference(equality_resolution,[],[f30])).
% 6.90/1.28  fof(f30,plain,(
% 6.90/1.28    ( ! [X2,X0,X1] : (~sP7(X2,X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 6.90/1.28    inference(cnf_transformation,[],[f5])).
% 6.90/1.28  fof(f102,plain,(
% 6.90/1.28    ( ! [X2,X0,X3,X1] : (sP7(X0,k1_relat_1(k1_enumset1(X1,X1,k4_tarski(k4_tarski(X0,X2),X3))))) )),
% 6.90/1.28    inference(unit_resulting_resolution,[],[f95,f29])).
% 6.90/1.28  fof(f29,plain,(
% 6.90/1.28    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | sP7(X2,X0)) )),
% 6.90/1.28    inference(cnf_transformation,[],[f5])).
% 6.90/1.28  fof(f95,plain,(
% 6.90/1.28    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k1_enumset1(X1,X1,k4_tarski(X0,X2))))) )),
% 6.90/1.28    inference(unit_resulting_resolution,[],[f72,f57])).
% 6.90/1.28  fof(f72,plain,(
% 6.90/1.28    ( ! [X2,X0,X1] : (sP7(X0,k1_enumset1(X1,X1,k4_tarski(X0,X2)))) )),
% 6.90/1.28    inference(unit_resulting_resolution,[],[f66,f29])).
% 6.90/1.28  fof(f66,plain,(
% 6.90/1.28    ( ! [X0,X1] : (r2_hidden(X0,k1_enumset1(X1,X1,X0))) )),
% 6.90/1.28    inference(unit_resulting_resolution,[],[f51,f50])).
% 6.90/1.28  fof(f50,plain,(
% 6.90/1.28    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,k1_enumset1(X0,X0,X1))) )),
% 6.90/1.28    inference(equality_resolution,[],[f44])).
% 6.90/1.28  fof(f44,plain,(
% 6.90/1.28    ( ! [X2,X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 6.90/1.28    inference(definition_unfolding,[],[f19,f35])).
% 6.90/1.28  fof(f19,plain,(
% 6.90/1.28    ( ! [X2,X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 6.90/1.28    inference(cnf_transformation,[],[f2])).
% 6.90/1.28  fof(f2,axiom,(
% 6.90/1.28    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 6.90/1.28    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 6.90/1.28  fof(f51,plain,(
% 6.90/1.28    ( ! [X0,X3] : (sP4(X3,X3,X0)) )),
% 6.90/1.28    inference(equality_resolution,[],[f17])).
% 6.90/1.28  fof(f17,plain,(
% 6.90/1.28    ( ! [X0,X3,X1] : (X1 != X3 | sP4(X3,X1,X0)) )),
% 6.90/1.28    inference(cnf_transformation,[],[f2])).
% 6.90/1.28  fof(f310,plain,(
% 6.90/1.28    sP7(sK5(sK0,k1_relat_1(k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))),k1_relat_1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))),
% 6.90/1.28    inference(unit_resulting_resolution,[],[f123,f37,f134])).
% 6.90/1.28  fof(f134,plain,(
% 6.90/1.28    ( ! [X2,X3] : (sP7(sK5(X2,k1_relat_1(X3)),X3) | ~r2_hidden(X2,k1_relat_1(X3)) | k1_enumset1(X2,X2,X2) = k1_relat_1(X3)) )),
% 6.90/1.28    inference(resolution,[],[f121,f56])).
% 6.90/1.29  % SZS output end Proof for theBenchmark
% 6.90/1.29  % (23927)------------------------------
% 6.90/1.29  % (23927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.90/1.29  % (23927)Termination reason: Refutation
% 6.90/1.29  
% 6.90/1.29  % (23927)Memory used [KB]: 7803
% 6.90/1.29  % (23927)Time elapsed: 0.833 s
% 6.90/1.29  % (23927)------------------------------
% 6.90/1.29  % (23927)------------------------------
% 6.90/1.29  % (23907)Success in time 0.91 s
%------------------------------------------------------------------------------
