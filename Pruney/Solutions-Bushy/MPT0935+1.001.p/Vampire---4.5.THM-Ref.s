%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0935+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:56 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   19 (  29 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   32 (  54 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,plain,(
    $false ),
    inference(subsumption_resolution,[],[f21,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(global_subsumption,[],[f13,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_relat_1(X4) = k2_tarski(X0,X2)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k1_relat_1(X4) = k2_tarski(X0,X2) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k1_relat_1(X4) = k2_tarski(X0,X2) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
       => ( k2_relat_1(X4) = k2_tarski(X1,X3)
          & k1_relat_1(X4) = k2_tarski(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relat_1)).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).

fof(f21,plain,(
    k2_tarski(sK0,sK3) != k1_relat_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK3,sK4))) ),
    inference(backward_demodulation,[],[f16,f20])).

% (16521)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (16519)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (16519)Refutation not found, incomplete strategy% (16519)------------------------------
% (16519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16519)Termination reason: Refutation not found, incomplete strategy

% (16519)Memory used [KB]: 10618
% (16519)Time elapsed: 0.097 s
% (16519)------------------------------
% (16519)------------------------------
fof(f16,plain,(
    k2_tarski(sK0,sK3) != k1_relat_1(k1_relat_1(k2_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK3,sK4),sK5)))) ),
    inference(definition_unfolding,[],[f11,f12,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f11,plain,(
    k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK3,sK4,sK5)))) != k2_tarski(sK0,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK3,sK4,sK5)))) != k2_tarski(sK0,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) != k2_tarski(X0,X3)
   => k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK3,sK4,sK5)))) != k2_tarski(sK0,sK3) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) != k2_tarski(X0,X3) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) = k2_tarski(X0,X3) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k1_relat_1(k1_relat_1(k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X3,X4,X5)))) = k2_tarski(X0,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_mcart_1)).

%------------------------------------------------------------------------------
