%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:12 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 190 expanded)
%              Number of leaves         :   12 (  49 expanded)
%              Depth                    :   17
%              Number of atoms          :  191 ( 780 expanded)
%              Number of equality atoms :   39 (  68 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f445,plain,(
    $false ),
    inference(subsumption_resolution,[],[f437,f33])).

fof(f33,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & v2_funct_1(sK2)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

fof(f437,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f51,f417])).

fof(f417,plain,(
    sK0 = k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(resolution,[],[f411,f69])).

fof(f69,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k1_setfam_1(k2_tarski(X3,X4)))
      | k1_setfam_1(k2_tarski(X3,X4)) = X3 ) ),
    inference(resolution,[],[f43,f46])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f411,plain,(
    r1_tarski(sK0,k1_setfam_1(k2_tarski(sK0,sK1))) ),
    inference(backward_demodulation,[],[f240,f406])).

fof(f406,plain,(
    sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f404,f337])).

fof(f337,plain,(
    ! [X6] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X6)),X6) ),
    inference(superposition,[],[f60,f331])).

fof(f331,plain,(
    ! [X0] : k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) = X0 ),
    inference(subsumption_resolution,[],[f330,f28])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f330,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) = X0 ) ),
    inference(subsumption_resolution,[],[f329,f29])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f329,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) = X0 ) ),
    inference(resolution,[],[f132,f32])).

fof(f32,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f132,plain,(
    ! [X4,X5] :
      ( ~ v2_funct_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k2_xboole_0(k10_relat_1(X4,k9_relat_1(X4,X5)),X5) = X5 ) ),
    inference(resolution,[],[f40,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f44,f49])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f404,plain,
    ( sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0) ),
    inference(resolution,[],[f383,f43])).

fof(f383,plain,(
    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))) ),
    inference(superposition,[],[f51,f365])).

fof(f365,plain,(
    sK0 = k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) ),
    inference(subsumption_resolution,[],[f362,f28])).

fof(f362,plain,
    ( ~ v1_relat_1(sK2)
    | sK0 = k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))) ),
    inference(resolution,[],[f109,f31])).

fof(f31,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_setfam_1(k2_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) = X0 ) ),
    inference(resolution,[],[f37,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f39,f36])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f240,plain,(
    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_tarski(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f239,f28])).

% (500)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% (482)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% (472)Refutation not found, incomplete strategy% (472)------------------------------
% (472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (472)Termination reason: Refutation not found, incomplete strategy

% (472)Memory used [KB]: 10746
% (472)Time elapsed: 0.111 s
% (472)------------------------------
% (472)------------------------------
% (504)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (504)Refutation not found, incomplete strategy% (504)------------------------------
% (504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (504)Termination reason: Refutation not found, incomplete strategy

% (504)Memory used [KB]: 1663
% (504)Time elapsed: 0.001 s
% (504)------------------------------
% (504)------------------------------
% (481)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% (483)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (471)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% (473)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% (469)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% (480)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (497)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f239,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_tarski(sK0,sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f238,f29])).

fof(f238,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_tarski(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f234,f32])).

fof(f234,plain,
    ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_tarski(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f40,f222])).

fof(f222,plain,(
    k9_relat_1(sK2,sK0) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1))) ),
    inference(superposition,[],[f162,f97])).

fof(f97,plain,(
    k9_relat_1(sK2,sK0) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f47,f30])).

fof(f30,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f162,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ),
    inference(subsumption_resolution,[],[f161,f28])).

fof(f161,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f160,f29])).

fof(f160,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f48,f32])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f45,f36,f36])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[],[f46,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:43:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (462)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (499)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (478)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (464)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (468)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (470)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (478)Refutation not found, incomplete strategy% (478)------------------------------
% 0.21/0.52  % (478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (478)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (478)Memory used [KB]: 10618
% 0.21/0.52  % (478)Time elapsed: 0.113 s
% 0.21/0.52  % (478)------------------------------
% 0.21/0.52  % (478)------------------------------
% 0.21/0.52  % (463)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (498)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (475)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (479)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (465)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (503)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (477)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (476)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (503)Refutation not found, incomplete strategy% (503)------------------------------
% 0.21/0.54  % (503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (503)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (503)Memory used [KB]: 10746
% 0.21/0.54  % (503)Time elapsed: 0.131 s
% 0.21/0.54  % (503)------------------------------
% 0.21/0.54  % (503)------------------------------
% 0.21/0.54  % (467)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.29/0.54  % (466)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.29/0.55  % (501)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.29/0.55  % (502)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.29/0.55  % (468)Refutation found. Thanks to Tanya!
% 1.29/0.55  % SZS status Theorem for theBenchmark
% 1.29/0.55  % (472)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.29/0.55  % SZS output start Proof for theBenchmark
% 1.29/0.55  fof(f445,plain,(
% 1.29/0.55    $false),
% 1.29/0.55    inference(subsumption_resolution,[],[f437,f33])).
% 1.29/0.55  fof(f33,plain,(
% 1.29/0.55    ~r1_tarski(sK0,sK1)),
% 1.29/0.55    inference(cnf_transformation,[],[f25])).
% 1.29/0.55  fof(f25,plain,(
% 1.29/0.55    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.29/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f24])).
% 1.29/0.55  fof(f24,plain,(
% 1.29/0.55    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.29/0.55    introduced(choice_axiom,[])).
% 1.29/0.55  fof(f14,plain,(
% 1.29/0.55    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.29/0.55    inference(flattening,[],[f13])).
% 1.29/0.55  fof(f13,plain,(
% 1.29/0.55    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.29/0.55    inference(ennf_transformation,[],[f12])).
% 1.29/0.55  fof(f12,negated_conjecture,(
% 1.29/0.55    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.29/0.55    inference(negated_conjecture,[],[f11])).
% 1.29/0.55  fof(f11,conjecture,(
% 1.29/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).
% 1.29/0.55  fof(f437,plain,(
% 1.29/0.55    r1_tarski(sK0,sK1)),
% 1.29/0.55    inference(superposition,[],[f51,f417])).
% 1.29/0.55  fof(f417,plain,(
% 1.29/0.55    sK0 = k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.29/0.55    inference(resolution,[],[f411,f69])).
% 1.29/0.55  fof(f69,plain,(
% 1.29/0.55    ( ! [X4,X3] : (~r1_tarski(X3,k1_setfam_1(k2_tarski(X3,X4))) | k1_setfam_1(k2_tarski(X3,X4)) = X3) )),
% 1.29/0.55    inference(resolution,[],[f43,f46])).
% 1.29/0.55  fof(f46,plain,(
% 1.29/0.55    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 1.29/0.55    inference(definition_unfolding,[],[f34,f36])).
% 1.29/0.55  fof(f36,plain,(
% 1.29/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.29/0.55    inference(cnf_transformation,[],[f7])).
% 1.29/0.55  fof(f7,axiom,(
% 1.29/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.29/0.55  fof(f34,plain,(
% 1.29/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f4])).
% 1.29/0.55  fof(f4,axiom,(
% 1.29/0.55    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.29/0.55  fof(f43,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f27])).
% 1.29/0.55  fof(f27,plain,(
% 1.29/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.29/0.55    inference(flattening,[],[f26])).
% 1.29/0.55  fof(f26,plain,(
% 1.29/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.29/0.55    inference(nnf_transformation,[],[f1])).
% 1.29/0.55  fof(f1,axiom,(
% 1.29/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.29/0.55  fof(f411,plain,(
% 1.29/0.55    r1_tarski(sK0,k1_setfam_1(k2_tarski(sK0,sK1)))),
% 1.29/0.55    inference(backward_demodulation,[],[f240,f406])).
% 1.29/0.55  fof(f406,plain,(
% 1.29/0.55    sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0))),
% 1.29/0.55    inference(subsumption_resolution,[],[f404,f337])).
% 1.29/0.55  fof(f337,plain,(
% 1.29/0.55    ( ! [X6] : (r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X6)),X6)) )),
% 1.29/0.55    inference(superposition,[],[f60,f331])).
% 1.29/0.55  fof(f331,plain,(
% 1.29/0.55    ( ! [X0] : (k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) = X0) )),
% 1.29/0.55    inference(subsumption_resolution,[],[f330,f28])).
% 1.29/0.55  fof(f28,plain,(
% 1.29/0.55    v1_relat_1(sK2)),
% 1.29/0.55    inference(cnf_transformation,[],[f25])).
% 1.29/0.55  fof(f330,plain,(
% 1.29/0.55    ( ! [X0] : (~v1_relat_1(sK2) | k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) = X0) )),
% 1.29/0.55    inference(subsumption_resolution,[],[f329,f29])).
% 1.29/0.55  fof(f29,plain,(
% 1.29/0.55    v1_funct_1(sK2)),
% 1.29/0.55    inference(cnf_transformation,[],[f25])).
% 1.29/0.55  fof(f329,plain,(
% 1.29/0.55    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_xboole_0(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) = X0) )),
% 1.29/0.55    inference(resolution,[],[f132,f32])).
% 1.29/0.55  fof(f32,plain,(
% 1.29/0.55    v2_funct_1(sK2)),
% 1.29/0.55    inference(cnf_transformation,[],[f25])).
% 1.29/0.55  fof(f132,plain,(
% 1.29/0.55    ( ! [X4,X5] : (~v2_funct_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | k2_xboole_0(k10_relat_1(X4,k9_relat_1(X4,X5)),X5) = X5) )),
% 1.29/0.55    inference(resolution,[],[f40,f38])).
% 1.29/0.55  fof(f38,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.29/0.55    inference(cnf_transformation,[],[f17])).
% 1.29/0.55  fof(f17,plain,(
% 1.29/0.55    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.29/0.55    inference(ennf_transformation,[],[f3])).
% 1.29/0.55  fof(f3,axiom,(
% 1.29/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.29/0.55  fof(f40,plain,(
% 1.29/0.55    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f20])).
% 1.29/0.55  fof(f20,plain,(
% 1.29/0.55    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.29/0.55    inference(flattening,[],[f19])).
% 1.29/0.55  fof(f19,plain,(
% 1.29/0.55    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.29/0.55    inference(ennf_transformation,[],[f10])).
% 1.29/0.55  fof(f10,axiom,(
% 1.29/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 1.29/0.55  fof(f60,plain,(
% 1.29/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.29/0.55    inference(resolution,[],[f44,f49])).
% 1.29/0.55  fof(f49,plain,(
% 1.29/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.29/0.55    inference(equality_resolution,[],[f42])).
% 1.29/0.55  fof(f42,plain,(
% 1.29/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.29/0.55    inference(cnf_transformation,[],[f27])).
% 1.29/0.55  fof(f44,plain,(
% 1.29/0.55    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f21])).
% 1.29/0.55  fof(f21,plain,(
% 1.29/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.29/0.55    inference(ennf_transformation,[],[f2])).
% 1.29/0.55  fof(f2,axiom,(
% 1.29/0.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.29/0.55  fof(f404,plain,(
% 1.29/0.55    sK0 = k10_relat_1(sK2,k9_relat_1(sK2,sK0)) | ~r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),sK0)),
% 1.29/0.55    inference(resolution,[],[f383,f43])).
% 1.29/0.55  fof(f383,plain,(
% 1.29/0.55    r1_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0)))),
% 1.29/0.55    inference(superposition,[],[f51,f365])).
% 1.29/0.55  fof(f365,plain,(
% 1.29/0.55    sK0 = k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))))),
% 1.29/0.55    inference(subsumption_resolution,[],[f362,f28])).
% 1.29/0.55  fof(f362,plain,(
% 1.29/0.55    ~v1_relat_1(sK2) | sK0 = k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,k9_relat_1(sK2,sK0))))),
% 1.29/0.55    inference(resolution,[],[f109,f31])).
% 1.29/0.55  fof(f31,plain,(
% 1.29/0.55    r1_tarski(sK0,k1_relat_1(sK2))),
% 1.29/0.55    inference(cnf_transformation,[],[f25])).
% 1.29/0.55  fof(f109,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_setfam_1(k2_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) = X0) )),
% 1.29/0.55    inference(resolution,[],[f37,f47])).
% 1.29/0.55  fof(f47,plain,(
% 1.29/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 1.29/0.55    inference(definition_unfolding,[],[f39,f36])).
% 1.29/0.55  fof(f39,plain,(
% 1.29/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f18])).
% 1.29/0.55  fof(f18,plain,(
% 1.29/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.29/0.55    inference(ennf_transformation,[],[f5])).
% 1.29/0.55  fof(f5,axiom,(
% 1.29/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.29/0.55  fof(f37,plain,(
% 1.29/0.55    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.29/0.55    inference(cnf_transformation,[],[f16])).
% 1.29/0.55  fof(f16,plain,(
% 1.29/0.55    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.29/0.55    inference(flattening,[],[f15])).
% 1.29/0.55  fof(f15,plain,(
% 1.29/0.55    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.29/0.55    inference(ennf_transformation,[],[f9])).
% 1.29/0.55  fof(f9,axiom,(
% 1.29/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.29/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 1.29/0.55  fof(f240,plain,(
% 1.29/0.55    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_tarski(sK0,sK1)))),
% 1.29/0.55    inference(subsumption_resolution,[],[f239,f28])).
% 1.29/0.55  % (500)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.29/0.55  % (482)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.29/0.55  % (472)Refutation not found, incomplete strategy% (472)------------------------------
% 1.29/0.55  % (472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (472)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (472)Memory used [KB]: 10746
% 1.29/0.55  % (472)Time elapsed: 0.111 s
% 1.29/0.55  % (472)------------------------------
% 1.29/0.55  % (472)------------------------------
% 1.29/0.55  % (504)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.29/0.55  % (504)Refutation not found, incomplete strategy% (504)------------------------------
% 1.29/0.55  % (504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (504)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (504)Memory used [KB]: 1663
% 1.29/0.55  % (504)Time elapsed: 0.001 s
% 1.29/0.55  % (504)------------------------------
% 1.29/0.55  % (504)------------------------------
% 1.29/0.55  % (481)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.29/0.55  % (483)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.29/0.56  % (471)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.29/0.56  % (473)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.29/0.56  % (469)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.49/0.57  % (480)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.49/0.57  % (497)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.49/0.57  fof(f239,plain,(
% 1.49/0.57    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_tarski(sK0,sK1))) | ~v1_relat_1(sK2)),
% 1.49/0.57    inference(subsumption_resolution,[],[f238,f29])).
% 1.49/0.57  fof(f238,plain,(
% 1.49/0.57    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_tarski(sK0,sK1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.49/0.57    inference(subsumption_resolution,[],[f234,f32])).
% 1.49/0.57  fof(f234,plain,(
% 1.49/0.57    r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,sK0)),k1_setfam_1(k2_tarski(sK0,sK1))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.49/0.57    inference(superposition,[],[f40,f222])).
% 1.49/0.57  fof(f222,plain,(
% 1.49/0.57    k9_relat_1(sK2,sK0) = k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,sK1)))),
% 1.49/0.57    inference(superposition,[],[f162,f97])).
% 1.49/0.57  fof(f97,plain,(
% 1.49/0.57    k9_relat_1(sK2,sK0) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 1.49/0.57    inference(resolution,[],[f47,f30])).
% 1.49/0.57  fof(f30,plain,(
% 1.49/0.57    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 1.49/0.57    inference(cnf_transformation,[],[f25])).
% 1.49/0.57  fof(f162,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f161,f28])).
% 1.49/0.57  fof(f161,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) | ~v1_relat_1(sK2)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f160,f29])).
% 1.49/0.57  fof(f160,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.49/0.57    inference(resolution,[],[f48,f32])).
% 1.49/0.57  fof(f48,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.49/0.57    inference(definition_unfolding,[],[f45,f36,f36])).
% 1.49/0.57  fof(f45,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f23])).
% 1.49/0.57  fof(f23,plain,(
% 1.49/0.57    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.49/0.57    inference(flattening,[],[f22])).
% 1.49/0.57  fof(f22,plain,(
% 1.49/0.57    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.49/0.57    inference(ennf_transformation,[],[f8])).
% 1.49/0.57  fof(f8,axiom,(
% 1.49/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).
% 1.49/0.57  fof(f51,plain,(
% 1.49/0.57    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) )),
% 1.49/0.57    inference(superposition,[],[f46,f35])).
% 1.49/0.57  fof(f35,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f6])).
% 1.49/0.57  fof(f6,axiom,(
% 1.49/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.49/0.57  % SZS output end Proof for theBenchmark
% 1.49/0.57  % (468)------------------------------
% 1.49/0.57  % (468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (468)Termination reason: Refutation
% 1.49/0.57  
% 1.49/0.57  % (468)Memory used [KB]: 11001
% 1.49/0.57  % (468)Time elapsed: 0.141 s
% 1.49/0.57  % (468)------------------------------
% 1.49/0.57  % (468)------------------------------
% 1.49/0.57  % (461)Success in time 0.203 s
%------------------------------------------------------------------------------
