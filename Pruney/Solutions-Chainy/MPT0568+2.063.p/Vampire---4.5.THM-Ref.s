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
% DateTime   : Thu Dec  3 12:50:18 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   57 (  71 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  159 ( 193 expanded)
%              Number of equality atoms :   21 (  23 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f126,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f37,f124,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f124,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k1_xboole_0,X0),X1) ),
    inference(subsumption_resolution,[],[f120,f60])).

fof(f60,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f58,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK3(X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK3(X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f58,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f57,f40])).

fof(f40,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f46,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f120,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,X0),X1)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f109,f70])).

fof(f70,plain,(
    ! [X0,X1] : ~ sP0(X0,k1_xboole_0,X1) ),
    inference(subsumption_resolution,[],[f69,f58])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,k1_xboole_0,X1),k1_xboole_0)
      | ~ sP0(X0,k1_xboole_0,X1) ) ),
    inference(superposition,[],[f51,f39])).

fof(f39,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),k2_relat_1(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(X3,k2_relat_1(X1)) ) )
      & ( ( r2_hidden(sK6(X0,X1,X2),X0)
          & r2_hidden(k4_tarski(X2,sK6(X0,X1,X2)),X1)
          & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(k4_tarski(X2,X4),X1)
          & r2_hidden(X4,k2_relat_1(X1)) )
     => ( r2_hidden(sK6(X0,X1,X2),X0)
        & r2_hidden(k4_tarski(X2,sK6(X0,X1,X2)),X1)
        & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(X3,k2_relat_1(X1)) ) )
      & ( ? [X4] :
            ( r2_hidden(X4,X0)
            & r2_hidden(k4_tarski(X2,X4),X1)
            & r2_hidden(X4,k2_relat_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f33])).

% (16939)Refutation not found, incomplete strategy% (16939)------------------------------
% (16939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16939)Termination reason: Refutation not found, incomplete strategy

% (16939)Memory used [KB]: 10618
% (16939)Time elapsed: 0.132 s
% (16939)------------------------------
% (16939)------------------------------
fof(f33,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X0,X3),X2)
            | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

% (16951)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f20,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(k4_tarski(X0,X3),X2)
          & r2_hidden(X3,k2_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,sK5(k10_relat_1(X1,X0),X2))
      | r1_tarski(k10_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f75,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f19,f21,f20])).

fof(f21,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f75,plain,(
    ! [X4,X2,X3] :
      ( ~ sP1(sK5(k10_relat_1(X3,X2),X4),X3,X2)
      | sP0(X2,X3,sK5(k10_relat_1(X3,X2),X4))
      | r1_tarski(k10_relat_1(X3,X2),X4) ) ),
    inference(resolution,[],[f49,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X1,X2))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,k10_relat_1(X1,X2)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f37,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f23])).

fof(f23,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (16938)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (16952)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (16944)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (16938)Refutation not found, incomplete strategy% (16938)------------------------------
% 0.20/0.52  % (16938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (16938)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (16938)Memory used [KB]: 10618
% 0.20/0.52  % (16938)Time elapsed: 0.103 s
% 0.20/0.52  % (16938)------------------------------
% 0.20/0.52  % (16938)------------------------------
% 0.20/0.52  % (16933)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (16933)Refutation not found, incomplete strategy% (16933)------------------------------
% 0.20/0.52  % (16933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (16933)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (16933)Memory used [KB]: 6140
% 0.20/0.52  % (16933)Time elapsed: 0.117 s
% 0.20/0.52  % (16933)------------------------------
% 0.20/0.52  % (16933)------------------------------
% 1.30/0.54  % (16955)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.30/0.54  % (16930)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.30/0.54  % (16941)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.54  % (16943)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.30/0.54  % (16929)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.30/0.54  % (16929)Refutation not found, incomplete strategy% (16929)------------------------------
% 1.30/0.54  % (16929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (16931)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.54  % (16929)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (16929)Memory used [KB]: 1663
% 1.30/0.54  % (16929)Time elapsed: 0.127 s
% 1.30/0.54  % (16929)------------------------------
% 1.30/0.54  % (16929)------------------------------
% 1.30/0.54  % (16932)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.30/0.54  % (16958)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.30/0.54  % (16934)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.30/0.54  % (16939)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.30/0.54  % (16958)Refutation found. Thanks to Tanya!
% 1.30/0.54  % SZS status Theorem for theBenchmark
% 1.30/0.54  % SZS output start Proof for theBenchmark
% 1.30/0.54  fof(f126,plain,(
% 1.30/0.54    $false),
% 1.30/0.54    inference(unit_resulting_resolution,[],[f37,f124,f42])).
% 1.30/0.54  fof(f42,plain,(
% 1.30/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.30/0.54    inference(cnf_transformation,[],[f15])).
% 1.30/0.54  fof(f15,plain,(
% 1.30/0.54    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.30/0.54    inference(ennf_transformation,[],[f4])).
% 1.30/0.54  fof(f4,axiom,(
% 1.30/0.54    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.30/0.54  fof(f124,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),X1)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f120,f60])).
% 1.30/0.54  fof(f60,plain,(
% 1.30/0.54    v1_relat_1(k1_xboole_0)),
% 1.30/0.54    inference(resolution,[],[f58,f43])).
% 1.30/0.54  fof(f43,plain,(
% 1.30/0.54    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_relat_1(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f26])).
% 1.30/0.54  fof(f26,plain,(
% 1.30/0.54    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK3(X0) & r2_hidden(sK3(X0),X0)))),
% 1.30/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f25])).
% 1.30/0.54  fof(f25,plain,(
% 1.30/0.54    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK3(X0) & r2_hidden(sK3(X0),X0)))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f16,plain,(
% 1.30/0.54    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f12])).
% 1.30/0.54  fof(f12,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 1.30/0.54    inference(unused_predicate_definition_removal,[],[f6])).
% 1.30/0.54  fof(f6,axiom,(
% 1.30/0.54    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 1.30/0.54  fof(f58,plain,(
% 1.30/0.54    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f57,f40])).
% 1.30/0.54  fof(f40,plain,(
% 1.30/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f5])).
% 1.30/0.54  fof(f5,axiom,(
% 1.30/0.54    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.30/0.54  fof(f57,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 1.30/0.54    inference(superposition,[],[f46,f41])).
% 1.30/0.54  fof(f41,plain,(
% 1.30/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f3])).
% 1.30/0.54  fof(f3,axiom,(
% 1.30/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.30/0.54  fof(f46,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f28])).
% 1.30/0.54  fof(f28,plain,(
% 1.30/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.30/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f27])).
% 1.30/0.54  fof(f27,plain,(
% 1.30/0.54    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f17,plain,(
% 1.30/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.30/0.54    inference(ennf_transformation,[],[f11])).
% 1.30/0.54  fof(f11,plain,(
% 1.30/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.30/0.54    inference(rectify,[],[f2])).
% 1.30/0.54  fof(f2,axiom,(
% 1.30/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.30/0.54  fof(f120,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),X1) | ~v1_relat_1(k1_xboole_0)) )),
% 1.30/0.54    inference(resolution,[],[f109,f70])).
% 1.30/0.54  fof(f70,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~sP0(X0,k1_xboole_0,X1)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f69,f58])).
% 1.30/0.54  fof(f69,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r2_hidden(sK6(X0,k1_xboole_0,X1),k1_xboole_0) | ~sP0(X0,k1_xboole_0,X1)) )),
% 1.30/0.54    inference(superposition,[],[f51,f39])).
% 1.30/0.54  fof(f39,plain,(
% 1.30/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.30/0.54    inference(cnf_transformation,[],[f8])).
% 1.30/0.54  fof(f8,axiom,(
% 1.30/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.30/0.54  fof(f51,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),k2_relat_1(X1)) | ~sP0(X0,X1,X2)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f36])).
% 1.30/0.54  fof(f36,plain,(
% 1.30/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(X3,k2_relat_1(X1)))) & ((r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(k4_tarski(X2,sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X1))) | ~sP0(X0,X1,X2)))),
% 1.30/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).
% 1.30/0.54  fof(f35,plain,(
% 1.30/0.54    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X2,X4),X1) & r2_hidden(X4,k2_relat_1(X1))) => (r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(k4_tarski(X2,sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X1))))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f34,plain,(
% 1.30/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(X3,k2_relat_1(X1)))) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X2,X4),X1) & r2_hidden(X4,k2_relat_1(X1))) | ~sP0(X0,X1,X2)))),
% 1.30/0.54    inference(rectify,[],[f33])).
% 1.30/0.54  % (16939)Refutation not found, incomplete strategy% (16939)------------------------------
% 1.30/0.54  % (16939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (16939)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (16939)Memory used [KB]: 10618
% 1.30/0.54  % (16939)Time elapsed: 0.132 s
% 1.30/0.54  % (16939)------------------------------
% 1.30/0.54  % (16939)------------------------------
% 1.30/0.54  fof(f33,plain,(
% 1.30/0.54    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~sP0(X1,X2,X0)))),
% 1.30/0.54    inference(nnf_transformation,[],[f20])).
% 1.30/0.54  % (16951)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.30/0.54  fof(f20,plain,(
% 1.30/0.54    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))))),
% 1.30/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.30/0.54  fof(f109,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (sP0(X0,X1,sK5(k10_relat_1(X1,X0),X2)) | r1_tarski(k10_relat_1(X1,X0),X2) | ~v1_relat_1(X1)) )),
% 1.30/0.54    inference(resolution,[],[f75,f55])).
% 1.30/0.54  fof(f55,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~v1_relat_1(X2)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f22])).
% 1.30/0.54  fof(f22,plain,(
% 1.30/0.54    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~v1_relat_1(X2))),
% 1.30/0.54    inference(definition_folding,[],[f19,f21,f20])).
% 1.30/0.54  fof(f21,plain,(
% 1.30/0.54    ! [X0,X2,X1] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 1.30/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.30/0.54  fof(f19,plain,(
% 1.30/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.30/0.54    inference(ennf_transformation,[],[f7])).
% 1.30/0.54  fof(f7,axiom,(
% 1.30/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 1.30/0.54  fof(f75,plain,(
% 1.30/0.54    ( ! [X4,X2,X3] : (~sP1(sK5(k10_relat_1(X3,X2),X4),X3,X2) | sP0(X2,X3,sK5(k10_relat_1(X3,X2),X4)) | r1_tarski(k10_relat_1(X3,X2),X4)) )),
% 1.30/0.54    inference(resolution,[],[f49,f47])).
% 1.30/0.54  fof(f47,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f30])).
% 1.30/0.54  fof(f30,plain,(
% 1.30/0.54    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.30/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f29])).
% 1.30/0.54  fof(f29,plain,(
% 1.30/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f18,plain,(
% 1.30/0.54    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f13])).
% 1.30/0.54  fof(f13,plain,(
% 1.30/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.30/0.54    inference(unused_predicate_definition_removal,[],[f1])).
% 1.30/0.54  fof(f1,axiom,(
% 1.30/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.30/0.54  fof(f49,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X1,X2)) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f32])).
% 1.30/0.54  fof(f32,plain,(
% 1.30/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X1,X2)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,k10_relat_1(X1,X2)))) | ~sP1(X0,X1,X2))),
% 1.30/0.54    inference(rectify,[],[f31])).
% 1.30/0.54  fof(f31,plain,(
% 1.30/0.54    ! [X0,X2,X1] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~sP1(X0,X2,X1))),
% 1.30/0.54    inference(nnf_transformation,[],[f21])).
% 1.30/0.54  fof(f37,plain,(
% 1.30/0.54    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2)),
% 1.30/0.54    inference(cnf_transformation,[],[f24])).
% 1.30/0.54  fof(f24,plain,(
% 1.30/0.54    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2)),
% 1.30/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f23])).
% 1.30/0.54  fof(f23,plain,(
% 1.30/0.54    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2)),
% 1.30/0.54    introduced(choice_axiom,[])).
% 1.30/0.54  fof(f14,plain,(
% 1.30/0.54    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 1.30/0.54    inference(ennf_transformation,[],[f10])).
% 1.30/0.54  fof(f10,negated_conjecture,(
% 1.30/0.54    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.30/0.54    inference(negated_conjecture,[],[f9])).
% 1.30/0.54  fof(f9,conjecture,(
% 1.30/0.54    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
% 1.30/0.54  % SZS output end Proof for theBenchmark
% 1.30/0.54  % (16958)------------------------------
% 1.30/0.54  % (16958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (16958)Termination reason: Refutation
% 1.30/0.54  
% 1.30/0.54  % (16958)Memory used [KB]: 1791
% 1.30/0.54  % (16958)Time elapsed: 0.141 s
% 1.30/0.54  % (16958)------------------------------
% 1.30/0.54  % (16958)------------------------------
% 1.30/0.54  % (16940)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.30/0.54  % (16928)Success in time 0.183 s
%------------------------------------------------------------------------------
