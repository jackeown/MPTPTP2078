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
% DateTime   : Thu Dec  3 12:50:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 190 expanded)
%              Number of leaves         :   21 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  160 ( 297 expanded)
%              Number of equality atoms :   55 ( 171 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f86,f39,f89,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1,sK4(k10_relat_1(X1,X0)))
      | k1_xboole_0 = k10_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f77,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f21,f23,f22])).

fof(f22,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(k4_tarski(X0,X3),X2)
          & r2_hidden(X3,k2_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f77,plain,(
    ! [X2,X3] :
      ( ~ sP1(sK4(k10_relat_1(X3,X2)),X3,X2)
      | sP0(X2,X3,sK4(k10_relat_1(X3,X2)))
      | k1_xboole_0 = k10_relat_1(X3,X2) ) ),
    inference(resolution,[],[f49,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

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
    inference(nnf_transformation,[],[f23])).

fof(f89,plain,(
    ! [X2,X3] : ~ sP0(X2,k1_xboole_0,X3) ),
    inference(resolution,[],[f85,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK5(X0,X1,X2)),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(X3,k2_relat_1(X1)) ) )
      & ( ( r2_hidden(sK5(X0,X1,X2),X0)
          & r2_hidden(k4_tarski(X2,sK5(X0,X1,X2)),X1)
          & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(k4_tarski(X2,X4),X1)
          & r2_hidden(X4,k2_relat_1(X1)) )
     => ( r2_hidden(sK5(X0,X1,X2),X0)
        & r2_hidden(k4_tarski(X2,sK5(X0,X1,X2)),X1)
        & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X1)) ) ) ),
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
    inference(nnf_transformation,[],[f22])).

fof(f85,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f75,f71])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) ),
    inference(definition_unfolding,[],[f40,f69])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f47,f68])).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f59,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f60,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f75,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))) ) ),
    inference(definition_unfolding,[],[f57,f69,f70])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f67])).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f39,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f25])).

fof(f25,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

fof(f86,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f85,f42])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK3(X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK3(X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (5947)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.49  % (5954)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.50  % (5965)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.50  % (5970)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.50  % (5954)Refutation not found, incomplete strategy% (5954)------------------------------
% 0.20/0.50  % (5954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (5949)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (5966)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (5948)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (5962)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (5954)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (5954)Memory used [KB]: 10618
% 0.20/0.51  % (5954)Time elapsed: 0.104 s
% 0.20/0.51  % (5954)------------------------------
% 0.20/0.51  % (5954)------------------------------
% 0.20/0.51  % (5948)Refutation not found, incomplete strategy% (5948)------------------------------
% 0.20/0.51  % (5948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5948)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (5948)Memory used [KB]: 6140
% 0.20/0.51  % (5948)Time elapsed: 0.109 s
% 0.20/0.51  % (5948)------------------------------
% 0.20/0.51  % (5948)------------------------------
% 0.20/0.51  % (5958)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (5945)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (5946)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (5946)Refutation not found, incomplete strategy% (5946)------------------------------
% 0.20/0.51  % (5946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5946)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (5946)Memory used [KB]: 10618
% 0.20/0.51  % (5946)Time elapsed: 0.116 s
% 0.20/0.51  % (5946)------------------------------
% 0.20/0.51  % (5946)------------------------------
% 0.20/0.51  % (5970)Refutation not found, incomplete strategy% (5970)------------------------------
% 0.20/0.51  % (5970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5973)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (5973)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f86,f39,f89,f106])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    ( ! [X0,X1] : (sP0(X0,X1,sK4(k10_relat_1(X1,X0))) | k1_xboole_0 = k10_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(resolution,[],[f77,f55])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(definition_folding,[],[f21,f23,f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X2,X1] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~sP1(sK4(k10_relat_1(X3,X2)),X3,X2) | sP0(X2,X3,sK4(k10_relat_1(X3,X2))) | k1_xboole_0 = k10_relat_1(X3,X2)) )),
% 0.20/0.52    inference(resolution,[],[f49,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X1,X2)) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X1,X2)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,k10_relat_1(X1,X2)))) | ~sP1(X0,X1,X2))),
% 0.20/0.52    inference(rectify,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0,X2,X1] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~sP1(X0,X2,X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f23])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~sP0(X2,k1_xboole_0,X3)) )),
% 0.20/0.52    inference(resolution,[],[f85,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK5(X0,X1,X2)),X1) | ~sP0(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(X3,k2_relat_1(X1)))) & ((r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(k4_tarski(X2,sK5(X0,X1,X2)),X1) & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X1))) | ~sP0(X0,X1,X2)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X2,X4),X1) & r2_hidden(X4,k2_relat_1(X1))) => (r2_hidden(sK5(X0,X1,X2),X0) & r2_hidden(k4_tarski(X2,sK5(X0,X1,X2)),X1) & r2_hidden(sK5(X0,X1,X2),k2_relat_1(X1))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(X3,k2_relat_1(X1)))) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X2,X4),X1) & r2_hidden(X4,k2_relat_1(X1))) | ~sP0(X0,X1,X2)))),
% 0.20/0.52    inference(rectify,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~sP0(X1,X2,X0)))),
% 0.20/0.52    inference(nnf_transformation,[],[f22])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(superposition,[],[f75,f71])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f40,f69])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f47,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f45,f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f46,f66])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f48,f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f59,f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f60,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f61,f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) )),
% 0.20/0.52    inference(equality_resolution,[],[f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f57,f69,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f41,f67])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.20/0.52    inference(flattening,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.20/0.52    inference(nnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK2)),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.20/0.52    inference(ennf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,negated_conjecture,(
% 0.20/0.52    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.20/0.52    inference(negated_conjecture,[],[f15])).
% 0.20/0.52  fof(f15,conjecture,(
% 0.20/0.52    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    v1_relat_1(k1_xboole_0)),
% 0.20/0.52    inference(resolution,[],[f85,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK3(X0) & r2_hidden(sK3(X0),X0)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK3(X0) & r2_hidden(sK3(X0),X0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.20/0.52    inference(unused_predicate_definition_removal,[],[f13])).
% 0.20/0.52  fof(f13,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (5973)------------------------------
% 0.20/0.52  % (5973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5973)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (5973)Memory used [KB]: 1791
% 0.20/0.52  % (5973)Time elapsed: 0.119 s
% 0.20/0.52  % (5973)------------------------------
% 0.20/0.52  % (5973)------------------------------
% 0.20/0.52  % (5970)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  % (5944)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  
% 0.20/0.52  % (5970)Memory used [KB]: 10618
% 0.20/0.52  % (5970)Time elapsed: 0.115 s
% 0.20/0.52  % (5970)------------------------------
% 0.20/0.52  % (5970)------------------------------
% 0.20/0.52  % (5943)Success in time 0.165 s
%------------------------------------------------------------------------------
