%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   76 (  83 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :   17
%              Number of atoms          :  245 ( 269 expanded)
%              Number of equality atoms :  124 ( 138 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f303,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f296])).

fof(f296,plain,(
    k6_subset_1(k1_relat_1(sK3),sK2) != k6_subset_1(k1_relat_1(sK3),sK2) ),
    inference(superposition,[],[f41,f289])).

fof(f289,plain,(
    ! [X0] : k6_subset_1(k1_relat_1(sK3),X0) = k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),X0))) ),
    inference(resolution,[],[f240,f40])).

fof(f40,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k6_subset_1(k1_relat_1(sK3),sK2) != k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2)))
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
        & v1_relat_1(X1) )
   => ( k6_subset_1(k1_relat_1(sK3),sK2) != k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2)))
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

fof(f240,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X12)
      | k6_subset_1(k1_relat_1(X12),X13) = k1_relat_1(k7_relat_1(X12,k6_subset_1(k1_relat_1(X12),X13))) ) ),
    inference(resolution,[],[f228,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f228,plain,(
    ! [X2,X3] : r1_tarski(k6_subset_1(X2,X3),X2) ),
    inference(subsumption_resolution,[],[f220,f81])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f220,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X2)
      | r1_tarski(k6_subset_1(X2,X3),X2) ) ),
    inference(resolution,[],[f211,f84])).

fof(f84,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X2,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f37])).

% (19135)Refutation not found, incomplete strategy% (19135)------------------------------
% (19135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19135)Termination reason: Refutation not found, incomplete strategy

% (19135)Memory used [KB]: 1663
% (19135)Time elapsed: 0.138 s
% (19135)------------------------------
% (19135)------------------------------
fof(f37,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
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
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
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
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f211,plain,(
    ! [X4,X5,X3] :
      ( ~ sP0(X3,X4,X5,X5,X5,X5,X5,X5,X5)
      | ~ r1_tarski(X5,X3)
      | r1_tarski(k6_subset_1(X5,X4),X3) ) ),
    inference(resolution,[],[f153,f188])).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
      | ~ r1_tarski(X0,X2)
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(resolution,[],[f123,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)
      | r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,X2) ) ),
    inference(superposition,[],[f53,f80])).

fof(f80,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f46,f42,f78])).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f55,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

% (19133)Refutation not found, incomplete strategy% (19133)------------------------------
% (19133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19133)Termination reason: Refutation not found, incomplete strategy

% (19133)Memory used [KB]: 10618
% (19133)Time elapsed: 0.135 s
% (19133)------------------------------
% (19133)------------------------------
fof(f52,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

% (19124)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f153,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1))
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(resolution,[],[f59,f91])).

fof(f91,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f24,f26,f25])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f59,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | r2_hidden(X10,X8) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ~ sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).

fof(f34,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X9,X8) )
          & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X9,X8) ) )
     => ( ( ~ sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f41,plain,(
    k6_subset_1(k1_relat_1(sK3),sK2) != k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:03:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (19140)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.51  % (19127)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (19123)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (19139)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.52  % (19133)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (19131)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (19122)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (19127)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (19134)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (19144)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (19136)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (19131)Refutation not found, incomplete strategy% (19131)------------------------------
% 0.22/0.54  % (19131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (19131)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (19131)Memory used [KB]: 10746
% 0.22/0.54  % (19131)Time elapsed: 0.120 s
% 0.22/0.54  % (19131)------------------------------
% 0.22/0.54  % (19131)------------------------------
% 0.22/0.54  % (19126)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.40/0.54  % (19135)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.40/0.54  % SZS output start Proof for theBenchmark
% 1.40/0.54  fof(f303,plain,(
% 1.40/0.54    $false),
% 1.40/0.54    inference(trivial_inequality_removal,[],[f296])).
% 1.40/0.54  fof(f296,plain,(
% 1.40/0.54    k6_subset_1(k1_relat_1(sK3),sK2) != k6_subset_1(k1_relat_1(sK3),sK2)),
% 1.40/0.54    inference(superposition,[],[f41,f289])).
% 1.40/0.54  fof(f289,plain,(
% 1.40/0.54    ( ! [X0] : (k6_subset_1(k1_relat_1(sK3),X0) = k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),X0)))) )),
% 1.40/0.54    inference(resolution,[],[f240,f40])).
% 1.40/0.54  fof(f40,plain,(
% 1.40/0.54    v1_relat_1(sK3)),
% 1.40/0.54    inference(cnf_transformation,[],[f29])).
% 1.40/0.54  fof(f29,plain,(
% 1.40/0.54    k6_subset_1(k1_relat_1(sK3),sK2) != k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))) & v1_relat_1(sK3)),
% 1.40/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f28])).
% 1.40/0.54  fof(f28,plain,(
% 1.40/0.54    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) & v1_relat_1(X1)) => (k6_subset_1(k1_relat_1(sK3),sK2) != k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))) & v1_relat_1(sK3))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f18,plain,(
% 1.40/0.54    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) & v1_relat_1(X1))),
% 1.40/0.54    inference(ennf_transformation,[],[f17])).
% 1.40/0.54  fof(f17,negated_conjecture,(
% 1.40/0.54    ~! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))))),
% 1.40/0.54    inference(negated_conjecture,[],[f16])).
% 1.40/0.54  fof(f16,conjecture,(
% 1.40/0.54    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).
% 1.40/0.54  fof(f240,plain,(
% 1.40/0.54    ( ! [X12,X13] : (~v1_relat_1(X12) | k6_subset_1(k1_relat_1(X12),X13) = k1_relat_1(k7_relat_1(X12,k6_subset_1(k1_relat_1(X12),X13)))) )),
% 1.40/0.54    inference(resolution,[],[f228,f47])).
% 1.40/0.54  fof(f47,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f20])).
% 1.40/0.54  fof(f20,plain,(
% 1.40/0.54    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.40/0.54    inference(flattening,[],[f19])).
% 1.40/0.54  fof(f19,plain,(
% 1.40/0.54    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.40/0.54    inference(ennf_transformation,[],[f15])).
% 1.40/0.54  fof(f15,axiom,(
% 1.40/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.40/0.54  fof(f228,plain,(
% 1.40/0.54    ( ! [X2,X3] : (r1_tarski(k6_subset_1(X2,X3),X2)) )),
% 1.40/0.54    inference(subsumption_resolution,[],[f220,f81])).
% 1.40/0.54  fof(f81,plain,(
% 1.40/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.40/0.54    inference(equality_resolution,[],[f50])).
% 1.40/0.54  fof(f50,plain,(
% 1.40/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.40/0.54    inference(cnf_transformation,[],[f31])).
% 1.40/0.54  fof(f31,plain,(
% 1.40/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.54    inference(flattening,[],[f30])).
% 1.40/0.54  fof(f30,plain,(
% 1.40/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.54    inference(nnf_transformation,[],[f1])).
% 1.40/0.54  fof(f1,axiom,(
% 1.40/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.40/0.54  fof(f220,plain,(
% 1.40/0.54    ( ! [X2,X3] : (~r1_tarski(X2,X2) | r1_tarski(k6_subset_1(X2,X3),X2)) )),
% 1.40/0.54    inference(resolution,[],[f211,f84])).
% 1.40/0.54  fof(f84,plain,(
% 1.40/0.54    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X2,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 1.40/0.54    inference(equality_resolution,[],[f69])).
% 1.40/0.54  fof(f69,plain,(
% 1.40/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X2) )),
% 1.40/0.54    inference(cnf_transformation,[],[f38])).
% 1.40/0.54  fof(f38,plain,(
% 1.40/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.40/0.54    inference(rectify,[],[f37])).
% 1.40/0.54  % (19135)Refutation not found, incomplete strategy% (19135)------------------------------
% 1.40/0.54  % (19135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (19135)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (19135)Memory used [KB]: 1663
% 1.40/0.54  % (19135)Time elapsed: 0.138 s
% 1.40/0.54  % (19135)------------------------------
% 1.40/0.54  % (19135)------------------------------
% 1.40/0.54  fof(f37,plain,(
% 1.40/0.54    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.40/0.54    inference(flattening,[],[f36])).
% 1.40/0.54  fof(f36,plain,(
% 1.40/0.54    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.40/0.54    inference(nnf_transformation,[],[f25])).
% 1.40/0.54  fof(f25,plain,(
% 1.40/0.54    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 1.40/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.40/0.54  fof(f211,plain,(
% 1.40/0.54    ( ! [X4,X5,X3] : (~sP0(X3,X4,X5,X5,X5,X5,X5,X5,X5) | ~r1_tarski(X5,X3) | r1_tarski(k6_subset_1(X5,X4),X3)) )),
% 1.40/0.54    inference(resolution,[],[f153,f188])).
% 1.40/0.54  fof(f188,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) | ~r1_tarski(X0,X2) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 1.40/0.54    inference(resolution,[],[f123,f48])).
% 1.40/0.54  fof(f48,plain,(
% 1.40/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f21])).
% 1.40/0.54  fof(f21,plain,(
% 1.40/0.54    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 1.40/0.54    inference(ennf_transformation,[],[f14])).
% 1.40/0.54  fof(f14,axiom,(
% 1.40/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 1.40/0.54  fof(f123,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) | r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,X2)) )),
% 1.40/0.54    inference(superposition,[],[f53,f80])).
% 1.40/0.54  fof(f80,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.40/0.54    inference(definition_unfolding,[],[f46,f42,f78])).
% 1.40/0.54  fof(f78,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.40/0.54    inference(definition_unfolding,[],[f44,f77])).
% 1.40/0.54  fof(f77,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.40/0.54    inference(definition_unfolding,[],[f45,f76])).
% 1.40/0.54  fof(f76,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.40/0.54    inference(definition_unfolding,[],[f52,f75])).
% 1.40/0.54  fof(f75,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.40/0.54    inference(definition_unfolding,[],[f54,f74])).
% 1.40/0.54  fof(f74,plain,(
% 1.40/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.40/0.54    inference(definition_unfolding,[],[f55,f73])).
% 1.40/0.54  fof(f73,plain,(
% 1.40/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.40/0.54    inference(definition_unfolding,[],[f56,f57])).
% 1.40/0.54  fof(f57,plain,(
% 1.40/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f10])).
% 1.40/0.54  fof(f10,axiom,(
% 1.40/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.40/0.54  fof(f56,plain,(
% 1.40/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f9])).
% 1.40/0.54  fof(f9,axiom,(
% 1.40/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.40/0.54  fof(f55,plain,(
% 1.40/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f8])).
% 1.40/0.54  fof(f8,axiom,(
% 1.40/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.40/0.54  fof(f54,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f7])).
% 1.40/0.54  fof(f7,axiom,(
% 1.40/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.40/0.54  % (19133)Refutation not found, incomplete strategy% (19133)------------------------------
% 1.40/0.54  % (19133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (19133)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (19133)Memory used [KB]: 10618
% 1.40/0.54  % (19133)Time elapsed: 0.135 s
% 1.40/0.54  % (19133)------------------------------
% 1.40/0.54  % (19133)------------------------------
% 1.40/0.54  fof(f52,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f6])).
% 1.40/0.54  fof(f6,axiom,(
% 1.40/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.40/0.54  % (19124)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.40/0.54  fof(f45,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f5])).
% 1.40/0.54  fof(f5,axiom,(
% 1.40/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.40/0.54  fof(f44,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f13])).
% 1.40/0.54  fof(f13,axiom,(
% 1.40/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.40/0.54  fof(f42,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f12])).
% 1.40/0.54  fof(f12,axiom,(
% 1.40/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.40/0.54  fof(f46,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f2])).
% 1.40/0.54  fof(f2,axiom,(
% 1.40/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.40/0.54  fof(f53,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f23])).
% 1.40/0.54  fof(f23,plain,(
% 1.40/0.54    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.40/0.54    inference(flattening,[],[f22])).
% 1.40/0.54  fof(f22,plain,(
% 1.40/0.54    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.40/0.54    inference(ennf_transformation,[],[f3])).
% 1.40/0.54  fof(f3,axiom,(
% 1.40/0.54    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).
% 1.40/0.54  fof(f153,plain,(
% 1.40/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1)) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 1.40/0.54    inference(resolution,[],[f59,f91])).
% 1.40/0.54  fof(f91,plain,(
% 1.40/0.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 1.40/0.54    inference(equality_resolution,[],[f71])).
% 1.40/0.54  fof(f71,plain,(
% 1.40/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 1.40/0.54    inference(cnf_transformation,[],[f39])).
% 1.40/0.54  fof(f39,plain,(
% 1.40/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 1.40/0.54    inference(nnf_transformation,[],[f27])).
% 1.40/0.54  fof(f27,plain,(
% 1.40/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 1.40/0.54    inference(definition_folding,[],[f24,f26,f25])).
% 1.40/0.54  fof(f26,plain,(
% 1.40/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.40/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.40/0.54  fof(f24,plain,(
% 1.40/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 1.40/0.54    inference(ennf_transformation,[],[f11])).
% 1.40/0.54  fof(f11,axiom,(
% 1.40/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).
% 1.40/0.54  fof(f59,plain,(
% 1.40/0.54    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X8)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f35])).
% 1.40/0.54  fof(f35,plain,(
% 1.40/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.40/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f34])).
% 1.40/0.54  fof(f34,plain,(
% 1.40/0.54    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f33,plain,(
% 1.40/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.40/0.54    inference(rectify,[],[f32])).
% 1.40/0.54  fof(f32,plain,(
% 1.40/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.40/0.54    inference(nnf_transformation,[],[f26])).
% 1.40/0.54  fof(f41,plain,(
% 1.40/0.54    k6_subset_1(k1_relat_1(sK3),sK2) != k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2)))),
% 1.40/0.54    inference(cnf_transformation,[],[f29])).
% 1.40/0.54  % SZS output end Proof for theBenchmark
% 1.40/0.54  % (19127)------------------------------
% 1.40/0.54  % (19127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (19127)Termination reason: Refutation
% 1.40/0.54  
% 1.40/0.54  % (19127)Memory used [KB]: 11001
% 1.40/0.54  % (19127)Time elapsed: 0.123 s
% 1.40/0.54  % (19127)------------------------------
% 1.40/0.54  % (19127)------------------------------
% 1.40/0.54  % (19120)Success in time 0.181 s
%------------------------------------------------------------------------------
