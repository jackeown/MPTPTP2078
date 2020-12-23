%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:06 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   95 (1079 expanded)
%              Number of leaves         :   11 ( 307 expanded)
%              Depth                    :   19
%              Number of atoms          :  236 (2188 expanded)
%              Number of equality atoms :   62 (1056 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2387,plain,(
    $false ),
    inference(resolution,[],[f2340,f78])).

fof(f78,plain,(
    ! [X4,X2,X1] : sP8(X4,X2,X1,X4) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( X0 != X4
      | sP8(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f2340,plain,(
    ~ sP8(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) ),
    inference(backward_demodulation,[],[f2053,f2280])).

fof(f2280,plain,(
    sK0 = sK2(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f1769,f71])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f54])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f27,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f1769,plain,(
    ! [X0,X1] : r2_hidden(sK2(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),k2_enumset1(X0,X0,X1,sK0)) ),
    inference(unit_resulting_resolution,[],[f506,f83,f1636,f189])).

fof(f189,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK2(k1_wellord2(X0),X1),X3)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(k1_wellord2(X0),X1)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f181,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(k1_wellord2(X0),X1),X2)
      | r1_tarski(k1_wellord2(X0),X1)
      | ~ r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f180,f35])).

fof(f180,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k1_wellord2(X0),X1),X0)
      | r1_tarski(k1_wellord2(X0),X1) ) ),
    inference(global_subsumption,[],[f22,f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k1_wellord2(X0),X1),X0)
      | r1_tarski(k1_wellord2(X0),X1)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f143,f79])).

fof(f79,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_subsumption,[],[f22,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | k3_relat_1(k1_wellord2(X0)) = X0 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f143,plain,(
    ! [X10,X9] :
      ( r2_hidden(sK2(X9,X10),k3_relat_1(X9))
      | r1_tarski(X9,X10)
      | ~ v1_relat_1(X9) ) ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,(
    ! [X10,X9] :
      ( ~ v1_relat_1(X9)
      | r1_tarski(X9,X10)
      | ~ v1_relat_1(X9)
      | r2_hidden(sK2(X9,X10),k3_relat_1(X9)) ) ),
    inference(resolution,[],[f25,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X1,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f1636,plain,(
    ~ r1_tarski(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f1417,f1465,f35])).

fof(f1465,plain,(
    ~ r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f1424,f71])).

fof(f1424,plain,(
    k4_tarski(sK0,sK0) != sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f55,f1417,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) != X0
      | ~ r2_hidden(sK6(X0,X1),X1)
      | k2_enumset1(X0,X0,X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f41,f54])).

fof(f41,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) != X0
      | ~ r2_hidden(sK6(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f55,plain,(
    k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)) != k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) ),
    inference(definition_unfolding,[],[f21,f54,f54])).

fof(f21,plain,(
    k1_wellord2(k1_tarski(sK0)) != k1_tarski(k4_tarski(sK0,sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] : k1_wellord2(k1_tarski(X0)) != k1_tarski(k4_tarski(X0,X0)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord2)).

fof(f1417,plain,(
    r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f83,f232,f1407])).

fof(f1407,plain,(
    ! [X4] :
      ( r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),X4)
      | ~ r2_hidden(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)))
      | ~ r1_tarski(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),X4) ) ),
    inference(global_subsumption,[],[f55,f1406])).

fof(f1406,plain,(
    ! [X4] :
      ( ~ r2_hidden(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)))
      | k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)) = k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))
      | r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),X4)
      | ~ r1_tarski(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),X4) ) ),
    inference(trivial_inequality_removal,[],[f1405])).

fof(f1405,plain,(
    ! [X4] :
      ( k4_tarski(sK0,sK0) != k4_tarski(sK0,sK0)
      | ~ r2_hidden(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)))
      | k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)) = k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))
      | r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),X4)
      | ~ r1_tarski(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),X4) ) ),
    inference(superposition,[],[f56,f478])).

fof(f478,plain,(
    ! [X0] :
      ( k4_tarski(sK0,sK0) = sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)))
      | r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),X0)
      | ~ r1_tarski(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),X0) ) ),
    inference(resolution,[],[f364,f35])).

fof(f364,plain,
    ( r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)))
    | k4_tarski(sK0,sK0) = sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(equality_resolution,[],[f362])).

fof(f362,plain,(
    ! [X38] :
      ( k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)) != X38
      | r2_hidden(sK6(k4_tarski(sK0,sK0),X38),X38)
      | k4_tarski(sK0,sK0) = sK6(k4_tarski(sK0,sK0),X38) ) ),
    inference(superposition,[],[f55,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | r2_hidden(sK6(X0,X1),X1)
      | sK6(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f40,f54])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) = X0
      | r2_hidden(sK6(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f232,plain,(
    ! [X2,X0,X1] : r2_hidden(k4_tarski(X0,X0),k1_wellord2(k2_enumset1(X0,X0,X1,X2))) ),
    inference(unit_resulting_resolution,[],[f83,f106,f106,f81])).

fof(f81,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0))
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X2,X3)
      | ~ r2_hidden(X2,X0) ) ),
    inference(global_subsumption,[],[f22,f70])).

fof(f70,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X2,X3)
      | r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X2,X3)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f106,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(unit_resulting_resolution,[],[f78,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | ~ sP8(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP8(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f49,f42])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP8(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f83,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f37,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f506,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X0)) ),
    inference(unit_resulting_resolution,[],[f104,f502])).

fof(f502,plain,(
    ! [X8,X7] :
      ( r1_tarski(k2_enumset1(X7,X7,X7,X7),X8)
      | ~ r2_hidden(X7,X8) ) ),
    inference(duplicate_literal_removal,[],[f499])).

fof(f499,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X7,X8)
      | r1_tarski(k2_enumset1(X7,X7,X7,X7),X8)
      | r1_tarski(k2_enumset1(X7,X7,X7,X7),X8) ) ),
    inference(superposition,[],[f37,f91])).

fof(f91,plain,(
    ! [X2,X1] :
      ( sK5(k2_enumset1(X1,X1,X1,X1),X2) = X1
      | r1_tarski(k2_enumset1(X1,X1,X1,X1),X2) ) ),
    inference(resolution,[],[f71,f36])).

fof(f104,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(unit_resulting_resolution,[],[f76,f75])).

fof(f76,plain,(
    ! [X4,X0,X1] : sP8(X4,X4,X1,X0) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( X2 != X4
      | sP8(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2053,plain,(
    ~ sP8(k4_tarski(sK0,sK2(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)))),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) ),
    inference(backward_demodulation,[],[f1726,f2005])).

fof(f2005,plain,(
    sK0 = sK1(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f1753,f71])).

fof(f1753,plain,(
    ! [X0,X1] : r2_hidden(sK1(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),k2_enumset1(X0,X0,X1,sK0)) ),
    inference(unit_resulting_resolution,[],[f506,f83,f1636,f184])).

fof(f184,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK1(k1_wellord2(X0),X1),X3)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(k1_wellord2(X0),X1)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f164,f35])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(k1_wellord2(X0),X1),X2)
      | r1_tarski(k1_wellord2(X0),X1)
      | ~ r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f163,f35])).

% (14030)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
fof(f163,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(k1_wellord2(X0),X1),X0)
      | r1_tarski(k1_wellord2(X0),X1) ) ),
    inference(global_subsumption,[],[f22,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(k1_wellord2(X0),X1),X0)
      | r1_tarski(k1_wellord2(X0),X1)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f142,f79])).

fof(f142,plain,(
    ! [X12,X11] :
      ( r2_hidden(sK1(X11,X12),k3_relat_1(X11))
      | r1_tarski(X11,X12)
      | ~ v1_relat_1(X11) ) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
    ! [X12,X11] :
      ( ~ v1_relat_1(X11)
      | r1_tarski(X11,X12)
      | ~ v1_relat_1(X11)
      | r2_hidden(sK1(X11,X12),k3_relat_1(X11)) ) ),
    inference(resolution,[],[f25,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1726,plain,(
    ~ sP8(k4_tarski(sK1(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),sK2(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)))),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f22,f1636,f157])).

fof(f157,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ sP8(k4_tarski(sK1(X1,k2_enumset1(X2,X2,X3,X4)),sK2(X1,k2_enumset1(X2,X2,X3,X4))),X4,X3,X2)
      | r1_tarski(X1,k2_enumset1(X2,X2,X3,X4))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f26,f75])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:44:16 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (13972)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.56  % (13996)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.57  % (13968)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.57  % (13974)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.57  % (13969)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.57  % (13980)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (13971)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.58  % (13973)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.56/0.58  % (13970)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.56/0.58  % (13992)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.56/0.59  % (13976)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.56/0.59  % (13976)Refutation not found, incomplete strategy% (13976)------------------------------
% 1.56/0.59  % (13976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.59  % (13991)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.81/0.60  % (13976)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.60  
% 1.81/0.60  % (13976)Memory used [KB]: 10746
% 1.81/0.60  % (13976)Time elapsed: 0.159 s
% 1.81/0.60  % (13976)------------------------------
% 1.81/0.60  % (13976)------------------------------
% 1.81/0.60  % (13986)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.81/0.60  % (13970)Refutation not found, incomplete strategy% (13970)------------------------------
% 1.81/0.60  % (13970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.60  % (13970)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.60  
% 1.81/0.60  % (13970)Memory used [KB]: 10746
% 1.81/0.60  % (13970)Time elapsed: 0.172 s
% 1.81/0.60  % (13970)------------------------------
% 1.81/0.60  % (13970)------------------------------
% 1.81/0.60  % (13993)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.81/0.61  % (13982)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.81/0.61  % (13983)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.81/0.61  % (13994)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.81/0.61  % (13985)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.81/0.61  % (13995)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.81/0.61  % (13985)Refutation not found, incomplete strategy% (13985)------------------------------
% 1.81/0.61  % (13985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.61  % (13985)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.61  
% 1.81/0.61  % (13985)Memory used [KB]: 10618
% 1.81/0.61  % (13985)Time elapsed: 0.165 s
% 1.81/0.61  % (13985)------------------------------
% 1.81/0.61  % (13985)------------------------------
% 1.81/0.61  % (13989)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.81/0.61  % (13989)Refutation not found, incomplete strategy% (13989)------------------------------
% 1.81/0.61  % (13989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.61  % (13989)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.61  
% 1.81/0.61  % (13989)Memory used [KB]: 1663
% 1.81/0.61  % (13989)Time elapsed: 0.182 s
% 1.81/0.61  % (13989)------------------------------
% 1.81/0.61  % (13989)------------------------------
% 1.81/0.61  % (13979)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.81/0.61  % (13990)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.81/0.62  % (13987)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.81/0.62  % (13978)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.81/0.62  % (13975)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.81/0.62  % (13977)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.81/0.62  % (13981)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.81/0.62  % (13997)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.81/0.62  % (13988)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.81/0.62  % (13984)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.81/0.62  % (13988)Refutation not found, incomplete strategy% (13988)------------------------------
% 1.81/0.62  % (13988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.62  % (13988)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.62  
% 1.81/0.62  % (13988)Memory used [KB]: 10746
% 1.81/0.62  % (13988)Time elapsed: 0.191 s
% 1.81/0.62  % (13988)------------------------------
% 1.81/0.62  % (13988)------------------------------
% 1.81/0.64  % (13978)Refutation not found, incomplete strategy% (13978)------------------------------
% 1.81/0.64  % (13978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.64  % (13978)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.64  
% 1.81/0.64  % (13978)Memory used [KB]: 10618
% 1.81/0.64  % (13978)Time elapsed: 0.202 s
% 1.81/0.64  % (13978)------------------------------
% 1.81/0.64  % (13978)------------------------------
% 1.81/0.64  % (13979)Refutation not found, incomplete strategy% (13979)------------------------------
% 1.81/0.64  % (13979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.64  % (13979)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.64  
% 1.81/0.64  % (13979)Memory used [KB]: 10746
% 1.81/0.64  % (13979)Time elapsed: 0.187 s
% 1.81/0.64  % (13979)------------------------------
% 1.81/0.64  % (13979)------------------------------
% 2.21/0.73  % (13992)Refutation found. Thanks to Tanya!
% 2.21/0.73  % SZS status Theorem for theBenchmark
% 2.21/0.73  % SZS output start Proof for theBenchmark
% 2.21/0.73  fof(f2387,plain,(
% 2.21/0.73    $false),
% 2.21/0.73    inference(resolution,[],[f2340,f78])).
% 2.21/0.73  fof(f78,plain,(
% 2.21/0.73    ( ! [X4,X2,X1] : (sP8(X4,X2,X1,X4)) )),
% 2.21/0.73    inference(equality_resolution,[],[f45])).
% 2.21/0.73  fof(f45,plain,(
% 2.21/0.73    ( ! [X4,X2,X0,X1] : (X0 != X4 | sP8(X4,X2,X1,X0)) )),
% 2.21/0.73    inference(cnf_transformation,[],[f20])).
% 2.21/0.73  fof(f20,plain,(
% 2.21/0.73    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.21/0.73    inference(ennf_transformation,[],[f2])).
% 2.21/0.73  fof(f2,axiom,(
% 2.21/0.73    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.21/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 2.21/0.73  fof(f2340,plain,(
% 2.21/0.73    ~sP8(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),
% 2.21/0.73    inference(backward_demodulation,[],[f2053,f2280])).
% 2.21/0.73  fof(f2280,plain,(
% 2.21/0.73    sK0 = sK2(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)))),
% 2.21/0.73    inference(unit_resulting_resolution,[],[f1769,f71])).
% 2.21/0.73  fof(f71,plain,(
% 2.21/0.73    ( ! [X2,X0] : (~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) | X0 = X2) )),
% 2.21/0.73    inference(equality_resolution,[],[f58])).
% 2.21/0.73  fof(f58,plain,(
% 2.21/0.73    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 2.21/0.73    inference(definition_unfolding,[],[f39,f54])).
% 2.21/0.73  fof(f54,plain,(
% 2.21/0.73    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.21/0.73    inference(definition_unfolding,[],[f23,f53])).
% 2.21/0.73  fof(f53,plain,(
% 2.21/0.73    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.21/0.73    inference(definition_unfolding,[],[f27,f42])).
% 2.21/0.73  fof(f42,plain,(
% 2.21/0.73    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.21/0.73    inference(cnf_transformation,[],[f6])).
% 2.21/0.73  fof(f6,axiom,(
% 2.21/0.73    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.21/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.21/0.73  fof(f27,plain,(
% 2.21/0.73    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.21/0.73    inference(cnf_transformation,[],[f5])).
% 2.21/0.73  fof(f5,axiom,(
% 2.21/0.73    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.21/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.21/0.73  fof(f23,plain,(
% 2.21/0.73    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.21/0.73    inference(cnf_transformation,[],[f4])).
% 2.21/0.73  fof(f4,axiom,(
% 2.21/0.73    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.21/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.21/0.73  fof(f39,plain,(
% 2.21/0.73    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 2.21/0.73    inference(cnf_transformation,[],[f3])).
% 2.21/0.73  fof(f3,axiom,(
% 2.21/0.73    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.21/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.21/0.73  fof(f1769,plain,(
% 2.21/0.73    ( ! [X0,X1] : (r2_hidden(sK2(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),k2_enumset1(X0,X0,X1,sK0))) )),
% 2.21/0.73    inference(unit_resulting_resolution,[],[f506,f83,f1636,f189])).
% 2.21/0.73  fof(f189,plain,(
% 2.21/0.73    ( ! [X2,X0,X3,X1] : (r2_hidden(sK2(k1_wellord2(X0),X1),X3) | ~r1_tarski(X0,X2) | r1_tarski(k1_wellord2(X0),X1) | ~r1_tarski(X2,X3)) )),
% 2.21/0.73    inference(resolution,[],[f181,f35])).
% 2.21/0.73  fof(f35,plain,(
% 2.21/0.73    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.21/0.73    inference(cnf_transformation,[],[f17])).
% 2.21/0.73  fof(f17,plain,(
% 2.21/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.21/0.73    inference(ennf_transformation,[],[f1])).
% 2.21/0.73  fof(f1,axiom,(
% 2.21/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.21/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.21/0.73  fof(f181,plain,(
% 2.21/0.73    ( ! [X2,X0,X1] : (r2_hidden(sK2(k1_wellord2(X0),X1),X2) | r1_tarski(k1_wellord2(X0),X1) | ~r1_tarski(X0,X2)) )),
% 2.21/0.73    inference(resolution,[],[f180,f35])).
% 2.21/0.73  fof(f180,plain,(
% 2.21/0.73    ( ! [X0,X1] : (r2_hidden(sK2(k1_wellord2(X0),X1),X0) | r1_tarski(k1_wellord2(X0),X1)) )),
% 2.21/0.73    inference(global_subsumption,[],[f22,f179])).
% 2.21/0.73  fof(f179,plain,(
% 2.21/0.73    ( ! [X0,X1] : (r2_hidden(sK2(k1_wellord2(X0),X1),X0) | r1_tarski(k1_wellord2(X0),X1) | ~v1_relat_1(k1_wellord2(X0))) )),
% 2.21/0.73    inference(superposition,[],[f143,f79])).
% 2.21/0.73  fof(f79,plain,(
% 2.21/0.73    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 2.21/0.73    inference(global_subsumption,[],[f22,f64])).
% 2.21/0.73  fof(f64,plain,(
% 2.21/0.73    ( ! [X0] : (~v1_relat_1(k1_wellord2(X0)) | k3_relat_1(k1_wellord2(X0)) = X0) )),
% 2.21/0.73    inference(equality_resolution,[],[f34])).
% 2.21/0.73  fof(f34,plain,(
% 2.21/0.73    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1) )),
% 2.21/0.73    inference(cnf_transformation,[],[f16])).
% 2.21/0.73  fof(f16,plain,(
% 2.21/0.73    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 2.21/0.73    inference(flattening,[],[f15])).
% 2.21/0.73  fof(f15,plain,(
% 2.21/0.73    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 2.21/0.73    inference(ennf_transformation,[],[f9])).
% 2.21/0.73  fof(f9,axiom,(
% 2.21/0.73    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 2.21/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 2.21/0.73  fof(f143,plain,(
% 2.21/0.73    ( ! [X10,X9] : (r2_hidden(sK2(X9,X10),k3_relat_1(X9)) | r1_tarski(X9,X10) | ~v1_relat_1(X9)) )),
% 2.21/0.73    inference(duplicate_literal_removal,[],[f140])).
% 2.21/0.73  fof(f140,plain,(
% 2.21/0.73    ( ! [X10,X9] : (~v1_relat_1(X9) | r1_tarski(X9,X10) | ~v1_relat_1(X9) | r2_hidden(sK2(X9,X10),k3_relat_1(X9))) )),
% 2.21/0.73    inference(resolution,[],[f25,f44])).
% 2.21/0.73  fof(f44,plain,(
% 2.21/0.73    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X1,k3_relat_1(X2))) )),
% 2.21/0.73    inference(cnf_transformation,[],[f19])).
% 2.21/0.73  fof(f19,plain,(
% 2.21/0.73    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 2.21/0.73    inference(flattening,[],[f18])).
% 2.21/0.73  fof(f18,plain,(
% 2.21/0.73    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 2.21/0.73    inference(ennf_transformation,[],[f8])).
% 2.21/0.73  fof(f8,axiom,(
% 2.21/0.73    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 2.21/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).
% 2.21/0.73  fof(f25,plain,(
% 2.21/0.73    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | ~v1_relat_1(X0) | r1_tarski(X0,X1)) )),
% 2.21/0.73    inference(cnf_transformation,[],[f14])).
% 2.21/0.73  fof(f14,plain,(
% 2.21/0.73    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 2.21/0.73    inference(ennf_transformation,[],[f7])).
% 2.21/0.73  fof(f7,axiom,(
% 2.21/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 2.21/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 2.21/0.73  fof(f22,plain,(
% 2.21/0.73    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 2.21/0.73    inference(cnf_transformation,[],[f10])).
% 2.21/0.73  fof(f10,axiom,(
% 2.21/0.73    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 2.21/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 2.21/0.73  fof(f1636,plain,(
% 2.21/0.73    ~r1_tarski(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)))),
% 2.21/0.73    inference(unit_resulting_resolution,[],[f1417,f1465,f35])).
% 2.21/0.73  fof(f1465,plain,(
% 2.21/0.73    ~r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)))),
% 2.21/0.73    inference(unit_resulting_resolution,[],[f1424,f71])).
% 2.21/0.73  fof(f1424,plain,(
% 2.21/0.73    k4_tarski(sK0,sK0) != sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)))),
% 2.21/0.73    inference(unit_resulting_resolution,[],[f55,f1417,f56])).
% 2.21/0.73  fof(f56,plain,(
% 2.21/0.73    ( ! [X0,X1] : (sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1) | k2_enumset1(X0,X0,X0,X0) = X1) )),
% 2.21/0.73    inference(definition_unfolding,[],[f41,f54])).
% 2.21/0.73  fof(f41,plain,(
% 2.21/0.73    ( ! [X0,X1] : (sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 2.21/0.73    inference(cnf_transformation,[],[f3])).
% 2.21/0.73  fof(f55,plain,(
% 2.21/0.73    k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)) != k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),
% 2.21/0.73    inference(definition_unfolding,[],[f21,f54,f54])).
% 2.21/0.73  fof(f21,plain,(
% 2.21/0.73    k1_wellord2(k1_tarski(sK0)) != k1_tarski(k4_tarski(sK0,sK0))),
% 2.21/0.73    inference(cnf_transformation,[],[f13])).
% 2.21/0.73  fof(f13,plain,(
% 2.21/0.73    ? [X0] : k1_wellord2(k1_tarski(X0)) != k1_tarski(k4_tarski(X0,X0))),
% 2.21/0.73    inference(ennf_transformation,[],[f12])).
% 2.21/0.73  fof(f12,negated_conjecture,(
% 2.21/0.73    ~! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0))),
% 2.21/0.73    inference(negated_conjecture,[],[f11])).
% 2.21/0.73  fof(f11,conjecture,(
% 2.21/0.73    ! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0))),
% 2.21/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord2)).
% 2.21/0.73  fof(f1417,plain,(
% 2.21/0.73    r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)))),
% 2.21/0.73    inference(unit_resulting_resolution,[],[f83,f232,f1407])).
% 2.21/0.73  fof(f1407,plain,(
% 2.21/0.73    ( ! [X4] : (r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),X4) | ~r2_hidden(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))) | ~r1_tarski(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),X4)) )),
% 2.21/0.73    inference(global_subsumption,[],[f55,f1406])).
% 2.21/0.73  fof(f1406,plain,(
% 2.21/0.73    ( ! [X4] : (~r2_hidden(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))) | k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)) = k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) | r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),X4) | ~r1_tarski(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),X4)) )),
% 2.21/0.73    inference(trivial_inequality_removal,[],[f1405])).
% 2.21/0.73  fof(f1405,plain,(
% 2.21/0.73    ( ! [X4] : (k4_tarski(sK0,sK0) != k4_tarski(sK0,sK0) | ~r2_hidden(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))) | k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)) = k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) | r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),X4) | ~r1_tarski(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),X4)) )),
% 2.21/0.73    inference(superposition,[],[f56,f478])).
% 2.21/0.73  fof(f478,plain,(
% 2.21/0.73    ( ! [X0] : (k4_tarski(sK0,sK0) = sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))) | r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),X0) | ~r1_tarski(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),X0)) )),
% 2.21/0.73    inference(resolution,[],[f364,f35])).
% 2.21/0.73  fof(f364,plain,(
% 2.21/0.73    r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))) | k4_tarski(sK0,sK0) = sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)))),
% 2.21/0.73    inference(equality_resolution,[],[f362])).
% 2.21/0.73  fof(f362,plain,(
% 2.21/0.73    ( ! [X38] : (k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)) != X38 | r2_hidden(sK6(k4_tarski(sK0,sK0),X38),X38) | k4_tarski(sK0,sK0) = sK6(k4_tarski(sK0,sK0),X38)) )),
% 2.21/0.73    inference(superposition,[],[f55,f57])).
% 2.21/0.73  fof(f57,plain,(
% 2.21/0.73    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | r2_hidden(sK6(X0,X1),X1) | sK6(X0,X1) = X0) )),
% 2.21/0.73    inference(definition_unfolding,[],[f40,f54])).
% 2.21/0.73  fof(f40,plain,(
% 2.21/0.73    ( ! [X0,X1] : (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 2.21/0.73    inference(cnf_transformation,[],[f3])).
% 2.21/0.73  fof(f232,plain,(
% 2.21/0.73    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X0),k1_wellord2(k2_enumset1(X0,X0,X1,X2)))) )),
% 2.21/0.73    inference(unit_resulting_resolution,[],[f83,f106,f106,f81])).
% 2.21/0.73  fof(f81,plain,(
% 2.21/0.73    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0)) | ~r2_hidden(X3,X0) | ~r1_tarski(X2,X3) | ~r2_hidden(X2,X0)) )),
% 2.21/0.73    inference(global_subsumption,[],[f22,f70])).
% 2.21/0.73  fof(f70,plain,(
% 2.21/0.73    ( ! [X2,X0,X3] : (~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | ~r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0))) )),
% 2.21/0.73    inference(equality_resolution,[],[f28])).
% 2.21/0.73  fof(f28,plain,(
% 2.21/0.73    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | ~r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1) | k1_wellord2(X0) != X1) )),
% 2.21/0.73    inference(cnf_transformation,[],[f16])).
% 2.21/0.73  fof(f106,plain,(
% 2.21/0.73    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_enumset1(X0,X0,X1,X2))) )),
% 2.21/0.73    inference(unit_resulting_resolution,[],[f78,f75])).
% 2.21/0.73  fof(f75,plain,(
% 2.21/0.73    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | ~sP8(X4,X2,X1,X0)) )),
% 2.21/0.73    inference(equality_resolution,[],[f63])).
% 2.21/0.73  fof(f63,plain,(
% 2.21/0.73    ( ! [X4,X2,X0,X3,X1] : (~sP8(X4,X2,X1,X0) | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 2.21/0.73    inference(definition_unfolding,[],[f49,f42])).
% 2.21/0.73  fof(f49,plain,(
% 2.21/0.73    ( ! [X4,X2,X0,X3,X1] : (~sP8(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.21/0.73    inference(cnf_transformation,[],[f20])).
% 2.21/0.73  fof(f83,plain,(
% 2.21/0.73    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.21/0.73    inference(duplicate_literal_removal,[],[f82])).
% 2.21/0.73  fof(f82,plain,(
% 2.21/0.73    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 2.21/0.73    inference(resolution,[],[f37,f36])).
% 2.21/0.73  fof(f36,plain,(
% 2.21/0.73    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.21/0.73    inference(cnf_transformation,[],[f17])).
% 2.21/0.73  fof(f37,plain,(
% 2.21/0.73    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.21/0.73    inference(cnf_transformation,[],[f17])).
% 2.21/0.73  fof(f506,plain,(
% 2.21/0.73    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X0))) )),
% 2.21/0.73    inference(unit_resulting_resolution,[],[f104,f502])).
% 2.21/0.73  fof(f502,plain,(
% 2.21/0.73    ( ! [X8,X7] : (r1_tarski(k2_enumset1(X7,X7,X7,X7),X8) | ~r2_hidden(X7,X8)) )),
% 2.21/0.73    inference(duplicate_literal_removal,[],[f499])).
% 2.21/0.73  fof(f499,plain,(
% 2.21/0.73    ( ! [X8,X7] : (~r2_hidden(X7,X8) | r1_tarski(k2_enumset1(X7,X7,X7,X7),X8) | r1_tarski(k2_enumset1(X7,X7,X7,X7),X8)) )),
% 2.21/0.73    inference(superposition,[],[f37,f91])).
% 2.21/0.73  fof(f91,plain,(
% 2.21/0.73    ( ! [X2,X1] : (sK5(k2_enumset1(X1,X1,X1,X1),X2) = X1 | r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)) )),
% 2.21/0.73    inference(resolution,[],[f71,f36])).
% 2.21/0.73  fof(f104,plain,(
% 2.21/0.73    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_enumset1(X1,X1,X2,X0))) )),
% 2.21/0.73    inference(unit_resulting_resolution,[],[f76,f75])).
% 2.21/0.73  fof(f76,plain,(
% 2.21/0.73    ( ! [X4,X0,X1] : (sP8(X4,X4,X1,X0)) )),
% 2.21/0.73    inference(equality_resolution,[],[f47])).
% 2.21/0.73  fof(f47,plain,(
% 2.21/0.73    ( ! [X4,X2,X0,X1] : (X2 != X4 | sP8(X4,X2,X1,X0)) )),
% 2.21/0.73    inference(cnf_transformation,[],[f20])).
% 2.21/0.73  fof(f2053,plain,(
% 2.21/0.73    ~sP8(k4_tarski(sK0,sK2(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)))),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),
% 2.21/0.73    inference(backward_demodulation,[],[f1726,f2005])).
% 2.21/0.73  fof(f2005,plain,(
% 2.21/0.73    sK0 = sK1(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)))),
% 2.21/0.73    inference(unit_resulting_resolution,[],[f1753,f71])).
% 2.21/0.73  fof(f1753,plain,(
% 2.21/0.73    ( ! [X0,X1] : (r2_hidden(sK1(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),k2_enumset1(X0,X0,X1,sK0))) )),
% 2.21/0.73    inference(unit_resulting_resolution,[],[f506,f83,f1636,f184])).
% 2.21/0.73  fof(f184,plain,(
% 2.21/0.73    ( ! [X2,X0,X3,X1] : (r2_hidden(sK1(k1_wellord2(X0),X1),X3) | ~r1_tarski(X0,X2) | r1_tarski(k1_wellord2(X0),X1) | ~r1_tarski(X2,X3)) )),
% 2.21/0.73    inference(resolution,[],[f164,f35])).
% 2.21/0.73  fof(f164,plain,(
% 2.21/0.73    ( ! [X2,X0,X1] : (r2_hidden(sK1(k1_wellord2(X0),X1),X2) | r1_tarski(k1_wellord2(X0),X1) | ~r1_tarski(X0,X2)) )),
% 2.21/0.73    inference(resolution,[],[f163,f35])).
% 2.21/0.73  % (14030)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.21/0.73  fof(f163,plain,(
% 2.21/0.73    ( ! [X0,X1] : (r2_hidden(sK1(k1_wellord2(X0),X1),X0) | r1_tarski(k1_wellord2(X0),X1)) )),
% 2.21/0.73    inference(global_subsumption,[],[f22,f162])).
% 2.21/0.73  fof(f162,plain,(
% 2.21/0.73    ( ! [X0,X1] : (r2_hidden(sK1(k1_wellord2(X0),X1),X0) | r1_tarski(k1_wellord2(X0),X1) | ~v1_relat_1(k1_wellord2(X0))) )),
% 2.21/0.73    inference(superposition,[],[f142,f79])).
% 2.21/0.73  fof(f142,plain,(
% 2.21/0.73    ( ! [X12,X11] : (r2_hidden(sK1(X11,X12),k3_relat_1(X11)) | r1_tarski(X11,X12) | ~v1_relat_1(X11)) )),
% 2.21/0.73    inference(duplicate_literal_removal,[],[f141])).
% 2.21/0.73  fof(f141,plain,(
% 2.21/0.73    ( ! [X12,X11] : (~v1_relat_1(X11) | r1_tarski(X11,X12) | ~v1_relat_1(X11) | r2_hidden(sK1(X11,X12),k3_relat_1(X11))) )),
% 2.21/0.73    inference(resolution,[],[f25,f43])).
% 2.21/0.73  fof(f43,plain,(
% 2.21/0.73    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X0,k3_relat_1(X2))) )),
% 2.21/0.73    inference(cnf_transformation,[],[f19])).
% 2.21/0.73  fof(f1726,plain,(
% 2.21/0.73    ~sP8(k4_tarski(sK1(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),sK2(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)))),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),
% 2.21/0.73    inference(unit_resulting_resolution,[],[f22,f1636,f157])).
% 2.21/0.73  fof(f157,plain,(
% 2.21/0.73    ( ! [X4,X2,X3,X1] : (~sP8(k4_tarski(sK1(X1,k2_enumset1(X2,X2,X3,X4)),sK2(X1,k2_enumset1(X2,X2,X3,X4))),X4,X3,X2) | r1_tarski(X1,k2_enumset1(X2,X2,X3,X4)) | ~v1_relat_1(X1)) )),
% 2.21/0.73    inference(resolution,[],[f26,f75])).
% 2.21/0.73  fof(f26,plain,(
% 2.21/0.73    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) | ~v1_relat_1(X0) | r1_tarski(X0,X1)) )),
% 2.21/0.73    inference(cnf_transformation,[],[f14])).
% 2.21/0.73  % SZS output end Proof for theBenchmark
% 2.21/0.73  % (13992)------------------------------
% 2.21/0.73  % (13992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.73  % (13992)Termination reason: Refutation
% 2.21/0.73  
% 2.21/0.73  % (13992)Memory used [KB]: 7931
% 2.21/0.73  % (13992)Time elapsed: 0.285 s
% 2.21/0.73  % (13992)------------------------------
% 2.21/0.73  % (13992)------------------------------
% 2.21/0.74  % (13967)Success in time 0.363 s
%------------------------------------------------------------------------------
