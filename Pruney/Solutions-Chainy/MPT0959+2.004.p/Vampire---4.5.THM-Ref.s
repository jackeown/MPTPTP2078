%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:05 EST 2020

% Result     : Theorem 2.96s
% Output     : Refutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   95 (1024 expanded)
%              Number of leaves         :   12 ( 308 expanded)
%              Depth                    :   19
%              Number of atoms          :  233 (1871 expanded)
%              Number of equality atoms :   59 ( 979 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2224,plain,(
    $false ),
    inference(resolution,[],[f2164,f81])).

fof(f81,plain,(
    ! [X3,X1] : sP8(X3,X1,X3) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( X0 != X3
      | sP8(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f2164,plain,(
    ~ sP8(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) ),
    inference(backward_demodulation,[],[f1920,f2117])).

fof(f2117,plain,(
    sK0 = sK2(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f1557,f75])).

fof(f75,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f42,f56])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f27,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f1557,plain,(
    ! [X0] : r2_hidden(sK2(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),k2_enumset1(X0,X0,X0,sK0)) ),
    inference(unit_resulting_resolution,[],[f384,f73,f1391,f181])).

fof(f181,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK2(k1_wellord2(X0),X1),X3)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(k1_wellord2(X0),X1)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f172,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(k1_wellord2(X0),X1),X2)
      | r1_tarski(k1_wellord2(X0),X1)
      | ~ r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f169,f38])).

fof(f169,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k1_wellord2(X0),X1),X0)
      | r1_tarski(k1_wellord2(X0),X1) ) ),
    inference(global_subsumption,[],[f22,f168])).

fof(f168,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k1_wellord2(X0),X1),X0)
      | r1_tarski(k1_wellord2(X0),X1)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f148,f82])).

fof(f82,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_subsumption,[],[f22,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | k3_relat_1(k1_wellord2(X0)) = X0 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f148,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK2(X8,X9),k3_relat_1(X8))
      | r1_tarski(X8,X9)
      | ~ v1_relat_1(X8) ) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X8)
      | r1_tarski(X8,X9)
      | ~ v1_relat_1(X8)
      | r2_hidden(sK2(X8,X9),k3_relat_1(X8)) ) ),
    inference(resolution,[],[f25,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X1,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f1391,plain,(
    ~ r1_tarski(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f1090,f1140,f38])).

fof(f1140,plain,(
    ~ r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f1108,f75])).

fof(f1108,plain,(
    k4_tarski(sK0,sK0) != sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f57,f1090,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) != X0
      | ~ r2_hidden(sK6(X0,X1),X1)
      | k2_enumset1(X0,X0,X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f44,f56])).

fof(f44,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) != X0
      | ~ r2_hidden(sK6(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f57,plain,(
    k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)) != k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) ),
    inference(definition_unfolding,[],[f21,f56,f56])).

fof(f21,plain,(
    k1_wellord2(k1_tarski(sK0)) != k1_tarski(k4_tarski(sK0,sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] : k1_wellord2(k1_tarski(X0)) != k1_tarski(k4_tarski(X0,X0)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_wellord2)).

fof(f1090,plain,(
    r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f73,f218,f1088])).

fof(f1088,plain,(
    ! [X0] :
      ( r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),X0)
      | ~ r2_hidden(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)))
      | ~ r1_tarski(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),X0) ) ),
    inference(global_subsumption,[],[f57,f1087])).

fof(f1087,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)))
      | k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)) = k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))
      | r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),X0)
      | ~ r1_tarski(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),X0) ) ),
    inference(trivial_inequality_removal,[],[f1079])).

fof(f1079,plain,(
    ! [X0] :
      ( k4_tarski(sK0,sK0) != k4_tarski(sK0,sK0)
      | ~ r2_hidden(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)))
      | k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)) = k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))
      | r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),X0)
      | ~ r1_tarski(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),X0) ) ),
    inference(superposition,[],[f58,f371])).

fof(f371,plain,(
    ! [X0] :
      ( k4_tarski(sK0,sK0) = sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)))
      | r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),X0)
      | ~ r1_tarski(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),X0) ) ),
    inference(resolution,[],[f303,f38])).

fof(f303,plain,
    ( r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)))
    | k4_tarski(sK0,sK0) = sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(equality_resolution,[],[f300])).

fof(f300,plain,(
    ! [X39] :
      ( k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)) != X39
      | r2_hidden(sK6(k4_tarski(sK0,sK0),X39),X39)
      | k4_tarski(sK0,sK0) = sK6(k4_tarski(sK0,sK0),X39) ) ),
    inference(superposition,[],[f57,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | r2_hidden(sK6(X0,X1),X1)
      | sK6(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f43,f56])).

fof(f43,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) = X0
      | r2_hidden(sK6(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f218,plain,(
    ! [X0,X1] : r2_hidden(k4_tarski(X0,X0),k1_wellord2(k2_enumset1(X0,X0,X0,X1))) ),
    inference(unit_resulting_resolution,[],[f73,f113,f113,f84])).

fof(f84,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0))
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X2,X3)
      | ~ r2_hidden(X2,X0) ) ),
    inference(global_subsumption,[],[f22,f72])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f113,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(unit_resulting_resolution,[],[f81,f79])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_enumset1(X0,X0,X0,X1))
      | ~ sP8(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP8(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f51,f55])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP8(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f384,plain,(
    ! [X0,X1] : r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X0)) ),
    inference(unit_resulting_resolution,[],[f112,f380])).

fof(f380,plain,(
    ! [X8,X7] :
      ( r1_tarski(k2_enumset1(X7,X7,X7,X7),X8)
      | ~ r2_hidden(X7,X8) ) ),
    inference(duplicate_literal_removal,[],[f377])).

fof(f377,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X7,X8)
      | r1_tarski(k2_enumset1(X7,X7,X7,X7),X8)
      | r1_tarski(k2_enumset1(X7,X7,X7,X7),X8) ) ),
    inference(superposition,[],[f40,f104])).

fof(f104,plain,(
    ! [X2,X1] :
      ( sK5(k2_enumset1(X1,X1,X1,X1),X2) = X1
      | r1_tarski(k2_enumset1(X1,X1,X1,X1),X2) ) ),
    inference(resolution,[],[f75,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f112,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(unit_resulting_resolution,[],[f80,f79])).

fof(f80,plain,(
    ! [X0,X3] : sP8(X3,X3,X0) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( X1 != X3
      | sP8(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f1920,plain,(
    ~ sP8(k4_tarski(sK0,sK2(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)))),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) ),
    inference(backward_demodulation,[],[f1530,f1882])).

fof(f1882,plain,(
    sK0 = sK1(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f1548,f75])).

fof(f1548,plain,(
    ! [X0] : r2_hidden(sK1(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),k2_enumset1(X0,X0,X0,sK0)) ),
    inference(unit_resulting_resolution,[],[f384,f73,f1391,f176])).

fof(f176,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK1(k1_wellord2(X0),X1),X3)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(k1_wellord2(X0),X1)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f164,f38])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(k1_wellord2(X0),X1),X2)
      | r1_tarski(k1_wellord2(X0),X1)
      | ~ r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f163,f38])).

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
    inference(superposition,[],[f147,f82])).

fof(f147,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK1(X10,X11),k3_relat_1(X10))
      | r1_tarski(X10,X11)
      | ~ v1_relat_1(X10) ) ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | r1_tarski(X10,X11)
      | ~ v1_relat_1(X10)
      | r2_hidden(sK1(X10,X11),k3_relat_1(X10)) ) ),
    inference(resolution,[],[f25,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1530,plain,(
    ~ sP8(k4_tarski(sK1(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),sK2(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)))),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f22,f1391,f159])).

fof(f159,plain,(
    ! [X2,X3,X1] :
      ( ~ sP8(k4_tarski(sK1(X1,k2_enumset1(X2,X2,X2,X3)),sK2(X1,k2_enumset1(X2,X2,X2,X3))),X3,X2)
      | r1_tarski(X1,k2_enumset1(X2,X2,X2,X3))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f26,f79])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (16903)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (16907)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (16929)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (16904)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (16924)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (16903)Refutation not found, incomplete strategy% (16903)------------------------------
% 0.20/0.52  % (16903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (16903)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (16903)Memory used [KB]: 10746
% 0.20/0.52  % (16903)Time elapsed: 0.112 s
% 0.20/0.52  % (16903)------------------------------
% 0.20/0.52  % (16903)------------------------------
% 0.20/0.52  % (16914)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (16913)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (16917)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (16901)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (16930)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (16911)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (16905)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (16925)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (16902)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.55  % (16931)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (16922)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (16918)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (16928)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (16915)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (16922)Refutation not found, incomplete strategy% (16922)------------------------------
% 0.20/0.55  % (16922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (16923)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (16908)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (16923)Refutation not found, incomplete strategy% (16923)------------------------------
% 0.20/0.55  % (16923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (16923)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (16923)Memory used [KB]: 1663
% 0.20/0.55  % (16923)Time elapsed: 0.115 s
% 0.20/0.55  % (16923)------------------------------
% 0.20/0.55  % (16923)------------------------------
% 0.20/0.56  % (16916)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.54/0.56  % (16906)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.54/0.56  % (16927)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.54/0.56  % (16920)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.54/0.57  % (16922)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (16922)Memory used [KB]: 10746
% 1.54/0.57  % (16922)Time elapsed: 0.147 s
% 1.54/0.57  % (16922)------------------------------
% 1.54/0.57  % (16922)------------------------------
% 1.54/0.57  % (16921)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.54/0.57  % (16919)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.54/0.57  % (16909)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.54/0.57  % (16912)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.54/0.57  % (16912)Refutation not found, incomplete strategy% (16912)------------------------------
% 1.54/0.57  % (16912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (16912)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (16912)Memory used [KB]: 10618
% 1.54/0.57  % (16912)Time elapsed: 0.162 s
% 1.54/0.57  % (16912)------------------------------
% 1.54/0.57  % (16912)------------------------------
% 1.54/0.57  % (16909)Refutation not found, incomplete strategy% (16909)------------------------------
% 1.54/0.57  % (16909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (16909)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (16909)Memory used [KB]: 10618
% 1.54/0.57  % (16909)Time elapsed: 0.138 s
% 1.54/0.57  % (16909)------------------------------
% 1.54/0.57  % (16909)------------------------------
% 1.54/0.58  % (16926)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.72/0.58  % (16919)Refutation not found, incomplete strategy% (16919)------------------------------
% 1.72/0.58  % (16919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.58  % (16919)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.58  
% 1.72/0.58  % (16919)Memory used [KB]: 10746
% 1.72/0.58  % (16919)Time elapsed: 0.144 s
% 1.72/0.58  % (16919)------------------------------
% 1.72/0.58  % (16919)------------------------------
% 2.12/0.64  % (16932)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.20/0.69  % (16933)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.20/0.71  % (16934)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.63/0.73  % (16937)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.63/0.74  % (16938)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.63/0.75  % (16936)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.96/0.82  % (16926)Refutation found. Thanks to Tanya!
% 2.96/0.82  % SZS status Theorem for theBenchmark
% 2.96/0.82  % SZS output start Proof for theBenchmark
% 2.96/0.82  fof(f2224,plain,(
% 2.96/0.82    $false),
% 2.96/0.82    inference(resolution,[],[f2164,f81])).
% 2.96/0.82  fof(f81,plain,(
% 2.96/0.82    ( ! [X3,X1] : (sP8(X3,X1,X3)) )),
% 2.96/0.82    inference(equality_resolution,[],[f48])).
% 2.96/0.82  fof(f48,plain,(
% 2.96/0.82    ( ! [X0,X3,X1] : (X0 != X3 | sP8(X3,X1,X0)) )),
% 2.96/0.82    inference(cnf_transformation,[],[f4])).
% 2.96/0.82  fof(f4,axiom,(
% 2.96/0.82    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.96/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 2.96/0.82  fof(f2164,plain,(
% 2.96/0.82    ~sP8(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),
% 2.96/0.82    inference(backward_demodulation,[],[f1920,f2117])).
% 2.96/0.82  fof(f2117,plain,(
% 2.96/0.82    sK0 = sK2(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)))),
% 2.96/0.82    inference(unit_resulting_resolution,[],[f1557,f75])).
% 2.96/0.82  fof(f75,plain,(
% 2.96/0.82    ( ! [X2,X0] : (~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) | X0 = X2) )),
% 2.96/0.82    inference(equality_resolution,[],[f60])).
% 2.96/0.82  fof(f60,plain,(
% 2.96/0.82    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 2.96/0.82    inference(definition_unfolding,[],[f42,f56])).
% 2.96/0.82  fof(f56,plain,(
% 2.96/0.82    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.96/0.82    inference(definition_unfolding,[],[f23,f55])).
% 2.96/0.82  fof(f55,plain,(
% 2.96/0.82    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.96/0.82    inference(definition_unfolding,[],[f27,f45])).
% 2.96/0.82  fof(f45,plain,(
% 2.96/0.82    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.96/0.82    inference(cnf_transformation,[],[f7])).
% 2.96/0.82  fof(f7,axiom,(
% 2.96/0.82    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.96/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.96/0.82  fof(f27,plain,(
% 2.96/0.82    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.96/0.82    inference(cnf_transformation,[],[f6])).
% 2.96/0.82  fof(f6,axiom,(
% 2.96/0.82    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.96/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.96/0.82  fof(f23,plain,(
% 2.96/0.82    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.96/0.82    inference(cnf_transformation,[],[f5])).
% 2.96/0.82  fof(f5,axiom,(
% 2.96/0.82    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.96/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.96/0.82  fof(f42,plain,(
% 2.96/0.82    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 2.96/0.82    inference(cnf_transformation,[],[f3])).
% 2.96/0.82  fof(f3,axiom,(
% 2.96/0.82    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.96/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 2.96/0.82  fof(f1557,plain,(
% 2.96/0.82    ( ! [X0] : (r2_hidden(sK2(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),k2_enumset1(X0,X0,X0,sK0))) )),
% 2.96/0.82    inference(unit_resulting_resolution,[],[f384,f73,f1391,f181])).
% 2.96/0.82  fof(f181,plain,(
% 2.96/0.82    ( ! [X2,X0,X3,X1] : (r2_hidden(sK2(k1_wellord2(X0),X1),X3) | ~r1_tarski(X0,X2) | r1_tarski(k1_wellord2(X0),X1) | ~r1_tarski(X2,X3)) )),
% 2.96/0.82    inference(resolution,[],[f172,f38])).
% 2.96/0.82  fof(f38,plain,(
% 2.96/0.82    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.96/0.82    inference(cnf_transformation,[],[f18])).
% 2.96/0.82  fof(f18,plain,(
% 2.96/0.82    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.96/0.82    inference(ennf_transformation,[],[f1])).
% 2.96/0.82  fof(f1,axiom,(
% 2.96/0.82    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.96/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.96/0.82  fof(f172,plain,(
% 2.96/0.82    ( ! [X2,X0,X1] : (r2_hidden(sK2(k1_wellord2(X0),X1),X2) | r1_tarski(k1_wellord2(X0),X1) | ~r1_tarski(X0,X2)) )),
% 2.96/0.82    inference(resolution,[],[f169,f38])).
% 2.96/0.82  fof(f169,plain,(
% 2.96/0.82    ( ! [X0,X1] : (r2_hidden(sK2(k1_wellord2(X0),X1),X0) | r1_tarski(k1_wellord2(X0),X1)) )),
% 2.96/0.82    inference(global_subsumption,[],[f22,f168])).
% 2.96/0.82  fof(f168,plain,(
% 2.96/0.82    ( ! [X0,X1] : (r2_hidden(sK2(k1_wellord2(X0),X1),X0) | r1_tarski(k1_wellord2(X0),X1) | ~v1_relat_1(k1_wellord2(X0))) )),
% 2.96/0.82    inference(superposition,[],[f148,f82])).
% 2.96/0.82  fof(f82,plain,(
% 2.96/0.82    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 2.96/0.82    inference(global_subsumption,[],[f22,f66])).
% 2.96/0.82  fof(f66,plain,(
% 2.96/0.82    ( ! [X0] : (~v1_relat_1(k1_wellord2(X0)) | k3_relat_1(k1_wellord2(X0)) = X0) )),
% 2.96/0.82    inference(equality_resolution,[],[f34])).
% 2.96/0.82  fof(f34,plain,(
% 2.96/0.82    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1) )),
% 2.96/0.82    inference(cnf_transformation,[],[f17])).
% 2.96/0.82  fof(f17,plain,(
% 2.96/0.82    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 2.96/0.82    inference(flattening,[],[f16])).
% 2.96/0.82  fof(f16,plain,(
% 2.96/0.82    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 2.96/0.82    inference(ennf_transformation,[],[f10])).
% 2.96/0.82  fof(f10,axiom,(
% 2.96/0.82    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 2.96/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 2.96/0.82  fof(f148,plain,(
% 2.96/0.82    ( ! [X8,X9] : (r2_hidden(sK2(X8,X9),k3_relat_1(X8)) | r1_tarski(X8,X9) | ~v1_relat_1(X8)) )),
% 2.96/0.82    inference(duplicate_literal_removal,[],[f145])).
% 2.96/0.82  fof(f145,plain,(
% 2.96/0.82    ( ! [X8,X9] : (~v1_relat_1(X8) | r1_tarski(X8,X9) | ~v1_relat_1(X8) | r2_hidden(sK2(X8,X9),k3_relat_1(X8))) )),
% 2.96/0.82    inference(resolution,[],[f25,f47])).
% 2.96/0.82  fof(f47,plain,(
% 2.96/0.82    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X1,k3_relat_1(X2))) )),
% 2.96/0.82    inference(cnf_transformation,[],[f20])).
% 2.96/0.83  fof(f20,plain,(
% 2.96/0.83    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 2.96/0.83    inference(flattening,[],[f19])).
% 2.96/0.83  fof(f19,plain,(
% 2.96/0.83    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 2.96/0.83    inference(ennf_transformation,[],[f9])).
% 2.96/0.83  fof(f9,axiom,(
% 2.96/0.83    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 2.96/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).
% 2.96/0.83  fof(f25,plain,(
% 2.96/0.83    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | ~v1_relat_1(X0) | r1_tarski(X0,X1)) )),
% 2.96/0.83    inference(cnf_transformation,[],[f15])).
% 2.96/0.83  fof(f15,plain,(
% 2.96/0.83    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 2.96/0.83    inference(ennf_transformation,[],[f8])).
% 2.96/0.83  fof(f8,axiom,(
% 2.96/0.83    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 2.96/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).
% 2.96/0.83  fof(f22,plain,(
% 2.96/0.83    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 2.96/0.83    inference(cnf_transformation,[],[f11])).
% 2.96/0.83  fof(f11,axiom,(
% 2.96/0.83    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 2.96/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 2.96/0.83  fof(f1391,plain,(
% 2.96/0.83    ~r1_tarski(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)))),
% 2.96/0.83    inference(unit_resulting_resolution,[],[f1090,f1140,f38])).
% 2.96/0.83  fof(f1140,plain,(
% 2.96/0.83    ~r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)))),
% 2.96/0.83    inference(unit_resulting_resolution,[],[f1108,f75])).
% 2.96/0.83  fof(f1108,plain,(
% 2.96/0.83    k4_tarski(sK0,sK0) != sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)))),
% 2.96/0.83    inference(unit_resulting_resolution,[],[f57,f1090,f58])).
% 2.96/0.83  fof(f58,plain,(
% 2.96/0.83    ( ! [X0,X1] : (sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1) | k2_enumset1(X0,X0,X0,X0) = X1) )),
% 2.96/0.83    inference(definition_unfolding,[],[f44,f56])).
% 2.96/0.83  fof(f44,plain,(
% 2.96/0.83    ( ! [X0,X1] : (sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 2.96/0.83    inference(cnf_transformation,[],[f3])).
% 2.96/0.83  fof(f57,plain,(
% 2.96/0.83    k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)) != k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),
% 2.96/0.83    inference(definition_unfolding,[],[f21,f56,f56])).
% 2.96/0.83  fof(f21,plain,(
% 2.96/0.83    k1_wellord2(k1_tarski(sK0)) != k1_tarski(k4_tarski(sK0,sK0))),
% 2.96/0.83    inference(cnf_transformation,[],[f14])).
% 2.96/0.83  fof(f14,plain,(
% 2.96/0.83    ? [X0] : k1_wellord2(k1_tarski(X0)) != k1_tarski(k4_tarski(X0,X0))),
% 2.96/0.83    inference(ennf_transformation,[],[f13])).
% 2.96/0.83  fof(f13,negated_conjecture,(
% 2.96/0.83    ~! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0))),
% 2.96/0.83    inference(negated_conjecture,[],[f12])).
% 2.96/0.83  fof(f12,conjecture,(
% 2.96/0.83    ! [X0] : k1_wellord2(k1_tarski(X0)) = k1_tarski(k4_tarski(X0,X0))),
% 2.96/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_wellord2)).
% 2.96/0.83  fof(f1090,plain,(
% 2.96/0.83    r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)))),
% 2.96/0.83    inference(unit_resulting_resolution,[],[f73,f218,f1088])).
% 2.96/0.83  fof(f1088,plain,(
% 2.96/0.83    ( ! [X0] : (r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),X0) | ~r2_hidden(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))) | ~r1_tarski(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),X0)) )),
% 2.96/0.83    inference(global_subsumption,[],[f57,f1087])).
% 2.96/0.83  fof(f1087,plain,(
% 2.96/0.83    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))) | k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)) = k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) | r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),X0) | ~r1_tarski(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),X0)) )),
% 2.96/0.83    inference(trivial_inequality_removal,[],[f1079])).
% 2.96/0.83  fof(f1079,plain,(
% 2.96/0.83    ( ! [X0] : (k4_tarski(sK0,sK0) != k4_tarski(sK0,sK0) | ~r2_hidden(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))) | k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)) = k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)) | r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),X0) | ~r1_tarski(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),X0)) )),
% 2.96/0.83    inference(superposition,[],[f58,f371])).
% 2.96/0.83  fof(f371,plain,(
% 2.96/0.83    ( ! [X0] : (k4_tarski(sK0,sK0) = sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))) | r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),X0) | ~r1_tarski(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),X0)) )),
% 2.96/0.83    inference(resolution,[],[f303,f38])).
% 2.96/0.83  fof(f303,plain,(
% 2.96/0.83    r2_hidden(sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0))) | k4_tarski(sK0,sK0) = sK6(k4_tarski(sK0,sK0),k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)))),
% 2.96/0.83    inference(equality_resolution,[],[f300])).
% 2.96/0.83  fof(f300,plain,(
% 2.96/0.83    ( ! [X39] : (k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)) != X39 | r2_hidden(sK6(k4_tarski(sK0,sK0),X39),X39) | k4_tarski(sK0,sK0) = sK6(k4_tarski(sK0,sK0),X39)) )),
% 2.96/0.83    inference(superposition,[],[f57,f59])).
% 2.96/0.83  fof(f59,plain,(
% 2.96/0.83    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | r2_hidden(sK6(X0,X1),X1) | sK6(X0,X1) = X0) )),
% 2.96/0.83    inference(definition_unfolding,[],[f43,f56])).
% 2.96/0.83  fof(f43,plain,(
% 2.96/0.83    ( ! [X0,X1] : (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 2.96/0.83    inference(cnf_transformation,[],[f3])).
% 2.96/0.83  fof(f218,plain,(
% 2.96/0.83    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X0),k1_wellord2(k2_enumset1(X0,X0,X0,X1)))) )),
% 2.96/0.83    inference(unit_resulting_resolution,[],[f73,f113,f113,f84])).
% 2.96/0.83  fof(f84,plain,(
% 2.96/0.83    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0)) | ~r2_hidden(X3,X0) | ~r1_tarski(X2,X3) | ~r2_hidden(X2,X0)) )),
% 2.96/0.83    inference(global_subsumption,[],[f22,f72])).
% 2.96/0.83  fof(f72,plain,(
% 2.96/0.83    ( ! [X2,X0,X3] : (~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | ~r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0))) )),
% 2.96/0.83    inference(equality_resolution,[],[f28])).
% 2.96/0.83  fof(f28,plain,(
% 2.96/0.83    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | ~r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1) | k1_wellord2(X0) != X1) )),
% 2.96/0.83    inference(cnf_transformation,[],[f17])).
% 2.96/0.83  fof(f113,plain,(
% 2.96/0.83    ( ! [X0,X1] : (r2_hidden(X0,k2_enumset1(X0,X0,X0,X1))) )),
% 2.96/0.83    inference(unit_resulting_resolution,[],[f81,f79])).
% 2.96/0.83  fof(f79,plain,(
% 2.96/0.83    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_enumset1(X0,X0,X0,X1)) | ~sP8(X3,X1,X0)) )),
% 2.96/0.83    inference(equality_resolution,[],[f65])).
% 2.96/0.83  fof(f65,plain,(
% 2.96/0.83    ( ! [X2,X0,X3,X1] : (~sP8(X3,X1,X0) | r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 2.96/0.83    inference(definition_unfolding,[],[f51,f55])).
% 2.96/0.83  fof(f51,plain,(
% 2.96/0.83    ( ! [X2,X0,X3,X1] : (~sP8(X3,X1,X0) | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 2.96/0.83    inference(cnf_transformation,[],[f4])).
% 2.96/0.83  fof(f73,plain,(
% 2.96/0.83    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.96/0.83    inference(equality_resolution,[],[f36])).
% 2.96/0.83  fof(f36,plain,(
% 2.96/0.83    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.96/0.83    inference(cnf_transformation,[],[f2])).
% 2.96/0.83  fof(f2,axiom,(
% 2.96/0.83    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.96/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.96/0.83  fof(f384,plain,(
% 2.96/0.83    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X0))) )),
% 2.96/0.83    inference(unit_resulting_resolution,[],[f112,f380])).
% 2.96/0.83  fof(f380,plain,(
% 2.96/0.83    ( ! [X8,X7] : (r1_tarski(k2_enumset1(X7,X7,X7,X7),X8) | ~r2_hidden(X7,X8)) )),
% 2.96/0.83    inference(duplicate_literal_removal,[],[f377])).
% 2.96/0.83  fof(f377,plain,(
% 2.96/0.83    ( ! [X8,X7] : (~r2_hidden(X7,X8) | r1_tarski(k2_enumset1(X7,X7,X7,X7),X8) | r1_tarski(k2_enumset1(X7,X7,X7,X7),X8)) )),
% 2.96/0.83    inference(superposition,[],[f40,f104])).
% 2.96/0.83  fof(f104,plain,(
% 2.96/0.83    ( ! [X2,X1] : (sK5(k2_enumset1(X1,X1,X1,X1),X2) = X1 | r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)) )),
% 2.96/0.83    inference(resolution,[],[f75,f39])).
% 2.96/0.83  fof(f39,plain,(
% 2.96/0.83    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.96/0.83    inference(cnf_transformation,[],[f18])).
% 2.96/0.83  fof(f40,plain,(
% 2.96/0.83    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.96/0.83    inference(cnf_transformation,[],[f18])).
% 2.96/0.83  fof(f112,plain,(
% 2.96/0.83    ( ! [X0,X1] : (r2_hidden(X0,k2_enumset1(X1,X1,X1,X0))) )),
% 2.96/0.83    inference(unit_resulting_resolution,[],[f80,f79])).
% 2.96/0.83  fof(f80,plain,(
% 2.96/0.83    ( ! [X0,X3] : (sP8(X3,X3,X0)) )),
% 2.96/0.83    inference(equality_resolution,[],[f49])).
% 2.96/0.83  fof(f49,plain,(
% 2.96/0.83    ( ! [X0,X3,X1] : (X1 != X3 | sP8(X3,X1,X0)) )),
% 2.96/0.83    inference(cnf_transformation,[],[f4])).
% 2.96/0.83  fof(f1920,plain,(
% 2.96/0.83    ~sP8(k4_tarski(sK0,sK2(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)))),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),
% 2.96/0.83    inference(backward_demodulation,[],[f1530,f1882])).
% 2.96/0.83  fof(f1882,plain,(
% 2.96/0.83    sK0 = sK1(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)))),
% 2.96/0.83    inference(unit_resulting_resolution,[],[f1548,f75])).
% 2.96/0.83  fof(f1548,plain,(
% 2.96/0.83    ( ! [X0] : (r2_hidden(sK1(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),k2_enumset1(X0,X0,X0,sK0))) )),
% 2.96/0.83    inference(unit_resulting_resolution,[],[f384,f73,f1391,f176])).
% 2.96/0.83  fof(f176,plain,(
% 2.96/0.83    ( ! [X2,X0,X3,X1] : (r2_hidden(sK1(k1_wellord2(X0),X1),X3) | ~r1_tarski(X0,X2) | r1_tarski(k1_wellord2(X0),X1) | ~r1_tarski(X2,X3)) )),
% 2.96/0.83    inference(resolution,[],[f164,f38])).
% 2.96/0.83  fof(f164,plain,(
% 2.96/0.83    ( ! [X2,X0,X1] : (r2_hidden(sK1(k1_wellord2(X0),X1),X2) | r1_tarski(k1_wellord2(X0),X1) | ~r1_tarski(X0,X2)) )),
% 2.96/0.83    inference(resolution,[],[f163,f38])).
% 2.96/0.83  fof(f163,plain,(
% 2.96/0.83    ( ! [X0,X1] : (r2_hidden(sK1(k1_wellord2(X0),X1),X0) | r1_tarski(k1_wellord2(X0),X1)) )),
% 2.96/0.83    inference(global_subsumption,[],[f22,f162])).
% 2.96/0.83  fof(f162,plain,(
% 2.96/0.83    ( ! [X0,X1] : (r2_hidden(sK1(k1_wellord2(X0),X1),X0) | r1_tarski(k1_wellord2(X0),X1) | ~v1_relat_1(k1_wellord2(X0))) )),
% 2.96/0.83    inference(superposition,[],[f147,f82])).
% 2.96/0.83  fof(f147,plain,(
% 2.96/0.83    ( ! [X10,X11] : (r2_hidden(sK1(X10,X11),k3_relat_1(X10)) | r1_tarski(X10,X11) | ~v1_relat_1(X10)) )),
% 2.96/0.83    inference(duplicate_literal_removal,[],[f146])).
% 2.96/0.83  fof(f146,plain,(
% 2.96/0.83    ( ! [X10,X11] : (~v1_relat_1(X10) | r1_tarski(X10,X11) | ~v1_relat_1(X10) | r2_hidden(sK1(X10,X11),k3_relat_1(X10))) )),
% 2.96/0.83    inference(resolution,[],[f25,f46])).
% 2.96/0.83  fof(f46,plain,(
% 2.96/0.83    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X0,k3_relat_1(X2))) )),
% 2.96/0.83    inference(cnf_transformation,[],[f20])).
% 2.96/0.83  fof(f1530,plain,(
% 2.96/0.83    ~sP8(k4_tarski(sK1(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),sK2(k1_wellord2(k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0)))),k4_tarski(sK0,sK0),k4_tarski(sK0,sK0))),
% 2.96/0.83    inference(unit_resulting_resolution,[],[f22,f1391,f159])).
% 2.96/0.83  fof(f159,plain,(
% 2.96/0.83    ( ! [X2,X3,X1] : (~sP8(k4_tarski(sK1(X1,k2_enumset1(X2,X2,X2,X3)),sK2(X1,k2_enumset1(X2,X2,X2,X3))),X3,X2) | r1_tarski(X1,k2_enumset1(X2,X2,X2,X3)) | ~v1_relat_1(X1)) )),
% 2.96/0.83    inference(resolution,[],[f26,f79])).
% 2.96/0.83  fof(f26,plain,(
% 2.96/0.83    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) | ~v1_relat_1(X0) | r1_tarski(X0,X1)) )),
% 2.96/0.83    inference(cnf_transformation,[],[f15])).
% 2.96/0.83  % SZS output end Proof for theBenchmark
% 2.96/0.83  % (16926)------------------------------
% 2.96/0.83  % (16926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.96/0.83  % (16926)Termination reason: Refutation
% 2.96/0.83  
% 2.96/0.83  % (16926)Memory used [KB]: 8059
% 2.96/0.83  % (16926)Time elapsed: 0.375 s
% 2.96/0.83  % (16926)------------------------------
% 2.96/0.83  % (16926)------------------------------
% 2.96/0.83  % (16906)Time limit reached!
% 2.96/0.83  % (16906)------------------------------
% 2.96/0.83  % (16906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.96/0.83  % (16906)Termination reason: Time limit
% 2.96/0.83  
% 2.96/0.83  % (16906)Memory used [KB]: 7675
% 2.96/0.83  % (16906)Time elapsed: 0.401 s
% 2.96/0.83  % (16906)------------------------------
% 2.96/0.83  % (16906)------------------------------
% 2.96/0.84  % (16900)Success in time 0.47 s
%------------------------------------------------------------------------------
