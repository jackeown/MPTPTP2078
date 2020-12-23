%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t36_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:26 EDT 2019

% Result     : Theorem 10.08s
% Output     : Refutation 10.08s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 236 expanded)
%              Number of leaves         :    9 (  51 expanded)
%              Depth                    :   28
%              Number of atoms          :  231 ( 702 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14089,plain,(
    $false ),
    inference(subsumption_resolution,[],[f14088,f101])).

fof(f101,plain,(
    v3_ordinal1(k3_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f98,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK1(X0))
      | v3_ordinal1(k3_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => v3_ordinal1(X1) )
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t36_ordinal1.p',t35_ordinal1)).

fof(f98,plain,
    ( v3_ordinal1(k3_tarski(sK0))
    | v3_ordinal1(sK1(sK0)) ),
    inference(resolution,[],[f64,f56])).

fof(f56,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_tarski(X0,X1)
          | ~ v3_ordinal1(X1) )
      & ! [X2] :
          ( v3_ordinal1(X2)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,plain,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ( v3_ordinal1(X1)
             => ~ r1_tarski(X0,X1) )
          & ! [X2] :
              ( r2_hidden(X2,X0)
             => v3_ordinal1(X2) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ( v3_ordinal1(X1)
             => ~ r1_tarski(X0,X1) )
          & ! [X1] :
              ( r2_hidden(X1,X0)
             => v3_ordinal1(X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ( v3_ordinal1(X1)
           => ~ r1_tarski(X0,X1) )
        & ! [X1] :
            ( r2_hidden(X1,X0)
           => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t36_ordinal1.p',t36_ordinal1)).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v3_ordinal1(k3_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14088,plain,(
    ~ v3_ordinal1(k3_tarski(sK0)) ),
    inference(resolution,[],[f14087,f61])).

fof(f61,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v3_ordinal1(k1_ordinal1(X0))
        & ~ v1_xboole_0(k1_ordinal1(X0)) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v3_ordinal1(k1_ordinal1(X0))
        & ~ v1_xboole_0(k1_ordinal1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t36_ordinal1.p',fc2_ordinal1)).

fof(f14087,plain,(
    ~ v3_ordinal1(k1_ordinal1(k3_tarski(sK0))) ),
    inference(resolution,[],[f14079,f61])).

fof(f14079,plain,(
    ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(k3_tarski(sK0)))) ),
    inference(resolution,[],[f14077,f55])).

fof(f55,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14077,plain,(
    r1_tarski(sK0,k1_ordinal1(k1_ordinal1(k3_tarski(sK0)))) ),
    inference(subsumption_resolution,[],[f14076,f101])).

fof(f14076,plain,
    ( r1_tarski(sK0,k1_ordinal1(k1_ordinal1(k3_tarski(sK0))))
    | ~ v3_ordinal1(k3_tarski(sK0)) ),
    inference(resolution,[],[f14073,f61])).

fof(f14073,plain,
    ( ~ v3_ordinal1(k1_ordinal1(k3_tarski(sK0)))
    | r1_tarski(sK0,k1_ordinal1(k1_ordinal1(k3_tarski(sK0)))) ),
    inference(duplicate_literal_removal,[],[f14066])).

fof(f14066,plain,
    ( r1_tarski(sK0,k1_ordinal1(k1_ordinal1(k3_tarski(sK0))))
    | r1_tarski(sK0,k1_ordinal1(k1_ordinal1(k3_tarski(sK0))))
    | ~ v3_ordinal1(k1_ordinal1(k3_tarski(sK0))) ),
    inference(resolution,[],[f14063,f2831])).

fof(f2831,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK3(sK0,k1_ordinal1(X0)),X0)
      | r1_tarski(sK0,k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f2824,f129])).

fof(f129,plain,(
    ! [X6] :
      ( v3_ordinal1(sK3(sK0,X6))
      | r1_tarski(sK0,X6) ) ),
    inference(resolution,[],[f77,f56])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t36_ordinal1.p',d3_tarski)).

fof(f2824,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_tarski(sK0,k1_ordinal1(X0))
      | ~ r1_tarski(sK3(sK0,k1_ordinal1(X0)),X0)
      | ~ v3_ordinal1(sK3(sK0,k1_ordinal1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f2822])).

fof(f2822,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r1_tarski(sK0,k1_ordinal1(X0))
      | ~ v3_ordinal1(X0)
      | ~ r1_tarski(sK3(sK0,k1_ordinal1(X0)),X0)
      | ~ v3_ordinal1(sK3(sK0,k1_ordinal1(X0))) ) ),
    inference(resolution,[],[f2793,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t36_ordinal1.p',redefinition_r1_ordinal1)).

fof(f2793,plain,(
    ! [X0] :
      ( ~ r1_ordinal1(sK3(sK0,k1_ordinal1(X0)),X0)
      | ~ v3_ordinal1(X0)
      | r1_tarski(sK0,k1_ordinal1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f2792])).

fof(f2792,plain,(
    ! [X0] :
      ( ~ r1_ordinal1(sK3(sK0,k1_ordinal1(X0)),X0)
      | ~ v3_ordinal1(X0)
      | r1_tarski(sK0,k1_ordinal1(X0))
      | r1_tarski(sK0,k1_ordinal1(X0)) ) ),
    inference(resolution,[],[f358,f129])).

fof(f358,plain,(
    ! [X10,X11] :
      ( ~ v3_ordinal1(sK3(X11,k1_ordinal1(X10)))
      | ~ r1_ordinal1(sK3(X11,k1_ordinal1(X10)),X10)
      | ~ v3_ordinal1(X10)
      | r1_tarski(X11,k1_ordinal1(X10)) ) ),
    inference(resolution,[],[f62,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t36_ordinal1.p',t34_ordinal1)).

fof(f14063,plain,(
    ! [X0] :
      ( r1_tarski(sK3(sK0,X0),k1_ordinal1(k3_tarski(sK0)))
      | r1_tarski(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f14029])).

fof(f14029,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | r1_tarski(sK3(sK0,X0),k1_ordinal1(k3_tarski(sK0)))
      | r1_tarski(sK3(sK0,X0),k1_ordinal1(k3_tarski(sK0))) ) ),
    inference(resolution,[],[f1516,f2657])).

fof(f2657,plain,(
    ! [X10] :
      ( ~ r2_hidden(sK3(X10,k1_ordinal1(k3_tarski(sK0))),k3_tarski(sK0))
      | r1_tarski(X10,k1_ordinal1(k3_tarski(sK0))) ) ),
    inference(resolution,[],[f2648,f78])).

fof(f2648,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_ordinal1(k3_tarski(sK0)))
      | ~ r2_hidden(X0,k3_tarski(sK0)) ) ),
    inference(resolution,[],[f2624,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f2624,plain,(
    r1_tarski(k3_tarski(sK0),k1_ordinal1(k3_tarski(sK0))) ),
    inference(subsumption_resolution,[],[f2623,f101])).

fof(f2623,plain,
    ( r1_tarski(k3_tarski(sK0),k1_ordinal1(k3_tarski(sK0)))
    | ~ v3_ordinal1(k3_tarski(sK0)) ),
    inference(duplicate_literal_removal,[],[f2622])).

fof(f2622,plain,
    ( r1_tarski(k3_tarski(sK0),k1_ordinal1(k3_tarski(sK0)))
    | ~ v3_ordinal1(k3_tarski(sK0))
    | ~ v3_ordinal1(k3_tarski(sK0)) ),
    inference(resolution,[],[f2620,f274])).

fof(f274,plain,(
    ! [X6,X7] :
      ( ~ r1_ordinal1(X6,k1_ordinal1(X7))
      | r1_tarski(X6,k1_ordinal1(X7))
      | ~ v3_ordinal1(X6)
      | ~ v3_ordinal1(X7) ) ),
    inference(resolution,[],[f75,f61])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f2620,plain,(
    r1_ordinal1(k3_tarski(sK0),k1_ordinal1(k3_tarski(sK0))) ),
    inference(subsumption_resolution,[],[f2619,f101])).

fof(f2619,plain,
    ( ~ v3_ordinal1(k3_tarski(sK0))
    | r1_ordinal1(k3_tarski(sK0),k1_ordinal1(k3_tarski(sK0))) ),
    inference(duplicate_literal_removal,[],[f2606])).

fof(f2606,plain,
    ( ~ v3_ordinal1(k3_tarski(sK0))
    | r1_ordinal1(k3_tarski(sK0),k1_ordinal1(k3_tarski(sK0)))
    | r1_ordinal1(k3_tarski(sK0),k1_ordinal1(k3_tarski(sK0))) ),
    inference(resolution,[],[f2603,f1305])).

fof(f1305,plain,
    ( r1_ordinal1(k1_ordinal1(k3_tarski(sK0)),k3_tarski(sK0))
    | r1_ordinal1(k3_tarski(sK0),k1_ordinal1(k3_tarski(sK0))) ),
    inference(resolution,[],[f1257,f101])).

fof(f1257,plain,(
    ! [X8] :
      ( ~ v3_ordinal1(X8)
      | r1_ordinal1(k1_ordinal1(k3_tarski(sK0)),X8)
      | r1_ordinal1(X8,k1_ordinal1(k3_tarski(sK0))) ) ),
    inference(resolution,[],[f233,f101])).

fof(f233,plain,(
    ! [X6,X7] :
      ( ~ v3_ordinal1(X7)
      | r1_ordinal1(X6,k1_ordinal1(X7))
      | r1_ordinal1(k1_ordinal1(X7),X6)
      | ~ v3_ordinal1(X6) ) ),
    inference(resolution,[],[f73,f61])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,X1)
      | r1_ordinal1(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t36_ordinal1.p',connectedness_r1_ordinal1)).

fof(f2603,plain,(
    ! [X0] :
      ( ~ r1_ordinal1(k1_ordinal1(k3_tarski(sK0)),X0)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(k3_tarski(sK0),k1_ordinal1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f2598])).

fof(f2598,plain,(
    ! [X0] :
      ( ~ r1_ordinal1(k1_ordinal1(k3_tarski(sK0)),X0)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(k3_tarski(sK0),k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f2541,f241])).

fof(f241,plain,(
    ! [X1] :
      ( r1_ordinal1(k1_ordinal1(X1),k3_tarski(sK0))
      | r1_ordinal1(k3_tarski(sK0),k1_ordinal1(X1))
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f231,f61])).

fof(f231,plain,(
    ! [X4] :
      ( ~ v3_ordinal1(X4)
      | r1_ordinal1(X4,k3_tarski(sK0))
      | r1_ordinal1(k3_tarski(sK0),X4) ) ),
    inference(resolution,[],[f73,f101])).

fof(f2541,plain,(
    ! [X7] :
      ( ~ r1_ordinal1(k1_ordinal1(X7),k3_tarski(sK0))
      | ~ r1_ordinal1(k1_ordinal1(k3_tarski(sK0)),X7)
      | ~ v3_ordinal1(X7) ) ),
    inference(resolution,[],[f1025,f101])).

fof(f1025,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r1_ordinal1(k1_ordinal1(X1),X0) ) ),
    inference(subsumption_resolution,[],[f1024,f61])).

fof(f1024,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ r1_ordinal1(k1_ordinal1(X1),X0)
      | ~ v3_ordinal1(k1_ordinal1(X1)) ) ),
    inference(subsumption_resolution,[],[f1021,f61])).

fof(f1021,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ r1_ordinal1(k1_ordinal1(X1),X0)
      | ~ v3_ordinal1(k1_ordinal1(X1)) ) ),
    inference(resolution,[],[f356,f62])).

fof(f356,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(k1_ordinal1(X6),X7)
      | ~ r1_ordinal1(X7,X6)
      | ~ v3_ordinal1(X7)
      | ~ v3_ordinal1(X6) ) ),
    inference(resolution,[],[f62,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t36_ordinal1.p',antisymmetry_r2_hidden)).

fof(f1516,plain,(
    ! [X12,X10,X11] :
      ( r2_hidden(sK3(sK3(X10,X11),X12),k3_tarski(X10))
      | r1_tarski(X10,X11)
      | r1_tarski(sK3(X10,X11),X12) ) ),
    inference(resolution,[],[f337,f77])).

fof(f337,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X6,sK3(X7,X8))
      | r2_hidden(X6,k3_tarski(X7))
      | r1_tarski(X7,X8) ) ),
    inference(resolution,[],[f91,f77])).

fof(f91,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X2,X3)
      | r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t36_ordinal1.p',d4_tarski)).
%------------------------------------------------------------------------------
