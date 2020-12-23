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
% DateTime   : Thu Dec  3 12:47:08 EST 2020

% Result     : Theorem 2.99s
% Output     : Refutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  126 (1539 expanded)
%              Number of leaves         :   24 ( 453 expanded)
%              Depth                    :   23
%              Number of atoms          :  221 (2934 expanded)
%              Number of equality atoms :   46 ( 660 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4092,plain,(
    $false ),
    inference(global_subsumption,[],[f50,f4091])).

fof(f4091,plain,(
    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f4090,f501])).

fof(f501,plain,(
    k3_relat_1(sK0) = k3_tarski(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f51,f93])).

fof(f93,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f57,f91])).

fof(f91,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f65,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f51,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f4090,plain,(
    r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0))),k3_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f4082,f95])).

fof(f95,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f61,f64,f64])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f4082,plain,(
    r1_tarski(k3_tarski(k1_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k1_relat_1(sK0))),k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1561,f4011,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f89,f91])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f4011,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f802,f3983])).

fof(f3983,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_relat_1(sK1))
      | r1_tarski(X2,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f228,f500])).

fof(f500,plain,(
    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f48,f93])).

fof(f48,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f228,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0)))
      | ~ r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f101,f95])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f85,f91])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f802,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f771,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f84,f62])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f771,plain,(
    k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f54,f755,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f755,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f754,f444])).

fof(f444,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f436,f438])).

fof(f438,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_relat_1(k1_xboole_0),X0) ),
    inference(unit_resulting_resolution,[],[f320,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f83,f62])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f320,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(unit_resulting_resolution,[],[f309,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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

fof(f309,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f304,f108])).

fof(f108,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | sP6(X2,X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( sP6(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f304,plain,(
    ! [X0] : ~ sP6(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f289,f77])).

fof(f77,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0)
      | ~ sP6(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f289,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f279,f133])).

fof(f133,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f54,f100])).

fof(f279,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,X1))) ),
    inference(unit_resulting_resolution,[],[f115,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k6_subset_1(X0,k6_subset_1(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f98,f96])).

fof(f96,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f66,f90,f62,f62])).

fof(f90,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f90])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f115,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f53,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f53,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f436,plain,(
    ! [X0] : k1_relat_1(k1_xboole_0) = k6_subset_1(k1_relat_1(k1_xboole_0),X0) ),
    inference(unit_resulting_resolution,[],[f94,f320,f73])).

fof(f94,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f60,f62])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f754,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f726,f135])).

fof(f135,plain,(
    k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f49,f100])).

fof(f49,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f726,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f51,f48,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1561,plain,(
    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1026,f1493])).

fof(f1493,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,k2_relat_1(sK1))
      | r1_tarski(X4,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f101,f500])).

fof(f1026,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f882,f99])).

fof(f882,plain,(
    k1_xboole_0 = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f843,f862])).

fof(f862,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f858,f861])).

fof(f861,plain,(
    k1_xboole_0 = k1_relat_1(k2_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f836,f843])).

fof(f836,plain,(
    k1_xboole_0 = k1_relat_1(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f289,f717,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( sP6(sK5(X0,X1),X0)
      | r2_hidden(sK5(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f717,plain,(
    ! [X0] : ~ sP6(X0,k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f696,f77])).

fof(f696,plain,(
    ! [X0] : ~ r2_hidden(X0,k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f319,f688,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f688,plain,(
    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f661,f135])).

fof(f661,plain,(
    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f51,f48,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

fof(f319,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f112,f309,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

fof(f112,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f52,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f858,plain,(
    k2_relat_1(k1_xboole_0) = k1_relat_1(k2_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f837,f843])).

fof(f837,plain,(
    k2_relat_1(k1_xboole_0) = k1_relat_1(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f319,f717,f81])).

fof(f843,plain,(
    k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f838,f837])).

fof(f838,plain,(
    k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)) = k1_relat_1(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f696,f717,f81])).

fof(f50,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:44:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (26912)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (26906)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (26917)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (26904)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (26903)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (26895)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (26913)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (26892)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (26896)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (26914)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (26897)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (26912)Refutation not found, incomplete strategy% (26912)------------------------------
% 0.21/0.54  % (26912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26912)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (26912)Memory used [KB]: 10746
% 0.21/0.54  % (26912)Time elapsed: 0.124 s
% 0.21/0.54  % (26912)------------------------------
% 0.21/0.54  % (26912)------------------------------
% 0.21/0.55  % (26898)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (26902)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (26889)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (26910)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (26907)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (26899)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (26911)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (26901)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (26891)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (26894)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.56  % (26890)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.56  % (26908)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (26919)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (26915)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.52/0.56  % (26916)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.52/0.57  % (26893)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.52/0.57  % (26918)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.52/0.57  % (26900)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.52/0.57  % (26899)Refutation not found, incomplete strategy% (26899)------------------------------
% 1.52/0.57  % (26899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (26899)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.57  
% 1.52/0.57  % (26899)Memory used [KB]: 10618
% 1.52/0.57  % (26899)Time elapsed: 0.156 s
% 1.52/0.57  % (26899)------------------------------
% 1.52/0.57  % (26899)------------------------------
% 1.52/0.58  % (26909)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.64/0.59  % (26900)Refutation not found, incomplete strategy% (26900)------------------------------
% 1.64/0.59  % (26900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.59  % (26900)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.59  
% 1.64/0.59  % (26900)Memory used [KB]: 10618
% 1.64/0.59  % (26900)Time elapsed: 0.176 s
% 1.64/0.59  % (26900)------------------------------
% 1.64/0.59  % (26900)------------------------------
% 2.09/0.69  % (26941)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.09/0.70  % (26963)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.09/0.71  % (26952)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.99/0.79  % (26914)Refutation found. Thanks to Tanya!
% 2.99/0.79  % SZS status Theorem for theBenchmark
% 2.99/0.79  % SZS output start Proof for theBenchmark
% 2.99/0.79  fof(f4092,plain,(
% 2.99/0.79    $false),
% 2.99/0.79    inference(global_subsumption,[],[f50,f4091])).
% 2.99/0.79  fof(f4091,plain,(
% 2.99/0.79    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 2.99/0.79    inference(forward_demodulation,[],[f4090,f501])).
% 2.99/0.79  fof(f501,plain,(
% 2.99/0.79    k3_relat_1(sK0) = k3_tarski(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0)))),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f51,f93])).
% 2.99/0.79  fof(f93,plain,(
% 2.99/0.79    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 2.99/0.79    inference(definition_unfolding,[],[f57,f91])).
% 2.99/0.79  fof(f91,plain,(
% 2.99/0.79    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.99/0.79    inference(definition_unfolding,[],[f65,f64])).
% 2.99/0.79  fof(f64,plain,(
% 2.99/0.79    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.99/0.79    inference(cnf_transformation,[],[f18])).
% 2.99/0.79  fof(f18,axiom,(
% 2.99/0.79    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.99/0.79  fof(f65,plain,(
% 2.99/0.79    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.99/0.79    inference(cnf_transformation,[],[f19])).
% 2.99/0.79  fof(f19,axiom,(
% 2.99/0.79    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.99/0.79  fof(f57,plain,(
% 2.99/0.79    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 2.99/0.79    inference(cnf_transformation,[],[f34])).
% 2.99/0.79  fof(f34,plain,(
% 2.99/0.79    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.99/0.79    inference(ennf_transformation,[],[f24])).
% 2.99/0.79  fof(f24,axiom,(
% 2.99/0.79    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 2.99/0.79  fof(f51,plain,(
% 2.99/0.79    v1_relat_1(sK0)),
% 2.99/0.79    inference(cnf_transformation,[],[f32])).
% 2.99/0.79  fof(f32,plain,(
% 2.99/0.79    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.99/0.79    inference(flattening,[],[f31])).
% 2.99/0.79  fof(f31,plain,(
% 2.99/0.79    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.99/0.79    inference(ennf_transformation,[],[f29])).
% 2.99/0.79  fof(f29,negated_conjecture,(
% 2.99/0.79    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.99/0.79    inference(negated_conjecture,[],[f28])).
% 2.99/0.79  fof(f28,conjecture,(
% 2.99/0.79    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 2.99/0.79  fof(f4090,plain,(
% 2.99/0.79    r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0))),k3_relat_1(sK1))),
% 2.99/0.79    inference(forward_demodulation,[],[f4082,f95])).
% 2.99/0.79  fof(f95,plain,(
% 2.99/0.79    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 2.99/0.79    inference(definition_unfolding,[],[f61,f64,f64])).
% 2.99/0.79  fof(f61,plain,(
% 2.99/0.79    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.99/0.79    inference(cnf_transformation,[],[f17])).
% 2.99/0.79  fof(f17,axiom,(
% 2.99/0.79    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.99/0.79  fof(f4082,plain,(
% 2.99/0.79    r1_tarski(k3_tarski(k1_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k1_relat_1(sK0))),k3_relat_1(sK1))),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f1561,f4011,f105])).
% 2.99/0.79  fof(f105,plain,(
% 2.99/0.79    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.99/0.79    inference(definition_unfolding,[],[f89,f91])).
% 2.99/0.79  fof(f89,plain,(
% 2.99/0.79    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1)) )),
% 2.99/0.79    inference(cnf_transformation,[],[f47])).
% 2.99/0.79  fof(f47,plain,(
% 2.99/0.79    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.99/0.79    inference(flattening,[],[f46])).
% 2.99/0.79  fof(f46,plain,(
% 2.99/0.79    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.99/0.79    inference(ennf_transformation,[],[f16])).
% 2.99/0.79  fof(f16,axiom,(
% 2.99/0.79    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 2.99/0.79  fof(f4011,plain,(
% 2.99/0.79    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f802,f3983])).
% 2.99/0.79  fof(f3983,plain,(
% 2.99/0.79    ( ! [X2] : (~r1_tarski(X2,k1_relat_1(sK1)) | r1_tarski(X2,k3_relat_1(sK1))) )),
% 2.99/0.79    inference(superposition,[],[f228,f500])).
% 2.99/0.79  fof(f500,plain,(
% 2.99/0.79    k3_relat_1(sK1) = k3_tarski(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1)))),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f48,f93])).
% 2.99/0.79  fof(f48,plain,(
% 2.99/0.79    v1_relat_1(sK1)),
% 2.99/0.79    inference(cnf_transformation,[],[f32])).
% 2.99/0.79  fof(f228,plain,(
% 2.99/0.79    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0))) | ~r1_tarski(X2,X1)) )),
% 2.99/0.79    inference(superposition,[],[f101,f95])).
% 2.99/0.79  fof(f101,plain,(
% 2.99/0.79    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 2.99/0.79    inference(definition_unfolding,[],[f85,f91])).
% 2.99/0.79  fof(f85,plain,(
% 2.99/0.79    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 2.99/0.79    inference(cnf_transformation,[],[f42])).
% 2.99/0.79  fof(f42,plain,(
% 2.99/0.79    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.99/0.79    inference(ennf_transformation,[],[f7])).
% 2.99/0.79  fof(f7,axiom,(
% 2.99/0.79    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.99/0.79  fof(f802,plain,(
% 2.99/0.79    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f771,f99])).
% 2.99/0.79  fof(f99,plain,(
% 2.99/0.79    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 2.99/0.79    inference(definition_unfolding,[],[f84,f62])).
% 2.99/0.79  fof(f62,plain,(
% 2.99/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.99/0.79    inference(cnf_transformation,[],[f20])).
% 2.99/0.79  fof(f20,axiom,(
% 2.99/0.79    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.99/0.79  fof(f84,plain,(
% 2.99/0.79    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 2.99/0.79    inference(cnf_transformation,[],[f6])).
% 2.99/0.79  fof(f6,axiom,(
% 2.99/0.79    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.99/0.79  fof(f771,plain,(
% 2.99/0.79    k1_xboole_0 = k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1))),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f54,f755,f73])).
% 2.99/0.79  fof(f73,plain,(
% 2.99/0.79    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.99/0.79    inference(cnf_transformation,[],[f5])).
% 2.99/0.79  fof(f5,axiom,(
% 2.99/0.79    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.99/0.79  fof(f755,plain,(
% 2.99/0.79    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_xboole_0)),
% 2.99/0.79    inference(forward_demodulation,[],[f754,f444])).
% 2.99/0.79  fof(f444,plain,(
% 2.99/0.79    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.99/0.79    inference(forward_demodulation,[],[f436,f438])).
% 2.99/0.79  fof(f438,plain,(
% 2.99/0.79    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_relat_1(k1_xboole_0),X0)) )),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f320,f100])).
% 2.99/0.79  fof(f100,plain,(
% 2.99/0.79    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.99/0.79    inference(definition_unfolding,[],[f83,f62])).
% 2.99/0.79  fof(f83,plain,(
% 2.99/0.79    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 2.99/0.79    inference(cnf_transformation,[],[f6])).
% 2.99/0.79  fof(f320,plain,(
% 2.99/0.79    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f309,f75])).
% 2.99/0.79  fof(f75,plain,(
% 2.99/0.79    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.99/0.79    inference(cnf_transformation,[],[f41])).
% 2.99/0.79  fof(f41,plain,(
% 2.99/0.79    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.99/0.79    inference(ennf_transformation,[],[f1])).
% 2.99/0.79  fof(f1,axiom,(
% 2.99/0.79    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.99/0.79  fof(f309,plain,(
% 2.99/0.79    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f304,f108])).
% 2.99/0.79  fof(f108,plain,(
% 2.99/0.79    ( ! [X2,X0] : (~r2_hidden(X2,k1_relat_1(X0)) | sP6(X2,X0)) )),
% 2.99/0.79    inference(equality_resolution,[],[f80])).
% 2.99/0.79  fof(f80,plain,(
% 2.99/0.79    ( ! [X2,X0,X1] : (sP6(X2,X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 2.99/0.79    inference(cnf_transformation,[],[f23])).
% 2.99/0.79  fof(f23,axiom,(
% 2.99/0.79    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 2.99/0.79  fof(f304,plain,(
% 2.99/0.79    ( ! [X0] : (~sP6(X0,k1_xboole_0)) )),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f289,f77])).
% 2.99/0.79  fof(f77,plain,(
% 2.99/0.79    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0) | ~sP6(X2,X0)) )),
% 2.99/0.79    inference(cnf_transformation,[],[f23])).
% 2.99/0.79  fof(f289,plain,(
% 2.99/0.79    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.99/0.79    inference(forward_demodulation,[],[f279,f133])).
% 2.99/0.79  fof(f133,plain,(
% 2.99/0.79    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) )),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f54,f100])).
% 2.99/0.79  fof(f279,plain,(
% 2.99/0.79    ( ! [X0,X1] : (~r2_hidden(X0,k6_subset_1(k1_xboole_0,k6_subset_1(k1_xboole_0,X1)))) )),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f115,f111])).
% 2.99/0.79  fof(f111,plain,(
% 2.99/0.79    ( ! [X2,X0,X1] : (~r2_hidden(X2,k6_subset_1(X0,k6_subset_1(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 2.99/0.79    inference(forward_demodulation,[],[f98,f96])).
% 2.99/0.79  fof(f96,plain,(
% 2.99/0.79    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 2.99/0.79    inference(definition_unfolding,[],[f66,f90,f62,f62])).
% 2.99/0.79  fof(f90,plain,(
% 2.99/0.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.99/0.79    inference(definition_unfolding,[],[f63,f64])).
% 2.99/0.79  fof(f63,plain,(
% 2.99/0.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.99/0.79    inference(cnf_transformation,[],[f21])).
% 2.99/0.79  fof(f21,axiom,(
% 2.99/0.79    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.99/0.79  fof(f66,plain,(
% 2.99/0.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.99/0.79    inference(cnf_transformation,[],[f14])).
% 2.99/0.79  fof(f14,axiom,(
% 2.99/0.79    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.99/0.79  fof(f98,plain,(
% 2.99/0.79    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 2.99/0.79    inference(definition_unfolding,[],[f67,f90])).
% 2.99/0.79  fof(f67,plain,(
% 2.99/0.79    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.99/0.79    inference(cnf_transformation,[],[f37])).
% 2.99/0.79  fof(f37,plain,(
% 2.99/0.79    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.99/0.79    inference(ennf_transformation,[],[f30])).
% 2.99/0.79  fof(f30,plain,(
% 2.99/0.79    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.99/0.79    inference(rectify,[],[f4])).
% 2.99/0.79  fof(f4,axiom,(
% 2.99/0.79    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.99/0.79  fof(f115,plain,(
% 2.99/0.79    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f53,f70])).
% 2.99/0.79  fof(f70,plain,(
% 2.99/0.79    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.99/0.79    inference(cnf_transformation,[],[f40])).
% 2.99/0.79  fof(f40,plain,(
% 2.99/0.79    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.99/0.79    inference(ennf_transformation,[],[f3])).
% 2.99/0.79  fof(f3,axiom,(
% 2.99/0.79    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.99/0.79  fof(f53,plain,(
% 2.99/0.79    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.99/0.79    inference(cnf_transformation,[],[f15])).
% 2.99/0.79  fof(f15,axiom,(
% 2.99/0.79    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.99/0.79  fof(f436,plain,(
% 2.99/0.79    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k6_subset_1(k1_relat_1(k1_xboole_0),X0)) )),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f94,f320,f73])).
% 2.99/0.79  fof(f94,plain,(
% 2.99/0.79    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 2.99/0.79    inference(definition_unfolding,[],[f60,f62])).
% 2.99/0.79  fof(f60,plain,(
% 2.99/0.79    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.99/0.79    inference(cnf_transformation,[],[f10])).
% 2.99/0.79  fof(f10,axiom,(
% 2.99/0.79    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.99/0.79  fof(f754,plain,(
% 2.99/0.79    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))),
% 2.99/0.79    inference(forward_demodulation,[],[f726,f135])).
% 2.99/0.79  fof(f135,plain,(
% 2.99/0.79    k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f49,f100])).
% 2.99/0.79  fof(f49,plain,(
% 2.99/0.79    r1_tarski(sK0,sK1)),
% 2.99/0.79    inference(cnf_transformation,[],[f32])).
% 2.99/0.79  fof(f726,plain,(
% 2.99/0.79    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f51,f48,f59])).
% 2.99/0.79  fof(f59,plain,(
% 2.99/0.79    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.99/0.79    inference(cnf_transformation,[],[f36])).
% 2.99/0.79  fof(f36,plain,(
% 2.99/0.79    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.99/0.79    inference(ennf_transformation,[],[f25])).
% 2.99/0.79  fof(f25,axiom,(
% 2.99/0.79    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).
% 2.99/0.79  fof(f54,plain,(
% 2.99/0.79    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.99/0.79    inference(cnf_transformation,[],[f9])).
% 2.99/0.79  fof(f9,axiom,(
% 2.99/0.79    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.99/0.79  fof(f1561,plain,(
% 2.99/0.79    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f1026,f1493])).
% 2.99/0.79  fof(f1493,plain,(
% 2.99/0.79    ( ! [X4] : (~r1_tarski(X4,k2_relat_1(sK1)) | r1_tarski(X4,k3_relat_1(sK1))) )),
% 2.99/0.79    inference(superposition,[],[f101,f500])).
% 2.99/0.79  fof(f1026,plain,(
% 2.99/0.79    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f882,f99])).
% 2.99/0.79  fof(f882,plain,(
% 2.99/0.79    k1_xboole_0 = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))),
% 2.99/0.79    inference(backward_demodulation,[],[f843,f862])).
% 2.99/0.79  fof(f862,plain,(
% 2.99/0.79    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.99/0.79    inference(backward_demodulation,[],[f858,f861])).
% 2.99/0.79  fof(f861,plain,(
% 2.99/0.79    k1_xboole_0 = k1_relat_1(k2_relat_1(k1_xboole_0))),
% 2.99/0.79    inference(forward_demodulation,[],[f836,f843])).
% 2.99/0.79  fof(f836,plain,(
% 2.99/0.79    k1_xboole_0 = k1_relat_1(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f289,f717,f81])).
% 2.99/0.79  fof(f81,plain,(
% 2.99/0.79    ( ! [X0,X1] : (sP6(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 2.99/0.79    inference(cnf_transformation,[],[f23])).
% 2.99/0.79  fof(f717,plain,(
% 2.99/0.79    ( ! [X0] : (~sP6(X0,k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)))) )),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f696,f77])).
% 2.99/0.79  fof(f696,plain,(
% 2.99/0.79    ( ! [X0] : (~r2_hidden(X0,k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)))) )),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f319,f688,f74])).
% 2.99/0.79  fof(f74,plain,(
% 2.99/0.79    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.99/0.79    inference(cnf_transformation,[],[f41])).
% 2.99/0.79  fof(f688,plain,(
% 2.99/0.79    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0))),
% 2.99/0.79    inference(forward_demodulation,[],[f661,f135])).
% 2.99/0.79  fof(f661,plain,(
% 2.99/0.79    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f51,f48,f58])).
% 2.99/0.79  fof(f58,plain,(
% 2.99/0.79    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.99/0.79    inference(cnf_transformation,[],[f35])).
% 2.99/0.79  fof(f35,plain,(
% 2.99/0.79    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.99/0.79    inference(ennf_transformation,[],[f27])).
% 2.99/0.79  fof(f27,axiom,(
% 2.99/0.79    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).
% 2.99/0.79  fof(f319,plain,(
% 2.99/0.79    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0))) )),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f112,f309,f69])).
% 2.99/0.79  fof(f69,plain,(
% 2.99/0.79    ( ! [X0,X1] : (r2_hidden(sK3(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.99/0.79    inference(cnf_transformation,[],[f39])).
% 2.99/0.79  fof(f39,plain,(
% 2.99/0.79    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.99/0.79    inference(flattening,[],[f38])).
% 2.99/0.79  fof(f38,plain,(
% 2.99/0.79    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.99/0.79    inference(ennf_transformation,[],[f26])).
% 2.99/0.79  fof(f26,axiom,(
% 2.99/0.79    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).
% 2.99/0.79  fof(f112,plain,(
% 2.99/0.79    v1_relat_1(k1_xboole_0)),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f52,f56])).
% 2.99/0.79  fof(f56,plain,(
% 2.99/0.79    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 2.99/0.79    inference(cnf_transformation,[],[f33])).
% 2.99/0.79  fof(f33,plain,(
% 2.99/0.79    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 2.99/0.79    inference(ennf_transformation,[],[f22])).
% 2.99/0.79  fof(f22,axiom,(
% 2.99/0.79    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 2.99/0.79  fof(f52,plain,(
% 2.99/0.79    v1_xboole_0(k1_xboole_0)),
% 2.99/0.79    inference(cnf_transformation,[],[f2])).
% 2.99/0.79  fof(f2,axiom,(
% 2.99/0.79    v1_xboole_0(k1_xboole_0)),
% 2.99/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.99/0.79  fof(f858,plain,(
% 2.99/0.79    k2_relat_1(k1_xboole_0) = k1_relat_1(k2_relat_1(k1_xboole_0))),
% 2.99/0.79    inference(backward_demodulation,[],[f837,f843])).
% 2.99/0.79  fof(f837,plain,(
% 2.99/0.79    k2_relat_1(k1_xboole_0) = k1_relat_1(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f319,f717,f81])).
% 2.99/0.79  fof(f843,plain,(
% 2.99/0.79    k2_relat_1(k1_xboole_0) = k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1))),
% 2.99/0.79    inference(backward_demodulation,[],[f838,f837])).
% 2.99/0.79  fof(f838,plain,(
% 2.99/0.79    k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)) = k1_relat_1(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 2.99/0.79    inference(unit_resulting_resolution,[],[f696,f717,f81])).
% 2.99/0.79  fof(f50,plain,(
% 2.99/0.79    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 2.99/0.79    inference(cnf_transformation,[],[f32])).
% 2.99/0.79  % SZS output end Proof for theBenchmark
% 2.99/0.79  % (26914)------------------------------
% 2.99/0.79  % (26914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.99/0.79  % (26914)Termination reason: Refutation
% 2.99/0.79  
% 2.99/0.79  % (26914)Memory used [KB]: 9594
% 2.99/0.79  % (26914)Time elapsed: 0.341 s
% 2.99/0.79  % (26914)------------------------------
% 2.99/0.79  % (26914)------------------------------
% 2.99/0.79  % (26888)Success in time 0.42 s
%------------------------------------------------------------------------------
