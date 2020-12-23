%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 826 expanded)
%              Number of leaves         :   26 ( 256 expanded)
%              Depth                    :   19
%              Number of atoms          :  272 (2098 expanded)
%              Number of equality atoms :   49 ( 325 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1515,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1514,f61])).

fof(f61,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f1514,plain,(
    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f1503,f109])).

fof(f109,plain,(
    k3_relat_1(sK0) = k3_tarski(k2_tarski(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f58,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f64,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f64,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f58,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f1503,plain,(
    r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK0),k2_relat_1(sK0))),k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1077,f1433,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f89,f72])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f1433,plain,(
    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1230,f1205,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1205,plain,(
    r1_tarski(k2_relat_1(sK1),k3_relat_1(sK1)) ),
    inference(superposition,[],[f746,f120])).

fof(f120,plain,(
    k3_relat_1(sK1) = k3_tarski(k2_tarski(k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f59,f90])).

fof(f59,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f746,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) ),
    inference(backward_demodulation,[],[f654,f626])).

fof(f626,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(unit_resulting_resolution,[],[f92,f243,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f243,plain,(
    ! [X0] : r1_tarski(k3_tarski(k2_tarski(X0,k1_xboole_0)),X0) ),
    inference(backward_demodulation,[],[f223,f197])).

fof(f197,plain,(
    k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f63,f161,f79])).

fof(f161,plain,(
    ! [X0] : r1_tarski(k6_subset_1(sK0,sK1),X0) ),
    inference(unit_resulting_resolution,[],[f125,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f85,f69,f72])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f125,plain,(
    ! [X0] : r1_tarski(sK0,k3_tarski(k2_tarski(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f92,f60,f88])).

fof(f60,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f63,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f223,plain,(
    ! [X0] : r1_tarski(k3_tarski(k2_tarski(X0,k6_subset_1(sK0,sK1))),X0) ),
    inference(unit_resulting_resolution,[],[f101,f161,f100])).

fof(f101,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f92,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f68,f72])).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f654,plain,(
    ! [X0,X1] : r1_tarski(k3_tarski(k2_tarski(X0,k1_xboole_0)),k3_tarski(k2_tarski(X1,X0))) ),
    inference(unit_resulting_resolution,[],[f243,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f84,f72])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f1230,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f1136,f1213])).

fof(f1213,plain,(
    sK1 = k3_tarski(k2_tarski(sK0,sK1)) ),
    inference(backward_demodulation,[],[f500,f1177])).

fof(f1177,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = X0 ),
    inference(unit_resulting_resolution,[],[f746,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f76,f71])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f500,plain,(
    k3_tarski(k2_tarski(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f472,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f472,plain,(
    k3_tarski(k2_tarski(sK0,sK1)) = k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(sK0,sK1)),sK1)) ),
    inference(unit_resulting_resolution,[],[f144,f95])).

fof(f144,plain,(
    r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),sK1) ),
    inference(forward_demodulation,[],[f139,f70])).

fof(f139,plain,(
    r1_tarski(k3_tarski(k2_tarski(sK1,sK0)),sK1) ),
    inference(unit_resulting_resolution,[],[f101,f60,f100])).

fof(f1136,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK0,sK1)))) ),
    inference(superposition,[],[f92,f118])).

fof(f118,plain,(
    k2_relat_1(k3_tarski(k2_tarski(sK0,sK1))) = k3_tarski(k2_tarski(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f58,f59,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_relat_1(X0),k2_relat_1(X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f65,f72,f72])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

fof(f1077,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f818,f1033,f88])).

fof(f1033,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f908,f999])).

fof(f999,plain,(
    ! [X0] : k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f626,f70])).

fof(f908,plain,(
    r1_tarski(k1_relat_1(sK0),k3_tarski(k2_tarski(k1_xboole_0,k1_relat_1(sK1)))) ),
    inference(backward_demodulation,[],[f621,f894])).

fof(f894,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f890,f890,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | k1_relat_1(X0) = X1
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f53,f56,f55,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f890,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f889,f62])).

fof(f62,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f889,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ r1_xboole_0(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f93,f513])).

fof(f513,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(superposition,[],[f239,f70])).

fof(f239,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) ),
    inference(backward_demodulation,[],[f212,f197])).

fof(f212,plain,(
    ! [X0] : k6_subset_1(sK0,sK1) = k1_setfam_1(k2_tarski(k6_subset_1(sK0,sK1),X0)) ),
    inference(unit_resulting_resolution,[],[f161,f95])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f74,f71])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f621,plain,(
    r1_tarski(k1_relat_1(sK0),k3_tarski(k2_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(sK1)))) ),
    inference(forward_demodulation,[],[f593,f70])).

fof(f593,plain,(
    r1_tarski(k1_relat_1(sK0),k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k1_xboole_0)))) ),
    inference(unit_resulting_resolution,[],[f236,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f86,f72,f69])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f236,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f114,f197])).

fof(f114,plain,(
    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f58,f59,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

fof(f818,plain,(
    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1)) ),
    inference(superposition,[],[f92,f120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (976)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (995)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.51  % (971)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (978)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (973)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (989)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (987)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (979)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (962)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (991)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (981)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (983)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (977)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (988)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (990)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (994)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (972)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (975)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (974)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (986)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (998)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (993)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (996)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (982)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (997)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (1001)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (985)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (992)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (980)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.57  % (984)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.63  % (981)Refutation found. Thanks to Tanya!
% 0.21/0.63  % SZS status Theorem for theBenchmark
% 0.21/0.63  % SZS output start Proof for theBenchmark
% 0.21/0.63  fof(f1515,plain,(
% 0.21/0.63    $false),
% 0.21/0.63    inference(subsumption_resolution,[],[f1514,f61])).
% 0.21/0.63  fof(f61,plain,(
% 0.21/0.63    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 0.21/0.63    inference(cnf_transformation,[],[f45])).
% 0.21/0.63  fof(f45,plain,(
% 0.21/0.63    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f44,f43])).
% 0.21/0.63  fof(f43,plain,(
% 0.21/0.63    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.63    introduced(choice_axiom,[])).
% 0.21/0.63  fof(f44,plain,(
% 0.21/0.63    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 0.21/0.63    introduced(choice_axiom,[])).
% 0.21/0.63  fof(f27,plain,(
% 0.21/0.63    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.63    inference(flattening,[],[f26])).
% 0.21/0.63  fof(f26,plain,(
% 0.21/0.63    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.63    inference(ennf_transformation,[],[f24])).
% 0.21/0.63  fof(f24,negated_conjecture,(
% 0.21/0.63    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.63    inference(negated_conjecture,[],[f23])).
% 0.21/0.63  fof(f23,conjecture,(
% 0.21/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 0.21/0.63  fof(f1514,plain,(
% 0.21/0.63    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 0.21/0.63    inference(forward_demodulation,[],[f1503,f109])).
% 0.21/0.63  fof(f109,plain,(
% 0.21/0.63    k3_relat_1(sK0) = k3_tarski(k2_tarski(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.21/0.63    inference(unit_resulting_resolution,[],[f58,f90])).
% 0.21/0.63  fof(f90,plain,(
% 0.21/0.63    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.21/0.63    inference(definition_unfolding,[],[f64,f72])).
% 0.21/0.63  fof(f72,plain,(
% 0.21/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.63    inference(cnf_transformation,[],[f16])).
% 0.21/0.63  fof(f16,axiom,(
% 0.21/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.63  fof(f64,plain,(
% 0.21/0.63    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f28])).
% 0.21/0.63  fof(f28,plain,(
% 0.21/0.63    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.63    inference(ennf_transformation,[],[f20])).
% 0.21/0.63  fof(f20,axiom,(
% 0.21/0.63    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.63  fof(f58,plain,(
% 0.21/0.63    v1_relat_1(sK0)),
% 0.21/0.63    inference(cnf_transformation,[],[f45])).
% 0.21/0.63  fof(f1503,plain,(
% 0.21/0.63    r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK0),k2_relat_1(sK0))),k3_relat_1(sK1))),
% 0.21/0.63    inference(unit_resulting_resolution,[],[f1077,f1433,f100])).
% 0.21/0.63  fof(f100,plain,(
% 0.21/0.63    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.63    inference(definition_unfolding,[],[f89,f72])).
% 0.21/0.63  fof(f89,plain,(
% 0.21/0.63    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f42])).
% 0.21/0.63  fof(f42,plain,(
% 0.21/0.63    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.63    inference(flattening,[],[f41])).
% 0.21/0.63  fof(f41,plain,(
% 0.21/0.63    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.63    inference(ennf_transformation,[],[f14])).
% 0.21/0.63  fof(f14,axiom,(
% 0.21/0.63    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.63  fof(f1433,plain,(
% 0.21/0.63    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 0.21/0.63    inference(unit_resulting_resolution,[],[f1230,f1205,f88])).
% 0.21/0.63  fof(f88,plain,(
% 0.21/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f40])).
% 0.21/0.63  fof(f40,plain,(
% 0.21/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.63    inference(flattening,[],[f39])).
% 0.21/0.63  fof(f39,plain,(
% 0.21/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.63    inference(ennf_transformation,[],[f7])).
% 0.21/0.63  fof(f7,axiom,(
% 0.21/0.63    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.63  fof(f1205,plain,(
% 0.21/0.63    r1_tarski(k2_relat_1(sK1),k3_relat_1(sK1))),
% 0.21/0.63    inference(superposition,[],[f746,f120])).
% 0.21/0.63  fof(f120,plain,(
% 0.21/0.63    k3_relat_1(sK1) = k3_tarski(k2_tarski(k1_relat_1(sK1),k2_relat_1(sK1)))),
% 0.21/0.63    inference(unit_resulting_resolution,[],[f59,f90])).
% 0.21/0.63  fof(f59,plain,(
% 0.21/0.63    v1_relat_1(sK1)),
% 0.21/0.63    inference(cnf_transformation,[],[f45])).
% 0.21/0.63  fof(f746,plain,(
% 0.21/0.63    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) )),
% 0.21/0.63    inference(backward_demodulation,[],[f654,f626])).
% 0.21/0.63  fof(f626,plain,(
% 0.21/0.63    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 0.21/0.63    inference(unit_resulting_resolution,[],[f92,f243,f79])).
% 0.21/0.63  fof(f79,plain,(
% 0.21/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f51])).
% 0.21/0.63  fof(f51,plain,(
% 0.21/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.63    inference(flattening,[],[f50])).
% 0.21/0.63  fof(f50,plain,(
% 0.21/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.63    inference(nnf_transformation,[],[f4])).
% 0.21/0.63  fof(f4,axiom,(
% 0.21/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.63  fof(f243,plain,(
% 0.21/0.63    ( ! [X0] : (r1_tarski(k3_tarski(k2_tarski(X0,k1_xboole_0)),X0)) )),
% 0.21/0.63    inference(backward_demodulation,[],[f223,f197])).
% 0.21/0.63  fof(f197,plain,(
% 0.21/0.63    k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 0.21/0.63    inference(unit_resulting_resolution,[],[f63,f161,f79])).
% 0.21/0.63  fof(f161,plain,(
% 0.21/0.63    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,sK1),X0)) )),
% 0.21/0.63    inference(unit_resulting_resolution,[],[f125,f97])).
% 0.21/0.63  fof(f97,plain,(
% 0.21/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 0.21/0.63    inference(definition_unfolding,[],[f85,f69,f72])).
% 0.21/0.63  fof(f69,plain,(
% 0.21/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f17])).
% 0.21/0.63  fof(f17,axiom,(
% 0.21/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.63  fof(f85,plain,(
% 0.21/0.63    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.63    inference(cnf_transformation,[],[f36])).
% 0.21/0.63  fof(f36,plain,(
% 0.21/0.63    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.63    inference(ennf_transformation,[],[f10])).
% 0.21/0.63  fof(f10,axiom,(
% 0.21/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.21/0.63  fof(f125,plain,(
% 0.21/0.63    ( ! [X0] : (r1_tarski(sK0,k3_tarski(k2_tarski(sK1,X0)))) )),
% 0.21/0.63    inference(unit_resulting_resolution,[],[f92,f60,f88])).
% 0.21/0.63  fof(f60,plain,(
% 0.21/0.63    r1_tarski(sK0,sK1)),
% 0.21/0.63    inference(cnf_transformation,[],[f45])).
% 0.21/0.63  fof(f63,plain,(
% 0.21/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f9])).
% 0.21/0.63  fof(f9,axiom,(
% 0.21/0.63    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.63  fof(f223,plain,(
% 0.21/0.63    ( ! [X0] : (r1_tarski(k3_tarski(k2_tarski(X0,k6_subset_1(sK0,sK1))),X0)) )),
% 0.21/0.63    inference(unit_resulting_resolution,[],[f101,f161,f100])).
% 0.21/0.63  fof(f101,plain,(
% 0.21/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.63    inference(equality_resolution,[],[f78])).
% 0.21/0.63  fof(f78,plain,(
% 0.21/0.63    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.63    inference(cnf_transformation,[],[f51])).
% 0.21/0.63  fof(f92,plain,(
% 0.21/0.63    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 0.21/0.63    inference(definition_unfolding,[],[f68,f72])).
% 0.21/0.63  fof(f68,plain,(
% 0.21/0.63    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.63    inference(cnf_transformation,[],[f13])).
% 0.21/0.63  fof(f13,axiom,(
% 0.21/0.63    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.63  fof(f654,plain,(
% 0.21/0.63    ( ! [X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,k1_xboole_0)),k3_tarski(k2_tarski(X1,X0)))) )),
% 0.21/0.63    inference(unit_resulting_resolution,[],[f243,f96])).
% 0.21/0.63  fof(f96,plain,(
% 0.21/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 0.21/0.63    inference(definition_unfolding,[],[f84,f72])).
% 0.21/0.63  fof(f84,plain,(
% 0.21/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f35])).
% 0.21/0.63  fof(f35,plain,(
% 0.21/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.63    inference(ennf_transformation,[],[f5])).
% 0.21/0.63  fof(f5,axiom,(
% 0.21/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.63  fof(f1230,plain,(
% 0.21/0.63    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 0.21/0.63    inference(backward_demodulation,[],[f1136,f1213])).
% 0.21/0.63  fof(f1213,plain,(
% 0.21/0.63    sK1 = k3_tarski(k2_tarski(sK0,sK1))),
% 0.21/0.63    inference(backward_demodulation,[],[f500,f1177])).
% 0.21/0.63  fof(f1177,plain,(
% 0.21/0.63    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = X0) )),
% 0.21/0.63    inference(unit_resulting_resolution,[],[f746,f95])).
% 0.21/0.63  fof(f95,plain,(
% 0.21/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.21/0.63    inference(definition_unfolding,[],[f76,f71])).
% 0.21/0.63  fof(f71,plain,(
% 0.21/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.63    inference(cnf_transformation,[],[f18])).
% 0.21/0.63  fof(f18,axiom,(
% 0.21/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.63  fof(f76,plain,(
% 0.21/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f34])).
% 0.21/0.63  fof(f34,plain,(
% 0.21/0.63    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.63    inference(ennf_transformation,[],[f8])).
% 0.21/0.63  fof(f8,axiom,(
% 0.21/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.63  fof(f500,plain,(
% 0.21/0.63    k3_tarski(k2_tarski(sK0,sK1)) = k1_setfam_1(k2_tarski(sK1,k3_tarski(k2_tarski(sK0,sK1))))),
% 0.21/0.63    inference(forward_demodulation,[],[f472,f70])).
% 0.21/0.63  fof(f70,plain,(
% 0.21/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f15])).
% 0.21/0.63  fof(f15,axiom,(
% 0.21/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.63  fof(f472,plain,(
% 0.21/0.63    k3_tarski(k2_tarski(sK0,sK1)) = k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(sK0,sK1)),sK1))),
% 0.21/0.63    inference(unit_resulting_resolution,[],[f144,f95])).
% 0.21/0.63  fof(f144,plain,(
% 0.21/0.63    r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),sK1)),
% 0.21/0.63    inference(forward_demodulation,[],[f139,f70])).
% 0.21/0.63  fof(f139,plain,(
% 0.21/0.63    r1_tarski(k3_tarski(k2_tarski(sK1,sK0)),sK1)),
% 0.21/0.63    inference(unit_resulting_resolution,[],[f101,f60,f100])).
% 0.21/0.63  fof(f1136,plain,(
% 0.21/0.63    r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK0,sK1))))),
% 0.21/0.63    inference(superposition,[],[f92,f118])).
% 0.21/0.63  fof(f118,plain,(
% 0.21/0.63    k2_relat_1(k3_tarski(k2_tarski(sK0,sK1))) = k3_tarski(k2_tarski(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 0.21/0.63    inference(unit_resulting_resolution,[],[f58,f59,f91])).
% 0.21/0.63  fof(f91,plain,(
% 0.21/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X0)) )),
% 0.21/0.63    inference(definition_unfolding,[],[f65,f72,f72])).
% 0.21/0.63  fof(f65,plain,(
% 0.21/0.63    ( ! [X0,X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f29])).
% 0.21/0.63  fof(f29,plain,(
% 0.21/0.63    ! [X0] : (! [X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.63    inference(ennf_transformation,[],[f22])).
% 0.21/0.63  fof(f22,axiom,(
% 0.21/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))))),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).
% 0.21/0.63  fof(f1077,plain,(
% 0.21/0.63    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 0.21/0.63    inference(unit_resulting_resolution,[],[f818,f1033,f88])).
% 0.21/0.63  fof(f1033,plain,(
% 0.21/0.63    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.21/0.63    inference(backward_demodulation,[],[f908,f999])).
% 0.21/0.63  fof(f999,plain,(
% 0.21/0.63    ( ! [X0] : (k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0) )),
% 0.21/0.63    inference(superposition,[],[f626,f70])).
% 0.21/0.63  fof(f908,plain,(
% 0.21/0.63    r1_tarski(k1_relat_1(sK0),k3_tarski(k2_tarski(k1_xboole_0,k1_relat_1(sK1))))),
% 0.21/0.63    inference(backward_demodulation,[],[f621,f894])).
% 0.21/0.63  fof(f894,plain,(
% 0.21/0.63    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.63    inference(unit_resulting_resolution,[],[f890,f890,f82])).
% 0.21/0.63  fof(f82,plain,(
% 0.21/0.63    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | k1_relat_1(X0) = X1 | r2_hidden(sK4(X0,X1),X1)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f57])).
% 0.21/0.63  fof(f57,plain,(
% 0.21/0.63    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f53,f56,f55,f54])).
% 0.21/0.63  fof(f54,plain,(
% 0.21/0.63    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK4(X0,X1),X3),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.63    introduced(choice_axiom,[])).
% 0.21/0.63  fof(f55,plain,(
% 0.21/0.63    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))),
% 0.21/0.63    introduced(choice_axiom,[])).
% 0.21/0.63  fof(f56,plain,(
% 0.21/0.63    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0))),
% 0.21/0.63    introduced(choice_axiom,[])).
% 0.21/0.63  fof(f53,plain,(
% 0.21/0.63    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.63    inference(rectify,[],[f52])).
% 0.21/0.63  fof(f52,plain,(
% 0.21/0.63    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.63    inference(nnf_transformation,[],[f19])).
% 0.21/0.63  fof(f19,axiom,(
% 0.21/0.63    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.63  fof(f890,plain,(
% 0.21/0.63    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 0.21/0.63    inference(subsumption_resolution,[],[f889,f62])).
% 0.21/0.63  fof(f62,plain,(
% 0.21/0.63    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f12])).
% 0.21/0.63  fof(f12,axiom,(
% 0.21/0.63    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.63  fof(f889,plain,(
% 0.21/0.63    ( ! [X2,X1] : (~r2_hidden(X2,k1_xboole_0) | ~r1_xboole_0(X1,k1_xboole_0)) )),
% 0.21/0.63    inference(superposition,[],[f93,f513])).
% 0.21/0.63  fof(f513,plain,(
% 0.21/0.63    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 0.21/0.63    inference(superposition,[],[f239,f70])).
% 0.21/0.63  fof(f239,plain,(
% 0.21/0.63    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))) )),
% 0.21/0.63    inference(backward_demodulation,[],[f212,f197])).
% 0.21/0.63  fof(f212,plain,(
% 0.21/0.63    ( ! [X0] : (k6_subset_1(sK0,sK1) = k1_setfam_1(k2_tarski(k6_subset_1(sK0,sK1),X0))) )),
% 0.21/0.63    inference(unit_resulting_resolution,[],[f161,f95])).
% 0.21/0.63  fof(f93,plain,(
% 0.21/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.63    inference(definition_unfolding,[],[f74,f71])).
% 0.21/0.63  fof(f74,plain,(
% 0.21/0.63    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.63    inference(cnf_transformation,[],[f49])).
% 0.21/0.63  fof(f49,plain,(
% 0.21/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f48])).
% 0.21/0.63  fof(f48,plain,(
% 0.21/0.63    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.63    introduced(choice_axiom,[])).
% 0.21/0.63  fof(f32,plain,(
% 0.21/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.63    inference(ennf_transformation,[],[f25])).
% 0.21/0.63  fof(f25,plain,(
% 0.21/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.63    inference(rectify,[],[f2])).
% 0.21/0.63  fof(f2,axiom,(
% 0.21/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.63  fof(f621,plain,(
% 0.21/0.63    r1_tarski(k1_relat_1(sK0),k3_tarski(k2_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(sK1))))),
% 0.21/0.63    inference(forward_demodulation,[],[f593,f70])).
% 0.21/0.63  fof(f593,plain,(
% 0.21/0.63    r1_tarski(k1_relat_1(sK0),k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(k1_xboole_0))))),
% 0.21/0.63    inference(unit_resulting_resolution,[],[f236,f98])).
% 0.21/0.63  fof(f98,plain,(
% 0.21/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 0.21/0.63    inference(definition_unfolding,[],[f86,f72,f69])).
% 0.21/0.63  fof(f86,plain,(
% 0.21/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f37])).
% 0.21/0.63  fof(f37,plain,(
% 0.21/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.63    inference(ennf_transformation,[],[f11])).
% 0.21/0.63  fof(f11,axiom,(
% 0.21/0.63    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.21/0.63  fof(f236,plain,(
% 0.21/0.63    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k1_xboole_0))),
% 0.21/0.63    inference(backward_demodulation,[],[f114,f197])).
% 0.21/0.63  fof(f114,plain,(
% 0.21/0.63    r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))),
% 0.21/0.63    inference(unit_resulting_resolution,[],[f58,f59,f66])).
% 0.21/0.63  fof(f66,plain,(
% 0.21/0.63    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.63    inference(cnf_transformation,[],[f30])).
% 0.21/0.63  fof(f30,plain,(
% 0.21/0.63    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.63    inference(ennf_transformation,[],[f21])).
% 0.21/0.63  fof(f21,axiom,(
% 0.21/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 0.21/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).
% 0.21/0.63  fof(f818,plain,(
% 0.21/0.63    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1))),
% 0.21/0.63    inference(superposition,[],[f92,f120])).
% 0.21/0.63  % SZS output end Proof for theBenchmark
% 0.21/0.63  % (981)------------------------------
% 0.21/0.63  % (981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.63  % (981)Termination reason: Refutation
% 0.21/0.63  
% 0.21/0.63  % (981)Memory used [KB]: 6908
% 0.21/0.63  % (981)Time elapsed: 0.227 s
% 0.21/0.63  % (981)------------------------------
% 0.21/0.63  % (981)------------------------------
% 0.21/0.65  % (961)Success in time 0.29 s
%------------------------------------------------------------------------------
