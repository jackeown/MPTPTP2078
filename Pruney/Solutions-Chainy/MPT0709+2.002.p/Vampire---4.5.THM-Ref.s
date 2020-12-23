%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:35 EST 2020

% Result     : Theorem 3.09s
% Output     : Refutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 273 expanded)
%              Number of leaves         :   18 (  75 expanded)
%              Depth                    :   20
%              Number of atoms          :  228 ( 594 expanded)
%              Number of equality atoms :   65 ( 225 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3055,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3029,f51])).

fof(f51,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f3029,plain,(
    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f3028,f49])).

fof(f49,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f3028,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 ) ),
    inference(global_subsumption,[],[f187,f2249])).

fof(f2249,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    inference(subsumption_resolution,[],[f2236,f307])).

fof(f307,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f303])).

fof(f303,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f283,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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

fof(f283,plain,(
    ! [X8,X7] :
      ( r2_hidden(sK4(k10_relat_1(sK1,X7),X8),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,X7),X8) ) ),
    inference(resolution,[],[f279,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f279,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(sK1,X1))
      | r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f278,f47])).

fof(f47,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f278,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f97,f48])).

fof(f48,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(f2236,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ) ),
    inference(resolution,[],[f1184,f1921])).

fof(f1921,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(superposition,[],[f101,f1901])).

fof(f1901,plain,(
    ! [X1] : k9_relat_1(sK1,k10_relat_1(sK1,X1)) = k10_relat_1(k6_relat_1(X1),k2_relat_1(sK1)) ),
    inference(superposition,[],[f1710,f514])).

fof(f514,plain,(
    ! [X6,X7] : k2_relat_1(k5_relat_1(k6_relat_1(X7),k6_relat_1(X6))) = k10_relat_1(k6_relat_1(X7),X6) ),
    inference(backward_demodulation,[],[f359,f507])).

fof(f507,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(resolution,[],[f135,f53])).

fof(f53,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f135,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X2) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) ) ),
    inference(forward_demodulation,[],[f134,f55])).

fof(f55,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f134,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,k1_relat_1(k6_relat_1(X2))) ) ),
    inference(resolution,[],[f58,f53])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f359,plain,(
    ! [X6,X7] : k2_relat_1(k5_relat_1(k6_relat_1(X7),k6_relat_1(X6))) = k1_relat_1(k5_relat_1(k6_relat_1(X7),k6_relat_1(X6))) ),
    inference(forward_demodulation,[],[f344,f343])).

fof(f343,plain,(
    ! [X4,X5] : k1_setfam_1(k3_enumset1(X4,X4,X4,X4,X5)) = k1_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X4))) ),
    inference(superposition,[],[f55,f93])).

fof(f93,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f68,f91])).

fof(f91,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f67,f90])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f85,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f85,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f67,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f68,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f344,plain,(
    ! [X6,X7] : k1_setfam_1(k3_enumset1(X6,X6,X6,X6,X7)) = k2_relat_1(k5_relat_1(k6_relat_1(X7),k6_relat_1(X6))) ),
    inference(superposition,[],[f56,f93])).

fof(f56,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f1710,plain,(
    ! [X3] : k9_relat_1(sK1,k10_relat_1(sK1,X3)) = k2_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(k2_relat_1(sK1)))) ),
    inference(superposition,[],[f56,f955])).

fof(f955,plain,(
    ! [X7] : k5_relat_1(k6_relat_1(X7),k6_relat_1(k2_relat_1(sK1))) = k6_relat_1(k9_relat_1(sK1,k10_relat_1(sK1,X7))) ),
    inference(superposition,[],[f512,f946])).

fof(f946,plain,(
    ! [X0] : k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X0) ),
    inference(forward_demodulation,[],[f945,f109])).

fof(f109,plain,(
    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) ),
    inference(resolution,[],[f57,f47])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f945,plain,(
    ! [X0] : k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k10_relat_1(k6_relat_1(k9_relat_1(sK1,k1_relat_1(sK1))),X0) ),
    inference(subsumption_resolution,[],[f944,f47])).

fof(f944,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k10_relat_1(k6_relat_1(k9_relat_1(sK1,k1_relat_1(sK1))),X0) ) ),
    inference(resolution,[],[f527,f48])).

fof(f527,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k10_relat_1(k6_relat_1(k9_relat_1(X1,k1_relat_1(X1))),X0) ) ),
    inference(backward_demodulation,[],[f358,f507])).

fof(f358,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_relat_1(k5_relat_1(k6_relat_1(k9_relat_1(X1,k1_relat_1(X1))),k6_relat_1(X0)))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(backward_demodulation,[],[f94,f343])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) ) ),
    inference(definition_unfolding,[],[f77,f91])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(f512,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(backward_demodulation,[],[f356,f507])).

fof(f356,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) ),
    inference(backward_demodulation,[],[f339,f343])).

fof(f339,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X0))) ),
    inference(superposition,[],[f93,f92])).

fof(f92,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f65,f90,f90])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f101,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f100,f53])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f72,f55])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f1184,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ r1_tarski(X0,k1_relat_1(sK1))
      | r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f1183,f50])).

fof(f50,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f1183,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ r1_tarski(X0,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f1182,f47])).

fof(f1182,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ r1_tarski(X0,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f87,f48])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v2_funct_1(X2)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

fof(f187,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK1))
      | ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1)
      | k10_relat_1(sK1,k9_relat_1(sK1,X1)) = X1 ) ),
    inference(resolution,[],[f183,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f183,plain,(
    ! [X0] :
      ( r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f73,f47])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : run_vampire %s %d
% 0.10/0.31  % Computer   : n023.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 10:17:06 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.16/0.47  % (16449)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.16/0.47  % (16457)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.16/0.48  % (16447)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.16/0.48  % (16449)Refutation not found, incomplete strategy% (16449)------------------------------
% 0.16/0.48  % (16449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.48  % (16453)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.16/0.48  % (16465)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.16/0.48  % (16449)Termination reason: Refutation not found, incomplete strategy
% 0.16/0.48  
% 0.16/0.48  % (16449)Memory used [KB]: 6268
% 0.16/0.48  % (16449)Time elapsed: 0.096 s
% 0.16/0.48  % (16449)------------------------------
% 0.16/0.48  % (16449)------------------------------
% 0.16/0.49  % (16467)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.16/0.49  % (16458)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.16/0.49  % (16467)Refutation not found, incomplete strategy% (16467)------------------------------
% 0.16/0.49  % (16467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.49  % (16467)Termination reason: Refutation not found, incomplete strategy
% 0.16/0.49  
% 0.16/0.49  % (16467)Memory used [KB]: 10746
% 0.16/0.49  % (16467)Time elapsed: 0.084 s
% 0.16/0.49  % (16467)------------------------------
% 0.16/0.49  % (16467)------------------------------
% 0.16/0.50  % (16450)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.16/0.50  % (16459)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.16/0.50  % (16445)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.16/0.50  % (16446)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.16/0.51  % (16471)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.16/0.51  % (16451)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.16/0.51  % (16468)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.16/0.51  % (16448)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.16/0.51  % (16462)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.16/0.51  % (16462)Refutation not found, incomplete strategy% (16462)------------------------------
% 0.16/0.51  % (16462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.51  % (16462)Termination reason: Refutation not found, incomplete strategy
% 0.16/0.51  
% 0.16/0.51  % (16462)Memory used [KB]: 10618
% 0.16/0.51  % (16462)Time elapsed: 0.137 s
% 0.16/0.51  % (16462)------------------------------
% 0.16/0.51  % (16462)------------------------------
% 0.16/0.51  % (16454)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.16/0.51  % (16460)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.16/0.51  % (16463)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.16/0.52  % (16473)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.16/0.52  % (16470)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.16/0.52  % (16455)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.16/0.52  % (16464)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.16/0.52  % (16466)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.16/0.52  % (16452)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.16/0.52  % (16455)Refutation not found, incomplete strategy% (16455)------------------------------
% 0.16/0.52  % (16455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.52  % (16455)Termination reason: Refutation not found, incomplete strategy
% 0.16/0.52  
% 0.16/0.52  % (16455)Memory used [KB]: 10746
% 0.16/0.52  % (16455)Time elapsed: 0.152 s
% 0.16/0.52  % (16455)------------------------------
% 0.16/0.52  % (16455)------------------------------
% 0.16/0.52  % (16472)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.16/0.53  % (16461)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.16/0.53  % (16456)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.16/0.53  % (16474)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.52/0.54  % (16469)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.69/0.59  % (16475)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.69/0.61  % (16475)Refutation not found, incomplete strategy% (16475)------------------------------
% 1.69/0.61  % (16475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.61  % (16475)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.61  
% 1.69/0.61  % (16475)Memory used [KB]: 6396
% 1.69/0.61  % (16475)Time elapsed: 0.059 s
% 1.69/0.61  % (16475)------------------------------
% 1.69/0.61  % (16475)------------------------------
% 1.69/0.64  % (16477)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.36/0.66  % (16476)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.71/0.70  % (16478)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.71/0.73  % (16480)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 3.09/0.79  % (16450)Time limit reached!
% 3.09/0.79  % (16450)------------------------------
% 3.09/0.79  % (16450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.09/0.79  % (16450)Termination reason: Time limit
% 3.09/0.79  
% 3.09/0.79  % (16450)Memory used [KB]: 8059
% 3.09/0.79  % (16450)Time elapsed: 0.405 s
% 3.09/0.79  % (16450)------------------------------
% 3.09/0.79  % (16450)------------------------------
% 3.09/0.79  % (16451)Refutation found. Thanks to Tanya!
% 3.09/0.79  % SZS status Theorem for theBenchmark
% 3.09/0.79  % SZS output start Proof for theBenchmark
% 3.09/0.79  fof(f3055,plain,(
% 3.09/0.79    $false),
% 3.09/0.79    inference(subsumption_resolution,[],[f3029,f51])).
% 3.09/0.79  fof(f51,plain,(
% 3.09/0.79    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 3.09/0.79    inference(cnf_transformation,[],[f28])).
% 3.09/0.79  fof(f28,plain,(
% 3.09/0.79    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.09/0.79    inference(flattening,[],[f27])).
% 3.09/0.79  fof(f27,plain,(
% 3.09/0.79    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.09/0.79    inference(ennf_transformation,[],[f25])).
% 3.09/0.79  fof(f25,negated_conjecture,(
% 3.09/0.79    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.09/0.79    inference(negated_conjecture,[],[f24])).
% 3.09/0.79  fof(f24,conjecture,(
% 3.09/0.79    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 3.09/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 3.09/0.79  fof(f3029,plain,(
% 3.09/0.79    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 3.09/0.79    inference(resolution,[],[f3028,f49])).
% 3.09/0.79  fof(f49,plain,(
% 3.09/0.79    r1_tarski(sK0,k1_relat_1(sK1))),
% 3.09/0.79    inference(cnf_transformation,[],[f28])).
% 3.51/0.82  fof(f3028,plain,(
% 3.51/0.82    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0) )),
% 3.51/0.82    inference(global_subsumption,[],[f187,f2249])).
% 3.51/0.82  fof(f2249,plain,(
% 3.51/0.82    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) )),
% 3.51/0.82    inference(subsumption_resolution,[],[f2236,f307])).
% 3.51/0.82  fof(f307,plain,(
% 3.51/0.82    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 3.51/0.82    inference(duplicate_literal_removal,[],[f303])).
% 3.51/0.82  fof(f303,plain,(
% 3.51/0.82    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 3.51/0.82    inference(resolution,[],[f283,f84])).
% 3.51/0.82  fof(f84,plain,(
% 3.51/0.82    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 3.51/0.82    inference(cnf_transformation,[],[f43])).
% 3.51/0.82  fof(f43,plain,(
% 3.51/0.82    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.51/0.82    inference(ennf_transformation,[],[f1])).
% 3.51/0.82  fof(f1,axiom,(
% 3.51/0.82    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.51/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 3.51/0.82  fof(f283,plain,(
% 3.51/0.82    ( ! [X8,X7] : (r2_hidden(sK4(k10_relat_1(sK1,X7),X8),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,X7),X8)) )),
% 3.51/0.82    inference(resolution,[],[f279,f83])).
% 3.51/0.82  fof(f83,plain,(
% 3.51/0.82    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.51/0.82    inference(cnf_transformation,[],[f43])).
% 3.51/0.82  fof(f279,plain,(
% 3.51/0.82    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK1,X1)) | r2_hidden(X0,k1_relat_1(sK1))) )),
% 3.51/0.82    inference(subsumption_resolution,[],[f278,f47])).
% 3.51/0.82  fof(f47,plain,(
% 3.51/0.82    v1_relat_1(sK1)),
% 3.51/0.82    inference(cnf_transformation,[],[f28])).
% 3.51/0.82  fof(f278,plain,(
% 3.51/0.82    ( ! [X0,X1] : (~v1_relat_1(sK1) | r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) )),
% 3.51/0.82    inference(resolution,[],[f97,f48])).
% 3.51/0.82  fof(f48,plain,(
% 3.51/0.82    v1_funct_1(sK1)),
% 3.51/0.82    inference(cnf_transformation,[],[f28])).
% 3.51/0.82  fof(f97,plain,(
% 3.51/0.82    ( ! [X0,X3,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 3.51/0.82    inference(equality_resolution,[],[f62])).
% 3.51/0.82  fof(f62,plain,(
% 3.51/0.82    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 3.51/0.82    inference(cnf_transformation,[],[f32])).
% 3.51/0.82  fof(f32,plain,(
% 3.51/0.82    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.51/0.82    inference(flattening,[],[f31])).
% 3.51/0.82  fof(f31,plain,(
% 3.51/0.82    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.51/0.82    inference(ennf_transformation,[],[f17])).
% 3.51/0.82  fof(f17,axiom,(
% 3.51/0.82    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.51/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).
% 3.51/0.82  fof(f2236,plain,(
% 3.51/0.82    ( ! [X0] : (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) )),
% 3.51/0.82    inference(resolution,[],[f1184,f1921])).
% 3.51/0.82  fof(f1921,plain,(
% 3.51/0.82    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 3.51/0.82    inference(superposition,[],[f101,f1901])).
% 3.51/0.82  fof(f1901,plain,(
% 3.51/0.82    ( ! [X1] : (k9_relat_1(sK1,k10_relat_1(sK1,X1)) = k10_relat_1(k6_relat_1(X1),k2_relat_1(sK1))) )),
% 3.51/0.82    inference(superposition,[],[f1710,f514])).
% 3.51/0.82  fof(f514,plain,(
% 3.51/0.82    ( ! [X6,X7] : (k2_relat_1(k5_relat_1(k6_relat_1(X7),k6_relat_1(X6))) = k10_relat_1(k6_relat_1(X7),X6)) )),
% 3.51/0.82    inference(backward_demodulation,[],[f359,f507])).
% 3.51/0.82  fof(f507,plain,(
% 3.51/0.82    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) )),
% 3.51/0.82    inference(resolution,[],[f135,f53])).
% 3.51/0.82  fof(f53,plain,(
% 3.51/0.82    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.51/0.82    inference(cnf_transformation,[],[f18])).
% 3.51/0.82  fof(f18,axiom,(
% 3.51/0.82    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.51/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 3.51/0.82  fof(f135,plain,(
% 3.51/0.82    ( ! [X2,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X2) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))) )),
% 3.51/0.82    inference(forward_demodulation,[],[f134,f55])).
% 3.51/0.82  fof(f55,plain,(
% 3.51/0.82    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.51/0.82    inference(cnf_transformation,[],[f16])).
% 3.51/0.82  fof(f16,axiom,(
% 3.51/0.82    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.51/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 3.51/0.82  fof(f134,plain,(
% 3.51/0.82    ( ! [X2,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,k1_relat_1(k6_relat_1(X2)))) )),
% 3.51/0.82    inference(resolution,[],[f58,f53])).
% 3.51/0.82  fof(f58,plain,(
% 3.51/0.82    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 3.51/0.82    inference(cnf_transformation,[],[f30])).
% 3.51/0.82  fof(f30,plain,(
% 3.51/0.82    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.51/0.82    inference(ennf_transformation,[],[f15])).
% 3.51/0.82  fof(f15,axiom,(
% 3.51/0.82    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 3.51/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 3.51/0.82  fof(f359,plain,(
% 3.51/0.82    ( ! [X6,X7] : (k2_relat_1(k5_relat_1(k6_relat_1(X7),k6_relat_1(X6))) = k1_relat_1(k5_relat_1(k6_relat_1(X7),k6_relat_1(X6)))) )),
% 3.51/0.82    inference(forward_demodulation,[],[f344,f343])).
% 3.51/0.82  fof(f343,plain,(
% 3.51/0.82    ( ! [X4,X5] : (k1_setfam_1(k3_enumset1(X4,X4,X4,X4,X5)) = k1_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X4)))) )),
% 3.51/0.82    inference(superposition,[],[f55,f93])).
% 3.51/0.82  fof(f93,plain,(
% 3.51/0.82    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 3.51/0.82    inference(definition_unfolding,[],[f68,f91])).
% 3.51/0.82  fof(f91,plain,(
% 3.51/0.82    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.51/0.82    inference(definition_unfolding,[],[f67,f90])).
% 3.51/0.82  fof(f90,plain,(
% 3.51/0.82    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.51/0.82    inference(definition_unfolding,[],[f66,f89])).
% 3.51/0.82  fof(f89,plain,(
% 3.51/0.82    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.51/0.82    inference(definition_unfolding,[],[f85,f88])).
% 3.51/0.82  fof(f88,plain,(
% 3.51/0.82    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.51/0.82    inference(cnf_transformation,[],[f9])).
% 3.51/0.82  fof(f9,axiom,(
% 3.51/0.82    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.51/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 3.51/0.82  fof(f85,plain,(
% 3.51/0.82    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.51/0.82    inference(cnf_transformation,[],[f8])).
% 3.51/0.82  fof(f8,axiom,(
% 3.51/0.82    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.51/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 3.51/0.82  fof(f66,plain,(
% 3.51/0.82    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.51/0.82    inference(cnf_transformation,[],[f7])).
% 3.51/0.82  fof(f7,axiom,(
% 3.51/0.82    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.51/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.51/0.82  fof(f67,plain,(
% 3.51/0.82    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.51/0.82    inference(cnf_transformation,[],[f10])).
% 3.51/0.82  fof(f10,axiom,(
% 3.51/0.82    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.51/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.51/0.82  fof(f68,plain,(
% 3.51/0.82    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 3.51/0.82    inference(cnf_transformation,[],[f23])).
% 3.51/0.82  fof(f23,axiom,(
% 3.51/0.82    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.51/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 3.51/0.82  fof(f344,plain,(
% 3.51/0.82    ( ! [X6,X7] : (k1_setfam_1(k3_enumset1(X6,X6,X6,X6,X7)) = k2_relat_1(k5_relat_1(k6_relat_1(X7),k6_relat_1(X6)))) )),
% 3.51/0.82    inference(superposition,[],[f56,f93])).
% 3.51/0.82  fof(f56,plain,(
% 3.51/0.82    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.51/0.82    inference(cnf_transformation,[],[f16])).
% 3.51/0.82  fof(f1710,plain,(
% 3.51/0.82    ( ! [X3] : (k9_relat_1(sK1,k10_relat_1(sK1,X3)) = k2_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(k2_relat_1(sK1))))) )),
% 3.51/0.82    inference(superposition,[],[f56,f955])).
% 3.51/0.82  fof(f955,plain,(
% 3.51/0.82    ( ! [X7] : (k5_relat_1(k6_relat_1(X7),k6_relat_1(k2_relat_1(sK1))) = k6_relat_1(k9_relat_1(sK1,k10_relat_1(sK1,X7)))) )),
% 3.51/0.82    inference(superposition,[],[f512,f946])).
% 3.51/0.82  fof(f946,plain,(
% 3.51/0.82    ( ! [X0] : (k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X0)) )),
% 3.51/0.82    inference(forward_demodulation,[],[f945,f109])).
% 3.51/0.82  fof(f109,plain,(
% 3.51/0.82    k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1)),
% 3.51/0.82    inference(resolution,[],[f57,f47])).
% 3.51/0.82  fof(f57,plain,(
% 3.51/0.82    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 3.51/0.82    inference(cnf_transformation,[],[f29])).
% 3.51/0.82  fof(f29,plain,(
% 3.51/0.82    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.51/0.82    inference(ennf_transformation,[],[f11])).
% 3.51/0.82  fof(f11,axiom,(
% 3.51/0.82    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.51/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 3.51/0.82  fof(f945,plain,(
% 3.51/0.82    ( ! [X0] : (k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k10_relat_1(k6_relat_1(k9_relat_1(sK1,k1_relat_1(sK1))),X0)) )),
% 3.51/0.82    inference(subsumption_resolution,[],[f944,f47])).
% 3.51/0.82  fof(f944,plain,(
% 3.51/0.82    ( ! [X0] : (~v1_relat_1(sK1) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k10_relat_1(k6_relat_1(k9_relat_1(sK1,k1_relat_1(sK1))),X0)) )),
% 3.51/0.82    inference(resolution,[],[f527,f48])).
% 3.51/0.82  fof(f527,plain,(
% 3.51/0.82    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k10_relat_1(k6_relat_1(k9_relat_1(X1,k1_relat_1(X1))),X0)) )),
% 3.51/0.82    inference(backward_demodulation,[],[f358,f507])).
% 3.51/0.82  fof(f358,plain,(
% 3.51/0.82    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_relat_1(k5_relat_1(k6_relat_1(k9_relat_1(X1,k1_relat_1(X1))),k6_relat_1(X0))) | ~v1_relat_1(X1) | ~v1_funct_1(X1)) )),
% 3.51/0.82    inference(backward_demodulation,[],[f94,f343])).
% 3.51/0.82  fof(f94,plain,(
% 3.51/0.82    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1))))) )),
% 3.51/0.82    inference(definition_unfolding,[],[f77,f91])).
% 3.51/0.82  fof(f77,plain,(
% 3.51/0.82    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))) )),
% 3.51/0.82    inference(cnf_transformation,[],[f40])).
% 3.51/0.82  fof(f40,plain,(
% 3.51/0.82    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.51/0.82    inference(flattening,[],[f39])).
% 3.51/0.82  fof(f39,plain,(
% 3.51/0.82    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.51/0.82    inference(ennf_transformation,[],[f21])).
% 3.51/0.82  fof(f21,axiom,(
% 3.51/0.82    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 3.51/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
% 3.51/0.82  fof(f512,plain,(
% 3.51/0.82    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k10_relat_1(k6_relat_1(X0),X1))) )),
% 3.51/0.82    inference(backward_demodulation,[],[f356,f507])).
% 3.51/0.82  fof(f356,plain,(
% 3.51/0.82    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))))) )),
% 3.51/0.82    inference(backward_demodulation,[],[f339,f343])).
% 3.51/0.82  fof(f339,plain,(
% 3.51/0.82    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X0)))) )),
% 3.51/0.82    inference(superposition,[],[f93,f92])).
% 3.51/0.82  fof(f92,plain,(
% 3.51/0.82    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 3.51/0.82    inference(definition_unfolding,[],[f65,f90,f90])).
% 3.51/0.82  fof(f65,plain,(
% 3.51/0.82    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.51/0.82    inference(cnf_transformation,[],[f6])).
% 3.51/0.82  fof(f6,axiom,(
% 3.51/0.82    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.51/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.51/0.82  fof(f101,plain,(
% 3.51/0.82    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 3.51/0.82    inference(subsumption_resolution,[],[f100,f53])).
% 3.51/0.82  fof(f100,plain,(
% 3.51/0.82    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 3.51/0.82    inference(superposition,[],[f72,f55])).
% 3.51/0.82  fof(f72,plain,(
% 3.51/0.82    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.51/0.82    inference(cnf_transformation,[],[f34])).
% 3.51/0.82  fof(f34,plain,(
% 3.51/0.82    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.51/0.82    inference(ennf_transformation,[],[f13])).
% 3.51/0.82  fof(f13,axiom,(
% 3.51/0.82    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 3.51/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 3.51/0.82  fof(f1184,plain,(
% 3.51/0.82    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~r1_tarski(X0,k1_relat_1(sK1)) | r1_tarski(X0,X1)) )),
% 3.51/0.82    inference(subsumption_resolution,[],[f1183,f50])).
% 3.51/0.82  fof(f50,plain,(
% 3.51/0.82    v2_funct_1(sK1)),
% 3.51/0.82    inference(cnf_transformation,[],[f28])).
% 3.51/0.82  fof(f1183,plain,(
% 3.51/0.82    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~r1_tarski(X0,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | r1_tarski(X0,X1)) )),
% 3.51/0.82    inference(subsumption_resolution,[],[f1182,f47])).
% 3.51/0.82  fof(f1182,plain,(
% 3.51/0.82    ( ! [X0,X1] : (~v1_relat_1(sK1) | ~r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~r1_tarski(X0,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | r1_tarski(X0,X1)) )),
% 3.51/0.82    inference(resolution,[],[f87,f48])).
% 3.51/0.82  fof(f87,plain,(
% 3.51/0.82    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v2_funct_1(X2) | r1_tarski(X0,X1)) )),
% 3.51/0.82    inference(cnf_transformation,[],[f46])).
% 3.51/0.82  fof(f46,plain,(
% 3.51/0.82    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.51/0.82    inference(flattening,[],[f45])).
% 3.51/0.82  fof(f45,plain,(
% 3.51/0.82    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.51/0.82    inference(ennf_transformation,[],[f22])).
% 3.51/0.82  fof(f22,axiom,(
% 3.51/0.82    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 3.51/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).
% 3.51/0.82  fof(f187,plain,(
% 3.51/0.82    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK1)) | ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X1)),X1) | k10_relat_1(sK1,k9_relat_1(sK1,X1)) = X1) )),
% 3.51/0.82    inference(resolution,[],[f183,f81])).
% 3.51/0.82  fof(f81,plain,(
% 3.51/0.82    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 3.51/0.82    inference(cnf_transformation,[],[f3])).
% 3.51/0.82  fof(f3,axiom,(
% 3.51/0.82    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.51/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.51/0.82  fof(f183,plain,(
% 3.51/0.82    ( ! [X0] : (r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) | ~r1_tarski(X0,k1_relat_1(sK1))) )),
% 3.51/0.82    inference(resolution,[],[f73,f47])).
% 3.51/0.82  fof(f73,plain,(
% 3.51/0.82    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 3.51/0.82    inference(cnf_transformation,[],[f36])).
% 3.51/0.82  fof(f36,plain,(
% 3.51/0.82    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.51/0.82    inference(flattening,[],[f35])).
% 3.51/0.82  fof(f35,plain,(
% 3.51/0.82    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.51/0.82    inference(ennf_transformation,[],[f19])).
% 3.51/0.82  fof(f19,axiom,(
% 3.51/0.82    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.51/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 3.51/0.82  % SZS output end Proof for theBenchmark
% 3.51/0.82  % (16451)------------------------------
% 3.51/0.82  % (16451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.51/0.82  % (16451)Termination reason: Refutation
% 3.51/0.82  
% 3.51/0.82  % (16451)Memory used [KB]: 9083
% 3.51/0.82  % (16451)Time elapsed: 0.375 s
% 3.51/0.82  % (16451)------------------------------
% 3.51/0.82  % (16451)------------------------------
% 3.51/0.82  % (16442)Success in time 0.49 s
%------------------------------------------------------------------------------
