%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:18 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 127 expanded)
%              Number of leaves         :   18 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  192 ( 307 expanded)
%              Number of equality atoms :   57 (  93 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1177,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f212,f110,f450,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f450,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f446,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f446,plain,
    ( ~ r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2))
    | r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2))) ),
    inference(resolution,[],[f206,f148])).

fof(f148,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X4)
      | ~ r1_tarski(X3,X2)
      | r1_tarski(X3,k3_xboole_0(X4,X2)) ) ),
    inference(backward_demodulation,[],[f97,f145])).

fof(f145,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),X2) = k3_xboole_0(X2,X1) ),
    inference(forward_demodulation,[],[f144,f83])).

fof(f83,plain,(
    ! [X2,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(X1,X2) ),
    inference(forward_demodulation,[],[f82,f44])).

fof(f44,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f82,plain,(
    ! [X2,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(k1_relat_1(k6_relat_1(X1)),X2) ),
    inference(resolution,[],[f55,f42])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f144,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(forward_demodulation,[],[f143,f80])).

fof(f80,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f54,f42])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f143,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(resolution,[],[f90,f42])).

fof(f90,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X2) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) ) ),
    inference(forward_demodulation,[],[f89,f44])).

fof(f89,plain,(
    ! [X2,X1] :
      ( k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,k1_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f47,f42])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f97,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | ~ r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X4)
      | r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4)) ) ),
    inference(forward_demodulation,[],[f96,f44])).

fof(f96,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X4)
      | ~ r1_tarski(X3,k1_relat_1(k6_relat_1(X2)))
      | r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4)) ) ),
    inference(subsumption_resolution,[],[f94,f42])).

fof(f94,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X4)
      | ~ r1_tarski(X3,k1_relat_1(k6_relat_1(X2)))
      | r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(resolution,[],[f61,f43])).

fof(f43,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(f206,plain,(
    r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1) ),
    inference(resolution,[],[f135,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k10_relat_1(sK0,sK2))
      | r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f62,f40])).

fof(f40,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f135,plain,(
    ! [X0] : r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X0) ),
    inference(superposition,[],[f87,f70])).

fof(f70,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f69,f44])).

fof(f69,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f68,f45])).

fof(f45,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f46,f42])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f87,plain,(
    ! [X2,X1] : r1_tarski(k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)),X2) ),
    inference(subsumption_resolution,[],[f85,f42])).

fof(f85,plain,(
    ! [X2,X1] :
      ( r1_tarski(k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)),X2)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(resolution,[],[f56,f43])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f110,plain,(
    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    inference(superposition,[],[f41,f91])).

fof(f91,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK0,X1)) ),
    inference(resolution,[],[f60,f38])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f41,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f212,plain,(
    ! [X4,X5] : r1_tarski(k3_xboole_0(X5,X4),X4) ),
    inference(superposition,[],[f72,f121])).

fof(f121,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f65,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f51,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f48,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:48:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (3593)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.48  % (3609)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (3587)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (3584)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (3585)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (3606)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (3581)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (3581)Refutation not found, incomplete strategy% (3581)------------------------------
% 0.22/0.54  % (3581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (3581)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (3581)Memory used [KB]: 1663
% 0.22/0.54  % (3581)Time elapsed: 0.122 s
% 0.22/0.54  % (3581)------------------------------
% 0.22/0.54  % (3581)------------------------------
% 0.22/0.54  % (3607)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (3598)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (3580)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (3594)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (3583)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (3582)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (3595)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (3605)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (3601)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (3599)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (3600)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (3608)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (3589)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (3603)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (3586)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (3597)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (3602)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.56  % (3592)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (3588)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (3591)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (3590)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (3604)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.55/0.57  % (3596)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 2.14/0.67  % (3587)Refutation found. Thanks to Tanya!
% 2.14/0.67  % SZS status Theorem for theBenchmark
% 2.14/0.67  % (3580)Refutation not found, incomplete strategy% (3580)------------------------------
% 2.14/0.67  % (3580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.67  % (3580)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.67  
% 2.14/0.67  % (3580)Memory used [KB]: 1663
% 2.14/0.67  % (3580)Time elapsed: 0.241 s
% 2.14/0.67  % (3580)------------------------------
% 2.14/0.67  % (3580)------------------------------
% 2.14/0.67  % (3612)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.14/0.68  % SZS output start Proof for theBenchmark
% 2.14/0.68  fof(f1177,plain,(
% 2.14/0.68    $false),
% 2.14/0.68    inference(unit_resulting_resolution,[],[f212,f110,f450,f59])).
% 2.14/0.68  fof(f59,plain,(
% 2.14/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f37])).
% 2.14/0.68  fof(f37,plain,(
% 2.14/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/0.68    inference(flattening,[],[f36])).
% 2.14/0.68  fof(f36,plain,(
% 2.14/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/0.68    inference(nnf_transformation,[],[f1])).
% 2.14/0.68  fof(f1,axiom,(
% 2.14/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.14/0.68  fof(f450,plain,(
% 2.14/0.68    r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))),
% 2.14/0.68    inference(subsumption_resolution,[],[f446,f63])).
% 2.14/0.68  fof(f63,plain,(
% 2.14/0.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.14/0.68    inference(equality_resolution,[],[f58])).
% 2.14/0.68  fof(f58,plain,(
% 2.14/0.68    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.14/0.68    inference(cnf_transformation,[],[f37])).
% 2.14/0.68  fof(f446,plain,(
% 2.14/0.68    ~r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)) | r1_tarski(k10_relat_1(sK0,sK2),k3_xboole_0(sK1,k10_relat_1(sK0,sK2)))),
% 2.14/0.68    inference(resolution,[],[f206,f148])).
% 2.14/0.68  fof(f148,plain,(
% 2.14/0.68    ( ! [X4,X2,X3] : (~r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X4) | ~r1_tarski(X3,X2) | r1_tarski(X3,k3_xboole_0(X4,X2))) )),
% 2.14/0.68    inference(backward_demodulation,[],[f97,f145])).
% 2.14/0.68  fof(f145,plain,(
% 2.14/0.68    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),X2) = k3_xboole_0(X2,X1)) )),
% 2.14/0.68    inference(forward_demodulation,[],[f144,f83])).
% 2.14/0.68  fof(f83,plain,(
% 2.14/0.68    ( ! [X2,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(X1,X2)) )),
% 2.14/0.68    inference(forward_demodulation,[],[f82,f44])).
% 2.14/0.68  fof(f44,plain,(
% 2.14/0.68    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.14/0.68    inference(cnf_transformation,[],[f11])).
% 2.14/0.68  fof(f11,axiom,(
% 2.14/0.68    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.14/0.68  fof(f82,plain,(
% 2.14/0.68    ( ! [X2,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(k1_relat_1(k6_relat_1(X1)),X2)) )),
% 2.14/0.68    inference(resolution,[],[f55,f42])).
% 2.14/0.68  fof(f42,plain,(
% 2.14/0.68    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.14/0.68    inference(cnf_transformation,[],[f14])).
% 2.14/0.68  fof(f14,axiom,(
% 2.14/0.68    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.14/0.68  fof(f55,plain,(
% 2.14/0.68    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f25])).
% 2.14/0.68  fof(f25,plain,(
% 2.14/0.68    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.14/0.68    inference(ennf_transformation,[],[f12])).
% 2.14/0.68  fof(f12,axiom,(
% 2.14/0.68    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 2.14/0.68  fof(f144,plain,(
% 2.14/0.68    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) )),
% 2.14/0.68    inference(forward_demodulation,[],[f143,f80])).
% 2.14/0.68  fof(f80,plain,(
% 2.14/0.68    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 2.14/0.68    inference(resolution,[],[f54,f42])).
% 2.14/0.68  fof(f54,plain,(
% 2.14/0.68    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f24])).
% 2.14/0.68  fof(f24,plain,(
% 2.14/0.68    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.14/0.68    inference(ennf_transformation,[],[f13])).
% 2.14/0.68  fof(f13,axiom,(
% 2.14/0.68    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 2.14/0.68  fof(f143,plain,(
% 2.14/0.68    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) )),
% 2.14/0.68    inference(resolution,[],[f90,f42])).
% 2.14/0.68  fof(f90,plain,(
% 2.14/0.68    ( ! [X2,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X2) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))) )),
% 2.14/0.68    inference(forward_demodulation,[],[f89,f44])).
% 2.14/0.68  fof(f89,plain,(
% 2.14/0.68    ( ! [X2,X1] : (k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,k1_relat_1(k6_relat_1(X2))) | ~v1_relat_1(X1)) )),
% 2.14/0.68    inference(resolution,[],[f47,f42])).
% 2.14/0.68  fof(f47,plain,(
% 2.14/0.68    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f23])).
% 2.14/0.68  fof(f23,plain,(
% 2.14/0.68    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.14/0.68    inference(ennf_transformation,[],[f10])).
% 2.14/0.68  fof(f10,axiom,(
% 2.14/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 2.14/0.68  fof(f97,plain,(
% 2.14/0.68    ( ! [X4,X2,X3] : (~r1_tarski(X3,X2) | ~r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X4) | r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4))) )),
% 2.14/0.68    inference(forward_demodulation,[],[f96,f44])).
% 2.14/0.68  fof(f96,plain,(
% 2.14/0.68    ( ! [X4,X2,X3] : (~r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X4) | ~r1_tarski(X3,k1_relat_1(k6_relat_1(X2))) | r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4))) )),
% 2.14/0.68    inference(subsumption_resolution,[],[f94,f42])).
% 2.14/0.68  fof(f94,plain,(
% 2.14/0.68    ( ! [X4,X2,X3] : (~r1_tarski(k9_relat_1(k6_relat_1(X2),X3),X4) | ~r1_tarski(X3,k1_relat_1(k6_relat_1(X2))) | r1_tarski(X3,k10_relat_1(k6_relat_1(X2),X4)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 2.14/0.68    inference(resolution,[],[f61,f43])).
% 2.14/0.68  fof(f43,plain,(
% 2.14/0.68    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.14/0.68    inference(cnf_transformation,[],[f14])).
% 2.14/0.68  fof(f61,plain,(
% 2.14/0.68    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f30])).
% 2.14/0.68  fof(f30,plain,(
% 2.14/0.68    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.14/0.68    inference(flattening,[],[f29])).
% 2.14/0.68  fof(f29,plain,(
% 2.14/0.68    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.14/0.68    inference(ennf_transformation,[],[f17])).
% 2.14/0.68  fof(f17,axiom,(
% 2.14/0.68    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 2.14/0.68  fof(f206,plain,(
% 2.14/0.68    r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1)),
% 2.14/0.68    inference(resolution,[],[f135,f76])).
% 2.14/0.68  fof(f76,plain,(
% 2.14/0.68    ( ! [X0] : (~r1_tarski(X0,k10_relat_1(sK0,sK2)) | r1_tarski(X0,sK1)) )),
% 2.14/0.68    inference(resolution,[],[f62,f40])).
% 2.14/0.68  fof(f40,plain,(
% 2.14/0.68    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 2.14/0.68    inference(cnf_transformation,[],[f35])).
% 2.14/0.68  fof(f35,plain,(
% 2.14/0.68    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 2.14/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f34,f33])).
% 2.14/0.68  fof(f33,plain,(
% 2.14/0.68    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 2.14/0.68    introduced(choice_axiom,[])).
% 2.14/0.68  fof(f34,plain,(
% 2.14/0.68    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 2.14/0.68    introduced(choice_axiom,[])).
% 2.14/0.68  fof(f21,plain,(
% 2.14/0.68    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.14/0.68    inference(flattening,[],[f20])).
% 2.14/0.68  fof(f20,plain,(
% 2.14/0.68    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.14/0.68    inference(ennf_transformation,[],[f19])).
% 2.14/0.68  fof(f19,negated_conjecture,(
% 2.14/0.68    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 2.14/0.68    inference(negated_conjecture,[],[f18])).
% 2.14/0.68  fof(f18,conjecture,(
% 2.14/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).
% 2.14/0.68  fof(f62,plain,(
% 2.14/0.68    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f32])).
% 2.14/0.68  fof(f32,plain,(
% 2.14/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.14/0.68    inference(flattening,[],[f31])).
% 2.14/0.68  fof(f31,plain,(
% 2.14/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.14/0.68    inference(ennf_transformation,[],[f3])).
% 2.14/0.68  fof(f3,axiom,(
% 2.14/0.68    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.14/0.68  fof(f135,plain,(
% 2.14/0.68    ( ! [X0] : (r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X0)) )),
% 2.14/0.68    inference(superposition,[],[f87,f70])).
% 2.14/0.68  fof(f70,plain,(
% 2.14/0.68    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 2.14/0.68    inference(forward_demodulation,[],[f69,f44])).
% 2.14/0.68  fof(f69,plain,(
% 2.14/0.68    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 2.14/0.68    inference(forward_demodulation,[],[f68,f45])).
% 2.14/0.68  fof(f45,plain,(
% 2.14/0.68    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.14/0.68    inference(cnf_transformation,[],[f11])).
% 2.14/0.68  fof(f68,plain,(
% 2.14/0.68    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 2.14/0.68    inference(resolution,[],[f46,f42])).
% 2.14/0.68  fof(f46,plain,(
% 2.14/0.68    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f22])).
% 2.14/0.68  fof(f22,plain,(
% 2.14/0.68    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.14/0.68    inference(ennf_transformation,[],[f9])).
% 2.14/0.68  fof(f9,axiom,(
% 2.14/0.68    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 2.14/0.68  fof(f87,plain,(
% 2.14/0.68    ( ! [X2,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)),X2)) )),
% 2.14/0.68    inference(subsumption_resolution,[],[f85,f42])).
% 2.14/0.68  fof(f85,plain,(
% 2.14/0.68    ( ! [X2,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)),X2) | ~v1_relat_1(k6_relat_1(X1))) )),
% 2.14/0.68    inference(resolution,[],[f56,f43])).
% 2.14/0.68  fof(f56,plain,(
% 2.14/0.68    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f27])).
% 2.14/0.68  fof(f27,plain,(
% 2.14/0.68    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.14/0.68    inference(flattening,[],[f26])).
% 2.14/0.68  fof(f26,plain,(
% 2.14/0.68    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.14/0.68    inference(ennf_transformation,[],[f16])).
% 2.14/0.68  fof(f16,axiom,(
% 2.14/0.68    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 2.14/0.68  fof(f110,plain,(
% 2.14/0.68    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 2.14/0.68    inference(superposition,[],[f41,f91])).
% 2.14/0.68  fof(f91,plain,(
% 2.14/0.68    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK0,X1))) )),
% 2.14/0.68    inference(resolution,[],[f60,f38])).
% 2.14/0.68  fof(f38,plain,(
% 2.14/0.68    v1_relat_1(sK0)),
% 2.14/0.68    inference(cnf_transformation,[],[f35])).
% 2.14/0.68  fof(f60,plain,(
% 2.14/0.68    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 2.14/0.68    inference(cnf_transformation,[],[f28])).
% 2.14/0.68  fof(f28,plain,(
% 2.14/0.68    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 2.14/0.68    inference(ennf_transformation,[],[f15])).
% 2.14/0.68  fof(f15,axiom,(
% 2.14/0.68    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 2.14/0.68  fof(f41,plain,(
% 2.14/0.68    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 2.14/0.68    inference(cnf_transformation,[],[f35])).
% 2.14/0.68  fof(f212,plain,(
% 2.14/0.68    ( ! [X4,X5] : (r1_tarski(k3_xboole_0(X5,X4),X4)) )),
% 2.14/0.68    inference(superposition,[],[f72,f121])).
% 2.14/0.68  fof(f121,plain,(
% 2.14/0.68    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 2.14/0.68    inference(superposition,[],[f65,f51])).
% 2.14/0.68  fof(f51,plain,(
% 2.14/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.14/0.68    inference(cnf_transformation,[],[f8])).
% 2.14/0.68  fof(f8,axiom,(
% 2.14/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.14/0.68  fof(f65,plain,(
% 2.14/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 2.14/0.68    inference(superposition,[],[f51,f49])).
% 2.14/0.68  fof(f49,plain,(
% 2.14/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f6])).
% 2.14/0.68  fof(f6,axiom,(
% 2.14/0.68    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.14/0.68  fof(f72,plain,(
% 2.14/0.68    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.14/0.68    inference(superposition,[],[f48,f53])).
% 2.14/0.68  fof(f53,plain,(
% 2.14/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.14/0.68    inference(cnf_transformation,[],[f5])).
% 2.14/0.68  fof(f5,axiom,(
% 2.14/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.14/0.68  fof(f48,plain,(
% 2.14/0.68    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f4])).
% 2.14/0.68  fof(f4,axiom,(
% 2.14/0.68    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.14/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.14/0.68  % SZS output end Proof for theBenchmark
% 2.14/0.68  % (3587)------------------------------
% 2.14/0.68  % (3587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.68  % (3587)Termination reason: Refutation
% 2.14/0.68  
% 2.14/0.68  % (3587)Memory used [KB]: 3965
% 2.14/0.68  % (3587)Time elapsed: 0.241 s
% 2.14/0.68  % (3587)------------------------------
% 2.14/0.68  % (3587)------------------------------
% 2.14/0.68  % (3579)Success in time 0.313 s
%------------------------------------------------------------------------------
