%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:23 EST 2020

% Result     : Theorem 11.57s
% Output     : Refutation 12.29s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 370 expanded)
%              Number of leaves         :   12 (  80 expanded)
%              Depth                    :   19
%              Number of atoms          :  172 (1049 expanded)
%              Number of equality atoms :   27 ( 116 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20405,plain,(
    $false ),
    inference(resolution,[],[f20388,f14290])).

fof(f14290,plain,(
    ! [X31] : r1_tarski(k10_relat_1(sK2,k10_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),X31) ),
    inference(superposition,[],[f1876,f13333])).

fof(f13333,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k10_relat_1(sK2,k6_subset_1(X0,k6_subset_1(sK0,sK1))) ),
    inference(resolution,[],[f441,f7050])).

fof(f7050,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k6_subset_1(X0,k6_subset_1(sK0,sK1)))) ),
    inference(superposition,[],[f1406,f1490])).

fof(f1490,plain,(
    ! [X3] : k2_xboole_0(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),X3) = X3 ),
    inference(resolution,[],[f1479,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1479,plain,(
    ! [X4] : r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),X4) ),
    inference(resolution,[],[f436,f198])).

fof(f198,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),X0)) ),
    inference(resolution,[],[f84,f34])).

% (21644)Time limit reached!
% (21644)------------------------------
% (21644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21644)Termination reason: Time limit

% (21644)Memory used [KB]: 15479
% (21644)Time elapsed: 0.840 s
% (21644)------------------------------
% (21644)------------------------------
fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f84,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK2,sK1),X0)
      | r1_tarski(k10_relat_1(sK2,sK0),X0) ) ),
    inference(resolution,[],[f31,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f31,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(f436,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(k10_relat_1(sK2,X6),k2_xboole_0(k10_relat_1(sK2,X7),X8))
      | r1_tarski(k10_relat_1(sK2,k6_subset_1(X6,X7)),X8) ) ),
    inference(superposition,[],[f50,f58])).

fof(f58,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f56,f29])).

fof(f29,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2)
      | k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f30,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f43,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f1406,plain,(
    ! [X19,X18] : r1_tarski(k10_relat_1(sK2,X18),k2_xboole_0(k10_relat_1(sK2,X19),k10_relat_1(sK2,k6_subset_1(X18,X19)))) ),
    inference(resolution,[],[f435,f53])).

fof(f53,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f435,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k10_relat_1(sK2,k6_subset_1(X3,X4)),X5)
      | r1_tarski(k10_relat_1(sK2,X3),k2_xboole_0(k10_relat_1(sK2,X4),X5)) ) ),
    inference(superposition,[],[f51,f58])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f44,f36])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f441,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k10_relat_1(sK2,X3),k10_relat_1(sK2,k6_subset_1(X3,X4)))
      | k10_relat_1(sK2,X3) = k10_relat_1(sK2,k6_subset_1(X3,X4)) ) ),
    inference(resolution,[],[f438,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f438,plain,(
    ! [X12,X11] : r1_tarski(k10_relat_1(sK2,k6_subset_1(X11,X12)),k10_relat_1(sK2,X11)) ),
    inference(superposition,[],[f48,f58])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1876,plain,(
    ! [X4,X3] : r1_tarski(k10_relat_1(sK2,k10_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(X3,X3)))),X4) ),
    inference(superposition,[],[f1560,f58])).

fof(f1560,plain,(
    ! [X4,X3] : r1_tarski(k10_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(X3,X3))),X4) ),
    inference(superposition,[],[f1481,f58])).

fof(f1481,plain,(
    ! [X6,X7] : r1_tarski(k10_relat_1(sK2,k6_subset_1(X6,X6)),X7) ),
    inference(resolution,[],[f436,f34])).

fof(f20388,plain,(
    ! [X0] : ~ r1_tarski(X0,sK1) ),
    inference(subsumption_resolution,[],[f20347,f53])).

fof(f20347,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,sK1)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f20177,f7186])).

fof(f7186,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(sK0,k2_xboole_0(X5,X6))
      | ~ r1_tarski(X5,sK1)
      | ~ r1_tarski(X6,sK1) ) ),
    inference(resolution,[],[f164,f53])).

fof(f164,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_tarski(X5,k2_xboole_0(X6,X7))
      | ~ r1_tarski(sK0,X5)
      | ~ r1_tarski(X6,sK1)
      | ~ r1_tarski(X7,sK1) ) ),
    inference(resolution,[],[f75,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f75,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,sK1)
      | ~ r1_tarski(sK0,X4)
      | ~ r1_tarski(X4,X3) ) ),
    inference(resolution,[],[f60,f46])).

fof(f60,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f33,f46])).

fof(f33,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f20177,plain,(
    ! [X0] : r1_tarski(sK0,k2_xboole_0(sK1,X0)) ),
    inference(resolution,[],[f20147,f51])).

fof(f20147,plain,(
    ! [X10] : r1_tarski(k6_subset_1(sK0,sK1),X10) ),
    inference(subsumption_resolution,[],[f20029,f34])).

fof(f20029,plain,(
    ! [X10] :
      ( r1_tarski(k6_subset_1(sK0,sK1),X10)
      | ~ r1_tarski(k6_subset_1(sK0,sK1),k2_xboole_0(k6_subset_1(sK0,sK1),X10)) ) ),
    inference(superposition,[],[f50,f14340])).

fof(f14340,plain,(
    k6_subset_1(sK0,sK1) = k6_subset_1(k6_subset_1(sK0,sK1),k6_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f14267,f344])).

fof(f344,plain,(
    ! [X9] : k6_subset_1(sK0,X9) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X9))) ),
    inference(resolution,[],[f59,f99])).

fof(f99,plain,(
    ! [X4] : r1_tarski(k6_subset_1(sK0,X4),k2_relat_1(sK2)) ),
    inference(resolution,[],[f66,f48])).

fof(f66,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK0)
      | r1_tarski(X1,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f32,f46])).

fof(f32,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k2_relat_1(sK2))
      | k9_relat_1(sK2,k10_relat_1(sK2,X2)) = X2 ) ),
    inference(subsumption_resolution,[],[f57,f29])).

fof(f57,plain,(
    ! [X2] :
      ( ~ v1_relat_1(sK2)
      | ~ r1_tarski(X2,k2_relat_1(sK2))
      | k9_relat_1(sK2,k10_relat_1(sK2,X2)) = X2 ) ),
    inference(resolution,[],[f30,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f14267,plain,(
    k6_subset_1(k6_subset_1(sK0,sK1),k6_subset_1(sK0,sK1)) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(superposition,[],[f475,f13333])).

fof(f475,plain,(
    ! [X1] : k6_subset_1(X1,X1) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(X1,X1))) ),
    inference(resolution,[],[f462,f59])).

fof(f462,plain,(
    ! [X0] : r1_tarski(k6_subset_1(X0,X0),k2_relat_1(sK2)) ),
    inference(resolution,[],[f100,f34])).

fof(f100,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X5,k2_xboole_0(X6,sK0))
      | r1_tarski(k6_subset_1(X5,X6),k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f66,f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:01:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (21417)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.48  % (21423)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (21433)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.49  % (21431)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.49  % (21446)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (21425)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.50  % (21440)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (21421)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (21419)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (21439)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (21428)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.51  % (21429)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (21432)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (21438)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (21422)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (21424)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (21435)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (21436)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (21418)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (21430)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (21418)Refutation not found, incomplete strategy% (21418)------------------------------
% 0.20/0.53  % (21418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (21418)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (21418)Memory used [KB]: 1663
% 0.20/0.53  % (21418)Time elapsed: 0.124 s
% 0.20/0.53  % (21418)------------------------------
% 0.20/0.53  % (21418)------------------------------
% 0.20/0.53  % (21442)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (21420)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (21427)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (21434)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (21426)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (21445)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (21441)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (21444)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (21437)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (21443)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.80/0.61  % (21417)Refutation not found, incomplete strategy% (21417)------------------------------
% 1.80/0.61  % (21417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.61  % (21417)Termination reason: Refutation not found, incomplete strategy
% 1.80/0.61  
% 1.80/0.61  % (21417)Memory used [KB]: 1663
% 1.80/0.61  % (21417)Time elapsed: 0.227 s
% 1.80/0.61  % (21417)------------------------------
% 1.80/0.61  % (21417)------------------------------
% 2.11/0.67  % (21420)Refutation not found, incomplete strategy% (21420)------------------------------
% 2.11/0.67  % (21420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.68  % (21420)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.68  
% 2.11/0.68  % (21420)Memory used [KB]: 6140
% 2.11/0.68  % (21420)Time elapsed: 0.267 s
% 2.11/0.68  % (21420)------------------------------
% 2.11/0.68  % (21420)------------------------------
% 2.11/0.68  % (21546)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.76/0.77  % (21573)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.26/0.80  % (21587)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.26/0.80  % (21587)Refutation not found, incomplete strategy% (21587)------------------------------
% 3.26/0.80  % (21587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.26/0.80  % (21419)Time limit reached!
% 3.26/0.80  % (21419)------------------------------
% 3.26/0.80  % (21419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.26/0.80  % (21419)Termination reason: Time limit
% 3.26/0.80  
% 3.26/0.80  % (21419)Memory used [KB]: 6908
% 3.26/0.80  % (21419)Time elapsed: 0.406 s
% 3.26/0.80  % (21419)------------------------------
% 3.26/0.80  % (21419)------------------------------
% 3.26/0.80  % (21587)Termination reason: Refutation not found, incomplete strategy
% 3.26/0.80  
% 3.26/0.80  % (21587)Memory used [KB]: 6140
% 3.26/0.80  % (21587)Time elapsed: 0.075 s
% 3.26/0.80  % (21587)------------------------------
% 3.26/0.80  % (21587)------------------------------
% 3.26/0.81  % (21441)Time limit reached!
% 3.26/0.81  % (21441)------------------------------
% 3.26/0.81  % (21441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.26/0.81  % (21441)Termination reason: Time limit
% 3.26/0.81  % (21441)Termination phase: Saturation
% 3.26/0.81  
% 3.26/0.81  % (21441)Memory used [KB]: 13304
% 3.26/0.81  % (21441)Time elapsed: 0.400 s
% 3.26/0.81  % (21441)------------------------------
% 3.26/0.81  % (21441)------------------------------
% 4.01/0.90  % (21639)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.01/0.90  % (21431)Time limit reached!
% 4.01/0.90  % (21431)------------------------------
% 4.01/0.90  % (21431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.21/0.92  % (21446)Time limit reached!
% 4.21/0.92  % (21446)------------------------------
% 4.21/0.92  % (21446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.21/0.92  % (21423)Time limit reached!
% 4.21/0.92  % (21423)------------------------------
% 4.21/0.92  % (21423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.21/0.92  % (21423)Termination reason: Time limit
% 4.21/0.92  
% 4.21/0.92  % (21423)Memory used [KB]: 16630
% 4.21/0.92  % (21423)Time elapsed: 0.514 s
% 4.21/0.92  % (21423)------------------------------
% 4.21/0.92  % (21423)------------------------------
% 4.21/0.92  % (21446)Termination reason: Time limit
% 4.21/0.92  
% 4.21/0.92  % (21446)Memory used [KB]: 1918
% 4.21/0.92  % (21446)Time elapsed: 0.517 s
% 4.21/0.92  % (21446)------------------------------
% 4.21/0.92  % (21446)------------------------------
% 4.21/0.92  % (21431)Termination reason: Time limit
% 4.21/0.92  
% 4.21/0.92  % (21431)Memory used [KB]: 5628
% 4.21/0.92  % (21431)Time elapsed: 0.512 s
% 4.21/0.92  % (21431)------------------------------
% 4.21/0.92  % (21431)------------------------------
% 4.36/0.94  % (21638)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.36/0.95  % (21640)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.89/1.03  % (21643)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 4.89/1.03  % (21641)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.89/1.05  % (21424)Time limit reached!
% 4.89/1.05  % (21424)------------------------------
% 4.89/1.05  % (21424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.89/1.05  % (21642)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 4.89/1.06  % (21424)Termination reason: Time limit
% 4.89/1.06  
% 4.89/1.06  % (21424)Memory used [KB]: 6524
% 4.89/1.06  % (21424)Time elapsed: 0.617 s
% 4.89/1.06  % (21424)------------------------------
% 4.89/1.06  % (21424)------------------------------
% 5.31/1.17  % (21644)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 8.01/1.40  % (21444)Time limit reached!
% 8.01/1.40  % (21444)------------------------------
% 8.01/1.40  % (21444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.01/1.40  % (21444)Termination reason: Time limit
% 8.01/1.40  
% 8.01/1.40  % (21444)Memory used [KB]: 9850
% 8.01/1.40  % (21444)Time elapsed: 1.003 s
% 8.01/1.40  % (21444)------------------------------
% 8.01/1.40  % (21444)------------------------------
% 8.01/1.41  % (21429)Time limit reached!
% 8.01/1.41  % (21429)------------------------------
% 8.01/1.41  % (21429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.01/1.41  % (21429)Termination reason: Time limit
% 8.01/1.41  
% 8.01/1.41  % (21429)Memory used [KB]: 11129
% 8.01/1.41  % (21429)Time elapsed: 1.008 s
% 8.01/1.41  % (21429)------------------------------
% 8.01/1.41  % (21429)------------------------------
% 8.91/1.50  % (21645)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 9.18/1.54  % (21646)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 9.18/1.57  % (21641)Time limit reached!
% 9.18/1.57  % (21641)------------------------------
% 9.18/1.57  % (21641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.18/1.58  % (21641)Termination reason: Time limit
% 9.18/1.58  
% 9.18/1.58  % (21641)Memory used [KB]: 17526
% 9.18/1.58  % (21641)Time elapsed: 0.640 s
% 9.18/1.58  % (21641)------------------------------
% 9.18/1.58  % (21641)------------------------------
% 10.46/1.69  % (21422)Time limit reached!
% 10.46/1.69  % (21422)------------------------------
% 10.46/1.69  % (21422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.46/1.69  % (21422)Termination reason: Time limit
% 10.46/1.69  % (21422)Termination phase: Saturation
% 10.46/1.69  
% 10.46/1.69  % (21422)Memory used [KB]: 9466
% 10.46/1.69  % (21422)Time elapsed: 1.300 s
% 10.46/1.69  % (21422)------------------------------
% 10.46/1.69  % (21422)------------------------------
% 10.46/1.70  % (21433)Time limit reached!
% 10.46/1.70  % (21433)------------------------------
% 10.46/1.70  % (21433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.46/1.70  % (21433)Termination reason: Time limit
% 10.46/1.70  
% 10.46/1.70  % (21433)Memory used [KB]: 17782
% 10.46/1.70  % (21433)Time elapsed: 1.304 s
% 10.46/1.70  % (21433)------------------------------
% 10.46/1.70  % (21433)------------------------------
% 10.46/1.71  % (21647)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 11.42/1.82  % (21648)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 11.57/1.84  % (21649)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 11.57/1.90  % (21434)Refutation found. Thanks to Tanya!
% 11.57/1.90  % SZS status Theorem for theBenchmark
% 11.57/1.91  % SZS output start Proof for theBenchmark
% 11.57/1.92  fof(f20405,plain,(
% 11.57/1.92    $false),
% 11.57/1.92    inference(resolution,[],[f20388,f14290])).
% 11.57/1.92  fof(f14290,plain,(
% 11.57/1.92    ( ! [X31] : (r1_tarski(k10_relat_1(sK2,k10_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),X31)) )),
% 11.57/1.92    inference(superposition,[],[f1876,f13333])).
% 11.57/1.92  fof(f13333,plain,(
% 11.57/1.92    ( ! [X0] : (k10_relat_1(sK2,X0) = k10_relat_1(sK2,k6_subset_1(X0,k6_subset_1(sK0,sK1)))) )),
% 11.57/1.92    inference(resolution,[],[f441,f7050])).
% 11.57/1.92  fof(f7050,plain,(
% 11.57/1.92    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k6_subset_1(X0,k6_subset_1(sK0,sK1))))) )),
% 11.57/1.92    inference(superposition,[],[f1406,f1490])).
% 11.57/1.92  fof(f1490,plain,(
% 11.57/1.92    ( ! [X3] : (k2_xboole_0(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),X3) = X3) )),
% 11.57/1.92    inference(resolution,[],[f1479,f37])).
% 11.57/1.92  fof(f37,plain,(
% 11.57/1.92    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 11.57/1.92    inference(cnf_transformation,[],[f17])).
% 11.57/1.92  fof(f17,plain,(
% 11.57/1.92    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.57/1.92    inference(ennf_transformation,[],[f2])).
% 11.57/1.92  fof(f2,axiom,(
% 11.57/1.92    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.57/1.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 11.57/1.92  fof(f1479,plain,(
% 11.57/1.92    ( ! [X4] : (r1_tarski(k10_relat_1(sK2,k6_subset_1(sK0,sK1)),X4)) )),
% 11.57/1.92    inference(resolution,[],[f436,f198])).
% 11.57/1.92  fof(f198,plain,(
% 11.57/1.92    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,sK0),k2_xboole_0(k10_relat_1(sK2,sK1),X0))) )),
% 11.57/1.92    inference(resolution,[],[f84,f34])).
% 11.57/1.92  % (21644)Time limit reached!
% 11.57/1.92  % (21644)------------------------------
% 11.57/1.92  % (21644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.57/1.92  % (21644)Termination reason: Time limit
% 11.57/1.92  
% 11.57/1.92  % (21644)Memory used [KB]: 15479
% 11.57/1.92  % (21644)Time elapsed: 0.840 s
% 11.57/1.92  % (21644)------------------------------
% 11.57/1.92  % (21644)------------------------------
% 11.57/1.92  fof(f34,plain,(
% 11.57/1.92    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.57/1.92    inference(cnf_transformation,[],[f8])).
% 11.57/1.92  fof(f8,axiom,(
% 11.57/1.92    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.57/1.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 11.57/1.92  fof(f84,plain,(
% 11.57/1.92    ( ! [X0] : (~r1_tarski(k10_relat_1(sK2,sK1),X0) | r1_tarski(k10_relat_1(sK2,sK0),X0)) )),
% 11.57/1.92    inference(resolution,[],[f31,f46])).
% 11.57/1.92  fof(f46,plain,(
% 11.57/1.92    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 11.57/1.92    inference(cnf_transformation,[],[f26])).
% 11.57/1.92  fof(f26,plain,(
% 11.57/1.92    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.57/1.92    inference(flattening,[],[f25])).
% 11.57/1.92  fof(f25,plain,(
% 11.57/1.92    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.57/1.92    inference(ennf_transformation,[],[f3])).
% 11.57/1.92  fof(f3,axiom,(
% 11.57/1.92    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.57/1.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 11.57/1.92  fof(f31,plain,(
% 11.57/1.92    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 11.57/1.92    inference(cnf_transformation,[],[f16])).
% 11.57/1.92  fof(f16,plain,(
% 11.57/1.92    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 11.57/1.92    inference(flattening,[],[f15])).
% 11.57/1.92  fof(f15,plain,(
% 11.57/1.92    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 11.57/1.92    inference(ennf_transformation,[],[f14])).
% 11.57/1.92  fof(f14,negated_conjecture,(
% 11.57/1.92    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 11.57/1.92    inference(negated_conjecture,[],[f13])).
% 11.57/1.92  fof(f13,conjecture,(
% 11.57/1.92    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 11.57/1.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).
% 11.57/1.92  fof(f436,plain,(
% 11.57/1.92    ( ! [X6,X8,X7] : (~r1_tarski(k10_relat_1(sK2,X6),k2_xboole_0(k10_relat_1(sK2,X7),X8)) | r1_tarski(k10_relat_1(sK2,k6_subset_1(X6,X7)),X8)) )),
% 11.57/1.92    inference(superposition,[],[f50,f58])).
% 11.57/1.92  fof(f58,plain,(
% 11.57/1.92    ( ! [X0,X1] : (k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) )),
% 11.57/1.92    inference(subsumption_resolution,[],[f56,f29])).
% 11.57/1.92  fof(f29,plain,(
% 11.57/1.92    v1_relat_1(sK2)),
% 11.57/1.92    inference(cnf_transformation,[],[f16])).
% 11.57/1.92  fof(f56,plain,(
% 11.57/1.92    ( ! [X0,X1] : (~v1_relat_1(sK2) | k10_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) )),
% 11.57/1.92    inference(resolution,[],[f30,f45])).
% 11.57/1.92  fof(f45,plain,(
% 11.57/1.92    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 11.57/1.92    inference(cnf_transformation,[],[f24])).
% 11.57/1.92  fof(f24,plain,(
% 11.57/1.92    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 11.57/1.92    inference(flattening,[],[f23])).
% 12.29/1.92  fof(f23,plain,(
% 12.29/1.92    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 12.29/1.92    inference(ennf_transformation,[],[f11])).
% 12.29/1.92  fof(f11,axiom,(
% 12.29/1.92    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 12.29/1.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 12.29/1.92  fof(f30,plain,(
% 12.29/1.92    v1_funct_1(sK2)),
% 12.29/1.92    inference(cnf_transformation,[],[f16])).
% 12.29/1.92  fof(f50,plain,(
% 12.29/1.92    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 12.29/1.92    inference(definition_unfolding,[],[f43,f36])).
% 12.29/1.92  fof(f36,plain,(
% 12.29/1.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 12.29/1.92    inference(cnf_transformation,[],[f10])).
% 12.29/1.92  fof(f10,axiom,(
% 12.29/1.92    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 12.29/1.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 12.29/1.92  fof(f43,plain,(
% 12.29/1.92    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 12.29/1.92    inference(cnf_transformation,[],[f21])).
% 12.29/1.92  fof(f21,plain,(
% 12.29/1.92    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 12.29/1.92    inference(ennf_transformation,[],[f5])).
% 12.29/1.92  fof(f5,axiom,(
% 12.29/1.92    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 12.29/1.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 12.29/1.92  fof(f1406,plain,(
% 12.29/1.92    ( ! [X19,X18] : (r1_tarski(k10_relat_1(sK2,X18),k2_xboole_0(k10_relat_1(sK2,X19),k10_relat_1(sK2,k6_subset_1(X18,X19))))) )),
% 12.29/1.92    inference(resolution,[],[f435,f53])).
% 12.29/1.92  fof(f53,plain,(
% 12.29/1.92    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 12.29/1.92    inference(equality_resolution,[],[f40])).
% 12.29/1.92  fof(f40,plain,(
% 12.29/1.92    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 12.29/1.92    inference(cnf_transformation,[],[f1])).
% 12.29/1.92  fof(f1,axiom,(
% 12.29/1.92    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 12.29/1.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 12.29/1.92  fof(f435,plain,(
% 12.29/1.92    ( ! [X4,X5,X3] : (~r1_tarski(k10_relat_1(sK2,k6_subset_1(X3,X4)),X5) | r1_tarski(k10_relat_1(sK2,X3),k2_xboole_0(k10_relat_1(sK2,X4),X5))) )),
% 12.29/1.92    inference(superposition,[],[f51,f58])).
% 12.29/1.92  fof(f51,plain,(
% 12.29/1.92    ( ! [X2,X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 12.29/1.92    inference(definition_unfolding,[],[f44,f36])).
% 12.29/1.92  fof(f44,plain,(
% 12.29/1.92    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 12.29/1.92    inference(cnf_transformation,[],[f22])).
% 12.29/1.92  fof(f22,plain,(
% 12.29/1.92    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 12.29/1.92    inference(ennf_transformation,[],[f6])).
% 12.29/1.92  fof(f6,axiom,(
% 12.29/1.92    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 12.29/1.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 12.29/1.92  fof(f441,plain,(
% 12.29/1.92    ( ! [X4,X3] : (~r1_tarski(k10_relat_1(sK2,X3),k10_relat_1(sK2,k6_subset_1(X3,X4))) | k10_relat_1(sK2,X3) = k10_relat_1(sK2,k6_subset_1(X3,X4))) )),
% 12.29/1.92    inference(resolution,[],[f438,f42])).
% 12.29/1.92  fof(f42,plain,(
% 12.29/1.92    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 12.29/1.92    inference(cnf_transformation,[],[f1])).
% 12.29/1.92  fof(f438,plain,(
% 12.29/1.92    ( ! [X12,X11] : (r1_tarski(k10_relat_1(sK2,k6_subset_1(X11,X12)),k10_relat_1(sK2,X11))) )),
% 12.29/1.92    inference(superposition,[],[f48,f58])).
% 12.29/1.92  fof(f48,plain,(
% 12.29/1.92    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 12.29/1.92    inference(definition_unfolding,[],[f35,f36])).
% 12.29/1.92  fof(f35,plain,(
% 12.29/1.92    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 12.29/1.92    inference(cnf_transformation,[],[f4])).
% 12.29/1.92  fof(f4,axiom,(
% 12.29/1.92    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 12.29/1.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 12.29/1.92  fof(f1876,plain,(
% 12.29/1.92    ( ! [X4,X3] : (r1_tarski(k10_relat_1(sK2,k10_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(X3,X3)))),X4)) )),
% 12.29/1.92    inference(superposition,[],[f1560,f58])).
% 12.29/1.92  fof(f1560,plain,(
% 12.29/1.92    ( ! [X4,X3] : (r1_tarski(k10_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(X3,X3))),X4)) )),
% 12.29/1.92    inference(superposition,[],[f1481,f58])).
% 12.29/1.92  fof(f1481,plain,(
% 12.29/1.92    ( ! [X6,X7] : (r1_tarski(k10_relat_1(sK2,k6_subset_1(X6,X6)),X7)) )),
% 12.29/1.92    inference(resolution,[],[f436,f34])).
% 12.29/1.92  fof(f20388,plain,(
% 12.29/1.92    ( ! [X0] : (~r1_tarski(X0,sK1)) )),
% 12.29/1.92    inference(subsumption_resolution,[],[f20347,f53])).
% 12.29/1.92  fof(f20347,plain,(
% 12.29/1.92    ( ! [X0] : (~r1_tarski(sK1,sK1) | ~r1_tarski(X0,sK1)) )),
% 12.29/1.92    inference(resolution,[],[f20177,f7186])).
% 12.29/1.92  fof(f7186,plain,(
% 12.29/1.92    ( ! [X6,X5] : (~r1_tarski(sK0,k2_xboole_0(X5,X6)) | ~r1_tarski(X5,sK1) | ~r1_tarski(X6,sK1)) )),
% 12.29/1.92    inference(resolution,[],[f164,f53])).
% 12.29/1.92  fof(f164,plain,(
% 12.29/1.92    ( ! [X6,X7,X5] : (~r1_tarski(X5,k2_xboole_0(X6,X7)) | ~r1_tarski(sK0,X5) | ~r1_tarski(X6,sK1) | ~r1_tarski(X7,sK1)) )),
% 12.29/1.92    inference(resolution,[],[f75,f47])).
% 12.29/1.92  fof(f47,plain,(
% 12.29/1.92    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1)) )),
% 12.29/1.92    inference(cnf_transformation,[],[f28])).
% 12.29/1.92  fof(f28,plain,(
% 12.29/1.92    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 12.29/1.92    inference(flattening,[],[f27])).
% 12.29/1.92  fof(f27,plain,(
% 12.29/1.92    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 12.29/1.92    inference(ennf_transformation,[],[f9])).
% 12.29/1.92  fof(f9,axiom,(
% 12.29/1.92    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 12.29/1.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 12.29/1.92  fof(f75,plain,(
% 12.29/1.92    ( ! [X4,X3] : (~r1_tarski(X3,sK1) | ~r1_tarski(sK0,X4) | ~r1_tarski(X4,X3)) )),
% 12.29/1.92    inference(resolution,[],[f60,f46])).
% 12.29/1.92  fof(f60,plain,(
% 12.29/1.92    ( ! [X0] : (~r1_tarski(sK0,X0) | ~r1_tarski(X0,sK1)) )),
% 12.29/1.92    inference(resolution,[],[f33,f46])).
% 12.29/1.92  fof(f33,plain,(
% 12.29/1.92    ~r1_tarski(sK0,sK1)),
% 12.29/1.92    inference(cnf_transformation,[],[f16])).
% 12.29/1.92  fof(f20177,plain,(
% 12.29/1.92    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(sK1,X0))) )),
% 12.29/1.92    inference(resolution,[],[f20147,f51])).
% 12.29/1.92  fof(f20147,plain,(
% 12.29/1.92    ( ! [X10] : (r1_tarski(k6_subset_1(sK0,sK1),X10)) )),
% 12.29/1.92    inference(subsumption_resolution,[],[f20029,f34])).
% 12.29/1.92  fof(f20029,plain,(
% 12.29/1.92    ( ! [X10] : (r1_tarski(k6_subset_1(sK0,sK1),X10) | ~r1_tarski(k6_subset_1(sK0,sK1),k2_xboole_0(k6_subset_1(sK0,sK1),X10))) )),
% 12.29/1.92    inference(superposition,[],[f50,f14340])).
% 12.29/1.92  fof(f14340,plain,(
% 12.29/1.92    k6_subset_1(sK0,sK1) = k6_subset_1(k6_subset_1(sK0,sK1),k6_subset_1(sK0,sK1))),
% 12.29/1.92    inference(forward_demodulation,[],[f14267,f344])).
% 12.29/1.92  fof(f344,plain,(
% 12.29/1.92    ( ! [X9] : (k6_subset_1(sK0,X9) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,X9)))) )),
% 12.29/1.92    inference(resolution,[],[f59,f99])).
% 12.29/1.92  fof(f99,plain,(
% 12.29/1.92    ( ! [X4] : (r1_tarski(k6_subset_1(sK0,X4),k2_relat_1(sK2))) )),
% 12.29/1.92    inference(resolution,[],[f66,f48])).
% 12.29/1.92  fof(f66,plain,(
% 12.29/1.92    ( ! [X1] : (~r1_tarski(X1,sK0) | r1_tarski(X1,k2_relat_1(sK2))) )),
% 12.29/1.92    inference(resolution,[],[f32,f46])).
% 12.29/1.92  fof(f32,plain,(
% 12.29/1.92    r1_tarski(sK0,k2_relat_1(sK2))),
% 12.29/1.92    inference(cnf_transformation,[],[f16])).
% 12.29/1.92  fof(f59,plain,(
% 12.29/1.92    ( ! [X2] : (~r1_tarski(X2,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X2)) = X2) )),
% 12.29/1.92    inference(subsumption_resolution,[],[f57,f29])).
% 12.29/1.92  fof(f57,plain,(
% 12.29/1.92    ( ! [X2] : (~v1_relat_1(sK2) | ~r1_tarski(X2,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X2)) = X2) )),
% 12.29/1.92    inference(resolution,[],[f30,f39])).
% 12.29/1.92  fof(f39,plain,(
% 12.29/1.92    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0) )),
% 12.29/1.92    inference(cnf_transformation,[],[f20])).
% 12.29/1.92  fof(f20,plain,(
% 12.29/1.92    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 12.29/1.92    inference(flattening,[],[f19])).
% 12.29/1.92  fof(f19,plain,(
% 12.29/1.92    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 12.29/1.92    inference(ennf_transformation,[],[f12])).
% 12.29/1.92  fof(f12,axiom,(
% 12.29/1.92    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 12.29/1.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 12.29/1.92  fof(f14267,plain,(
% 12.29/1.92    k6_subset_1(k6_subset_1(sK0,sK1),k6_subset_1(sK0,sK1)) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 12.29/1.92    inference(superposition,[],[f475,f13333])).
% 12.29/1.92  fof(f475,plain,(
% 12.29/1.92    ( ! [X1] : (k6_subset_1(X1,X1) = k9_relat_1(sK2,k10_relat_1(sK2,k6_subset_1(X1,X1)))) )),
% 12.29/1.92    inference(resolution,[],[f462,f59])).
% 12.29/1.92  fof(f462,plain,(
% 12.29/1.92    ( ! [X0] : (r1_tarski(k6_subset_1(X0,X0),k2_relat_1(sK2))) )),
% 12.29/1.92    inference(resolution,[],[f100,f34])).
% 12.29/1.92  fof(f100,plain,(
% 12.29/1.92    ( ! [X6,X5] : (~r1_tarski(X5,k2_xboole_0(X6,sK0)) | r1_tarski(k6_subset_1(X5,X6),k2_relat_1(sK2))) )),
% 12.29/1.92    inference(resolution,[],[f66,f50])).
% 12.29/1.92  % SZS output end Proof for theBenchmark
% 12.29/1.92  % (21434)------------------------------
% 12.29/1.92  % (21434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.29/1.92  % (21434)Termination reason: Refutation
% 12.29/1.92  
% 12.29/1.92  % (21434)Memory used [KB]: 11513
% 12.29/1.92  % (21434)Time elapsed: 1.510 s
% 12.29/1.92  % (21434)------------------------------
% 12.29/1.92  % (21434)------------------------------
% 12.29/1.92  % (21413)Success in time 1.56 s
%------------------------------------------------------------------------------
