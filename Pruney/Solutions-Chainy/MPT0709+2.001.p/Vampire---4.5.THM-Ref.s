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
% DateTime   : Thu Dec  3 12:54:35 EST 2020

% Result     : Theorem 2.73s
% Output     : Refutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 315 expanded)
%              Number of leaves         :   18 (  76 expanded)
%              Depth                    :   22
%              Number of atoms          :  252 ( 860 expanded)
%              Number of equality atoms :   65 ( 222 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3913,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3886,f51])).

fof(f51,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f3886,plain,(
    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f3879,f49])).

fof(f49,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f3879,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f2847,f172])).

fof(f172,plain,(
    ! [X0] :
      ( r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f74,f47])).

fof(f47,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f2847,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))
      | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f2770,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2770,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    inference(resolution,[],[f2604,f503])).

fof(f503,plain,(
    ! [X2,X3] : r1_tarski(k10_relat_1(k6_relat_1(X3),X2),X2) ),
    inference(superposition,[],[f118,f488])).

fof(f488,plain,(
    ! [X4,X5] : k10_relat_1(k6_relat_1(X5),X4) = k10_relat_1(k6_relat_1(X4),X5) ),
    inference(superposition,[],[f408,f211])).

fof(f211,plain,(
    ! [X4,X5] : k1_setfam_1(k2_enumset1(X4,X4,X4,X5)) = k10_relat_1(k6_relat_1(X5),X4) ),
    inference(forward_demodulation,[],[f198,f165])).

fof(f165,plain,(
    ! [X2,X1] : k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) ),
    inference(resolution,[],[f156,f55])).

fof(f55,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f156,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X2) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) ) ),
    inference(forward_demodulation,[],[f155,f57])).

fof(f57,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f155,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,k1_relat_1(k6_relat_1(X2))) ) ),
    inference(resolution,[],[f59,f55])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f198,plain,(
    ! [X4,X5] : k1_setfam_1(k2_enumset1(X4,X4,X4,X5)) = k1_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X4))) ),
    inference(superposition,[],[f57,f100])).

fof(f100,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f71,f94])).

fof(f94,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f69,f93])).

fof(f93,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f71,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f408,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) = k10_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[],[f211,f99])).

fof(f99,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f67,f93,f93])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f118,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f117,f55])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f72,f57])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f2604,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X1),k9_relat_1(sK1,X2))
      | r1_tarski(k10_relat_1(sK1,X1),X2) ) ),
    inference(forward_demodulation,[],[f2594,f1553])).

fof(f1553,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X0) = k9_relat_1(sK1,k10_relat_1(sK1,X0)) ),
    inference(forward_demodulation,[],[f1552,f1014])).

fof(f1014,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f1010,f386])).

fof(f386,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f378,f371])).

fof(f371,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f368])).

fof(f368,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f363,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
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

fof(f363,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1))
      | r1_tarski(k10_relat_1(sK1,X0),X1) ) ),
    inference(resolution,[],[f362,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f362,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(sK1,X1))
      | r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f361,f47])).

fof(f361,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f110,f48])).

fof(f48,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f378,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k2_relat_1(sK1)),k1_relat_1(sK1))
    | k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    inference(superposition,[],[f141,f375])).

fof(f375,plain,(
    k1_relat_1(sK1) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f374,f111])).

fof(f111,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f374,plain,
    ( k1_relat_1(sK1) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1)))
    | ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) ),
    inference(resolution,[],[f372,f172])).

fof(f372,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,X0))
      | k1_relat_1(sK1) = k10_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f371,f80])).

fof(f141,plain,(
    ! [X0] :
      ( ~ r1_tarski(k10_relat_1(sK1,k2_relat_1(sK1)),k10_relat_1(sK1,X0))
      | k10_relat_1(sK1,X0) = k10_relat_1(sK1,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f138,f80])).

fof(f138,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(resolution,[],[f73,f47])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

fof(f1010,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1))) ),
    inference(resolution,[],[f1008,f111])).

fof(f1008,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(sK1))
      | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f1007,f47])).

fof(f1007,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ r1_tarski(X0,k2_relat_1(sK1))
      | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f77,f48])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f1552,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(k9_relat_1(sK1,k1_relat_1(sK1))),X0) = k9_relat_1(sK1,k10_relat_1(sK1,X0)) ),
    inference(subsumption_resolution,[],[f1551,f47])).

fof(f1551,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | k10_relat_1(k6_relat_1(k9_relat_1(sK1,k1_relat_1(sK1))),X0) = k9_relat_1(sK1,k10_relat_1(sK1,X0)) ) ),
    inference(resolution,[],[f220,f48])).

fof(f220,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k10_relat_1(k6_relat_1(k9_relat_1(X1,k1_relat_1(X1))),X0) ) ),
    inference(backward_demodulation,[],[f101,f211])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) ) ),
    inference(definition_unfolding,[],[f76,f94])).

fof(f76,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(f2594,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X1)),k9_relat_1(sK1,X2))
      | r1_tarski(k10_relat_1(sK1,X1),X2) ) ),
    inference(resolution,[],[f2592,f371])).

fof(f2592,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(sK1))
      | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f2591,f50])).

fof(f50,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f2591,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ r1_tarski(X0,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f2590,f47])).

fof(f2590,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | ~ r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ r1_tarski(X0,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f86,f48])).

fof(f86,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:17:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (3550)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (3553)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (3558)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (3555)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (3554)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (3560)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (3578)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (3563)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (3572)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (3564)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (3569)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (3559)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (3577)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (3562)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (3559)Refutation not found, incomplete strategy% (3559)------------------------------
% 0.21/0.53  % (3559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3559)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3559)Memory used [KB]: 10746
% 0.21/0.53  % (3559)Time elapsed: 0.114 s
% 0.21/0.53  % (3559)------------------------------
% 0.21/0.53  % (3559)------------------------------
% 0.21/0.53  % (3552)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (3551)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (3571)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (3553)Refutation not found, incomplete strategy% (3553)------------------------------
% 0.21/0.54  % (3553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3553)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3553)Memory used [KB]: 6396
% 0.21/0.54  % (3553)Time elapsed: 0.119 s
% 0.21/0.54  % (3553)------------------------------
% 0.21/0.54  % (3553)------------------------------
% 0.21/0.54  % (3549)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (3571)Refutation not found, incomplete strategy% (3571)------------------------------
% 0.21/0.54  % (3571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3576)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (3566)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (3571)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3571)Memory used [KB]: 10746
% 0.21/0.54  % (3571)Time elapsed: 0.129 s
% 0.21/0.54  % (3571)------------------------------
% 0.21/0.54  % (3571)------------------------------
% 0.21/0.54  % (3570)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (3575)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (3566)Refutation not found, incomplete strategy% (3566)------------------------------
% 0.21/0.54  % (3566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3566)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3566)Memory used [KB]: 10618
% 0.21/0.54  % (3566)Time elapsed: 0.139 s
% 0.21/0.54  % (3566)------------------------------
% 0.21/0.54  % (3566)------------------------------
% 0.21/0.55  % (3574)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (3557)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (3567)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (3565)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (3561)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (3573)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (3556)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.57  % (3568)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.03/0.67  % (3584)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.03/0.68  % (3585)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.03/0.68  % (3586)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.03/0.68  % (3587)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.03/0.69  % (3584)Refutation not found, incomplete strategy% (3584)------------------------------
% 2.03/0.69  % (3584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.70  % (3584)Termination reason: Refutation not found, incomplete strategy
% 2.03/0.70  
% 2.03/0.70  % (3584)Memory used [KB]: 6396
% 2.03/0.70  % (3584)Time elapsed: 0.114 s
% 2.03/0.70  % (3584)------------------------------
% 2.03/0.70  % (3584)------------------------------
% 2.73/0.77  % (3555)Refutation found. Thanks to Tanya!
% 2.73/0.77  % SZS status Theorem for theBenchmark
% 2.73/0.77  % SZS output start Proof for theBenchmark
% 2.73/0.77  fof(f3913,plain,(
% 2.73/0.77    $false),
% 2.73/0.77    inference(subsumption_resolution,[],[f3886,f51])).
% 2.73/0.77  fof(f51,plain,(
% 2.73/0.77    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 2.73/0.77    inference(cnf_transformation,[],[f30])).
% 2.73/0.77  fof(f30,plain,(
% 2.73/0.77    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.73/0.77    inference(flattening,[],[f29])).
% 2.73/0.77  fof(f29,plain,(
% 2.73/0.77    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 2.73/0.77    inference(ennf_transformation,[],[f27])).
% 2.73/0.77  fof(f27,negated_conjecture,(
% 2.73/0.77    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 2.73/0.77    inference(negated_conjecture,[],[f26])).
% 2.73/0.77  fof(f26,conjecture,(
% 2.73/0.77    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 2.73/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 2.73/0.77  fof(f3886,plain,(
% 2.73/0.77    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 2.73/0.77    inference(resolution,[],[f3879,f49])).
% 2.73/0.77  fof(f49,plain,(
% 2.73/0.77    r1_tarski(sK0,k1_relat_1(sK1))),
% 2.73/0.77    inference(cnf_transformation,[],[f30])).
% 2.73/0.77  fof(f3879,plain,(
% 2.73/0.77    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0) )),
% 2.73/0.77    inference(resolution,[],[f2847,f172])).
% 2.73/0.77  fof(f172,plain,(
% 2.73/0.77    ( ! [X0] : (r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) | ~r1_tarski(X0,k1_relat_1(sK1))) )),
% 2.73/0.77    inference(resolution,[],[f74,f47])).
% 2.73/0.77  fof(f47,plain,(
% 2.73/0.77    v1_relat_1(sK1)),
% 2.73/0.77    inference(cnf_transformation,[],[f30])).
% 2.73/0.77  fof(f74,plain,(
% 2.73/0.77    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 2.73/0.77    inference(cnf_transformation,[],[f37])).
% 2.73/0.77  fof(f37,plain,(
% 2.73/0.77    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.73/0.77    inference(flattening,[],[f36])).
% 2.73/0.77  fof(f36,plain,(
% 2.73/0.77    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.73/0.77    inference(ennf_transformation,[],[f21])).
% 2.73/0.77  fof(f21,axiom,(
% 2.73/0.77    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.73/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 2.73/0.77  fof(f2847,plain,(
% 2.73/0.77    ( ! [X0] : (~r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0) )),
% 2.73/0.77    inference(resolution,[],[f2770,f80])).
% 2.73/0.77  fof(f80,plain,(
% 2.73/0.77    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.73/0.77    inference(cnf_transformation,[],[f4])).
% 2.73/0.77  fof(f4,axiom,(
% 2.73/0.77    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.73/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.73/0.77  fof(f2770,plain,(
% 2.73/0.77    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) )),
% 2.73/0.77    inference(resolution,[],[f2604,f503])).
% 2.73/0.77  fof(f503,plain,(
% 2.73/0.77    ( ! [X2,X3] : (r1_tarski(k10_relat_1(k6_relat_1(X3),X2),X2)) )),
% 2.73/0.77    inference(superposition,[],[f118,f488])).
% 2.73/0.77  fof(f488,plain,(
% 2.73/0.77    ( ! [X4,X5] : (k10_relat_1(k6_relat_1(X5),X4) = k10_relat_1(k6_relat_1(X4),X5)) )),
% 2.73/0.77    inference(superposition,[],[f408,f211])).
% 2.73/0.77  fof(f211,plain,(
% 2.73/0.77    ( ! [X4,X5] : (k1_setfam_1(k2_enumset1(X4,X4,X4,X5)) = k10_relat_1(k6_relat_1(X5),X4)) )),
% 2.73/0.77    inference(forward_demodulation,[],[f198,f165])).
% 2.73/0.77  fof(f165,plain,(
% 2.73/0.77    ( ! [X2,X1] : (k10_relat_1(k6_relat_1(X1),X2) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) )),
% 2.73/0.77    inference(resolution,[],[f156,f55])).
% 2.73/0.77  fof(f55,plain,(
% 2.73/0.77    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.73/0.77    inference(cnf_transformation,[],[f20])).
% 2.73/0.77  fof(f20,axiom,(
% 2.73/0.77    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.73/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.73/0.77  fof(f156,plain,(
% 2.73/0.77    ( ! [X2,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X2) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))) )),
% 2.73/0.77    inference(forward_demodulation,[],[f155,f57])).
% 2.73/0.77  fof(f57,plain,(
% 2.73/0.77    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.73/0.77    inference(cnf_transformation,[],[f18])).
% 2.73/0.77  fof(f18,axiom,(
% 2.73/0.77    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.73/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.73/0.77  fof(f155,plain,(
% 2.73/0.77    ( ! [X2,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,k1_relat_1(k6_relat_1(X2)))) )),
% 2.73/0.77    inference(resolution,[],[f59,f55])).
% 2.73/0.77  fof(f59,plain,(
% 2.73/0.77    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 2.73/0.77    inference(cnf_transformation,[],[f31])).
% 2.73/0.77  fof(f31,plain,(
% 2.73/0.77    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.73/0.77    inference(ennf_transformation,[],[f17])).
% 2.73/0.77  fof(f17,axiom,(
% 2.73/0.77    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.73/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 2.73/0.77  fof(f198,plain,(
% 2.73/0.77    ( ! [X4,X5] : (k1_setfam_1(k2_enumset1(X4,X4,X4,X5)) = k1_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X4)))) )),
% 2.73/0.77    inference(superposition,[],[f57,f100])).
% 2.73/0.77  fof(f100,plain,(
% 2.73/0.77    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 2.73/0.77    inference(definition_unfolding,[],[f71,f94])).
% 2.73/0.77  fof(f94,plain,(
% 2.73/0.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 2.73/0.77    inference(definition_unfolding,[],[f69,f93])).
% 2.73/0.77  fof(f93,plain,(
% 2.73/0.77    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.73/0.77    inference(definition_unfolding,[],[f68,f84])).
% 2.73/0.77  fof(f84,plain,(
% 2.73/0.77    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.73/0.77    inference(cnf_transformation,[],[f12])).
% 2.73/0.77  fof(f12,axiom,(
% 2.73/0.77    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.73/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.73/0.77  fof(f68,plain,(
% 2.73/0.77    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.73/0.77    inference(cnf_transformation,[],[f11])).
% 2.73/0.77  fof(f11,axiom,(
% 2.73/0.77    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.73/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.73/0.77  fof(f69,plain,(
% 2.73/0.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.73/0.77    inference(cnf_transformation,[],[f13])).
% 2.73/0.77  fof(f13,axiom,(
% 2.73/0.77    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.73/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.73/0.77  fof(f71,plain,(
% 2.73/0.77    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 2.73/0.77    inference(cnf_transformation,[],[f25])).
% 2.73/0.77  fof(f25,axiom,(
% 2.73/0.77    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.73/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 2.73/0.77  fof(f408,plain,(
% 2.73/0.77    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) = k10_relat_1(k6_relat_1(X1),X0)) )),
% 2.73/0.77    inference(superposition,[],[f211,f99])).
% 2.73/0.77  fof(f99,plain,(
% 2.73/0.77    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 2.73/0.77    inference(definition_unfolding,[],[f67,f93,f93])).
% 2.73/0.77  fof(f67,plain,(
% 2.73/0.77    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.73/0.77    inference(cnf_transformation,[],[f10])).
% 2.73/0.77  fof(f10,axiom,(
% 2.73/0.77    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.73/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.73/0.77  fof(f118,plain,(
% 2.73/0.77    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 2.73/0.77    inference(subsumption_resolution,[],[f117,f55])).
% 2.73/0.77  fof(f117,plain,(
% 2.73/0.77    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.73/0.77    inference(superposition,[],[f72,f57])).
% 2.73/0.77  fof(f72,plain,(
% 2.73/0.77    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.73/0.77    inference(cnf_transformation,[],[f34])).
% 2.73/0.77  fof(f34,plain,(
% 2.73/0.77    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.73/0.77    inference(ennf_transformation,[],[f14])).
% 2.73/0.77  fof(f14,axiom,(
% 2.73/0.77    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.73/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 2.73/0.77  fof(f2604,plain,(
% 2.73/0.77    ( ! [X2,X1] : (~r1_tarski(k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X1),k9_relat_1(sK1,X2)) | r1_tarski(k10_relat_1(sK1,X1),X2)) )),
% 2.73/0.77    inference(forward_demodulation,[],[f2594,f1553])).
% 2.73/0.77  fof(f1553,plain,(
% 2.73/0.77    ( ! [X0] : (k10_relat_1(k6_relat_1(k2_relat_1(sK1)),X0) = k9_relat_1(sK1,k10_relat_1(sK1,X0))) )),
% 2.73/0.77    inference(forward_demodulation,[],[f1552,f1014])).
% 2.73/0.77  fof(f1014,plain,(
% 2.73/0.77    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 2.73/0.77    inference(forward_demodulation,[],[f1010,f386])).
% 2.73/0.77  fof(f386,plain,(
% 2.73/0.77    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 2.73/0.77    inference(subsumption_resolution,[],[f378,f371])).
% 2.73/0.77  fof(f371,plain,(
% 2.73/0.77    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 2.73/0.77    inference(duplicate_literal_removal,[],[f368])).
% 2.73/0.77  fof(f368,plain,(
% 2.73/0.77    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 2.73/0.77    inference(resolution,[],[f363,f83])).
% 2.73/0.77  fof(f83,plain,(
% 2.73/0.77    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.73/0.77    inference(cnf_transformation,[],[f43])).
% 2.73/0.77  fof(f43,plain,(
% 2.73/0.77    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.73/0.77    inference(ennf_transformation,[],[f1])).
% 2.73/0.77  fof(f1,axiom,(
% 2.73/0.77    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.73/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.73/0.77  fof(f363,plain,(
% 2.73/0.77    ( ! [X0,X1] : (r2_hidden(sK3(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1)) | r1_tarski(k10_relat_1(sK1,X0),X1)) )),
% 2.73/0.77    inference(resolution,[],[f362,f82])).
% 2.73/0.77  fof(f82,plain,(
% 2.73/0.77    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.73/0.77    inference(cnf_transformation,[],[f43])).
% 2.73/0.77  fof(f362,plain,(
% 2.73/0.77    ( ! [X0,X1] : (~r2_hidden(X0,k10_relat_1(sK1,X1)) | r2_hidden(X0,k1_relat_1(sK1))) )),
% 2.73/0.77    inference(subsumption_resolution,[],[f361,f47])).
% 2.73/0.77  fof(f361,plain,(
% 2.73/0.77    ( ! [X0,X1] : (~v1_relat_1(sK1) | r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) )),
% 2.73/0.77    inference(resolution,[],[f110,f48])).
% 2.73/0.77  fof(f48,plain,(
% 2.73/0.77    v1_funct_1(sK1)),
% 2.73/0.77    inference(cnf_transformation,[],[f30])).
% 2.73/0.77  fof(f110,plain,(
% 2.73/0.77    ( ! [X0,X3,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 2.73/0.77    inference(equality_resolution,[],[f63])).
% 2.73/0.77  fof(f63,plain,(
% 2.73/0.77    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 2.73/0.77    inference(cnf_transformation,[],[f33])).
% 2.73/0.77  fof(f33,plain,(
% 2.73/0.77    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.73/0.77    inference(flattening,[],[f32])).
% 2.73/0.77  fof(f32,plain,(
% 2.73/0.77    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.73/0.77    inference(ennf_transformation,[],[f19])).
% 2.73/0.77  fof(f19,axiom,(
% 2.73/0.77    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 2.73/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).
% 2.73/0.77  fof(f378,plain,(
% 2.73/0.77    ~r1_tarski(k10_relat_1(sK1,k2_relat_1(sK1)),k1_relat_1(sK1)) | k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 2.73/0.77    inference(superposition,[],[f141,f375])).
% 2.73/0.77  fof(f375,plain,(
% 2.73/0.77    k1_relat_1(sK1) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1)))),
% 2.73/0.77    inference(subsumption_resolution,[],[f374,f111])).
% 2.73/0.77  fof(f111,plain,(
% 2.73/0.77    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.73/0.77    inference(equality_resolution,[],[f79])).
% 2.73/0.77  fof(f79,plain,(
% 2.73/0.77    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.73/0.77    inference(cnf_transformation,[],[f4])).
% 2.73/0.77  fof(f374,plain,(
% 2.73/0.77    k1_relat_1(sK1) = k10_relat_1(sK1,k9_relat_1(sK1,k1_relat_1(sK1))) | ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))),
% 2.73/0.77    inference(resolution,[],[f372,f172])).
% 2.73/0.77  fof(f372,plain,(
% 2.73/0.77    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),k10_relat_1(sK1,X0)) | k1_relat_1(sK1) = k10_relat_1(sK1,X0)) )),
% 2.73/0.77    inference(resolution,[],[f371,f80])).
% 2.73/0.77  fof(f141,plain,(
% 2.73/0.77    ( ! [X0] : (~r1_tarski(k10_relat_1(sK1,k2_relat_1(sK1)),k10_relat_1(sK1,X0)) | k10_relat_1(sK1,X0) = k10_relat_1(sK1,k2_relat_1(sK1))) )),
% 2.73/0.77    inference(resolution,[],[f138,f80])).
% 2.73/0.77  fof(f138,plain,(
% 2.73/0.77    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k2_relat_1(sK1)))) )),
% 2.73/0.77    inference(resolution,[],[f73,f47])).
% 2.73/0.77  fof(f73,plain,(
% 2.73/0.77    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))) )),
% 2.73/0.77    inference(cnf_transformation,[],[f35])).
% 2.73/0.77  fof(f35,plain,(
% 2.73/0.77    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.73/0.77    inference(ennf_transformation,[],[f15])).
% 2.73/0.77  fof(f15,axiom,(
% 2.73/0.77    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 2.73/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).
% 2.73/0.77  fof(f1010,plain,(
% 2.73/0.77    k2_relat_1(sK1) = k9_relat_1(sK1,k10_relat_1(sK1,k2_relat_1(sK1)))),
% 2.73/0.77    inference(resolution,[],[f1008,f111])).
% 2.73/0.77  fof(f1008,plain,(
% 2.73/0.77    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK1)) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0) )),
% 2.73/0.77    inference(subsumption_resolution,[],[f1007,f47])).
% 2.73/0.77  fof(f1007,plain,(
% 2.73/0.77    ( ! [X0] : (~v1_relat_1(sK1) | ~r1_tarski(X0,k2_relat_1(sK1)) | k9_relat_1(sK1,k10_relat_1(sK1,X0)) = X0) )),
% 2.73/0.77    inference(resolution,[],[f77,f48])).
% 2.73/0.77  fof(f77,plain,(
% 2.73/0.77    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0) )),
% 2.73/0.77    inference(cnf_transformation,[],[f42])).
% 2.73/0.77  fof(f42,plain,(
% 2.73/0.77    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.73/0.77    inference(flattening,[],[f41])).
% 2.73/0.77  fof(f41,plain,(
% 2.73/0.77    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.73/0.77    inference(ennf_transformation,[],[f22])).
% 2.73/0.77  fof(f22,axiom,(
% 2.73/0.77    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 2.73/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 2.73/0.77  fof(f1552,plain,(
% 2.73/0.77    ( ! [X0] : (k10_relat_1(k6_relat_1(k9_relat_1(sK1,k1_relat_1(sK1))),X0) = k9_relat_1(sK1,k10_relat_1(sK1,X0))) )),
% 2.73/0.77    inference(subsumption_resolution,[],[f1551,f47])).
% 2.73/0.77  fof(f1551,plain,(
% 2.73/0.77    ( ! [X0] : (~v1_relat_1(sK1) | k10_relat_1(k6_relat_1(k9_relat_1(sK1,k1_relat_1(sK1))),X0) = k9_relat_1(sK1,k10_relat_1(sK1,X0))) )),
% 2.73/0.77    inference(resolution,[],[f220,f48])).
% 2.73/0.77  fof(f220,plain,(
% 2.73/0.77    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k10_relat_1(k6_relat_1(k9_relat_1(X1,k1_relat_1(X1))),X0)) )),
% 2.73/0.77    inference(backward_demodulation,[],[f101,f211])).
% 2.73/0.77  fof(f101,plain,(
% 2.73/0.77    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1))))) )),
% 2.73/0.77    inference(definition_unfolding,[],[f76,f94])).
% 2.73/0.77  fof(f76,plain,(
% 2.73/0.77    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))) )),
% 2.73/0.77    inference(cnf_transformation,[],[f40])).
% 2.73/0.77  fof(f40,plain,(
% 2.73/0.77    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.73/0.77    inference(flattening,[],[f39])).
% 2.73/0.77  fof(f39,plain,(
% 2.73/0.77    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.73/0.77    inference(ennf_transformation,[],[f23])).
% 2.73/0.77  fof(f23,axiom,(
% 2.73/0.77    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 2.73/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
% 2.73/0.77  fof(f2594,plain,(
% 2.73/0.77    ( ! [X2,X1] : (~r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X1)),k9_relat_1(sK1,X2)) | r1_tarski(k10_relat_1(sK1,X1),X2)) )),
% 2.73/0.77    inference(resolution,[],[f2592,f371])).
% 2.73/0.77  fof(f2592,plain,(
% 2.73/0.77    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(sK1)) | ~r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | r1_tarski(X0,X1)) )),
% 2.73/0.77    inference(subsumption_resolution,[],[f2591,f50])).
% 2.73/0.77  fof(f50,plain,(
% 2.73/0.77    v2_funct_1(sK1)),
% 2.73/0.77    inference(cnf_transformation,[],[f30])).
% 2.73/0.77  fof(f2591,plain,(
% 2.73/0.77    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~r1_tarski(X0,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | r1_tarski(X0,X1)) )),
% 2.73/0.77    inference(subsumption_resolution,[],[f2590,f47])).
% 2.73/0.77  fof(f2590,plain,(
% 2.73/0.77    ( ! [X0,X1] : (~v1_relat_1(sK1) | ~r1_tarski(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~r1_tarski(X0,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | r1_tarski(X0,X1)) )),
% 2.73/0.77    inference(resolution,[],[f86,f48])).
% 2.73/0.77  fof(f86,plain,(
% 2.73/0.77    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v2_funct_1(X2) | r1_tarski(X0,X1)) )),
% 2.73/0.77    inference(cnf_transformation,[],[f46])).
% 2.73/0.77  fof(f46,plain,(
% 2.73/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.73/0.77    inference(flattening,[],[f45])).
% 2.73/0.77  fof(f45,plain,(
% 2.73/0.77    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.73/0.77    inference(ennf_transformation,[],[f24])).
% 2.73/0.77  fof(f24,axiom,(
% 2.73/0.77    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 2.73/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).
% 2.73/0.77  % SZS output end Proof for theBenchmark
% 2.73/0.77  % (3555)------------------------------
% 2.73/0.77  % (3555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.73/0.77  % (3555)Termination reason: Refutation
% 2.73/0.77  
% 2.73/0.77  % (3555)Memory used [KB]: 8955
% 2.73/0.77  % (3555)Time elapsed: 0.362 s
% 2.73/0.77  % (3555)------------------------------
% 2.73/0.77  % (3555)------------------------------
% 2.73/0.77  % (3548)Success in time 0.409 s
%------------------------------------------------------------------------------
