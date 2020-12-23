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
% DateTime   : Thu Dec  3 12:53:57 EST 2020

% Result     : Theorem 6.03s
% Output     : Refutation 6.03s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 187 expanded)
%              Number of leaves         :   17 (  51 expanded)
%              Depth                    :   21
%              Number of atoms          :  216 ( 497 expanded)
%              Number of equality atoms :   77 ( 177 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15895,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f15882])).

fof(f15882,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f44,f15875])).

fof(f15875,plain,(
    sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f15874,f41])).

fof(f41,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0))
    & r1_tarski(sK0,k2_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k2_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0))
      & r1_tarski(sK0,k2_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f15874,plain,
    ( ~ v1_relat_1(sK1)
    | sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f15275,f42])).

fof(f42,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f15275,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f15219,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k9_relat_1(X0,k10_relat_1(X0,X1)))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k9_relat_1(X0,k10_relat_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f48,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f15219,plain,(
    r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f116,f15105])).

fof(f15105,plain,(
    sK0 = k1_setfam_1(k2_tarski(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0)) ),
    inference(superposition,[],[f15085,f137])).

fof(f137,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(forward_demodulation,[],[f72,f71])).

fof(f71,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f63,f65])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f61,f62,f62])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f72,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f64,f65,f65])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f15085,plain,(
    ! [X0] : sK0 = k6_subset_1(sK0,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) ),
    inference(resolution,[],[f5628,f41])).

fof(f5628,plain,(
    ! [X2] :
      ( ~ v1_relat_1(sK1)
      | sK0 = k6_subset_1(sK0,k6_subset_1(X2,k9_relat_1(sK1,k10_relat_1(sK1,X2)))) ) ),
    inference(trivial_inequality_removal,[],[f5616])).

fof(f5616,plain,(
    ! [X2] :
      ( k1_xboole_0 != k1_xboole_0
      | sK0 = k6_subset_1(sK0,k6_subset_1(X2,k9_relat_1(sK1,k10_relat_1(sK1,X2))))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f2150,f5330])).

fof(f5330,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) ),
    inference(resolution,[],[f660,f41])).

fof(f660,plain,(
    ! [X11] :
      ( ~ v1_relat_1(sK1)
      | k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X11,k9_relat_1(sK1,k10_relat_1(sK1,X11)))) ) ),
    inference(forward_demodulation,[],[f659,f162])).

fof(f162,plain,(
    ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    inference(resolution,[],[f161,f41])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f56,f42])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f659,plain,(
    ! [X11] :
      ( ~ v1_relat_1(sK1)
      | k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X11),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X11)))) ) ),
    inference(duplicate_literal_removal,[],[f655])).

fof(f655,plain,(
    ! [X11] :
      ( ~ v1_relat_1(sK1)
      | k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X11),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X11))))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f159,f105])).

fof(f105,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f50,f99])).

fof(f99,plain,(
    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(resolution,[],[f55,f41])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

fof(f159,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,k1_relat_1(X5))
      | ~ v1_relat_1(X5)
      | k1_xboole_0 = k6_subset_1(X4,k10_relat_1(X5,k9_relat_1(X5,X4))) ) ),
    inference(resolution,[],[f49,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f62])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f2150,plain,(
    ! [X0] :
      ( k1_xboole_0 != k10_relat_1(sK1,X0)
      | sK0 = k6_subset_1(sK0,X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f2125,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_relat_1(X1),X0)
      | k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f2125,plain,(
    ! [X44] :
      ( ~ r1_xboole_0(k2_relat_1(sK1),X44)
      | sK0 = k6_subset_1(sK0,X44) ) ),
    inference(trivial_inequality_removal,[],[f2123])).

fof(f2123,plain,(
    ! [X44] :
      ( k1_xboole_0 != k1_xboole_0
      | sK0 = k6_subset_1(sK0,X44)
      | ~ r1_xboole_0(k2_relat_1(sK1),X44) ) ),
    inference(superposition,[],[f336,f76])).

fof(f76,plain,(
    k1_xboole_0 = k6_subset_1(sK0,k2_relat_1(sK1)) ),
    inference(resolution,[],[f69,f43])).

fof(f43,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f336,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k6_subset_1(X2,X3)
      | k6_subset_1(X2,X4) = X2
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f95,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f62])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X0)
      | k6_subset_1(X2,X1) = X2 ) ),
    inference(resolution,[],[f51,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k6_subset_1(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f57,f62])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f116,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[],[f66,f71])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f52,f62])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f44,plain,(
    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (5148)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.49  % (5156)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.50  % (5140)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (5157)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (5150)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.33/0.52  % (5150)Refutation not found, incomplete strategy% (5150)------------------------------
% 1.33/0.52  % (5150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.52  % (5141)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.33/0.52  % (5150)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.52  
% 1.33/0.52  % (5150)Memory used [KB]: 10618
% 1.33/0.52  % (5150)Time elapsed: 0.080 s
% 1.33/0.52  % (5150)------------------------------
% 1.33/0.52  % (5150)------------------------------
% 1.33/0.53  % (5135)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.33/0.53  % (5135)Refutation not found, incomplete strategy% (5135)------------------------------
% 1.33/0.53  % (5135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (5135)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (5135)Memory used [KB]: 1663
% 1.33/0.53  % (5135)Time elapsed: 0.111 s
% 1.33/0.53  % (5135)------------------------------
% 1.33/0.53  % (5135)------------------------------
% 1.33/0.53  % (5162)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.33/0.53  % (5137)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.33/0.53  % (5134)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.33/0.53  % (5163)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.33/0.53  % (5163)Refutation not found, incomplete strategy% (5163)------------------------------
% 1.33/0.53  % (5163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (5163)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (5163)Memory used [KB]: 1663
% 1.33/0.53  % (5163)Time elapsed: 0.128 s
% 1.33/0.53  % (5163)------------------------------
% 1.33/0.53  % (5163)------------------------------
% 1.33/0.53  % (5138)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.33/0.53  % (5139)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.33/0.53  % (5161)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.33/0.54  % (5159)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.33/0.54  % (5153)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.33/0.54  % (5149)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.33/0.54  % (5151)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.46/0.54  % (5147)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.46/0.54  % (5155)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.46/0.54  % (5144)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.46/0.54  % (5146)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.46/0.54  % (5158)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.46/0.54  % (5142)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.46/0.55  % (5146)Refutation not found, incomplete strategy% (5146)------------------------------
% 1.46/0.55  % (5146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (5146)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (5146)Memory used [KB]: 10618
% 1.46/0.55  % (5146)Time elapsed: 0.136 s
% 1.46/0.55  % (5146)------------------------------
% 1.46/0.55  % (5146)------------------------------
% 1.46/0.55  % (5160)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.46/0.55  % (5154)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.46/0.55  % (5136)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.46/0.55  % (5145)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.46/0.56  % (5152)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.46/0.56  % (5143)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.46/0.60  % (5144)Refutation not found, incomplete strategy% (5144)------------------------------
% 1.46/0.60  % (5144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.60  % (5144)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.60  
% 1.46/0.60  % (5144)Memory used [KB]: 11129
% 1.46/0.60  % (5144)Time elapsed: 0.185 s
% 1.46/0.60  % (5144)------------------------------
% 1.46/0.60  % (5144)------------------------------
% 2.08/0.67  % (5170)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.08/0.67  % (5172)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.08/0.67  % (5134)Refutation not found, incomplete strategy% (5134)------------------------------
% 2.08/0.67  % (5134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.67  % (5171)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.08/0.67  % (5172)Refutation not found, incomplete strategy% (5172)------------------------------
% 2.08/0.67  % (5172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.68  % (5137)Refutation not found, incomplete strategy% (5137)------------------------------
% 2.08/0.68  % (5137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.68  % (5137)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.68  
% 2.08/0.68  % (5137)Memory used [KB]: 6140
% 2.08/0.68  % (5137)Time elapsed: 0.268 s
% 2.08/0.68  % (5137)------------------------------
% 2.08/0.68  % (5137)------------------------------
% 2.44/0.69  % (5172)Termination reason: Refutation not found, incomplete strategy
% 2.44/0.69  
% 2.44/0.69  % (5172)Memory used [KB]: 6140
% 2.44/0.69  % (5172)Time elapsed: 0.109 s
% 2.44/0.69  % (5172)------------------------------
% 2.44/0.69  % (5172)------------------------------
% 2.44/0.69  % (5134)Termination reason: Refutation not found, incomplete strategy
% 2.44/0.69  
% 2.44/0.69  % (5134)Memory used [KB]: 1663
% 2.44/0.69  % (5134)Time elapsed: 0.254 s
% 2.44/0.69  % (5134)------------------------------
% 2.44/0.69  % (5134)------------------------------
% 2.44/0.69  % (5149)Refutation not found, incomplete strategy% (5149)------------------------------
% 2.44/0.69  % (5149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.44/0.69  % (5149)Termination reason: Refutation not found, incomplete strategy
% 2.44/0.69  
% 2.44/0.69  % (5149)Memory used [KB]: 6140
% 2.44/0.69  % (5149)Time elapsed: 0.283 s
% 2.44/0.69  % (5149)------------------------------
% 2.44/0.69  % (5149)------------------------------
% 2.44/0.72  % (5174)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.44/0.74  % (5180)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 3.27/0.82  % (5183)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 3.27/0.82  % (5136)Time limit reached!
% 3.27/0.82  % (5136)------------------------------
% 3.27/0.82  % (5136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.27/0.82  % (5136)Termination reason: Time limit
% 3.27/0.82  % (5136)Termination phase: Saturation
% 3.27/0.82  
% 3.27/0.82  % (5136)Memory used [KB]: 6524
% 3.27/0.82  % (5136)Time elapsed: 0.400 s
% 3.27/0.82  % (5136)------------------------------
% 3.27/0.82  % (5136)------------------------------
% 3.27/0.82  % (5184)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 3.27/0.83  % (5182)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 3.27/0.83  % (5158)Time limit reached!
% 3.27/0.83  % (5158)------------------------------
% 3.27/0.83  % (5158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.47/0.84  % (5158)Termination reason: Time limit
% 3.47/0.84  % (5158)Termination phase: Saturation
% 3.47/0.84  
% 3.47/0.84  % (5158)Memory used [KB]: 14328
% 3.47/0.84  % (5158)Time elapsed: 0.400 s
% 3.47/0.84  % (5158)------------------------------
% 3.47/0.84  % (5158)------------------------------
% 3.47/0.85  % (5185)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 3.47/0.91  % (5148)Time limit reached!
% 3.47/0.91  % (5148)------------------------------
% 3.47/0.91  % (5148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.47/0.91  % (5140)Time limit reached!
% 3.47/0.91  % (5140)------------------------------
% 3.47/0.91  % (5140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.47/0.91  % (5140)Termination reason: Time limit
% 3.47/0.91  
% 3.47/0.91  % (5140)Memory used [KB]: 15479
% 3.47/0.91  % (5140)Time elapsed: 0.505 s
% 3.47/0.91  % (5140)------------------------------
% 3.47/0.91  % (5140)------------------------------
% 3.47/0.92  % (5148)Termination reason: Time limit
% 3.47/0.92  
% 3.47/0.92  % (5148)Memory used [KB]: 6268
% 3.47/0.92  % (5148)Time elapsed: 0.506 s
% 3.47/0.92  % (5148)------------------------------
% 3.47/0.92  % (5148)------------------------------
% 3.93/0.93  % (5235)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 4.22/0.98  % (5241)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 4.22/1.04  % (5141)Time limit reached!
% 4.22/1.04  % (5141)------------------------------
% 4.22/1.04  % (5141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.22/1.04  % (5141)Termination reason: Time limit
% 4.22/1.04  
% 4.22/1.04  % (5141)Memory used [KB]: 6012
% 4.22/1.04  % (5141)Time elapsed: 0.602 s
% 4.22/1.04  % (5141)------------------------------
% 4.22/1.04  % (5141)------------------------------
% 4.22/1.05  % (5289)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 4.22/1.05  % (5290)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 6.03/1.13  % (5139)Refutation found. Thanks to Tanya!
% 6.03/1.13  % SZS status Theorem for theBenchmark
% 6.03/1.13  % SZS output start Proof for theBenchmark
% 6.03/1.13  fof(f15895,plain,(
% 6.03/1.13    $false),
% 6.03/1.13    inference(trivial_inequality_removal,[],[f15882])).
% 6.03/1.13  fof(f15882,plain,(
% 6.03/1.13    sK0 != sK0),
% 6.03/1.13    inference(superposition,[],[f44,f15875])).
% 6.03/1.13  fof(f15875,plain,(
% 6.03/1.13    sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0))),
% 6.03/1.13    inference(resolution,[],[f15874,f41])).
% 6.03/1.13  fof(f41,plain,(
% 6.03/1.13    v1_relat_1(sK1)),
% 6.03/1.13    inference(cnf_transformation,[],[f35])).
% 6.03/1.13  fof(f35,plain,(
% 6.03/1.13    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) & r1_tarski(sK0,k2_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 6.03/1.13    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f34])).
% 6.03/1.13  fof(f34,plain,(
% 6.03/1.13    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) & r1_tarski(sK0,k2_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 6.03/1.13    introduced(choice_axiom,[])).
% 6.03/1.13  fof(f22,plain,(
% 6.03/1.13    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 6.03/1.13    inference(flattening,[],[f21])).
% 6.03/1.13  fof(f21,plain,(
% 6.03/1.13    ? [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 6.03/1.13    inference(ennf_transformation,[],[f20])).
% 6.03/1.13  fof(f20,negated_conjecture,(
% 6.03/1.13    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 6.03/1.13    inference(negated_conjecture,[],[f19])).
% 6.03/1.13  fof(f19,conjecture,(
% 6.03/1.13    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 6.03/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 6.03/1.13  fof(f15874,plain,(
% 6.03/1.13    ~v1_relat_1(sK1) | sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0))),
% 6.03/1.13    inference(resolution,[],[f15275,f42])).
% 6.03/1.13  fof(f42,plain,(
% 6.03/1.13    v1_funct_1(sK1)),
% 6.03/1.13    inference(cnf_transformation,[],[f35])).
% 6.03/1.13  fof(f15275,plain,(
% 6.03/1.13    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0))),
% 6.03/1.13    inference(resolution,[],[f15219,f120])).
% 6.03/1.13  fof(f120,plain,(
% 6.03/1.13    ( ! [X0,X1] : (~r1_tarski(X1,k9_relat_1(X0,k10_relat_1(X0,X1))) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k9_relat_1(X0,k10_relat_1(X0,X1)) = X1) )),
% 6.03/1.13    inference(resolution,[],[f48,f47])).
% 6.03/1.13  fof(f47,plain,(
% 6.03/1.13    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 6.03/1.13    inference(cnf_transformation,[],[f37])).
% 6.03/1.13  fof(f37,plain,(
% 6.03/1.13    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.03/1.13    inference(flattening,[],[f36])).
% 6.03/1.13  fof(f36,plain,(
% 6.03/1.13    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.03/1.13    inference(nnf_transformation,[],[f2])).
% 6.03/1.13  fof(f2,axiom,(
% 6.03/1.13    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.03/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.03/1.13  fof(f48,plain,(
% 6.03/1.13    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.03/1.13    inference(cnf_transformation,[],[f24])).
% 6.03/1.13  fof(f24,plain,(
% 6.03/1.13    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 6.03/1.13    inference(flattening,[],[f23])).
% 6.03/1.13  fof(f23,plain,(
% 6.03/1.13    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 6.03/1.13    inference(ennf_transformation,[],[f17])).
% 6.03/1.13  fof(f17,axiom,(
% 6.03/1.13    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 6.03/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 6.03/1.13  fof(f15219,plain,(
% 6.03/1.13    r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 6.03/1.13    inference(superposition,[],[f116,f15105])).
% 6.03/1.13  fof(f15105,plain,(
% 6.03/1.13    sK0 = k1_setfam_1(k2_tarski(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0))),
% 6.03/1.13    inference(superposition,[],[f15085,f137])).
% 6.03/1.13  fof(f137,plain,(
% 6.03/1.13    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 6.03/1.13    inference(forward_demodulation,[],[f72,f71])).
% 6.03/1.13  fof(f71,plain,(
% 6.03/1.13    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 6.03/1.13    inference(definition_unfolding,[],[f63,f65])).
% 6.03/1.13  fof(f65,plain,(
% 6.03/1.13    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 6.03/1.13    inference(definition_unfolding,[],[f61,f62,f62])).
% 6.03/1.13  fof(f62,plain,(
% 6.03/1.13    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 6.03/1.13    inference(cnf_transformation,[],[f11])).
% 6.03/1.13  fof(f11,axiom,(
% 6.03/1.13    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 6.03/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 6.03/1.13  fof(f61,plain,(
% 6.03/1.13    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.03/1.13    inference(cnf_transformation,[],[f5])).
% 6.03/1.13  fof(f5,axiom,(
% 6.03/1.13    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.03/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 6.03/1.13  fof(f63,plain,(
% 6.03/1.13    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 6.03/1.13    inference(cnf_transformation,[],[f12])).
% 6.03/1.13  fof(f12,axiom,(
% 6.03/1.13    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 6.03/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 6.03/1.13  fof(f72,plain,(
% 6.03/1.13    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0))) )),
% 6.03/1.13    inference(definition_unfolding,[],[f64,f65,f65])).
% 6.03/1.13  fof(f64,plain,(
% 6.03/1.13    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.03/1.13    inference(cnf_transformation,[],[f1])).
% 6.03/1.13  fof(f1,axiom,(
% 6.03/1.13    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.03/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 6.03/1.13  fof(f15085,plain,(
% 6.03/1.13    ( ! [X0] : (sK0 = k6_subset_1(sK0,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) )),
% 6.03/1.13    inference(resolution,[],[f5628,f41])).
% 6.03/1.13  fof(f5628,plain,(
% 6.03/1.13    ( ! [X2] : (~v1_relat_1(sK1) | sK0 = k6_subset_1(sK0,k6_subset_1(X2,k9_relat_1(sK1,k10_relat_1(sK1,X2))))) )),
% 6.03/1.13    inference(trivial_inequality_removal,[],[f5616])).
% 6.03/1.13  fof(f5616,plain,(
% 6.03/1.13    ( ! [X2] : (k1_xboole_0 != k1_xboole_0 | sK0 = k6_subset_1(sK0,k6_subset_1(X2,k9_relat_1(sK1,k10_relat_1(sK1,X2)))) | ~v1_relat_1(sK1)) )),
% 6.03/1.13    inference(superposition,[],[f2150,f5330])).
% 6.03/1.13  fof(f5330,plain,(
% 6.03/1.13    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) )),
% 6.03/1.13    inference(resolution,[],[f660,f41])).
% 6.03/1.13  fof(f660,plain,(
% 6.03/1.13    ( ! [X11] : (~v1_relat_1(sK1) | k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X11,k9_relat_1(sK1,k10_relat_1(sK1,X11))))) )),
% 6.03/1.13    inference(forward_demodulation,[],[f659,f162])).
% 6.03/1.13  fof(f162,plain,(
% 6.03/1.13    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 6.03/1.13    inference(resolution,[],[f161,f41])).
% 6.03/1.13  fof(f161,plain,(
% 6.03/1.13    ( ! [X0,X1] : (~v1_relat_1(sK1) | k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 6.03/1.13    inference(resolution,[],[f56,f42])).
% 6.03/1.13  fof(f56,plain,(
% 6.03/1.13    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 6.03/1.13    inference(cnf_transformation,[],[f33])).
% 6.03/1.13  fof(f33,plain,(
% 6.03/1.13    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 6.03/1.13    inference(flattening,[],[f32])).
% 6.03/1.13  fof(f32,plain,(
% 6.03/1.13    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 6.03/1.13    inference(ennf_transformation,[],[f16])).
% 6.03/1.13  fof(f16,axiom,(
% 6.03/1.13    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 6.03/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 6.03/1.13  fof(f659,plain,(
% 6.03/1.13    ( ! [X11] : (~v1_relat_1(sK1) | k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X11),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X11))))) )),
% 6.03/1.13    inference(duplicate_literal_removal,[],[f655])).
% 6.03/1.13  fof(f655,plain,(
% 6.03/1.13    ( ! [X11] : (~v1_relat_1(sK1) | k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X11),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X11)))) | ~v1_relat_1(sK1)) )),
% 6.03/1.13    inference(resolution,[],[f159,f105])).
% 6.03/1.13  fof(f105,plain,(
% 6.03/1.13    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 6.03/1.13    inference(superposition,[],[f50,f99])).
% 6.03/1.13  fof(f99,plain,(
% 6.03/1.13    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1)),
% 6.03/1.13    inference(resolution,[],[f55,f41])).
% 6.03/1.13  fof(f55,plain,(
% 6.03/1.13    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 6.03/1.13    inference(cnf_transformation,[],[f31])).
% 6.03/1.13  fof(f31,plain,(
% 6.03/1.13    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 6.03/1.13    inference(ennf_transformation,[],[f13])).
% 6.03/1.13  fof(f13,axiom,(
% 6.03/1.13    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 6.03/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 6.03/1.13  fof(f50,plain,(
% 6.03/1.13    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 6.03/1.13    inference(cnf_transformation,[],[f27])).
% 6.03/1.13  fof(f27,plain,(
% 6.03/1.13    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 6.03/1.13    inference(ennf_transformation,[],[f14])).
% 6.03/1.13  fof(f14,axiom,(
% 6.03/1.13    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 6.03/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).
% 6.03/1.13  fof(f159,plain,(
% 6.03/1.13    ( ! [X4,X5] : (~r1_tarski(X4,k1_relat_1(X5)) | ~v1_relat_1(X5) | k1_xboole_0 = k6_subset_1(X4,k10_relat_1(X5,k9_relat_1(X5,X4)))) )),
% 6.03/1.13    inference(resolution,[],[f49,f69])).
% 6.03/1.13  fof(f69,plain,(
% 6.03/1.13    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 6.03/1.13    inference(definition_unfolding,[],[f60,f62])).
% 6.03/1.13  fof(f60,plain,(
% 6.03/1.13    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 6.03/1.13    inference(cnf_transformation,[],[f40])).
% 6.03/1.13  fof(f40,plain,(
% 6.03/1.13    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 6.03/1.13    inference(nnf_transformation,[],[f3])).
% 6.03/1.13  fof(f3,axiom,(
% 6.03/1.13    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 6.03/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 6.03/1.13  fof(f49,plain,(
% 6.03/1.13    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 6.03/1.13    inference(cnf_transformation,[],[f26])).
% 6.03/1.13  fof(f26,plain,(
% 6.03/1.13    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 6.03/1.13    inference(flattening,[],[f25])).
% 6.03/1.13  fof(f25,plain,(
% 6.03/1.13    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 6.03/1.13    inference(ennf_transformation,[],[f18])).
% 6.03/1.13  fof(f18,axiom,(
% 6.03/1.13    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 6.03/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 6.03/1.13  fof(f2150,plain,(
% 6.03/1.13    ( ! [X0] : (k1_xboole_0 != k10_relat_1(sK1,X0) | sK0 = k6_subset_1(sK0,X0) | ~v1_relat_1(sK1)) )),
% 6.03/1.13    inference(resolution,[],[f2125,f53])).
% 6.03/1.13  fof(f53,plain,(
% 6.03/1.13    ( ! [X0,X1] : (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.03/1.13    inference(cnf_transformation,[],[f38])).
% 6.03/1.13  fof(f38,plain,(
% 6.03/1.13    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 6.03/1.13    inference(nnf_transformation,[],[f30])).
% 6.03/1.13  fof(f30,plain,(
% 6.03/1.13    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.03/1.13    inference(ennf_transformation,[],[f15])).
% 6.03/1.13  fof(f15,axiom,(
% 6.03/1.13    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 6.03/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 6.03/1.13  fof(f2125,plain,(
% 6.03/1.13    ( ! [X44] : (~r1_xboole_0(k2_relat_1(sK1),X44) | sK0 = k6_subset_1(sK0,X44)) )),
% 6.03/1.13    inference(trivial_inequality_removal,[],[f2123])).
% 6.03/1.13  fof(f2123,plain,(
% 6.03/1.13    ( ! [X44] : (k1_xboole_0 != k1_xboole_0 | sK0 = k6_subset_1(sK0,X44) | ~r1_xboole_0(k2_relat_1(sK1),X44)) )),
% 6.03/1.13    inference(superposition,[],[f336,f76])).
% 6.03/1.13  fof(f76,plain,(
% 6.03/1.13    k1_xboole_0 = k6_subset_1(sK0,k2_relat_1(sK1))),
% 6.03/1.13    inference(resolution,[],[f69,f43])).
% 6.03/1.13  fof(f43,plain,(
% 6.03/1.13    r1_tarski(sK0,k2_relat_1(sK1))),
% 6.03/1.13    inference(cnf_transformation,[],[f35])).
% 6.03/1.13  fof(f336,plain,(
% 6.03/1.13    ( ! [X4,X2,X3] : (k1_xboole_0 != k6_subset_1(X2,X3) | k6_subset_1(X2,X4) = X2 | ~r1_xboole_0(X3,X4)) )),
% 6.03/1.13    inference(resolution,[],[f95,f70])).
% 6.03/1.13  fof(f70,plain,(
% 6.03/1.13    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 6.03/1.13    inference(definition_unfolding,[],[f59,f62])).
% 6.03/1.13  fof(f59,plain,(
% 6.03/1.13    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 6.03/1.13    inference(cnf_transformation,[],[f40])).
% 6.03/1.13  fof(f95,plain,(
% 6.03/1.13    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X0) | k6_subset_1(X2,X1) = X2) )),
% 6.03/1.13    inference(resolution,[],[f51,f68])).
% 6.03/1.13  fof(f68,plain,(
% 6.03/1.13    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k6_subset_1(X0,X1) = X0) )),
% 6.03/1.13    inference(definition_unfolding,[],[f57,f62])).
% 6.03/1.13  fof(f57,plain,(
% 6.03/1.13    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 6.03/1.13    inference(cnf_transformation,[],[f39])).
% 6.03/1.13  fof(f39,plain,(
% 6.03/1.13    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 6.03/1.13    inference(nnf_transformation,[],[f7])).
% 6.03/1.13  fof(f7,axiom,(
% 6.03/1.13    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 6.03/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 6.03/1.13  fof(f51,plain,(
% 6.03/1.13    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 6.03/1.13    inference(cnf_transformation,[],[f29])).
% 6.03/1.13  fof(f29,plain,(
% 6.03/1.13    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 6.03/1.13    inference(flattening,[],[f28])).
% 6.03/1.13  fof(f28,plain,(
% 6.03/1.13    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 6.03/1.13    inference(ennf_transformation,[],[f6])).
% 6.03/1.13  fof(f6,axiom,(
% 6.03/1.13    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 6.03/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 6.03/1.13  fof(f116,plain,(
% 6.03/1.13    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 6.03/1.13    inference(superposition,[],[f66,f71])).
% 6.03/1.13  fof(f66,plain,(
% 6.03/1.13    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 6.03/1.13    inference(definition_unfolding,[],[f52,f62])).
% 6.03/1.13  fof(f52,plain,(
% 6.03/1.13    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 6.03/1.13    inference(cnf_transformation,[],[f4])).
% 6.03/1.13  fof(f4,axiom,(
% 6.03/1.13    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 6.03/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 6.03/1.13  fof(f44,plain,(
% 6.03/1.13    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0))),
% 6.03/1.13    inference(cnf_transformation,[],[f35])).
% 6.03/1.13  % SZS output end Proof for theBenchmark
% 6.03/1.13  % (5139)------------------------------
% 6.03/1.13  % (5139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.03/1.13  % (5139)Termination reason: Refutation
% 6.03/1.13  
% 6.03/1.13  % (5139)Memory used [KB]: 7803
% 6.03/1.13  % (5139)Time elapsed: 0.714 s
% 6.03/1.13  % (5139)------------------------------
% 6.03/1.13  % (5139)------------------------------
% 6.03/1.13  % (5133)Success in time 0.772 s
%------------------------------------------------------------------------------
