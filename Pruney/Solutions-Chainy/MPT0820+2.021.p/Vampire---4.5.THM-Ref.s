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
% DateTime   : Thu Dec  3 12:56:22 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 299 expanded)
%              Number of leaves         :   18 (  95 expanded)
%              Depth                    :   19
%              Number of atoms          :  149 ( 438 expanded)
%              Number of equality atoms :   45 ( 200 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5065,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5063,f54])).

fof(f54,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f32,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f32,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

fof(f5063,plain,(
    r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    inference(superposition,[],[f5013,f109])).

fof(f109,plain,(
    sK1 = k3_tarski(k1_enumset1(sK1,sK1,k2_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f104,f105])).

fof(f105,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f101,f55])).

fof(f55,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f34,f53])).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f101,plain,(
    ! [X1] : k3_tarski(k1_enumset1(X1,X1,k1_xboole_0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f59,f63])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f48,f33])).

fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f53])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f104,plain,(
    k3_tarski(k1_enumset1(sK1,sK1,k2_relat_1(sK2))) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f59,f79])).

fof(f79,plain,(
    k1_xboole_0 = k4_xboole_0(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f77,f48])).

fof(f77,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(subsumption_resolution,[],[f76,f66])).

fof(f66,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f62,f31])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f36,f37])).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f76,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f75,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f75,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f52,f31])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f5013,plain,(
    ! [X0] : r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(X0,X0,k2_relat_1(sK2)))))) ),
    inference(superposition,[],[f4756,f57])).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f38,f39,f39])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f4756,plain,(
    ! [X0] : r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0))))) ),
    inference(forward_demodulation,[],[f4755,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1)),X2)) = k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X1,X1,X2)))) ),
    inference(definition_unfolding,[],[f49,f53,f53,f53,f53])).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f4755,plain,(
    ! [X0] : r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(sK0,sK0,k2_relat_1(sK2))),k3_tarski(k1_enumset1(sK0,sK0,k2_relat_1(sK2))),X0))) ),
    inference(subsumption_resolution,[],[f4743,f33])).

fof(f4743,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(sK0,sK0,k2_relat_1(sK2))),k3_tarski(k1_enumset1(sK0,sK0,k2_relat_1(sK2))),X0))) ) ),
    inference(superposition,[],[f61,f4697])).

fof(f4697,plain,(
    k1_xboole_0 = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,k2_relat_1(sK2)))) ),
    inference(superposition,[],[f192,f4551])).

fof(f4551,plain,(
    k3_tarski(k1_enumset1(sK0,sK0,k3_relat_1(sK2))) = k3_tarski(k1_enumset1(sK0,sK0,k2_relat_1(sK2))) ),
    inference(superposition,[],[f3566,f1125])).

fof(f1125,plain,(
    k3_relat_1(sK2) = k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(resolution,[],[f56,f66])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f35,f53])).

fof(f35,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f3566,plain,(
    ! [X19] : k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X19)))) = k3_tarski(k1_enumset1(sK0,sK0,X19)) ),
    inference(superposition,[],[f60,f108])).

fof(f108,plain,(
    sK0 = k3_tarski(k1_enumset1(sK0,sK0,k1_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f103,f105])).

fof(f103,plain,(
    k3_tarski(k1_enumset1(sK0,sK0,k1_relat_1(sK2))) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f59,f72])).

fof(f72,plain,(
    k1_xboole_0 = k4_xboole_0(k1_relat_1(sK2),sK0) ),
    inference(resolution,[],[f70,f48])).

fof(f70,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f69,f66])).

fof(f69,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f68,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f68,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f51,f31])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f192,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X0))) ),
    inference(resolution,[],[f185,f48])).

fof(f185,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0))) ),
    inference(superposition,[],[f128,f57])).

fof(f128,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(subsumption_resolution,[],[f122,f33])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ) ),
    inference(superposition,[],[f61,f90])).

fof(f90,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f88,f63])).

fof(f88,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f58,f82])).

fof(f82,plain,(
    ! [X0] : k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f55,f57])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),X1) ),
    inference(definition_unfolding,[],[f41,f53])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f50,f53])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:02:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (12054)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (12067)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (12058)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (12062)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (12059)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (12057)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (12061)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (12066)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (12055)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (12056)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (12063)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (12060)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (12053)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.50  % (12064)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (12069)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  % (12070)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (12068)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (12065)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 2.21/0.64  % (12067)Refutation found. Thanks to Tanya!
% 2.21/0.64  % SZS status Theorem for theBenchmark
% 2.21/0.64  % SZS output start Proof for theBenchmark
% 2.21/0.64  fof(f5065,plain,(
% 2.21/0.64    $false),
% 2.21/0.64    inference(subsumption_resolution,[],[f5063,f54])).
% 2.21/0.64  fof(f54,plain,(
% 2.21/0.64    ~r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 2.21/0.64    inference(definition_unfolding,[],[f32,f53])).
% 2.21/0.64  fof(f53,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.21/0.64    inference(definition_unfolding,[],[f40,f39])).
% 2.21/0.64  fof(f39,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f9])).
% 2.21/0.64  fof(f9,axiom,(
% 2.21/0.64    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.21/0.64  fof(f40,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.21/0.64    inference(cnf_transformation,[],[f10])).
% 2.21/0.64  fof(f10,axiom,(
% 2.21/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.21/0.64  fof(f32,plain,(
% 2.21/0.64    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 2.21/0.64    inference(cnf_transformation,[],[f27])).
% 2.21/0.64  fof(f27,plain,(
% 2.21/0.64    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.21/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f26])).
% 2.21/0.64  fof(f26,plain,(
% 2.21/0.64    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 2.21/0.64    introduced(choice_axiom,[])).
% 2.21/0.64  fof(f19,plain,(
% 2.21/0.64    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/0.64    inference(ennf_transformation,[],[f18])).
% 2.21/0.64  fof(f18,negated_conjecture,(
% 2.21/0.64    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 2.21/0.64    inference(negated_conjecture,[],[f17])).
% 2.21/0.64  fof(f17,conjecture,(
% 2.21/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).
% 2.21/0.64  fof(f5063,plain,(
% 2.21/0.64    r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 2.21/0.64    inference(superposition,[],[f5013,f109])).
% 2.21/0.64  fof(f109,plain,(
% 2.21/0.64    sK1 = k3_tarski(k1_enumset1(sK1,sK1,k2_relat_1(sK2)))),
% 2.21/0.64    inference(forward_demodulation,[],[f104,f105])).
% 2.21/0.64  fof(f105,plain,(
% 2.21/0.64    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1) )),
% 2.21/0.64    inference(forward_demodulation,[],[f101,f55])).
% 2.21/0.64  fof(f55,plain,(
% 2.21/0.64    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 2.21/0.64    inference(definition_unfolding,[],[f34,f53])).
% 2.21/0.64  fof(f34,plain,(
% 2.21/0.64    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.21/0.64    inference(cnf_transformation,[],[f2])).
% 2.21/0.64  fof(f2,axiom,(
% 2.21/0.64    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.21/0.64  fof(f101,plain,(
% 2.21/0.64    ( ! [X1] : (k3_tarski(k1_enumset1(X1,X1,k1_xboole_0)) = k5_xboole_0(X1,k1_xboole_0)) )),
% 2.21/0.64    inference(superposition,[],[f59,f63])).
% 2.21/0.64  fof(f63,plain,(
% 2.21/0.64    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.21/0.64    inference(resolution,[],[f48,f33])).
% 2.21/0.64  fof(f33,plain,(
% 2.21/0.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f3])).
% 2.21/0.64  fof(f3,axiom,(
% 2.21/0.64    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.21/0.64  fof(f48,plain,(
% 2.21/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.21/0.64    inference(cnf_transformation,[],[f30])).
% 2.21/0.64  fof(f30,plain,(
% 2.21/0.64    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.21/0.64    inference(nnf_transformation,[],[f1])).
% 2.21/0.64  fof(f1,axiom,(
% 2.21/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.21/0.64  fof(f59,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.21/0.64    inference(definition_unfolding,[],[f42,f53])).
% 2.21/0.64  fof(f42,plain,(
% 2.21/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.21/0.64    inference(cnf_transformation,[],[f7])).
% 2.21/0.64  fof(f7,axiom,(
% 2.21/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.21/0.64  fof(f104,plain,(
% 2.21/0.64    k3_tarski(k1_enumset1(sK1,sK1,k2_relat_1(sK2))) = k5_xboole_0(sK1,k1_xboole_0)),
% 2.21/0.64    inference(superposition,[],[f59,f79])).
% 2.21/0.64  fof(f79,plain,(
% 2.21/0.64    k1_xboole_0 = k4_xboole_0(k2_relat_1(sK2),sK1)),
% 2.21/0.64    inference(resolution,[],[f77,f48])).
% 2.21/0.64  fof(f77,plain,(
% 2.21/0.64    r1_tarski(k2_relat_1(sK2),sK1)),
% 2.21/0.64    inference(subsumption_resolution,[],[f76,f66])).
% 2.21/0.64  fof(f66,plain,(
% 2.21/0.64    v1_relat_1(sK2)),
% 2.21/0.64    inference(resolution,[],[f62,f31])).
% 2.21/0.64  fof(f31,plain,(
% 2.21/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.21/0.64    inference(cnf_transformation,[],[f27])).
% 2.21/0.64  fof(f62,plain,(
% 2.21/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 2.21/0.64    inference(resolution,[],[f36,f37])).
% 2.21/0.64  fof(f37,plain,(
% 2.21/0.64    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.21/0.64    inference(cnf_transformation,[],[f15])).
% 2.21/0.64  fof(f15,axiom,(
% 2.21/0.64    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.21/0.64  fof(f36,plain,(
% 2.21/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f21])).
% 2.21/0.64  fof(f21,plain,(
% 2.21/0.64    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.21/0.64    inference(ennf_transformation,[],[f11])).
% 2.21/0.64  fof(f11,axiom,(
% 2.21/0.64    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.21/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.21/0.64  fof(f76,plain,(
% 2.21/0.64    r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(sK2)),
% 2.21/0.64    inference(resolution,[],[f75,f45])).
% 2.21/0.64  fof(f45,plain,(
% 2.21/0.64    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.21/0.64    inference(cnf_transformation,[],[f29])).
% 2.21/0.65  fof(f29,plain,(
% 2.21/0.65    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.21/0.65    inference(nnf_transformation,[],[f23])).
% 2.21/0.65  fof(f23,plain,(
% 2.21/0.65    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.21/0.65    inference(ennf_transformation,[],[f13])).
% 2.21/0.65  fof(f13,axiom,(
% 2.21/0.65    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 2.21/0.65  fof(f75,plain,(
% 2.21/0.65    v5_relat_1(sK2,sK1)),
% 2.21/0.65    inference(resolution,[],[f52,f31])).
% 2.21/0.65  fof(f52,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f25])).
% 2.21/0.65  fof(f25,plain,(
% 2.21/0.65    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/0.65    inference(ennf_transformation,[],[f16])).
% 2.21/0.65  fof(f16,axiom,(
% 2.21/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.21/0.65  fof(f5013,plain,(
% 2.21/0.65    ( ! [X0] : (r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(X0,X0,k2_relat_1(sK2))))))) )),
% 2.21/0.65    inference(superposition,[],[f4756,f57])).
% 2.21/0.65  fof(f57,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 2.21/0.65    inference(definition_unfolding,[],[f38,f39,f39])).
% 2.21/0.65  fof(f38,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f8])).
% 2.21/0.65  fof(f8,axiom,(
% 2.21/0.65    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.21/0.65  fof(f4756,plain,(
% 2.21/0.65    ( ! [X0] : (r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),X0)))))) )),
% 2.21/0.65    inference(forward_demodulation,[],[f4755,f60])).
% 2.21/0.65  fof(f60,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(X0,X0,X1)),k3_tarski(k1_enumset1(X0,X0,X1)),X2)) = k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X1,X1,X2))))) )),
% 2.21/0.65    inference(definition_unfolding,[],[f49,f53,f53,f53,f53])).
% 2.21/0.65  fof(f49,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.21/0.65    inference(cnf_transformation,[],[f6])).
% 2.21/0.65  fof(f6,axiom,(
% 2.21/0.65    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 2.21/0.65  fof(f4755,plain,(
% 2.21/0.65    ( ! [X0] : (r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(sK0,sK0,k2_relat_1(sK2))),k3_tarski(k1_enumset1(sK0,sK0,k2_relat_1(sK2))),X0)))) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f4743,f33])).
% 2.21/0.65  fof(f4743,plain,(
% 2.21/0.65    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(sK0,sK0,k2_relat_1(sK2))),k3_tarski(k1_enumset1(sK0,sK0,k2_relat_1(sK2))),X0)))) )),
% 2.21/0.65    inference(superposition,[],[f61,f4697])).
% 2.21/0.65  fof(f4697,plain,(
% 2.21/0.65    k1_xboole_0 = k4_xboole_0(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,k2_relat_1(sK2))))),
% 2.21/0.65    inference(superposition,[],[f192,f4551])).
% 2.21/0.65  fof(f4551,plain,(
% 2.21/0.65    k3_tarski(k1_enumset1(sK0,sK0,k3_relat_1(sK2))) = k3_tarski(k1_enumset1(sK0,sK0,k2_relat_1(sK2)))),
% 2.21/0.65    inference(superposition,[],[f3566,f1125])).
% 2.21/0.65  fof(f1125,plain,(
% 2.21/0.65    k3_relat_1(sK2) = k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2)))),
% 2.21/0.65    inference(resolution,[],[f56,f66])).
% 2.21/0.65  fof(f56,plain,(
% 2.21/0.65    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 2.21/0.65    inference(definition_unfolding,[],[f35,f53])).
% 2.21/0.65  fof(f35,plain,(
% 2.21/0.65    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f20])).
% 2.21/0.65  fof(f20,plain,(
% 2.21/0.65    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.21/0.65    inference(ennf_transformation,[],[f14])).
% 2.21/0.65  fof(f14,axiom,(
% 2.21/0.65    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 2.21/0.65  fof(f3566,plain,(
% 2.21/0.65    ( ! [X19] : (k3_tarski(k1_enumset1(sK0,sK0,k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X19)))) = k3_tarski(k1_enumset1(sK0,sK0,X19))) )),
% 2.21/0.65    inference(superposition,[],[f60,f108])).
% 2.21/0.65  fof(f108,plain,(
% 2.21/0.65    sK0 = k3_tarski(k1_enumset1(sK0,sK0,k1_relat_1(sK2)))),
% 2.21/0.65    inference(forward_demodulation,[],[f103,f105])).
% 2.21/0.65  fof(f103,plain,(
% 2.21/0.65    k3_tarski(k1_enumset1(sK0,sK0,k1_relat_1(sK2))) = k5_xboole_0(sK0,k1_xboole_0)),
% 2.21/0.65    inference(superposition,[],[f59,f72])).
% 2.21/0.65  fof(f72,plain,(
% 2.21/0.65    k1_xboole_0 = k4_xboole_0(k1_relat_1(sK2),sK0)),
% 2.21/0.65    inference(resolution,[],[f70,f48])).
% 2.21/0.65  fof(f70,plain,(
% 2.21/0.65    r1_tarski(k1_relat_1(sK2),sK0)),
% 2.21/0.65    inference(subsumption_resolution,[],[f69,f66])).
% 2.21/0.65  fof(f69,plain,(
% 2.21/0.65    r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2)),
% 2.21/0.65    inference(resolution,[],[f68,f43])).
% 2.21/0.65  fof(f43,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f28])).
% 2.21/0.65  fof(f28,plain,(
% 2.21/0.65    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.21/0.65    inference(nnf_transformation,[],[f22])).
% 2.21/0.65  fof(f22,plain,(
% 2.21/0.65    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.21/0.65    inference(ennf_transformation,[],[f12])).
% 2.21/0.65  fof(f12,axiom,(
% 2.21/0.65    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 2.21/0.65  fof(f68,plain,(
% 2.21/0.65    v4_relat_1(sK2,sK0)),
% 2.21/0.65    inference(resolution,[],[f51,f31])).
% 2.21/0.65  fof(f51,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f25])).
% 2.21/0.65  fof(f192,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k1_enumset1(X1,X1,X0)))) )),
% 2.21/0.65    inference(resolution,[],[f185,f48])).
% 2.21/0.65  fof(f185,plain,(
% 2.21/0.65    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0)))) )),
% 2.21/0.65    inference(superposition,[],[f128,f57])).
% 2.21/0.65  fof(f128,plain,(
% 2.21/0.65    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 2.21/0.65    inference(subsumption_resolution,[],[f122,f33])).
% 2.21/0.65  fof(f122,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X1) | r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 2.21/0.65    inference(superposition,[],[f61,f90])).
% 2.21/0.65  fof(f90,plain,(
% 2.21/0.65    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 2.21/0.65    inference(forward_demodulation,[],[f88,f63])).
% 2.21/0.65  fof(f88,plain,(
% 2.21/0.65    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X1,X1)) )),
% 2.21/0.65    inference(superposition,[],[f58,f82])).
% 2.21/0.65  fof(f82,plain,(
% 2.21/0.65    ( ! [X0] : (k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 2.21/0.65    inference(superposition,[],[f55,f57])).
% 2.21/0.65  fof(f58,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),X1)) )),
% 2.21/0.65    inference(definition_unfolding,[],[f41,f53])).
% 2.21/0.65  fof(f41,plain,(
% 2.21/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f4])).
% 2.21/0.65  fof(f4,axiom,(
% 2.21/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.21/0.65  fof(f61,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) )),
% 2.21/0.65    inference(definition_unfolding,[],[f50,f53])).
% 2.21/0.65  fof(f50,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f24])).
% 2.21/0.65  fof(f24,plain,(
% 2.21/0.65    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.21/0.65    inference(ennf_transformation,[],[f5])).
% 2.21/0.65  fof(f5,axiom,(
% 2.21/0.65    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.21/0.65  % SZS output end Proof for theBenchmark
% 2.21/0.65  % (12067)------------------------------
% 2.21/0.65  % (12067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.65  % (12067)Termination reason: Refutation
% 2.21/0.65  
% 2.21/0.65  % (12067)Memory used [KB]: 9466
% 2.21/0.65  % (12067)Time elapsed: 0.174 s
% 2.21/0.65  % (12067)------------------------------
% 2.21/0.65  % (12067)------------------------------
% 2.21/0.65  % (12052)Success in time 0.285 s
%------------------------------------------------------------------------------
