%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 (8750 expanded)
%              Number of leaves         :    9 (1807 expanded)
%              Depth                    :   37
%              Number of atoms          :  222 (28724 expanded)
%              Number of equality atoms :  123 (19901 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f464,plain,(
    $false ),
    inference(subsumption_resolution,[],[f389,f463])).

fof(f463,plain,(
    ! [X0] : ~ m1_subset_1(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f462,f331])).

fof(f331,plain,(
    ! [X2] : k1_xboole_0 = X2 ),
    inference(subsumption_resolution,[],[f330,f28])).

fof(f28,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f330,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(subsumption_resolution,[],[f289,f325])).

fof(f325,plain,(
    ! [X0] : ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f318,f324])).

fof(f324,plain,(
    ! [X8,X9] :
      ( k1_xboole_0 = X8
      | ~ m1_subset_1(X9,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f315,f198])).

fof(f198,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(condensation,[],[f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f129,f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f129,plain,(
    ! [X2,X1] :
      ( v1_xboole_0(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f128,f38])).

fof(f38,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f128,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
      | k1_xboole_0 = X1
      | v1_xboole_0(X2) ) ),
    inference(forward_demodulation,[],[f86,f96])).

fof(f96,plain,(
    k1_xboole_0 = sK2 ),
    inference(condensation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f82,f29])).

fof(f82,plain,(
    ! [X1] :
      ( v1_xboole_0(sK2)
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f81,f38])).

fof(f81,plain,(
    ! [X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1)
      | v1_xboole_0(sK2)
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f79,f38])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1)
      | v1_xboole_0(sK2)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f61,f27])).

fof(f27,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f61,plain,(
    ! [X10,X8,X9] :
      ( ~ v1_xboole_0(X9)
      | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X9,X10),X8)
      | v1_xboole_0(sK2)
      | k1_xboole_0 = X8 ) ),
    inference(resolution,[],[f44,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2,k1_zfmisc_1(X0))
      | k1_xboole_0 = X1
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(superposition,[],[f39,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f25,f38])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    & v1_funct_2(sK2,k1_xboole_0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
      & v1_funct_2(sK2,k1_xboole_0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

fof(f86,plain,(
    ! [X2,X3,X1] :
      ( k1_xboole_0 = X1
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X3))) ) ),
    inference(resolution,[],[f82,f30])).

fof(f315,plain,(
    ! [X8,X9] :
      ( k1_xboole_0 != X9
      | k1_xboole_0 = X8
      | ~ m1_subset_1(X9,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(backward_demodulation,[],[f194,f309])).

fof(f309,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k8_relset_1(X0,X1,k1_xboole_0,X2) ),
    inference(condensation,[],[f308])).

fof(f308,plain,(
    ! [X4,X2,X0,X1] :
      ( k1_xboole_0 = k8_relset_1(X1,X2,k1_xboole_0,X4)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f307,f297])).

fof(f297,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(condensation,[],[f295])).

fof(f295,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 = k10_relat_1(k1_xboole_0,X5)
      | k1_xboole_0 = X4 ) ),
    inference(backward_demodulation,[],[f268,f293])).

fof(f293,plain,(
    ! [X0,X1] : k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X1) ),
    inference(condensation,[],[f287])).

fof(f287,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = X3
      | k1_xboole_0 = k8_relset_1(k1_xboole_0,X4,k1_xboole_0,X5) ) ),
    inference(resolution,[],[f251,f198])).

fof(f251,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k8_relset_1(k1_xboole_0,X3,k1_xboole_0,X5),k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X4 ) ),
    inference(subsumption_resolution,[],[f248,f38])).

fof(f248,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X4)
      | k1_xboole_0 = X4
      | m1_subset_1(k8_relset_1(k1_xboole_0,X3,k1_xboole_0,X5),k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f116,f38])).

fof(f116,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X5,X6),X4)
      | k1_xboole_0 = X4
      | m1_subset_1(k8_relset_1(X5,X6,k1_xboole_0,X7),k1_zfmisc_1(X5)) ) ),
    inference(backward_demodulation,[],[f60,f96])).

fof(f60,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_xboole_0 = X4
      | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X5,X6),X4)
      | m1_subset_1(k8_relset_1(X5,X6,sK2,X7),k1_zfmisc_1(X5)) ) ),
    inference(resolution,[],[f44,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f268,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = X4
      | k8_relset_1(k1_xboole_0,X3,k1_xboole_0,X5) = k10_relat_1(k1_xboole_0,X5) ) ),
    inference(subsumption_resolution,[],[f265,f38])).

fof(f265,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X4)
      | k1_xboole_0 = X4
      | k8_relset_1(k1_xboole_0,X3,k1_xboole_0,X5) = k10_relat_1(k1_xboole_0,X5) ) ),
    inference(superposition,[],[f115,f38])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X1,X2),X0)
      | k1_xboole_0 = X0
      | k8_relset_1(X1,X2,k1_xboole_0,X3) = k10_relat_1(k1_xboole_0,X3) ) ),
    inference(backward_demodulation,[],[f59,f96])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X1,X2),X0)
      | k8_relset_1(X1,X2,sK2,X3) = k10_relat_1(sK2,X3) ) ),
    inference(resolution,[],[f44,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f307,plain,(
    ! [X4,X2,X0,X1] :
      ( k8_relset_1(X1,X2,k1_xboole_0,X4) = k10_relat_1(k1_xboole_0,X4)
      | k1_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f273,f302])).

fof(f302,plain,(
    ! [X0,X1] : k1_xboole_0 = k8_relset_1(X0,k1_xboole_0,k1_xboole_0,X1) ),
    inference(condensation,[],[f299])).

fof(f299,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k8_relset_1(X0,k1_xboole_0,k1_xboole_0,X2)
      | k1_xboole_0 = X1 ) ),
    inference(backward_demodulation,[],[f267,f297])).

fof(f267,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X1
      | k10_relat_1(k1_xboole_0,X2) = k8_relset_1(X0,k1_xboole_0,k1_xboole_0,X2) ) ),
    inference(subsumption_resolution,[],[f264,f38])).

fof(f264,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1)
      | k1_xboole_0 = X1
      | k10_relat_1(k1_xboole_0,X2) = k8_relset_1(X0,k1_xboole_0,k1_xboole_0,X2) ) ),
    inference(superposition,[],[f115,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f273,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k8_relset_1(X1,X2,k8_relset_1(k2_zfmisc_1(X1,X2),k1_xboole_0,k1_xboole_0,X3),X4) = k10_relat_1(k8_relset_1(k2_zfmisc_1(X1,X2),k1_xboole_0,k1_xboole_0,X3),X4) ) ),
    inference(resolution,[],[f250,f36])).

fof(f250,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k8_relset_1(X0,k1_xboole_0,k1_xboole_0,X2),k1_zfmisc_1(X0))
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f247,f38])).

fof(f247,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1)
      | k1_xboole_0 = X1
      | m1_subset_1(k8_relset_1(X0,k1_xboole_0,k1_xboole_0,X2),k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f116,f37])).

fof(f194,plain,(
    ! [X8,X9] :
      ( k1_xboole_0 = X8
      | ~ m1_subset_1(X9,k1_zfmisc_1(k1_xboole_0))
      | k8_relset_1(X9,sK0,k1_xboole_0,sK1) != X9 ) ),
    inference(resolution,[],[f129,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k8_relset_1(X0,sK0,k1_xboole_0,sK1) != X0 ) ),
    inference(backward_demodulation,[],[f49,f96])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k8_relset_1(X0,sK0,sK2,sK1) != X0 ) ),
    inference(superposition,[],[f26,f29])).

fof(f26,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f318,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(backward_demodulation,[],[f239,f309])).

fof(f239,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k8_relset_1(X0,sK0,k1_xboole_0,sK1) != X0 ) ),
    inference(forward_demodulation,[],[f236,f38])).

fof(f236,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k8_relset_1(X0,sK0,k1_xboole_0,sK1) != X0 ) ),
    inference(resolution,[],[f114,f27])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k8_relset_1(X0,sK0,k1_xboole_0,sK1) != X0 ) ),
    inference(backward_demodulation,[],[f58,f96])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,sK0,sK2,sK1) != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f49,f30])).

fof(f289,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_relat_1(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X2
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(superposition,[],[f251,f36])).

fof(f462,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | ~ m1_subset_1(X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f461,f331])).

fof(f461,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_xboole_0)
      | k10_relat_1(X0,sK1) != X0 ) ),
    inference(forward_demodulation,[],[f427,f331])).

fof(f427,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k10_relat_1(X0,sK1) != X0 ) ),
    inference(duplicate_literal_removal,[],[f385])).

fof(f385,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k10_relat_1(X0,sK1) != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(backward_demodulation,[],[f272,f331])).

fof(f272,plain,(
    ! [X0] :
      ( k10_relat_1(X0,sK1) != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) ) ),
    inference(superposition,[],[f246,f36])).

fof(f246,plain,(
    ! [X0] :
      ( k8_relset_1(X0,sK0,X0,sK1) != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f243,f38])).

fof(f243,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k8_relset_1(X0,sK0,X0,sK1) != X0 ) ),
    inference(resolution,[],[f170,f27])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k8_relset_1(X0,sK0,X0,sK1) != X0 ) ),
    inference(resolution,[],[f155,f30])).

fof(f155,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k8_relset_1(X0,sK0,X0,sK1) != X0 ) ),
    inference(superposition,[],[f99,f29])).

fof(f99,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f26,f96])).

fof(f389,plain,(
    m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f28,f331])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:45:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (16627)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.46  % (16626)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (16626)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (16636)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (16635)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (16635)Refutation not found, incomplete strategy% (16635)------------------------------
% 0.21/0.48  % (16635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (16635)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (16635)Memory used [KB]: 1535
% 0.21/0.48  % (16635)Time elapsed: 0.072 s
% 0.21/0.48  % (16635)------------------------------
% 0.21/0.48  % (16635)------------------------------
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f464,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f389,f463])).
% 0.21/0.48  fof(f463,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f462,f331])).
% 0.21/0.48  fof(f331,plain,(
% 0.21/0.48    ( ! [X2] : (k1_xboole_0 = X2) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f330,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.48  fof(f330,plain,(
% 0.21/0.48    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f289,f325])).
% 0.21/0.48  fof(f325,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f318,f324])).
% 0.21/0.48  fof(f324,plain,(
% 0.21/0.48    ( ! [X8,X9] : (k1_xboole_0 = X8 | ~m1_subset_1(X9,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f315,f198])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(condensation,[],[f191])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X1) )),
% 0.21/0.48    inference(resolution,[],[f129,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    ( ! [X2,X1] : (v1_xboole_0(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f128,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ( ! [X2,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3))) | k1_xboole_0 = X1 | v1_xboole_0(X2)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f86,f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    k1_xboole_0 = sK2),
% 0.21/0.48    inference(condensation,[],[f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK2) )),
% 0.21/0.48    inference(resolution,[],[f82,f29])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ( ! [X1] : (v1_xboole_0(sK2) | k1_xboole_0 = X1) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f81,f38])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1) | v1_xboole_0(sK2) | k1_xboole_0 = X1) )),
% 0.21/0.48    inference(forward_demodulation,[],[f79,f38])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1) | v1_xboole_0(sK2) | k1_xboole_0 = X1) )),
% 0.21/0.48    inference(resolution,[],[f61,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X10,X8,X9] : (~v1_xboole_0(X9) | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X9,X10),X8) | v1_xboole_0(sK2) | k1_xboole_0 = X8) )),
% 0.21/0.48    inference(resolution,[],[f44,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(sK2,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 0.21/0.48    inference(superposition,[],[f39,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    inference(forward_demodulation,[],[f25,f38])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X2,X3,X1] : (k1_xboole_0 = X1 | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,X3)))) )),
% 0.21/0.48    inference(resolution,[],[f82,f30])).
% 0.21/0.48  fof(f315,plain,(
% 0.21/0.48    ( ! [X8,X9] : (k1_xboole_0 != X9 | k1_xboole_0 = X8 | ~m1_subset_1(X9,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.48    inference(backward_demodulation,[],[f194,f309])).
% 0.21/0.48  fof(f309,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_xboole_0 = k8_relset_1(X0,X1,k1_xboole_0,X2)) )),
% 0.21/0.48    inference(condensation,[],[f308])).
% 0.21/0.48  fof(f308,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X1] : (k1_xboole_0 = k8_relset_1(X1,X2,k1_xboole_0,X4) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(forward_demodulation,[],[f307,f297])).
% 0.21/0.48  fof(f297,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(condensation,[],[f295])).
% 0.21/0.48  fof(f295,plain,(
% 0.21/0.48    ( ! [X4,X5] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X5) | k1_xboole_0 = X4) )),
% 0.21/0.48    inference(backward_demodulation,[],[f268,f293])).
% 0.21/0.48  fof(f293,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X1)) )),
% 0.21/0.48    inference(condensation,[],[f287])).
% 0.21/0.48  fof(f287,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (k1_xboole_0 = X3 | k1_xboole_0 = k8_relset_1(k1_xboole_0,X4,k1_xboole_0,X5)) )),
% 0.21/0.48    inference(resolution,[],[f251,f198])).
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (m1_subset_1(k8_relset_1(k1_xboole_0,X3,k1_xboole_0,X5),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X4) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f248,f38])).
% 0.21/0.48  fof(f248,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X4) | k1_xboole_0 = X4 | m1_subset_1(k8_relset_1(k1_xboole_0,X3,k1_xboole_0,X5),k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.48    inference(superposition,[],[f116,f38])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ( ! [X6,X4,X7,X5] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X5,X6),X4) | k1_xboole_0 = X4 | m1_subset_1(k8_relset_1(X5,X6,k1_xboole_0,X7),k1_zfmisc_1(X5))) )),
% 0.21/0.48    inference(backward_demodulation,[],[f60,f96])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X6,X4,X7,X5] : (k1_xboole_0 = X4 | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X5,X6),X4) | m1_subset_1(k8_relset_1(X5,X6,sK2,X7),k1_zfmisc_1(X5))) )),
% 0.21/0.48    inference(resolution,[],[f44,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 0.21/0.48  fof(f268,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (k1_xboole_0 = X4 | k8_relset_1(k1_xboole_0,X3,k1_xboole_0,X5) = k10_relat_1(k1_xboole_0,X5)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f265,f38])).
% 0.21/0.48  fof(f265,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X4) | k1_xboole_0 = X4 | k8_relset_1(k1_xboole_0,X3,k1_xboole_0,X5) = k10_relat_1(k1_xboole_0,X5)) )),
% 0.21/0.48    inference(superposition,[],[f115,f38])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X1,X2),X0) | k1_xboole_0 = X0 | k8_relset_1(X1,X2,k1_xboole_0,X3) = k10_relat_1(k1_xboole_0,X3)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f59,f96])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X1,X2),X0) | k8_relset_1(X1,X2,sK2,X3) = k10_relat_1(sK2,X3)) )),
% 0.21/0.48    inference(resolution,[],[f44,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.48  fof(f307,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X1] : (k8_relset_1(X1,X2,k1_xboole_0,X4) = k10_relat_1(k1_xboole_0,X4) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(backward_demodulation,[],[f273,f302])).
% 0.21/0.48  fof(f302,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k8_relset_1(X0,k1_xboole_0,k1_xboole_0,X1)) )),
% 0.21/0.48    inference(condensation,[],[f299])).
% 0.21/0.48  fof(f299,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_xboole_0 = k8_relset_1(X0,k1_xboole_0,k1_xboole_0,X2) | k1_xboole_0 = X1) )),
% 0.21/0.48    inference(backward_demodulation,[],[f267,f297])).
% 0.21/0.48  fof(f267,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_xboole_0 = X1 | k10_relat_1(k1_xboole_0,X2) = k8_relset_1(X0,k1_xboole_0,k1_xboole_0,X2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f264,f38])).
% 0.21/0.48  fof(f264,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1) | k1_xboole_0 = X1 | k10_relat_1(k1_xboole_0,X2) = k8_relset_1(X0,k1_xboole_0,k1_xboole_0,X2)) )),
% 0.21/0.48    inference(superposition,[],[f115,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f273,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k8_relset_1(X1,X2,k8_relset_1(k2_zfmisc_1(X1,X2),k1_xboole_0,k1_xboole_0,X3),X4) = k10_relat_1(k8_relset_1(k2_zfmisc_1(X1,X2),k1_xboole_0,k1_xboole_0,X3),X4)) )),
% 0.21/0.48    inference(resolution,[],[f250,f36])).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k8_relset_1(X0,k1_xboole_0,k1_xboole_0,X2),k1_zfmisc_1(X0)) | k1_xboole_0 = X1) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f247,f38])).
% 0.21/0.48  fof(f247,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X1) | k1_xboole_0 = X1 | m1_subset_1(k8_relset_1(X0,k1_xboole_0,k1_xboole_0,X2),k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(superposition,[],[f116,f37])).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    ( ! [X8,X9] : (k1_xboole_0 = X8 | ~m1_subset_1(X9,k1_zfmisc_1(k1_xboole_0)) | k8_relset_1(X9,sK0,k1_xboole_0,sK1) != X9) )),
% 0.21/0.48    inference(resolution,[],[f129,f110])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k8_relset_1(X0,sK0,k1_xboole_0,sK1) != X0) )),
% 0.21/0.48    inference(backward_demodulation,[],[f49,f96])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k8_relset_1(X0,sK0,sK2,sK1) != X0) )),
% 0.21/0.48    inference(superposition,[],[f26,f29])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f318,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 != X0 | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.48    inference(backward_demodulation,[],[f239,f309])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k8_relset_1(X0,sK0,k1_xboole_0,sK1) != X0) )),
% 0.21/0.48    inference(forward_demodulation,[],[f236,f38])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k8_relset_1(X0,sK0,k1_xboole_0,sK1) != X0) )),
% 0.21/0.48    inference(resolution,[],[f114,f27])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k8_relset_1(X0,sK0,k1_xboole_0,sK1) != X0) )),
% 0.21/0.48    inference(backward_demodulation,[],[f58,f96])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k8_relset_1(X0,sK0,sK2,sK1) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_xboole_0(X1)) )),
% 0.21/0.48    inference(resolution,[],[f49,f30])).
% 0.21/0.48  fof(f289,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k10_relat_1(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X2 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 0.21/0.48    inference(superposition,[],[f251,f36])).
% 0.21/0.48  fof(f462,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 != X0 | ~m1_subset_1(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f461,f331])).
% 0.21/0.48  fof(f461,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_xboole_0) | k10_relat_1(X0,sK1) != X0) )),
% 0.21/0.48    inference(forward_demodulation,[],[f427,f331])).
% 0.21/0.48  fof(f427,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k10_relat_1(X0,sK1) != X0) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f385])).
% 0.21/0.48  fof(f385,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k10_relat_1(X0,sK1) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.48    inference(backward_demodulation,[],[f272,f331])).
% 0.21/0.48  fof(f272,plain,(
% 0.21/0.48    ( ! [X0] : (k10_relat_1(X0,sK1) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) )),
% 0.21/0.48    inference(superposition,[],[f246,f36])).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    ( ! [X0] : (k8_relset_1(X0,sK0,X0,sK1) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f243,f38])).
% 0.21/0.48  fof(f243,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k8_relset_1(X0,sK0,X0,sK1) != X0) )),
% 0.21/0.48    inference(resolution,[],[f170,f27])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k8_relset_1(X0,sK0,X0,sK1) != X0) )),
% 0.21/0.48    inference(resolution,[],[f155,f30])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k8_relset_1(X0,sK0,X0,sK1) != X0) )),
% 0.21/0.48    inference(superposition,[],[f99,f29])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),
% 0.21/0.48    inference(backward_demodulation,[],[f26,f96])).
% 0.21/0.48  fof(f389,plain,(
% 0.21/0.48    m1_subset_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    inference(backward_demodulation,[],[f28,f331])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (16626)------------------------------
% 0.21/0.48  % (16626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (16626)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (16626)Memory used [KB]: 1791
% 0.21/0.48  % (16626)Time elapsed: 0.062 s
% 0.21/0.48  % (16626)------------------------------
% 0.21/0.48  % (16626)------------------------------
% 0.21/0.48  % (16621)Success in time 0.129 s
%------------------------------------------------------------------------------
