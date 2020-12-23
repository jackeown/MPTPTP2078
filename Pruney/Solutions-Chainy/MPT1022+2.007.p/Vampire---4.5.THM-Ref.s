%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  116 (2808 expanded)
%              Number of leaves         :   12 ( 666 expanded)
%              Depth                    :   44
%              Number of atoms          :  380 (15648 expanded)
%              Number of equality atoms :  111 (4287 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f295,plain,(
    $false ),
    inference(subsumption_resolution,[],[f294,f206])).

fof(f206,plain,(
    v5_relat_1(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f57,f200])).

fof(f200,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f199,f57])).

fof(f199,plain,
    ( k1_xboole_0 = sK0
    | ~ v5_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f196,f38])).

fof(f38,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
      | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) )
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
          | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
        & r1_tarski(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
   => ( ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
        | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) )
      & r1_tarski(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).

fof(f196,plain,
    ( k1_xboole_0 = sK0
    | ~ r1_tarski(sK1,sK0)
    | ~ v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f194,f73])).

fof(f73,plain,(
    v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f72,f34])).

fof(f34,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f71,f36])).

fof(f36,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_2(sK2,sK0) ),
    inference(resolution,[],[f49,f37])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f194,plain,(
    ! [X0] :
      ( ~ v2_funct_2(sK2,X0)
      | k1_xboole_0 = sK0
      | ~ r1_tarski(sK1,X0)
      | ~ v5_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f193,f56])).

fof(f56,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f45,f37])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f193,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | k1_xboole_0 = sK0
      | ~ v2_funct_2(sK2,X0)
      | ~ v5_relat_1(sK2,X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f188,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f188,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f182,f38])).

fof(f182,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ r1_tarski(sK1,k2_relat_1(sK2))
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f127,f176])).

fof(f176,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f175,f57])).

fof(f175,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK0
    | ~ v5_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f174,f73])).

fof(f174,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK0
    | ~ v2_funct_2(sK2,sK0)
    | ~ v5_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f171,f56])).

fof(f171,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK0
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_2(sK2,sK0)
    | ~ v5_relat_1(sK2,sK0) ),
    inference(superposition,[],[f170,f61])).

fof(f61,plain,(
    ! [X2,X3] :
      ( k10_relat_1(X2,X3) = k1_relat_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v2_funct_2(X2,X3)
      | ~ v5_relat_1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,(
    ! [X2,X3] :
      ( k10_relat_1(X2,X3) = k1_relat_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v2_funct_2(X2,X3)
      | ~ v5_relat_1(X2,X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f40,f43])).

fof(f40,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f170,plain,
    ( sK0 = k10_relat_1(sK2,sK0)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f169,f34])).

fof(f169,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k10_relat_1(sK2,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f168,f35])).

fof(f35,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f168,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k10_relat_1(sK2,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f167,f37])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k10_relat_1(X2,X1) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f50,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

fof(f127,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK2))
    | ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f126,f56])).

fof(f126,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ r1_tarski(sK1,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f125,f34])).

fof(f125,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ r1_tarski(sK1,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f118,f66])).

fof(f66,plain,(
    v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f65,f34])).

fof(f65,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f64,f36])).

fof(f64,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f48,f37])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f118,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ r1_tarski(sK1,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f117])).

fof(f117,plain,
    ( sK1 != sK1
    | ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ r1_tarski(sK1,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f91,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f91,plain,
    ( sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f90,f56])).

fof(f90,plain,
    ( sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f88,f34])).

fof(f88,plain,
    ( sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f87])).

fof(f87,plain,
    ( sK1 != sK1
    | sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f85,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f85,plain,
    ( sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f84,f37])).

fof(f84,plain,
    ( sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f83,f53])).

fof(f83,plain,
    ( sK1 != k9_relat_1(sK2,k8_relset_1(sK0,sK0,sK2,sK1))
    | sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f80,f37])).

fof(f80,plain,
    ( sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | sK1 != k9_relat_1(sK2,k8_relset_1(sK0,sK0,sK2,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f77,f53])).

fof(f77,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))
    | sK1 != k9_relat_1(sK2,k8_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(subsumption_resolution,[],[f76,f37])).

fof(f76,plain,
    ( sK1 != k9_relat_1(sK2,k8_relset_1(sK0,sK0,sK2,sK1))
    | sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f75,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f75,plain,
    ( sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))
    | sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f74,f37])).

fof(f74,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))
    | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f39,f52])).

fof(f39,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
    | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f46,f37])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

% (19186)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f294,plain,(
    ~ v5_relat_1(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f291,f204])).

fof(f204,plain,(
    r1_tarski(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f38,f200])).

fof(f291,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ v5_relat_1(sK2,k1_xboole_0) ),
    inference(resolution,[],[f284,f207])).

fof(f207,plain,(
    v2_funct_2(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f73,f200])).

fof(f284,plain,(
    ! [X0] :
      ( ~ v2_funct_2(sK2,X0)
      | ~ r1_tarski(sK1,X0)
      | ~ v5_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f283,f56])).

fof(f283,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ v2_funct_2(sK2,X0)
      | ~ v5_relat_1(sK2,X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f270,f43])).

fof(f270,plain,(
    ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f256,f204])).

fof(f256,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f127,f251])).

fof(f251,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f250,f206])).

fof(f250,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ v5_relat_1(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f249,f207])).

fof(f249,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ v2_funct_2(sK2,k1_xboole_0)
    | ~ v5_relat_1(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f246,f56])).

fof(f246,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_2(sK2,k1_xboole_0)
    | ~ v5_relat_1(sK2,k1_xboole_0) ),
    inference(superposition,[],[f245,f61])).

fof(f245,plain,(
    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f244,f34])).

fof(f244,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f238,f201])).

fof(f201,plain,(
    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f35,f200])).

fof(f238,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f203,f163])).

fof(f163,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
      | k1_xboole_0 = k10_relat_1(X3,X2)
      | ~ v1_funct_2(X3,k1_xboole_0,X2)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f160])).

fof(f160,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k10_relat_1(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
      | ~ v1_funct_2(X3,k1_xboole_0,X2)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ) ),
    inference(superposition,[],[f55,f53])).

fof(f55,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f203,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f37,f200])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:52:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (19170)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (19170)Refutation not found, incomplete strategy% (19170)------------------------------
% 0.20/0.52  % (19170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (19171)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.52  % (19187)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.52  % (19170)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (19170)Memory used [KB]: 10618
% 0.20/0.52  % (19170)Time elapsed: 0.075 s
% 0.20/0.52  % (19170)------------------------------
% 0.20/0.52  % (19170)------------------------------
% 0.20/0.52  % (19179)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.53  % (19179)Refutation not found, incomplete strategy% (19179)------------------------------
% 0.20/0.53  % (19179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (19179)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (19179)Memory used [KB]: 6268
% 0.20/0.53  % (19179)Time elapsed: 0.073 s
% 0.20/0.53  % (19179)------------------------------
% 0.20/0.53  % (19179)------------------------------
% 0.20/0.53  % (19187)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f295,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f294,f206])).
% 0.20/0.53  fof(f206,plain,(
% 0.20/0.53    v5_relat_1(sK2,k1_xboole_0)),
% 0.20/0.53    inference(backward_demodulation,[],[f57,f200])).
% 0.20/0.53  fof(f200,plain,(
% 0.20/0.53    k1_xboole_0 = sK0),
% 0.20/0.53    inference(subsumption_resolution,[],[f199,f57])).
% 0.20/0.53  fof(f199,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | ~v5_relat_1(sK2,sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f196,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    r1_tarski(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    (sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 0.20/0.53    inference(flattening,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.20/0.53    inference(negated_conjecture,[],[f11])).
% 0.20/0.53  fof(f11,conjecture,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).
% 0.20/0.53  fof(f196,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | ~r1_tarski(sK1,sK0) | ~v5_relat_1(sK2,sK0)),
% 0.20/0.53    inference(resolution,[],[f194,f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    v2_funct_2(sK2,sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f72,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    v1_funct_1(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ~v1_funct_1(sK2) | v2_funct_2(sK2,sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f71,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    v3_funct_2(sK2,sK0,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | v2_funct_2(sK2,sK0)),
% 0.20/0.53    inference(resolution,[],[f49,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_2(X2,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(flattening,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.20/0.53  fof(f194,plain,(
% 0.20/0.53    ( ! [X0] : (~v2_funct_2(sK2,X0) | k1_xboole_0 = sK0 | ~r1_tarski(sK1,X0) | ~v5_relat_1(sK2,X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f193,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    v1_relat_1(sK2)),
% 0.20/0.53    inference(resolution,[],[f45,f37])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.53  fof(f193,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(sK1,X0) | k1_xboole_0 = sK0 | ~v2_funct_2(sK2,X0) | ~v5_relat_1(sK2,X0) | ~v1_relat_1(sK2)) )),
% 0.20/0.53    inference(superposition,[],[f188,f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.20/0.53  fof(f188,plain,(
% 0.20/0.53    ~r1_tarski(sK1,k2_relat_1(sK2)) | k1_xboole_0 = sK0),
% 0.20/0.53    inference(subsumption_resolution,[],[f182,f38])).
% 0.20/0.53  fof(f182,plain,(
% 0.20/0.53    ~r1_tarski(sK1,sK0) | ~r1_tarski(sK1,k2_relat_1(sK2)) | k1_xboole_0 = sK0),
% 0.20/0.53    inference(superposition,[],[f127,f176])).
% 0.20/0.53  fof(f176,plain,(
% 0.20/0.53    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK0),
% 0.20/0.53    inference(subsumption_resolution,[],[f175,f57])).
% 0.20/0.53  fof(f175,plain,(
% 0.20/0.53    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK0 | ~v5_relat_1(sK2,sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f174,f73])).
% 0.20/0.53  fof(f174,plain,(
% 0.20/0.53    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK0 | ~v2_funct_2(sK2,sK0) | ~v5_relat_1(sK2,sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f171,f56])).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK0 | ~v1_relat_1(sK2) | ~v2_funct_2(sK2,sK0) | ~v5_relat_1(sK2,sK0)),
% 0.20/0.53    inference(superposition,[],[f170,f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X2,X3] : (k10_relat_1(X2,X3) = k1_relat_1(X2) | ~v1_relat_1(X2) | ~v2_funct_2(X2,X3) | ~v5_relat_1(X2,X3)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X2,X3] : (k10_relat_1(X2,X3) = k1_relat_1(X2) | ~v1_relat_1(X2) | ~v2_funct_2(X2,X3) | ~v5_relat_1(X2,X3) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(superposition,[],[f40,f43])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.20/0.53  fof(f170,plain,(
% 0.20/0.53    sK0 = k10_relat_1(sK2,sK0) | k1_xboole_0 = sK0),
% 0.20/0.53    inference(subsumption_resolution,[],[f169,f34])).
% 0.20/0.53  fof(f169,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | sK0 = k10_relat_1(sK2,sK0) | ~v1_funct_1(sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f168,f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    v1_funct_2(sK2,sK0,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f168,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | sK0 = k10_relat_1(sK2,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.20/0.53    inference(resolution,[],[f167,f37])).
% 0.20/0.53  fof(f167,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k10_relat_1(X2,X1) = X0 | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f164])).
% 0.20/0.53  fof(f164,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k10_relat_1(X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(superposition,[],[f50,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.53    inference(flattening,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    ~r1_tarski(sK1,k1_relat_1(sK2)) | ~r1_tarski(sK1,k2_relat_1(sK2))),
% 0.20/0.53    inference(subsumption_resolution,[],[f126,f56])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    ~r1_tarski(sK1,k2_relat_1(sK2)) | ~r1_tarski(sK1,k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f125,f34])).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    ~r1_tarski(sK1,k2_relat_1(sK2)) | ~r1_tarski(sK1,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f118,f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    v2_funct_1(sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f65,f34])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ~v1_funct_1(sK2) | v2_funct_1(sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f64,f36])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | v2_funct_1(sK2)),
% 0.20/0.53    inference(resolution,[],[f48,f37])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    ~r1_tarski(sK1,k2_relat_1(sK2)) | ~v2_funct_1(sK2) | ~r1_tarski(sK1,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f117])).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    sK1 != sK1 | ~r1_tarski(sK1,k2_relat_1(sK2)) | ~v2_funct_1(sK2) | ~r1_tarski(sK1,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.53    inference(superposition,[],[f91,f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | ~r1_tarski(sK1,k2_relat_1(sK2))),
% 0.20/0.53    inference(subsumption_resolution,[],[f90,f56])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | ~r1_tarski(sK1,k2_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f88,f34])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | ~r1_tarski(sK1,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f87])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    sK1 != sK1 | sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | ~r1_tarski(sK1,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.53    inference(superposition,[],[f85,f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) | sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 0.20/0.53    inference(subsumption_resolution,[],[f84,f37])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) | sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.53    inference(superposition,[],[f83,f53])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    sK1 != k9_relat_1(sK2,k8_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 0.20/0.53    inference(subsumption_resolution,[],[f80,f37])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | sK1 != k9_relat_1(sK2,k8_relset_1(sK0,sK0,sK2,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.53    inference(superposition,[],[f77,f53])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) | sK1 != k9_relat_1(sK2,k8_relset_1(sK0,sK0,sK2,sK1))),
% 0.20/0.53    inference(subsumption_resolution,[],[f76,f37])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    sK1 != k9_relat_1(sK2,k8_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.53    inference(superposition,[],[f75,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))),
% 0.20/0.53    inference(subsumption_resolution,[],[f74,f37])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.53    inference(superposition,[],[f39,f52])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))),
% 0.20/0.53    inference(cnf_transformation,[],[f32])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    v5_relat_1(sK2,sK0)),
% 0.20/0.53    inference(resolution,[],[f46,f37])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.20/0.53    inference(pure_predicate_removal,[],[f5])).
% 0.20/0.53  % (19186)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.53  fof(f294,plain,(
% 0.20/0.53    ~v5_relat_1(sK2,k1_xboole_0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f291,f204])).
% 0.20/0.53  fof(f204,plain,(
% 0.20/0.53    r1_tarski(sK1,k1_xboole_0)),
% 0.20/0.53    inference(backward_demodulation,[],[f38,f200])).
% 0.20/0.53  fof(f291,plain,(
% 0.20/0.53    ~r1_tarski(sK1,k1_xboole_0) | ~v5_relat_1(sK2,k1_xboole_0)),
% 0.20/0.53    inference(resolution,[],[f284,f207])).
% 0.20/0.53  fof(f207,plain,(
% 0.20/0.53    v2_funct_2(sK2,k1_xboole_0)),
% 0.20/0.53    inference(backward_demodulation,[],[f73,f200])).
% 0.20/0.53  fof(f284,plain,(
% 0.20/0.53    ( ! [X0] : (~v2_funct_2(sK2,X0) | ~r1_tarski(sK1,X0) | ~v5_relat_1(sK2,X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f283,f56])).
% 0.20/0.53  fof(f283,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(sK1,X0) | ~v2_funct_2(sK2,X0) | ~v5_relat_1(sK2,X0) | ~v1_relat_1(sK2)) )),
% 0.20/0.53    inference(superposition,[],[f270,f43])).
% 0.20/0.53  fof(f270,plain,(
% 0.20/0.53    ~r1_tarski(sK1,k2_relat_1(sK2))),
% 0.20/0.53    inference(subsumption_resolution,[],[f256,f204])).
% 0.20/0.53  fof(f256,plain,(
% 0.20/0.53    ~r1_tarski(sK1,k1_xboole_0) | ~r1_tarski(sK1,k2_relat_1(sK2))),
% 0.20/0.53    inference(backward_demodulation,[],[f127,f251])).
% 0.20/0.53  fof(f251,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f250,f206])).
% 0.20/0.53  fof(f250,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(sK2) | ~v5_relat_1(sK2,k1_xboole_0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f249,f207])).
% 0.20/0.53  fof(f249,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(sK2) | ~v2_funct_2(sK2,k1_xboole_0) | ~v5_relat_1(sK2,k1_xboole_0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f246,f56])).
% 0.20/0.53  fof(f246,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_2(sK2,k1_xboole_0) | ~v5_relat_1(sK2,k1_xboole_0)),
% 0.20/0.53    inference(superposition,[],[f245,f61])).
% 0.20/0.53  fof(f245,plain,(
% 0.20/0.53    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f244,f34])).
% 0.20/0.53  fof(f244,plain,(
% 0.20/0.53    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) | ~v1_funct_1(sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f238,f201])).
% 0.20/0.53  fof(f201,plain,(
% 0.20/0.53    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.20/0.53    inference(backward_demodulation,[],[f35,f200])).
% 0.20/0.53  fof(f238,plain,(
% 0.20/0.53    k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK2)),
% 0.20/0.53    inference(resolution,[],[f203,f163])).
% 0.20/0.53  fof(f163,plain,(
% 0.20/0.53    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | k1_xboole_0 = k10_relat_1(X3,X2) | ~v1_funct_2(X3,k1_xboole_0,X2) | ~v1_funct_1(X3)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f160])).
% 0.20/0.53  fof(f160,plain,(
% 0.20/0.53    ( ! [X2,X3] : (k1_xboole_0 = k10_relat_1(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | ~v1_funct_2(X3,k1_xboole_0,X2) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))) )),
% 0.20/0.53    inference(superposition,[],[f55,f53])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X2,X1] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.53    inference(equality_resolution,[],[f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f203,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.53    inference(backward_demodulation,[],[f37,f200])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (19187)------------------------------
% 0.20/0.53  % (19187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (19187)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (19187)Memory used [KB]: 1663
% 0.20/0.53  % (19187)Time elapsed: 0.084 s
% 0.20/0.53  % (19187)------------------------------
% 0.20/0.53  % (19187)------------------------------
% 0.20/0.54  % (19168)Success in time 0.176 s
%------------------------------------------------------------------------------
