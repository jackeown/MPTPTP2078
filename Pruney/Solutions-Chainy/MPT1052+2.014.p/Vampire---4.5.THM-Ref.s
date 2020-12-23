%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  121 (3741 expanded)
%              Number of leaves         :   19 ( 821 expanded)
%              Depth                    :   33
%              Number of atoms          :  297 (10423 expanded)
%              Number of equality atoms :  134 (3688 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f332,plain,(
    $false ),
    inference(subsumption_resolution,[],[f328,f45])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f328,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f312,f327])).

fof(f327,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f326,f42])).

fof(f42,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( r1_tarski(k2_relat_1(X2),X1)
          & k1_relat_1(X2) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

fof(f326,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f323])).

fof(f323,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f53,f307])).

fof(f307,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f285,f301])).

fof(f301,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(resolution,[],[f286,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(k1_xboole_0,X0))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,X1) ) ),
    inference(resolution,[],[f158,f61])).

% (2095)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f157,f45])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X0) ) ),
    inference(superposition,[],[f74,f91])).

fof(f91,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k6_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f89,f46])).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f89,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | ~ v1_relat_1(k6_relat_1(X0))
      | k1_xboole_0 = k6_relat_1(X0) ) ),
    inference(superposition,[],[f50,f47])).

fof(f47,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
        & k1_relset_1(X1,X0,X2) = X1 )
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
        & k1_relset_1(X1,X0,X2) = X1 )
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
          & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relset_1)).

fof(f286,plain,(
    r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f230,f278])).

fof(f278,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f277,f44])).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f277,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f225,f122])).

fof(f122,plain,(
    ! [X2] :
      ( k1_xboole_0 = k5_partfun1(X2,k1_xboole_0,k3_partfun1(k1_xboole_0,X2,k1_xboole_0))
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f120,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f120,plain,(
    ! [X2] :
      ( v1_xboole_0(X2)
      | k1_xboole_0 = k5_partfun1(X2,k1_xboole_0,k3_partfun1(k1_xboole_0,X2,k1_xboole_0)) ) ),
    inference(resolution,[],[f118,f49])).

fof(f118,plain,(
    ! [X0] :
      ( v1_xboole_0(k5_partfun1(X0,k1_xboole_0,k3_partfun1(k1_xboole_0,X0,k1_xboole_0)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f77,f44])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f60,f59])).

fof(f59,plain,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_funct_2)).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

fof(f225,plain,(
    ~ v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,k3_partfun1(k1_xboole_0,sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f87,f222])).

fof(f222,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f221,f191])).

fof(f191,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f190])).

fof(f190,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f151,f180])).

fof(f180,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f179,f136])).

fof(f136,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f134,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f134,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f78,f76])).

fof(f76,plain,(
    r2_hidden(sK2,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f43,f59])).

fof(f43,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_unfolding,[],[f66,f59])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f179,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f178,f127])).

fof(f127,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f79,f76])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f59])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_funct_2(X0,X1))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f178,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f73,f134])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f151,plain,
    ( sK0 != k1_relat_1(sK2)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f147,f41])).

fof(f41,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | sK0 != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f147,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f142,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f142,plain,(
    r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f141,f42])).

fof(f141,plain,
    ( ~ v1_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f139,f58])).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f139,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ v1_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f137,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f137,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f134,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f221,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f220,f93])).

fof(f93,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f47,f91])).

fof(f220,plain,
    ( sK0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f219,f45])).

fof(f219,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | sK0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f196,f92])).

fof(f92,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f48,f91])).

fof(f48,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f196,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK1)
    | sK0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f41,f195])).

fof(f195,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f194,f191])).

fof(f194,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f188,f42])).

fof(f188,plain,
    ( k1_xboole_0 != sK0
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f50,f180])).

fof(f87,plain,(
    ~ v1_xboole_0(k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1))) ),
    inference(resolution,[],[f76,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f230,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f137,f222])).

fof(f285,plain,(
    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f229,f278])).

fof(f229,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f136,f222])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f312,plain,(
    ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f308])).

fof(f308,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0) ),
    inference(backward_demodulation,[],[f279,f307])).

fof(f279,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0) ),
    inference(backward_demodulation,[],[f223,f278])).

fof(f223,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | sK0 != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f41,f222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (2067)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (2073)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (2068)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (2075)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (2068)Refutation not found, incomplete strategy% (2068)------------------------------
% 0.21/0.52  % (2068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2068)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2068)Memory used [KB]: 10746
% 0.21/0.52  % (2068)Time elapsed: 0.109 s
% 0.21/0.52  % (2068)------------------------------
% 0.21/0.52  % (2068)------------------------------
% 0.21/0.52  % (2080)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (2093)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (2072)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (2076)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (2083)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (2074)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (2069)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (2092)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (2072)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (2087)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (2066)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (2087)Refutation not found, incomplete strategy% (2087)------------------------------
% 0.21/0.54  % (2087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2087)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2087)Memory used [KB]: 1791
% 0.21/0.54  % (2087)Time elapsed: 0.090 s
% 0.21/0.54  % (2087)------------------------------
% 0.21/0.54  % (2087)------------------------------
% 0.21/0.54  % (2084)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (2076)Refutation not found, incomplete strategy% (2076)------------------------------
% 0.21/0.54  % (2076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2076)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2076)Memory used [KB]: 10618
% 0.21/0.54  % (2076)Time elapsed: 0.133 s
% 0.21/0.54  % (2076)------------------------------
% 0.21/0.54  % (2076)------------------------------
% 0.21/0.54  % (2082)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (2094)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (2071)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (2070)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (2090)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (2085)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (2081)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (2088)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (2077)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (2086)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (2078)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (2079)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (2089)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.62/0.57  % SZS output start Proof for theBenchmark
% 1.62/0.57  fof(f332,plain,(
% 1.62/0.57    $false),
% 1.62/0.57    inference(subsumption_resolution,[],[f328,f45])).
% 1.62/0.57  fof(f45,plain,(
% 1.62/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f4])).
% 1.62/0.57  fof(f4,axiom,(
% 1.62/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.62/0.57  fof(f328,plain,(
% 1.62/0.57    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.62/0.57    inference(backward_demodulation,[],[f312,f327])).
% 1.62/0.57  fof(f327,plain,(
% 1.62/0.57    k1_xboole_0 = k2_relat_1(sK2)),
% 1.62/0.57    inference(subsumption_resolution,[],[f326,f42])).
% 1.62/0.57  fof(f42,plain,(
% 1.62/0.57    v1_relat_1(sK2)),
% 1.62/0.57    inference(cnf_transformation,[],[f25])).
% 1.62/0.57  fof(f25,plain,(
% 1.62/0.57    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_relat_1(X2))),
% 1.62/0.57    inference(flattening,[],[f24])).
% 1.62/0.57  fof(f24,plain,(
% 1.62/0.57    ? [X0,X1,X2] : (((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1))) & v1_relat_1(X2))),
% 1.62/0.57    inference(ennf_transformation,[],[f23])).
% 1.62/0.57  fof(f23,plain,(
% 1.62/0.57    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 1.62/0.57    inference(pure_predicate_removal,[],[f20])).
% 1.62/0.57  fof(f20,negated_conjecture,(
% 1.62/0.57    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 1.62/0.57    inference(negated_conjecture,[],[f19])).
% 1.62/0.57  fof(f19,conjecture,(
% 1.62/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).
% 1.62/0.57  fof(f326,plain,(
% 1.62/0.57    k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 1.62/0.57    inference(trivial_inequality_removal,[],[f323])).
% 1.62/0.57  fof(f323,plain,(
% 1.62/0.57    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(sK2)),
% 1.62/0.57    inference(superposition,[],[f53,f307])).
% 1.62/0.57  fof(f307,plain,(
% 1.62/0.57    k1_xboole_0 = k1_relat_1(sK2)),
% 1.62/0.57    inference(backward_demodulation,[],[f285,f301])).
% 1.62/0.57  fof(f301,plain,(
% 1.62/0.57    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 1.62/0.57    inference(resolution,[],[f286,f159])).
% 1.62/0.57  fof(f159,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~r1_tarski(X1,k2_zfmisc_1(k1_xboole_0,X0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,X1)) )),
% 1.62/0.57    inference(resolution,[],[f158,f61])).
% 1.62/0.57  % (2095)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.62/0.57  fof(f61,plain,(
% 1.62/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f5])).
% 1.62/0.57  fof(f5,axiom,(
% 1.62/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.62/0.57  fof(f158,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X0)) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f157,f45])).
% 1.62/0.57  fof(f157,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X0)) )),
% 1.62/0.57    inference(superposition,[],[f74,f91])).
% 1.62/0.57  fof(f91,plain,(
% 1.62/0.57    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.62/0.57    inference(equality_resolution,[],[f90])).
% 1.62/0.57  fof(f90,plain,(
% 1.62/0.57    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_relat_1(X0)) )),
% 1.62/0.57    inference(subsumption_resolution,[],[f89,f46])).
% 1.62/0.57  fof(f46,plain,(
% 1.62/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f21])).
% 1.62/0.57  fof(f21,plain,(
% 1.62/0.57    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.62/0.57    inference(pure_predicate_removal,[],[f12])).
% 1.62/0.57  fof(f12,axiom,(
% 1.62/0.57    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.62/0.57  fof(f89,plain,(
% 1.62/0.57    ( ! [X0] : (k1_xboole_0 != X0 | ~v1_relat_1(k6_relat_1(X0)) | k1_xboole_0 = k6_relat_1(X0)) )),
% 1.62/0.57    inference(superposition,[],[f50,f47])).
% 1.62/0.57  fof(f47,plain,(
% 1.62/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.62/0.57    inference(cnf_transformation,[],[f11])).
% 1.62/0.57  fof(f11,axiom,(
% 1.62/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.62/0.57  fof(f50,plain,(
% 1.62/0.57    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.62/0.57    inference(cnf_transformation,[],[f28])).
% 1.62/0.57  fof(f28,plain,(
% 1.62/0.57    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.62/0.57    inference(flattening,[],[f27])).
% 1.62/0.57  fof(f27,plain,(
% 1.62/0.57    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.62/0.57    inference(ennf_transformation,[],[f9])).
% 1.62/0.57  fof(f9,axiom,(
% 1.62/0.57    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.62/0.57  fof(f74,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k6_relat_1(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) = X1) )),
% 1.62/0.57    inference(cnf_transformation,[],[f40])).
% 1.62/0.57  fof(f40,plain,(
% 1.62/0.57    ! [X0,X1,X2] : ((r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1) | ~r1_tarski(k6_relat_1(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.62/0.57    inference(flattening,[],[f39])).
% 1.62/0.57  fof(f39,plain,(
% 1.62/0.57    ! [X0,X1,X2] : (((r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1) | ~r1_tarski(k6_relat_1(X1),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.62/0.57    inference(ennf_transformation,[],[f14])).
% 1.62/0.57  fof(f14,axiom,(
% 1.62/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(k6_relat_1(X1),X2) => (r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1)))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relset_1)).
% 1.62/0.57  fof(f286,plain,(
% 1.62/0.57    r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0))),
% 1.62/0.57    inference(backward_demodulation,[],[f230,f278])).
% 1.62/0.57  fof(f278,plain,(
% 1.62/0.57    k1_xboole_0 = sK0),
% 1.62/0.57    inference(subsumption_resolution,[],[f277,f44])).
% 1.62/0.57  fof(f44,plain,(
% 1.62/0.57    v1_xboole_0(k1_xboole_0)),
% 1.62/0.57    inference(cnf_transformation,[],[f2])).
% 1.62/0.57  fof(f2,axiom,(
% 1.62/0.57    v1_xboole_0(k1_xboole_0)),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.62/0.57  fof(f277,plain,(
% 1.62/0.57    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK0),
% 1.62/0.57    inference(superposition,[],[f225,f122])).
% 1.62/0.57  fof(f122,plain,(
% 1.62/0.57    ( ! [X2] : (k1_xboole_0 = k5_partfun1(X2,k1_xboole_0,k3_partfun1(k1_xboole_0,X2,k1_xboole_0)) | k1_xboole_0 = X2) )),
% 1.62/0.57    inference(resolution,[],[f120,f49])).
% 1.62/0.57  fof(f49,plain,(
% 1.62/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.62/0.57    inference(cnf_transformation,[],[f26])).
% 1.62/0.57  fof(f26,plain,(
% 1.62/0.57    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.62/0.57    inference(ennf_transformation,[],[f3])).
% 1.62/0.57  fof(f3,axiom,(
% 1.62/0.57    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.62/0.57  fof(f120,plain,(
% 1.62/0.57    ( ! [X2] : (v1_xboole_0(X2) | k1_xboole_0 = k5_partfun1(X2,k1_xboole_0,k3_partfun1(k1_xboole_0,X2,k1_xboole_0))) )),
% 1.62/0.57    inference(resolution,[],[f118,f49])).
% 1.62/0.57  fof(f118,plain,(
% 1.62/0.57    ( ! [X0] : (v1_xboole_0(k5_partfun1(X0,k1_xboole_0,k3_partfun1(k1_xboole_0,X0,k1_xboole_0))) | v1_xboole_0(X0)) )),
% 1.62/0.57    inference(resolution,[],[f77,f44])).
% 1.62/0.57  fof(f77,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_xboole_0(X0) | v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) )),
% 1.62/0.57    inference(definition_unfolding,[],[f60,f59])).
% 1.62/0.57  fof(f59,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f18])).
% 1.62/0.57  fof(f18,axiom,(
% 1.62/0.57    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_funct_2)).
% 1.62/0.57  fof(f60,plain,(
% 1.62/0.57    ( ! [X0,X1] : (v1_xboole_0(X0) | ~v1_xboole_0(X1) | v1_xboole_0(k1_funct_2(X0,X1))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f33])).
% 1.62/0.57  fof(f33,plain,(
% 1.62/0.57    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.62/0.57    inference(flattening,[],[f32])).
% 1.62/0.57  fof(f32,plain,(
% 1.62/0.57    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.62/0.57    inference(ennf_transformation,[],[f16])).
% 1.62/0.57  fof(f16,axiom,(
% 1.62/0.57    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).
% 1.62/0.57  fof(f225,plain,(
% 1.62/0.57    ~v1_xboole_0(k5_partfun1(sK0,k1_xboole_0,k3_partfun1(k1_xboole_0,sK0,k1_xboole_0)))),
% 1.62/0.57    inference(backward_demodulation,[],[f87,f222])).
% 1.62/0.57  fof(f222,plain,(
% 1.62/0.57    k1_xboole_0 = sK1),
% 1.62/0.57    inference(subsumption_resolution,[],[f221,f191])).
% 1.62/0.57  fof(f191,plain,(
% 1.62/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.62/0.57    inference(trivial_inequality_removal,[],[f190])).
% 1.62/0.57  fof(f190,plain,(
% 1.62/0.57    sK0 != sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 1.62/0.57    inference(duplicate_literal_removal,[],[f184])).
% 1.62/0.57  fof(f184,plain,(
% 1.62/0.57    sK0 != sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.62/0.57    inference(superposition,[],[f151,f180])).
% 1.62/0.57  fof(f180,plain,(
% 1.62/0.57    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 1.62/0.57    inference(superposition,[],[f179,f136])).
% 1.62/0.57  fof(f136,plain,(
% 1.62/0.57    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.62/0.57    inference(resolution,[],[f134,f67])).
% 1.62/0.57  fof(f67,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f36])).
% 1.62/0.57  fof(f36,plain,(
% 1.62/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.57    inference(ennf_transformation,[],[f13])).
% 1.62/0.57  fof(f13,axiom,(
% 1.62/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.62/0.57  fof(f134,plain,(
% 1.62/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.62/0.57    inference(resolution,[],[f78,f76])).
% 1.62/0.57  fof(f76,plain,(
% 1.62/0.57    r2_hidden(sK2,k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))),
% 1.62/0.57    inference(definition_unfolding,[],[f43,f59])).
% 1.62/0.57  fof(f43,plain,(
% 1.62/0.57    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 1.62/0.57    inference(cnf_transformation,[],[f25])).
% 1.62/0.57  fof(f78,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.62/0.57    inference(definition_unfolding,[],[f66,f59])).
% 1.62/0.57  fof(f66,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_funct_2(X0,X1)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f35])).
% 1.62/0.57  fof(f35,plain,(
% 1.62/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 1.62/0.57    inference(ennf_transformation,[],[f22])).
% 1.62/0.57  fof(f22,plain,(
% 1.62/0.57    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)))),
% 1.62/0.57    inference(pure_predicate_removal,[],[f17])).
% 1.62/0.57  fof(f17,axiom,(
% 1.62/0.57    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 1.62/0.57  fof(f179,plain,(
% 1.62/0.57    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 1.62/0.57    inference(subsumption_resolution,[],[f178,f127])).
% 1.62/0.57  fof(f127,plain,(
% 1.62/0.57    v1_funct_2(sK2,sK0,sK1)),
% 1.62/0.57    inference(resolution,[],[f79,f76])).
% 1.62/0.57  fof(f79,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 1.62/0.57    inference(definition_unfolding,[],[f65,f59])).
% 1.62/0.57  fof(f65,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_funct_2(X0,X1)) | v1_funct_2(X2,X0,X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f35])).
% 1.62/0.57  fof(f178,plain,(
% 1.62/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 1.62/0.57    inference(resolution,[],[f73,f134])).
% 1.62/0.57  fof(f73,plain,(
% 1.62/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f38])).
% 1.62/0.57  fof(f38,plain,(
% 1.62/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.57    inference(flattening,[],[f37])).
% 1.62/0.57  fof(f37,plain,(
% 1.62/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.57    inference(ennf_transformation,[],[f15])).
% 1.62/0.57  fof(f15,axiom,(
% 1.62/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.62/0.57  fof(f151,plain,(
% 1.62/0.57    sK0 != k1_relat_1(sK2) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 1.62/0.57    inference(resolution,[],[f147,f41])).
% 1.62/0.57  fof(f41,plain,(
% 1.62/0.57    ~r1_tarski(k2_relat_1(sK2),sK1) | sK0 != k1_relat_1(sK2)),
% 1.62/0.57    inference(cnf_transformation,[],[f25])).
% 1.62/0.57  fof(f147,plain,(
% 1.62/0.57    r1_tarski(k2_relat_1(sK2),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.62/0.57    inference(superposition,[],[f142,f64])).
% 1.62/0.57  fof(f64,plain,(
% 1.62/0.57    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.62/0.57    inference(cnf_transformation,[],[f34])).
% 1.62/0.57  fof(f34,plain,(
% 1.62/0.57    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.62/0.57    inference(ennf_transformation,[],[f7])).
% 1.62/0.57  fof(f7,axiom,(
% 1.62/0.57    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 1.62/0.57  fof(f142,plain,(
% 1.62/0.57    r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1)))),
% 1.62/0.57    inference(subsumption_resolution,[],[f141,f42])).
% 1.62/0.57  fof(f141,plain,(
% 1.62/0.57    ~v1_relat_1(sK2) | r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1)))),
% 1.62/0.57    inference(subsumption_resolution,[],[f139,f58])).
% 1.62/0.57  fof(f58,plain,(
% 1.62/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f6])).
% 1.62/0.57  fof(f6,axiom,(
% 1.62/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.62/0.57  fof(f139,plain,(
% 1.62/0.57    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~v1_relat_1(sK2) | r1_tarski(k2_relat_1(sK2),k2_relat_1(k2_zfmisc_1(sK0,sK1)))),
% 1.62/0.57    inference(resolution,[],[f137,f55])).
% 1.62/0.57  fof(f55,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))) )),
% 1.62/0.57    inference(cnf_transformation,[],[f31])).
% 1.62/0.57  fof(f31,plain,(
% 1.62/0.57    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.62/0.57    inference(flattening,[],[f30])).
% 1.62/0.57  fof(f30,plain,(
% 1.62/0.57    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.62/0.57    inference(ennf_transformation,[],[f8])).
% 1.62/0.57  fof(f8,axiom,(
% 1.62/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 1.62/0.57  fof(f137,plain,(
% 1.62/0.57    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.62/0.57    inference(resolution,[],[f134,f62])).
% 1.62/0.57  fof(f62,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f5])).
% 1.62/0.57  fof(f221,plain,(
% 1.62/0.57    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.62/0.57    inference(forward_demodulation,[],[f220,f93])).
% 1.62/0.57  fof(f93,plain,(
% 1.62/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.62/0.57    inference(superposition,[],[f47,f91])).
% 1.62/0.57  fof(f220,plain,(
% 1.62/0.57    sK0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = sK1),
% 1.62/0.57    inference(subsumption_resolution,[],[f219,f45])).
% 1.62/0.57  fof(f219,plain,(
% 1.62/0.57    ~r1_tarski(k1_xboole_0,sK1) | sK0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = sK1),
% 1.62/0.57    inference(forward_demodulation,[],[f196,f92])).
% 1.62/0.57  fof(f92,plain,(
% 1.62/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.62/0.57    inference(superposition,[],[f48,f91])).
% 1.62/0.57  fof(f48,plain,(
% 1.62/0.57    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.62/0.57    inference(cnf_transformation,[],[f11])).
% 1.62/0.57  fof(f196,plain,(
% 1.62/0.57    ~r1_tarski(k2_relat_1(k1_xboole_0),sK1) | sK0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = sK1),
% 1.62/0.57    inference(superposition,[],[f41,f195])).
% 1.62/0.57  fof(f195,plain,(
% 1.62/0.57    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.62/0.57    inference(subsumption_resolution,[],[f194,f191])).
% 1.62/0.57  fof(f194,plain,(
% 1.62/0.57    k1_xboole_0 != sK0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.62/0.57    inference(subsumption_resolution,[],[f188,f42])).
% 1.62/0.57  fof(f188,plain,(
% 1.62/0.57    k1_xboole_0 != sK0 | ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.62/0.57    inference(superposition,[],[f50,f180])).
% 1.62/0.57  fof(f87,plain,(
% 1.62/0.57    ~v1_xboole_0(k5_partfun1(sK0,sK1,k3_partfun1(k1_xboole_0,sK0,sK1)))),
% 1.62/0.57    inference(resolution,[],[f76,f57])).
% 1.62/0.57  fof(f57,plain,(
% 1.62/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f1])).
% 1.62/0.57  fof(f1,axiom,(
% 1.62/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.62/0.57  fof(f230,plain,(
% 1.62/0.57    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0))),
% 1.62/0.57    inference(backward_demodulation,[],[f137,f222])).
% 1.62/0.57  fof(f285,plain,(
% 1.62/0.57    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 1.62/0.57    inference(backward_demodulation,[],[f229,f278])).
% 1.62/0.57  fof(f229,plain,(
% 1.62/0.57    k1_relat_1(sK2) = k1_relset_1(sK0,k1_xboole_0,sK2)),
% 1.62/0.57    inference(backward_demodulation,[],[f136,f222])).
% 1.62/0.57  fof(f53,plain,(
% 1.62/0.57    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.62/0.57    inference(cnf_transformation,[],[f29])).
% 1.62/0.57  fof(f29,plain,(
% 1.62/0.57    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.62/0.57    inference(ennf_transformation,[],[f10])).
% 1.62/0.57  fof(f10,axiom,(
% 1.62/0.57    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.62/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 1.62/0.57  fof(f312,plain,(
% 1.62/0.57    ~r1_tarski(k2_relat_1(sK2),k1_xboole_0)),
% 1.62/0.57    inference(trivial_inequality_removal,[],[f308])).
% 1.62/0.57  fof(f308,plain,(
% 1.62/0.57    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k2_relat_1(sK2),k1_xboole_0)),
% 1.62/0.57    inference(backward_demodulation,[],[f279,f307])).
% 1.62/0.57  fof(f279,plain,(
% 1.62/0.57    k1_xboole_0 != k1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),k1_xboole_0)),
% 1.62/0.57    inference(backward_demodulation,[],[f223,f278])).
% 1.62/0.57  fof(f223,plain,(
% 1.62/0.57    ~r1_tarski(k2_relat_1(sK2),k1_xboole_0) | sK0 != k1_relat_1(sK2)),
% 1.62/0.57    inference(backward_demodulation,[],[f41,f222])).
% 1.62/0.57  % SZS output end Proof for theBenchmark
% 1.62/0.57  % (2072)------------------------------
% 1.62/0.57  % (2072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.57  % (2072)Termination reason: Refutation
% 1.62/0.57  
% 1.62/0.57  % (2072)Memory used [KB]: 6396
% 1.62/0.57  % (2072)Time elapsed: 0.116 s
% 1.62/0.57  % (2072)------------------------------
% 1.62/0.57  % (2072)------------------------------
% 1.62/0.58  % (2065)Success in time 0.215 s
%------------------------------------------------------------------------------
