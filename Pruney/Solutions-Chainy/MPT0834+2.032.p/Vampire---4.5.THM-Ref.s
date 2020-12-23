%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 202 expanded)
%              Number of leaves         :   20 (  55 expanded)
%              Depth                    :   27
%              Number of atoms          :  238 ( 504 expanded)
%              Number of equality atoms :   91 ( 224 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f368,plain,(
    $false ),
    inference(subsumption_resolution,[],[f367,f49])).

% (20197)Termination reason: Refutation not found, incomplete strategy
fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f367,plain,(
    ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f366,f40])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

% (20197)Memory used [KB]: 1663
fof(f38,plain,
    ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
      | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f37])).

% (20197)Time elapsed: 0.124 s
% (20197)------------------------------
% (20197)------------------------------
fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
          | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
        | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f366,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f365,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f365,plain,(
    ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f210,f364])).

fof(f364,plain,(
    k10_relat_1(sK2,sK1) != k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f363,f40])).

fof(f363,plain,
    ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(trivial_inequality_removal,[],[f362])).

fof(f362,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f361,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f361,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
    | k10_relat_1(sK2,sK1) != k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f360,f40])).

fof(f360,plain,
    ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f359,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f359,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1)
    | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f358,f40])).

fof(f358,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1)
    | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f357,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f357,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f356,f178])).

fof(f178,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f177,f49])).

fof(f177,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f174,f40])).

fof(f174,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f153,f48])).

fof(f153,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(resolution,[],[f107,f40])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k9_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(superposition,[],[f51,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X0,X1) = X0
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f56,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

% (20184)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
fof(f51,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f356,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(subsumption_resolution,[],[f355,f40])).

fof(f355,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f41,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f41,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

% (20181)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
fof(f210,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f209,f46])).

fof(f46,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f209,plain,(
    k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f208,f49])).

fof(f208,plain,
    ( k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f207,f40])).

fof(f207,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_relat_1(sK2))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f203,f48])).

fof(f203,plain,
    ( ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(superposition,[],[f52,f201])).

fof(f201,plain,(
    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK1) ),
    inference(forward_demodulation,[],[f200,f45])).

fof(f45,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f200,plain,(
    k2_relat_1(k6_relat_1(k2_relat_1(sK2))) = k3_xboole_0(k2_relat_1(sK2),sK1) ),
    inference(forward_demodulation,[],[f199,f113])).

fof(f113,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(forward_demodulation,[],[f112,f45])).

fof(f112,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f111,f50])).

fof(f50,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f111,plain,(
    ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(forward_demodulation,[],[f108,f45])).

fof(f108,plain,(
    ! [X0,X1] : k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f103,f42])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(X0)) ) ),
    inference(resolution,[],[f47,f42])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f199,plain,(
    k2_relat_1(k6_relat_1(k2_relat_1(sK2))) = k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) ),
    inference(subsumption_resolution,[],[f195,f42])).

fof(f195,plain,
    ( k2_relat_1(k6_relat_1(k2_relat_1(sK2))) = k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1)
    | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
    inference(superposition,[],[f51,f193])).

fof(f193,plain,(
    k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) ),
    inference(subsumption_resolution,[],[f192,f42])).

fof(f192,plain,
    ( k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1)
    | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
    inference(resolution,[],[f102,f43])).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),X1)))
      | k7_relat_1(X0,sK1) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f101,f59])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v4_relat_1(X0,k2_relat_1(sK2))
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,sK1) = X0 ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,k2_relat_1(sK2))
      | k7_relat_1(X0,sK1) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f93,f56])).

fof(f93,plain,(
    ! [X0] :
      ( v4_relat_1(X0,sK1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f91,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | v4_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

fof(f91,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(subsumption_resolution,[],[f90,f49])).

fof(f90,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f85,f40])).

fof(f85,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | r1_tarski(k2_relat_1(sK2),sK1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f75,f48])).

fof(f75,plain,
    ( ~ v1_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f68,f40])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k2_relat_1(X0),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f60,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:41:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (20191)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.46  % (20191)Refutation not found, incomplete strategy% (20191)------------------------------
% 0.22/0.46  % (20191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (20191)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (20191)Memory used [KB]: 1663
% 0.22/0.46  % (20191)Time elapsed: 0.004 s
% 0.22/0.46  % (20191)------------------------------
% 0.22/0.46  % (20191)------------------------------
% 0.22/0.48  % (20197)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.49  % (20177)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.49  % (20186)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.49  % (20176)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.49  % (20182)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (20182)Refutation not found, incomplete strategy% (20182)------------------------------
% 0.22/0.50  % (20182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (20182)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (20182)Memory used [KB]: 6140
% 0.22/0.50  % (20182)Time elapsed: 0.083 s
% 0.22/0.50  % (20182)------------------------------
% 0.22/0.50  % (20182)------------------------------
% 0.22/0.50  % (20175)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.50  % (20185)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.50  % (20194)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.50  % (20193)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.50  % (20179)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (20178)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (20192)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.51  % (20178)Refutation not found, incomplete strategy% (20178)------------------------------
% 0.22/0.51  % (20178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20178)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (20178)Memory used [KB]: 10618
% 0.22/0.51  % (20178)Time elapsed: 0.096 s
% 0.22/0.51  % (20178)------------------------------
% 0.22/0.51  % (20178)------------------------------
% 0.22/0.51  % (20187)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.51  % (20192)Refutation not found, incomplete strategy% (20192)------------------------------
% 0.22/0.51  % (20192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20192)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (20192)Memory used [KB]: 1791
% 0.22/0.51  % (20192)Time elapsed: 0.098 s
% 0.22/0.51  % (20192)------------------------------
% 0.22/0.51  % (20192)------------------------------
% 0.22/0.51  % (20190)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.52  % (20196)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (20196)Refutation not found, incomplete strategy% (20196)------------------------------
% 0.22/0.52  % (20196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20196)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (20196)Memory used [KB]: 1663
% 0.22/0.52  % (20196)Time elapsed: 0.092 s
% 0.22/0.52  % (20196)------------------------------
% 0.22/0.52  % (20196)------------------------------
% 0.22/0.52  % (20198)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.52  % (20185)Refutation not found, incomplete strategy% (20185)------------------------------
% 0.22/0.52  % (20185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20185)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (20185)Memory used [KB]: 10618
% 0.22/0.52  % (20185)Time elapsed: 0.104 s
% 0.22/0.52  % (20185)------------------------------
% 0.22/0.52  % (20185)------------------------------
% 0.22/0.52  % (20198)Refutation not found, incomplete strategy% (20198)------------------------------
% 0.22/0.52  % (20198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20198)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (20198)Memory used [KB]: 10618
% 0.22/0.52  % (20198)Time elapsed: 0.106 s
% 0.22/0.52  % (20198)------------------------------
% 0.22/0.52  % (20198)------------------------------
% 0.22/0.52  % (20183)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.52  % (20188)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (20183)Refutation not found, incomplete strategy% (20183)------------------------------
% 0.22/0.52  % (20183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20183)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (20183)Memory used [KB]: 10618
% 0.22/0.52  % (20183)Time elapsed: 0.118 s
% 0.22/0.52  % (20183)------------------------------
% 0.22/0.52  % (20183)------------------------------
% 0.22/0.52  % (20180)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.53  % (20197)Refutation not found, incomplete strategy% (20197)------------------------------
% 0.22/0.53  % (20197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20194)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f368,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f367,f49])).
% 0.22/0.53  % (20197)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.53  fof(f367,plain,(
% 0.22/0.53    ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.53    inference(resolution,[],[f366,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  
% 0.22/0.53  % (20197)Memory used [KB]: 1663
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    (k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f37])).
% 0.22/0.53  % (20197)Time elapsed: 0.124 s
% 0.22/0.53  % (20197)------------------------------
% 0.22/0.53  % (20197)------------------------------
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.22/0.53    inference(negated_conjecture,[],[f19])).
% 0.22/0.53  fof(f19,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.22/0.53  fof(f366,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(resolution,[],[f365,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.53  fof(f365,plain,(
% 0.22/0.53    ~v1_relat_1(sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f210,f364])).
% 0.22/0.53  fof(f364,plain,(
% 0.22/0.53    k10_relat_1(sK2,sK1) != k1_relat_1(sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f363,f40])).
% 0.22/0.53  fof(f363,plain,(
% 0.22/0.53    k10_relat_1(sK2,sK1) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f362])).
% 0.22/0.53  fof(f362,plain,(
% 0.22/0.53    k2_relat_1(sK2) != k2_relat_1(sK2) | k10_relat_1(sK2,sK1) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.53    inference(superposition,[],[f361,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.53  fof(f361,plain,(
% 0.22/0.53    k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2) | k10_relat_1(sK2,sK1) != k1_relat_1(sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f360,f40])).
% 0.22/0.53  fof(f360,plain,(
% 0.22/0.53    k10_relat_1(sK2,sK1) != k1_relat_1(sK2) | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.53    inference(superposition,[],[f359,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.53  fof(f359,plain,(
% 0.22/0.53    k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f358,f40])).
% 0.22/0.53  fof(f358,plain,(
% 0.22/0.53    k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.53    inference(superposition,[],[f357,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.53  fof(f357,plain,(
% 0.22/0.53    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k2_relat_1(sK2)),
% 0.22/0.53    inference(forward_demodulation,[],[f356,f178])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    k2_relat_1(sK2) = k9_relat_1(sK2,sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f177,f49])).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.53    inference(resolution,[],[f174,f40])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | k2_relat_1(sK2) = k9_relat_1(sK2,sK0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(resolution,[],[f153,f48])).
% 0.22/0.53  fof(f153,plain,(
% 0.22/0.53    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k9_relat_1(sK2,sK0)),
% 0.22/0.53    inference(resolution,[],[f107,f40])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_relat_1(X0) | k2_relat_1(X0) = k9_relat_1(X0,X1)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f106])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.53    inference(superposition,[],[f51,f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k7_relat_1(X0,X1) = X0 | ~v1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.53    inference(resolution,[],[f56,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.53  % (20184)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.53  fof(f356,plain,(
% 0.22/0.53    k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0) | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f355,f40])).
% 0.22/0.53  fof(f355,plain,(
% 0.22/0.53    k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0) | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.53    inference(superposition,[],[f41,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  % (20181)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.53  fof(f210,plain,(
% 0.22/0.53    k10_relat_1(sK2,sK1) = k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.53    inference(superposition,[],[f209,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.22/0.53  fof(f209,plain,(
% 0.22/0.53    k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.22/0.53    inference(subsumption_resolution,[],[f208,f49])).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.53    inference(resolution,[],[f207,f40])).
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(resolution,[],[f203,f48])).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    ~v1_relat_1(sK2) | k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.22/0.53    inference(superposition,[],[f52,f201])).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK1)),
% 0.22/0.53    inference(forward_demodulation,[],[f200,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.53  fof(f200,plain,(
% 0.22/0.53    k2_relat_1(k6_relat_1(k2_relat_1(sK2))) = k3_xboole_0(k2_relat_1(sK2),sK1)),
% 0.22/0.53    inference(forward_demodulation,[],[f199,f113])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f112,f45])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),X0) = k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))) )),
% 0.22/0.53    inference(forward_demodulation,[],[f111,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f108,f45])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0)))) )),
% 0.22/0.53    inference(resolution,[],[f103,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),k2_relat_1(X0))) )),
% 0.22/0.53    inference(resolution,[],[f47,f42])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.22/0.53  fof(f199,plain,(
% 0.22/0.53    k2_relat_1(k6_relat_1(k2_relat_1(sK2))) = k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f195,f42])).
% 0.22/0.53  fof(f195,plain,(
% 0.22/0.53    k2_relat_1(k6_relat_1(k2_relat_1(sK2))) = k9_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK2)))),
% 0.22/0.53    inference(superposition,[],[f51,f193])).
% 0.22/0.53  fof(f193,plain,(
% 0.22/0.53    k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f192,f42])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK2)))),
% 0.22/0.53    inference(resolution,[],[f102,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,axiom,(
% 0.22/0.53    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),X1))) | k7_relat_1(X0,sK1) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(resolution,[],[f101,f59])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ( ! [X0] : (~v4_relat_1(X0,k2_relat_1(sK2)) | ~v1_relat_1(X0) | k7_relat_1(X0,sK1) = X0) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f100])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(X0) | ~v4_relat_1(X0,k2_relat_1(sK2)) | k7_relat_1(X0,sK1) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(resolution,[],[f93,f56])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ( ! [X0] : (v4_relat_1(X0,sK1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,k2_relat_1(sK2))) )),
% 0.22/0.53    inference(resolution,[],[f91,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | v4_relat_1(X2,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f90,f49])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.53    inference(resolution,[],[f85,f40])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(resolution,[],[f75,f48])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ~v1_relat_1(sK2) | r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.53    inference(resolution,[],[f68,f40])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k2_relat_1(X0),X2) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(resolution,[],[f60,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (20194)------------------------------
% 0.22/0.53  % (20194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20194)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (20194)Memory used [KB]: 6524
% 0.22/0.53  % (20194)Time elapsed: 0.133 s
% 0.22/0.53  % (20194)------------------------------
% 0.22/0.53  % (20194)------------------------------
% 0.22/0.53  % (20174)Success in time 0.173 s
%------------------------------------------------------------------------------
