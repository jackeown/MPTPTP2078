%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:20 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 184 expanded)
%              Number of leaves         :   16 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  194 ( 480 expanded)
%              Number of equality atoms :   42 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f117,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f106,f116])).

fof(f116,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f114,f89])).

fof(f89,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f54,f33])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
      | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
        | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    inference(negated_conjecture,[],[f13])).

% (14124)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f114,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | spl3_2 ),
    inference(forward_demodulation,[],[f113,f93])).

fof(f93,plain,(
    sK2 = k8_relat_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f91,f66])).

fof(f66,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f64,f39])).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f64,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f38,f33])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f91,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k8_relat_1(sK1,sK2) ),
    inference(resolution,[],[f86,f72])).

fof(f72,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f47,f33])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f42,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f113,plain,
    ( ~ r2_relset_1(sK0,sK1,k8_relat_1(sK1,sK2),sK2)
    | spl3_2 ),
    inference(backward_demodulation,[],[f62,f111])).

fof(f111,plain,(
    ! [X0] : k8_relat_1(X0,sK2) = k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0)) ),
    inference(forward_demodulation,[],[f109,f79])).

fof(f79,plain,(
    ! [X3] : k8_relat_1(X3,sK2) = k5_relat_1(sK2,k6_partfun1(X3)) ),
    inference(resolution,[],[f51,f66])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_partfun1(X0)) ) ),
    inference(definition_unfolding,[],[f40,f35])).

fof(f35,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f109,plain,(
    ! [X0] : k5_relat_1(sK2,k6_partfun1(X0)) = k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0)) ),
    inference(resolution,[],[f98,f33])).

fof(f98,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k4_relset_1(X3,X4,X5,X5,X6,k6_partfun1(X5)) = k5_relat_1(X6,k6_partfun1(X5)) ) ),
    inference(resolution,[],[f50,f37])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f62,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_2
  <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f106,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f104,f89])).

fof(f104,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | spl3_1 ),
    inference(forward_demodulation,[],[f103,f76])).

fof(f76,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f74,f66])).

fof(f74,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f45,f70])).

fof(f70,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f46,f33])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f103,plain,
    ( ~ r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2)
    | spl3_1 ),
    inference(backward_demodulation,[],[f58,f101])).

fof(f101,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2) ),
    inference(forward_demodulation,[],[f100,f82])).

fof(f82,plain,(
    ! [X3] : k7_relat_1(sK2,X3) = k5_relat_1(k6_partfun1(X3),sK2) ),
    inference(resolution,[],[f52,f66])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) ) ),
    inference(definition_unfolding,[],[f41,f35])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f100,plain,(
    ! [X0] : k5_relat_1(k6_partfun1(X0),sK2) = k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2) ),
    inference(resolution,[],[f97,f37])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k4_relset_1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ) ),
    inference(resolution,[],[f50,f33])).

fof(f58,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_1
  <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f63,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f34,f60,f56])).

fof(f34,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:59:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.24/0.55  % (14128)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.24/0.56  % (14128)Refutation found. Thanks to Tanya!
% 1.24/0.56  % SZS status Theorem for theBenchmark
% 1.58/0.57  % (14140)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.58/0.57  % (14144)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.58/0.57  % SZS output start Proof for theBenchmark
% 1.58/0.57  fof(f117,plain,(
% 1.58/0.57    $false),
% 1.58/0.57    inference(avatar_sat_refutation,[],[f63,f106,f116])).
% 1.58/0.57  fof(f116,plain,(
% 1.58/0.57    spl3_2),
% 1.58/0.57    inference(avatar_contradiction_clause,[],[f115])).
% 1.58/0.57  fof(f115,plain,(
% 1.58/0.57    $false | spl3_2),
% 1.58/0.57    inference(subsumption_resolution,[],[f114,f89])).
% 1.58/0.57  fof(f89,plain,(
% 1.58/0.57    r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.58/0.57    inference(resolution,[],[f54,f33])).
% 1.58/0.57  fof(f33,plain,(
% 1.58/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.58/0.57    inference(cnf_transformation,[],[f30])).
% 1.58/0.57  fof(f30,plain,(
% 1.58/0.57    (~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.58/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f29])).
% 1.58/0.57  fof(f29,plain,(
% 1.58/0.57    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 1.58/0.57    introduced(choice_axiom,[])).
% 1.58/0.57  fof(f15,plain,(
% 1.58/0.57    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.57    inference(ennf_transformation,[],[f14])).
% 1.58/0.57  fof(f14,negated_conjecture,(
% 1.58/0.57    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 1.58/0.57    inference(negated_conjecture,[],[f13])).
% 1.58/0.57  % (14124)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.58/0.57  fof(f13,conjecture,(
% 1.58/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).
% 1.58/0.57  fof(f54,plain,(
% 1.58/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.58/0.57    inference(duplicate_literal_removal,[],[f53])).
% 1.58/0.57  fof(f53,plain,(
% 1.58/0.57    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.58/0.57    inference(equality_resolution,[],[f49])).
% 1.58/0.57  fof(f49,plain,(
% 1.58/0.57    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f32])).
% 1.58/0.57  fof(f32,plain,(
% 1.58/0.57    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.57    inference(nnf_transformation,[],[f26])).
% 1.58/0.57  fof(f26,plain,(
% 1.58/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.57    inference(flattening,[],[f25])).
% 1.58/0.57  fof(f25,plain,(
% 1.58/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.58/0.57    inference(ennf_transformation,[],[f10])).
% 1.58/0.57  fof(f10,axiom,(
% 1.58/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.58/0.57  fof(f114,plain,(
% 1.58/0.57    ~r2_relset_1(sK0,sK1,sK2,sK2) | spl3_2),
% 1.58/0.57    inference(forward_demodulation,[],[f113,f93])).
% 1.58/0.57  fof(f93,plain,(
% 1.58/0.57    sK2 = k8_relat_1(sK1,sK2)),
% 1.58/0.57    inference(subsumption_resolution,[],[f91,f66])).
% 1.58/0.57  fof(f66,plain,(
% 1.58/0.57    v1_relat_1(sK2)),
% 1.58/0.57    inference(subsumption_resolution,[],[f64,f39])).
% 1.58/0.57  fof(f39,plain,(
% 1.58/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f3])).
% 1.58/0.57  fof(f3,axiom,(
% 1.58/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.58/0.57  fof(f64,plain,(
% 1.58/0.57    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.58/0.57    inference(resolution,[],[f38,f33])).
% 1.58/0.57  fof(f38,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f16])).
% 1.58/0.57  fof(f16,plain,(
% 1.58/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.58/0.57    inference(ennf_transformation,[],[f1])).
% 1.58/0.57  fof(f1,axiom,(
% 1.58/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.58/0.57  fof(f91,plain,(
% 1.58/0.57    ~v1_relat_1(sK2) | sK2 = k8_relat_1(sK1,sK2)),
% 1.58/0.57    inference(resolution,[],[f86,f72])).
% 1.58/0.57  fof(f72,plain,(
% 1.58/0.57    v5_relat_1(sK2,sK1)),
% 1.58/0.57    inference(resolution,[],[f47,f33])).
% 1.58/0.57  fof(f47,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f24])).
% 1.58/0.57  fof(f24,plain,(
% 1.58/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.57    inference(ennf_transformation,[],[f8])).
% 1.58/0.57  fof(f8,axiom,(
% 1.58/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.58/0.57  fof(f86,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | k8_relat_1(X0,X1) = X1) )),
% 1.58/0.57    inference(duplicate_literal_removal,[],[f85])).
% 1.58/0.57  fof(f85,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.58/0.57    inference(resolution,[],[f42,f43])).
% 1.58/0.57  fof(f43,plain,(
% 1.58/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f31])).
% 1.58/0.57  fof(f31,plain,(
% 1.58/0.57    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.58/0.57    inference(nnf_transformation,[],[f21])).
% 1.58/0.57  fof(f21,plain,(
% 1.58/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.58/0.57    inference(ennf_transformation,[],[f2])).
% 1.58/0.57  fof(f2,axiom,(
% 1.58/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.58/0.57  fof(f42,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f20])).
% 1.58/0.57  fof(f20,plain,(
% 1.58/0.57    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.58/0.57    inference(flattening,[],[f19])).
% 1.58/0.57  fof(f19,plain,(
% 1.58/0.57    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.58/0.57    inference(ennf_transformation,[],[f5])).
% 1.58/0.57  fof(f5,axiom,(
% 1.58/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 1.58/0.57  fof(f113,plain,(
% 1.58/0.57    ~r2_relset_1(sK0,sK1,k8_relat_1(sK1,sK2),sK2) | spl3_2),
% 1.58/0.57    inference(backward_demodulation,[],[f62,f111])).
% 1.58/0.57  fof(f111,plain,(
% 1.58/0.57    ( ! [X0] : (k8_relat_1(X0,sK2) = k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0))) )),
% 1.58/0.57    inference(forward_demodulation,[],[f109,f79])).
% 1.58/0.57  fof(f79,plain,(
% 1.58/0.57    ( ! [X3] : (k8_relat_1(X3,sK2) = k5_relat_1(sK2,k6_partfun1(X3))) )),
% 1.58/0.57    inference(resolution,[],[f51,f66])).
% 1.58/0.57  fof(f51,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_partfun1(X0))) )),
% 1.58/0.57    inference(definition_unfolding,[],[f40,f35])).
% 1.58/0.57  fof(f35,plain,(
% 1.58/0.57    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f12])).
% 1.58/0.57  fof(f12,axiom,(
% 1.58/0.57    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.58/0.57  fof(f40,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f17])).
% 1.58/0.57  fof(f17,plain,(
% 1.58/0.57    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.58/0.57    inference(ennf_transformation,[],[f4])).
% 1.58/0.57  fof(f4,axiom,(
% 1.58/0.57    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 1.58/0.57  fof(f109,plain,(
% 1.58/0.57    ( ! [X0] : (k5_relat_1(sK2,k6_partfun1(X0)) = k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0))) )),
% 1.58/0.57    inference(resolution,[],[f98,f33])).
% 1.58/0.57  fof(f98,plain,(
% 1.58/0.57    ( ! [X6,X4,X5,X3] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k4_relset_1(X3,X4,X5,X5,X6,k6_partfun1(X5)) = k5_relat_1(X6,k6_partfun1(X5))) )),
% 1.58/0.57    inference(resolution,[],[f50,f37])).
% 1.58/0.57  fof(f37,plain,(
% 1.58/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f11])).
% 1.58/0.57  fof(f11,axiom,(
% 1.58/0.57    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.58/0.57  fof(f50,plain,(
% 1.58/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.58/0.57    inference(cnf_transformation,[],[f28])).
% 1.58/0.57  fof(f28,plain,(
% 1.58/0.57    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.57    inference(flattening,[],[f27])).
% 1.58/0.57  fof(f27,plain,(
% 1.58/0.57    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.58/0.57    inference(ennf_transformation,[],[f9])).
% 1.58/0.57  fof(f9,axiom,(
% 1.58/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 1.58/0.57  fof(f62,plain,(
% 1.58/0.57    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | spl3_2),
% 1.58/0.57    inference(avatar_component_clause,[],[f60])).
% 1.58/0.57  fof(f60,plain,(
% 1.58/0.57    spl3_2 <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)),
% 1.58/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.58/0.57  fof(f106,plain,(
% 1.58/0.57    spl3_1),
% 1.58/0.57    inference(avatar_contradiction_clause,[],[f105])).
% 1.58/0.57  fof(f105,plain,(
% 1.58/0.57    $false | spl3_1),
% 1.58/0.57    inference(subsumption_resolution,[],[f104,f89])).
% 1.58/0.57  fof(f104,plain,(
% 1.58/0.57    ~r2_relset_1(sK0,sK1,sK2,sK2) | spl3_1),
% 1.58/0.57    inference(forward_demodulation,[],[f103,f76])).
% 1.58/0.57  fof(f76,plain,(
% 1.58/0.57    sK2 = k7_relat_1(sK2,sK0)),
% 1.58/0.57    inference(subsumption_resolution,[],[f74,f66])).
% 1.58/0.57  fof(f74,plain,(
% 1.58/0.57    sK2 = k7_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 1.58/0.57    inference(resolution,[],[f45,f70])).
% 1.58/0.57  fof(f70,plain,(
% 1.58/0.57    v4_relat_1(sK2,sK0)),
% 1.58/0.57    inference(resolution,[],[f46,f33])).
% 1.58/0.57  fof(f46,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f24])).
% 1.58/0.57  fof(f45,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f23])).
% 1.58/0.57  fof(f23,plain,(
% 1.58/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.58/0.57    inference(flattening,[],[f22])).
% 1.58/0.57  fof(f22,plain,(
% 1.58/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.58/0.57    inference(ennf_transformation,[],[f6])).
% 1.58/0.57  fof(f6,axiom,(
% 1.58/0.57    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.58/0.57  fof(f103,plain,(
% 1.58/0.57    ~r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2) | spl3_1),
% 1.58/0.57    inference(backward_demodulation,[],[f58,f101])).
% 1.58/0.57  fof(f101,plain,(
% 1.58/0.57    ( ! [X0] : (k7_relat_1(sK2,X0) = k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2)) )),
% 1.58/0.57    inference(forward_demodulation,[],[f100,f82])).
% 1.58/0.57  fof(f82,plain,(
% 1.58/0.57    ( ! [X3] : (k7_relat_1(sK2,X3) = k5_relat_1(k6_partfun1(X3),sK2)) )),
% 1.58/0.57    inference(resolution,[],[f52,f66])).
% 1.58/0.57  fof(f52,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)) )),
% 1.58/0.57    inference(definition_unfolding,[],[f41,f35])).
% 1.58/0.57  fof(f41,plain,(
% 1.58/0.57    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.58/0.57    inference(cnf_transformation,[],[f18])).
% 1.58/0.57  fof(f18,plain,(
% 1.58/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.58/0.57    inference(ennf_transformation,[],[f7])).
% 1.58/0.57  fof(f7,axiom,(
% 1.58/0.57    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.58/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.58/0.57  fof(f100,plain,(
% 1.58/0.57    ( ! [X0] : (k5_relat_1(k6_partfun1(X0),sK2) = k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2)) )),
% 1.58/0.57    inference(resolution,[],[f97,f37])).
% 1.58/0.57  fof(f97,plain,(
% 1.58/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k4_relset_1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)) )),
% 1.58/0.57    inference(resolution,[],[f50,f33])).
% 1.58/0.57  fof(f58,plain,(
% 1.58/0.57    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) | spl3_1),
% 1.58/0.57    inference(avatar_component_clause,[],[f56])).
% 1.58/0.57  fof(f56,plain,(
% 1.58/0.57    spl3_1 <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 1.58/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.58/0.57  fof(f63,plain,(
% 1.58/0.57    ~spl3_1 | ~spl3_2),
% 1.58/0.57    inference(avatar_split_clause,[],[f34,f60,f56])).
% 1.58/0.57  fof(f34,plain,(
% 1.58/0.57    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 1.58/0.57    inference(cnf_transformation,[],[f30])).
% 1.58/0.57  % SZS output end Proof for theBenchmark
% 1.58/0.57  % (14128)------------------------------
% 1.58/0.57  % (14128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.57  % (14128)Termination reason: Refutation
% 1.58/0.57  
% 1.58/0.57  % (14128)Memory used [KB]: 10746
% 1.58/0.57  % (14128)Time elapsed: 0.133 s
% 1.58/0.57  % (14128)------------------------------
% 1.58/0.57  % (14128)------------------------------
% 1.58/0.58  % (14120)Success in time 0.213 s
%------------------------------------------------------------------------------
