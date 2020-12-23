%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 171 expanded)
%              Number of leaves         :   14 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  167 ( 435 expanded)
%              Number of equality atoms :   31 (  41 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f89,f97])).

fof(f97,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f95,f70])).

fof(f70,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f68,f29])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
      | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
        | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

fof(f68,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | r2_relset_1(sK0,sK1,X0,X0) ) ),
    inference(resolution,[],[f41,f29])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f95,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | spl3_2 ),
    inference(forward_demodulation,[],[f94,f64])).

fof(f64,plain,(
    sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) ),
    inference(subsumption_resolution,[],[f62,f46])).

fof(f46,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f38,f29])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f62,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) ),
    inference(resolution,[],[f61,f52])).

fof(f52,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f40,f29])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,k6_partfun1(X1)) = X0
      | ~ v1_relat_1(X0)
      | ~ v5_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f45,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f34,f31])).

fof(f31,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f94,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2)
    | spl3_2 ),
    inference(backward_demodulation,[],[f78,f92])).

fof(f92,plain,(
    ! [X0] : k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0)) = k5_relat_1(sK2,k6_partfun1(X0)) ),
    inference(resolution,[],[f82,f29])).

fof(f82,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k4_relset_1(X3,X4,X5,X5,X6,k6_partfun1(X5)) = k5_relat_1(X6,k6_partfun1(X5)) ) ),
    inference(resolution,[],[f42,f43])).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f78,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_2
  <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f89,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f87,f70])).

fof(f87,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | spl3_1 ),
    inference(forward_demodulation,[],[f86,f56])).

fof(f56,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f54,f46])).

fof(f54,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f37,f50])).

fof(f50,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f39,f29])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f86,plain,
    ( ~ r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2)
    | spl3_1 ),
    inference(backward_demodulation,[],[f74,f85])).

fof(f85,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2) ),
    inference(forward_demodulation,[],[f84,f58])).

fof(f58,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_partfun1(X0),sK2) ),
    inference(resolution,[],[f44,f46])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) ) ),
    inference(definition_unfolding,[],[f33,f31])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f84,plain,(
    ! [X0] : k5_relat_1(k6_partfun1(X0),sK2) = k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2) ),
    inference(resolution,[],[f81,f43])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k4_relset_1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ) ),
    inference(resolution,[],[f42,f29])).

fof(f74,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_1
  <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f79,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f30,f76,f72])).

fof(f30,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:54:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (30676)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.45  % (30676)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f99,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f79,f89,f97])).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    spl3_2),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f96])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    $false | spl3_2),
% 0.21/0.45    inference(subsumption_resolution,[],[f95,f70])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.21/0.45    inference(resolution,[],[f68,f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.45    inference(cnf_transformation,[],[f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    (~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 0.21/0.45    inference(negated_conjecture,[],[f11])).
% 0.21/0.45  fof(f11,conjecture,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | r2_relset_1(sK0,sK1,X0,X0)) )),
% 0.21/0.45    inference(resolution,[],[f41,f29])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(flattening,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.21/0.45  fof(f95,plain,(
% 0.21/0.45    ~r2_relset_1(sK0,sK1,sK2,sK2) | spl3_2),
% 0.21/0.45    inference(forward_demodulation,[],[f94,f64])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    sK2 = k5_relat_1(sK2,k6_partfun1(sK1))),
% 0.21/0.45    inference(subsumption_resolution,[],[f62,f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    v1_relat_1(sK2)),
% 0.21/0.45    inference(resolution,[],[f38,f29])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    ~v1_relat_1(sK2) | sK2 = k5_relat_1(sK2,k6_partfun1(sK1))),
% 0.21/0.45    inference(resolution,[],[f61,f52])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    v5_relat_1(sK2,sK1)),
% 0.21/0.45    inference(resolution,[],[f40,f29])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v5_relat_1(X0,X1) | ~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(X1)) = X0) )),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f60])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k5_relat_1(X0,k6_partfun1(X1)) = X0 | ~v1_relat_1(X0) | ~v5_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(resolution,[],[f45,f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(nnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f34,f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,axiom,(
% 0.21/0.45    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(flattening,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    ~r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2) | spl3_2),
% 0.21/0.45    inference(backward_demodulation,[],[f78,f92])).
% 0.21/0.45  fof(f92,plain,(
% 0.21/0.45    ( ! [X0] : (k4_relset_1(sK0,sK1,X0,X0,sK2,k6_partfun1(X0)) = k5_relat_1(sK2,k6_partfun1(X0))) )),
% 0.21/0.45    inference(resolution,[],[f82,f29])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    ( ! [X6,X4,X5,X3] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k4_relset_1(X3,X4,X5,X5,X6,k6_partfun1(X5)) = k5_relat_1(X6,k6_partfun1(X5))) )),
% 0.21/0.45    inference(resolution,[],[f42,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f32,f31])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(flattening,[],[f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f76])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    spl3_2 <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.45  fof(f89,plain,(
% 0.21/0.45    spl3_1),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f88])).
% 0.21/0.45  fof(f88,plain,(
% 0.21/0.45    $false | spl3_1),
% 0.21/0.45    inference(subsumption_resolution,[],[f87,f70])).
% 0.21/0.45  fof(f87,plain,(
% 0.21/0.45    ~r2_relset_1(sK0,sK1,sK2,sK2) | spl3_1),
% 0.21/0.45    inference(forward_demodulation,[],[f86,f56])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    sK2 = k7_relat_1(sK2,sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f54,f46])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    sK2 = k7_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 0.21/0.45    inference(resolution,[],[f37,f50])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    v4_relat_1(sK2,sK0)),
% 0.21/0.45    inference(resolution,[],[f39,f29])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(flattening,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    ~r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2) | spl3_1),
% 0.21/0.45    inference(backward_demodulation,[],[f74,f85])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    ( ! [X0] : (k7_relat_1(sK2,X0) = k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2)) )),
% 0.21/0.45    inference(forward_demodulation,[],[f84,f58])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_partfun1(X0),sK2)) )),
% 0.21/0.45    inference(resolution,[],[f44,f46])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f33,f31])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    ( ! [X0] : (k5_relat_1(k6_partfun1(X0),sK2) = k4_relset_1(X0,X0,sK0,sK1,k6_partfun1(X0),sK2)) )),
% 0.21/0.45    inference(resolution,[],[f81,f43])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k4_relset_1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)) )),
% 0.21/0.45    inference(resolution,[],[f42,f29])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) | spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f72])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    spl3_1 <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    ~spl3_1 | ~spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f30,f76,f72])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (30676)------------------------------
% 0.21/0.46  % (30676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (30676)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (30676)Memory used [KB]: 10618
% 0.21/0.46  % (30676)Time elapsed: 0.006 s
% 0.21/0.46  % (30676)------------------------------
% 0.21/0.46  % (30676)------------------------------
% 0.21/0.46  % (30666)Success in time 0.086 s
%------------------------------------------------------------------------------
