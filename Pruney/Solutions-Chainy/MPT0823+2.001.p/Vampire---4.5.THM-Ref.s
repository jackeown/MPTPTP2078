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
% DateTime   : Thu Dec  3 12:56:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 289 expanded)
%              Number of leaves         :   11 (  65 expanded)
%              Depth                    :   20
%              Number of atoms          :  242 ( 729 expanded)
%              Number of equality atoms :   62 ( 220 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f261,plain,(
    $false ),
    inference(subsumption_resolution,[],[f260,f43])).

fof(f43,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f35,f26])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        | k2_relset_1(X0,X1,X2) != k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
          & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).

fof(f35,plain,(
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

fof(f260,plain,(
    ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f259,f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f259,plain,(
    ~ v1_relat_1(k4_relat_1(sK2)) ),
    inference(global_subsumption,[],[f96,f254,f258])).

fof(f258,plain,
    ( k2_relat_1(sK2) = k1_relset_1(sK1,sK0,k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f257,f54])).

fof(f54,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f39,f26])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f257,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK2,X0)
      | k2_relat_1(sK2) = k1_relset_1(sK1,X0,k4_relat_1(sK2))
      | ~ v1_relat_1(k4_relat_1(sK2)) ) ),
    inference(resolution,[],[f256,f55])).

fof(f55,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f40,f26])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f256,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(sK2,X0)
      | k2_relat_1(sK2) = k1_relset_1(X0,X1,k4_relat_1(sK2))
      | ~ v4_relat_1(sK2,X1)
      | ~ v1_relat_1(k4_relat_1(sK2)) ) ),
    inference(duplicate_literal_removal,[],[f255])).

fof(f255,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k4_relat_1(sK2))
      | k2_relat_1(sK2) = k1_relset_1(X0,X1,k4_relat_1(sK2))
      | ~ v4_relat_1(sK2,X1)
      | ~ v1_relat_1(k4_relat_1(sK2))
      | ~ v5_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f203,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v4_relat_1(k4_relat_1(sK2),X0)
      | ~ v1_relat_1(k4_relat_1(sK2))
      | ~ v5_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f66,f43])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k4_relat_1(sK2))
      | v4_relat_1(k4_relat_1(sK2),X0)
      | ~ v1_relat_1(sK2)
      | ~ v5_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f46,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f46,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | ~ v1_relat_1(k4_relat_1(sK2))
      | v4_relat_1(k4_relat_1(sK2),X0) ) ),
    inference(superposition,[],[f30,f45])).

fof(f45,plain,(
    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f43,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f203,plain,(
    ! [X2,X1] :
      ( ~ v4_relat_1(k4_relat_1(sK2),X1)
      | ~ v1_relat_1(k4_relat_1(sK2))
      | k2_relat_1(sK2) = k1_relset_1(X1,X2,k4_relat_1(sK2))
      | ~ v4_relat_1(sK2,X2) ) ),
    inference(forward_demodulation,[],[f201,f45])).

fof(f201,plain,(
    ! [X2,X1] :
      ( k1_relat_1(k4_relat_1(sK2)) = k1_relset_1(X1,X2,k4_relat_1(sK2))
      | ~ v1_relat_1(k4_relat_1(sK2))
      | ~ v4_relat_1(k4_relat_1(sK2),X1)
      | ~ v4_relat_1(sK2,X2) ) ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,(
    ! [X2,X1] :
      ( k1_relat_1(k4_relat_1(sK2)) = k1_relset_1(X1,X2,k4_relat_1(sK2))
      | ~ v1_relat_1(k4_relat_1(sK2))
      | ~ v4_relat_1(k4_relat_1(sK2),X1)
      | ~ v1_relat_1(k4_relat_1(sK2))
      | ~ v4_relat_1(sK2,X2) ) ),
    inference(resolution,[],[f194,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v5_relat_1(k4_relat_1(sK2),X0)
      | ~ v1_relat_1(k4_relat_1(sK2))
      | ~ v4_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f73,f43])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k4_relat_1(sK2))
      | v5_relat_1(k4_relat_1(sK2),X0)
      | ~ v1_relat_1(sK2)
      | ~ v4_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f50,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | ~ v1_relat_1(k4_relat_1(sK2))
      | v5_relat_1(k4_relat_1(sK2),X0) ) ),
    inference(superposition,[],[f32,f44])).

fof(f44,plain,(
    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f43,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X0,X2)
      | k1_relat_1(X0) = k1_relset_1(X1,X2,X0)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relset_1(X1,X2,X0)
      | ~ v5_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(resolution,[],[f176,f31])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relset_1(X1,X2,X0)
      | ~ v5_relat_1(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k1_relset_1(X1,X2,X0)
      | ~ v1_relat_1(X0)
      | ~ v5_relat_1(X0,X2) ) ),
    inference(resolution,[],[f116,f33])).

fof(f116,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k2_relat_1(X3),X5)
      | ~ r1_tarski(k1_relat_1(X3),X4)
      | ~ v1_relat_1(X3)
      | k1_relat_1(X3) = k1_relset_1(X4,X5,X3) ) ),
    inference(resolution,[],[f34,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f254,plain,(
    k1_relat_1(sK2) = k2_relset_1(sK1,sK0,k4_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f253,f43])).

fof(f253,plain,
    ( k1_relat_1(sK2) = k2_relset_1(sK1,sK0,k4_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f252,f27])).

fof(f252,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | k1_relat_1(sK2) = k2_relset_1(sK1,sK0,k4_relat_1(sK2)) ),
    inference(resolution,[],[f251,f54])).

fof(f251,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK2,X0)
      | k1_relat_1(sK2) = k2_relset_1(sK1,X0,k4_relat_1(sK2))
      | ~ v1_relat_1(k4_relat_1(sK2)) ) ),
    inference(resolution,[],[f250,f55])).

fof(f250,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(sK2,X0)
      | k1_relat_1(sK2) = k2_relset_1(X0,X1,k4_relat_1(sK2))
      | ~ v4_relat_1(sK2,X1)
      | ~ v1_relat_1(k4_relat_1(sK2)) ) ),
    inference(duplicate_literal_removal,[],[f249])).

fof(f249,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k4_relat_1(sK2))
      | k1_relat_1(sK2) = k2_relset_1(X0,X1,k4_relat_1(sK2))
      | ~ v4_relat_1(sK2,X1)
      | ~ v1_relat_1(k4_relat_1(sK2))
      | ~ v5_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f165,f67])).

fof(f165,plain,(
    ! [X2,X1] :
      ( ~ v4_relat_1(k4_relat_1(sK2),X1)
      | ~ v1_relat_1(k4_relat_1(sK2))
      | k1_relat_1(sK2) = k2_relset_1(X1,X2,k4_relat_1(sK2))
      | ~ v4_relat_1(sK2,X2) ) ),
    inference(forward_demodulation,[],[f163,f44])).

fof(f163,plain,(
    ! [X2,X1] :
      ( k2_relat_1(k4_relat_1(sK2)) = k2_relset_1(X1,X2,k4_relat_1(sK2))
      | ~ v1_relat_1(k4_relat_1(sK2))
      | ~ v4_relat_1(k4_relat_1(sK2),X1)
      | ~ v4_relat_1(sK2,X2) ) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,(
    ! [X2,X1] :
      ( k2_relat_1(k4_relat_1(sK2)) = k2_relset_1(X1,X2,k4_relat_1(sK2))
      | ~ v1_relat_1(k4_relat_1(sK2))
      | ~ v4_relat_1(k4_relat_1(sK2),X1)
      | ~ v1_relat_1(k4_relat_1(sK2))
      | ~ v4_relat_1(sK2,X2) ) ),
    inference(resolution,[],[f151,f74])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X0,X2)
      | k2_relat_1(X0) = k2_relset_1(X1,X2,X0)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k2_relset_1(X1,X2,X0)
      | ~ v5_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(resolution,[],[f138,f31])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k2_relset_1(X1,X2,X0)
      | ~ v5_relat_1(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k2_relset_1(X1,X2,X0)
      | ~ v1_relat_1(X0)
      | ~ v5_relat_1(X0,X2) ) ),
    inference(resolution,[],[f115,f33])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),X2)
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k2_relset_1(X1,X2,X0) ) ),
    inference(resolution,[],[f34,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f96,plain,
    ( k2_relat_1(sK2) != k1_relset_1(sK1,sK0,k4_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f94,f95])).

fof(f95,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f38,f26])).

fof(f94,plain,
    ( k1_relat_1(sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))
    | k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f92,f93])).

fof(f93,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f37,f26])).

fof(f92,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k4_relat_1(sK2))
    | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f91,f90])).

fof(f90,plain,(
    k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2) ),
    inference(resolution,[],[f36,f26])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f91,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))
    | k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f25,f90])).

fof(f25,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))
    | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:25:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (18297)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.48  % (18297)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (18305)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f261,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f260,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    v1_relat_1(sK2)),
% 0.21/0.49    inference(resolution,[],[f35,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) | k2_relset_1(X0,X1,X2) != k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))))),
% 0.21/0.49    inference(negated_conjecture,[],[f11])).
% 0.21/0.49  fof(f11,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f260,plain,(
% 0.21/0.49    ~v1_relat_1(sK2)),
% 0.21/0.49    inference(resolution,[],[f259,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.49  fof(f259,plain,(
% 0.21/0.49    ~v1_relat_1(k4_relat_1(sK2))),
% 0.21/0.49    inference(global_subsumption,[],[f96,f254,f258])).
% 0.21/0.49  fof(f258,plain,(
% 0.21/0.49    k2_relat_1(sK2) = k1_relset_1(sK1,sK0,k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2))),
% 0.21/0.49    inference(resolution,[],[f257,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    v4_relat_1(sK2,sK0)),
% 0.21/0.49    inference(resolution,[],[f39,f26])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_relat_1(sK2,X0) | k2_relat_1(sK2) = k1_relset_1(sK1,X0,k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2))) )),
% 0.21/0.50    inference(resolution,[],[f256,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    v5_relat_1(sK2,sK1)),
% 0.21/0.50    inference(resolution,[],[f40,f26])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f256,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v5_relat_1(sK2,X0) | k2_relat_1(sK2) = k1_relset_1(X0,X1,k4_relat_1(sK2)) | ~v4_relat_1(sK2,X1) | ~v1_relat_1(k4_relat_1(sK2))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f255])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(k4_relat_1(sK2)) | k2_relat_1(sK2) = k1_relset_1(X0,X1,k4_relat_1(sK2)) | ~v4_relat_1(sK2,X1) | ~v1_relat_1(k4_relat_1(sK2)) | ~v5_relat_1(sK2,X0)) )),
% 0.21/0.50    inference(resolution,[],[f203,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0] : (v4_relat_1(k4_relat_1(sK2),X0) | ~v1_relat_1(k4_relat_1(sK2)) | ~v5_relat_1(sK2,X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f66,f43])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(k4_relat_1(sK2)) | v4_relat_1(k4_relat_1(sK2),X0) | ~v1_relat_1(sK2) | ~v5_relat_1(sK2,X0)) )),
% 0.21/0.50    inference(resolution,[],[f46,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | ~v1_relat_1(k4_relat_1(sK2)) | v4_relat_1(k4_relat_1(sK2),X0)) )),
% 0.21/0.50    inference(superposition,[],[f30,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))),
% 0.21/0.50    inference(resolution,[],[f43,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | v4_relat_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~v4_relat_1(k4_relat_1(sK2),X1) | ~v1_relat_1(k4_relat_1(sK2)) | k2_relat_1(sK2) = k1_relset_1(X1,X2,k4_relat_1(sK2)) | ~v4_relat_1(sK2,X2)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f201,f45])).
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k1_relat_1(k4_relat_1(sK2)) = k1_relset_1(X1,X2,k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | ~v4_relat_1(k4_relat_1(sK2),X1) | ~v4_relat_1(sK2,X2)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f196])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k1_relat_1(k4_relat_1(sK2)) = k1_relset_1(X1,X2,k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | ~v4_relat_1(k4_relat_1(sK2),X1) | ~v1_relat_1(k4_relat_1(sK2)) | ~v4_relat_1(sK2,X2)) )),
% 0.21/0.50    inference(resolution,[],[f194,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X0] : (v5_relat_1(k4_relat_1(sK2),X0) | ~v1_relat_1(k4_relat_1(sK2)) | ~v4_relat_1(sK2,X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f73,f43])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(k4_relat_1(sK2)) | v5_relat_1(k4_relat_1(sK2),X0) | ~v1_relat_1(sK2) | ~v4_relat_1(sK2,X0)) )),
% 0.21/0.50    inference(resolution,[],[f50,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | ~v1_relat_1(k4_relat_1(sK2)) | v5_relat_1(k4_relat_1(sK2),X0)) )),
% 0.21/0.50    inference(superposition,[],[f32,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 0.21/0.50    inference(resolution,[],[f43,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | v5_relat_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v5_relat_1(X0,X2) | k1_relat_1(X0) = k1_relset_1(X1,X2,X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f187])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k1_relat_1(X0) = k1_relset_1(X1,X2,X0) | ~v5_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 0.21/0.50    inference(resolution,[],[f176,f31])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relset_1(X1,X2,X0) | ~v5_relat_1(X0,X2)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f169])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | k1_relat_1(X0) = k1_relset_1(X1,X2,X0) | ~v1_relat_1(X0) | ~v5_relat_1(X0,X2)) )),
% 0.21/0.50    inference(resolution,[],[f116,f33])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (~r1_tarski(k2_relat_1(X3),X5) | ~r1_tarski(k1_relat_1(X3),X4) | ~v1_relat_1(X3) | k1_relat_1(X3) = k1_relset_1(X4,X5,X3)) )),
% 0.21/0.50    inference(resolution,[],[f34,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relset_1(sK1,sK0,k4_relat_1(sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f253,f43])).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relset_1(sK1,sK0,k4_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f252,f27])).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    ~v1_relat_1(k4_relat_1(sK2)) | k1_relat_1(sK2) = k2_relset_1(sK1,sK0,k4_relat_1(sK2))),
% 0.21/0.50    inference(resolution,[],[f251,f54])).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_relat_1(sK2,X0) | k1_relat_1(sK2) = k2_relset_1(sK1,X0,k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2))) )),
% 0.21/0.50    inference(resolution,[],[f250,f55])).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v5_relat_1(sK2,X0) | k1_relat_1(sK2) = k2_relset_1(X0,X1,k4_relat_1(sK2)) | ~v4_relat_1(sK2,X1) | ~v1_relat_1(k4_relat_1(sK2))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f249])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(k4_relat_1(sK2)) | k1_relat_1(sK2) = k2_relset_1(X0,X1,k4_relat_1(sK2)) | ~v4_relat_1(sK2,X1) | ~v1_relat_1(k4_relat_1(sK2)) | ~v5_relat_1(sK2,X0)) )),
% 0.21/0.50    inference(resolution,[],[f165,f67])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~v4_relat_1(k4_relat_1(sK2),X1) | ~v1_relat_1(k4_relat_1(sK2)) | k1_relat_1(sK2) = k2_relset_1(X1,X2,k4_relat_1(sK2)) | ~v4_relat_1(sK2,X2)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f163,f44])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k2_relat_1(k4_relat_1(sK2)) = k2_relset_1(X1,X2,k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | ~v4_relat_1(k4_relat_1(sK2),X1) | ~v4_relat_1(sK2,X2)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f158])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k2_relat_1(k4_relat_1(sK2)) = k2_relset_1(X1,X2,k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | ~v4_relat_1(k4_relat_1(sK2),X1) | ~v1_relat_1(k4_relat_1(sK2)) | ~v4_relat_1(sK2,X2)) )),
% 0.21/0.50    inference(resolution,[],[f151,f74])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v5_relat_1(X0,X2) | k2_relat_1(X0) = k2_relset_1(X1,X2,X0) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f144])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k2_relat_1(X0) = k2_relset_1(X1,X2,X0) | ~v5_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 0.21/0.50    inference(resolution,[],[f138,f31])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | k2_relat_1(X0) = k2_relset_1(X1,X2,X0) | ~v5_relat_1(X0,X2)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f131])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | k2_relat_1(X0) = k2_relset_1(X1,X2,X0) | ~v1_relat_1(X0) | ~v5_relat_1(X0,X2)) )),
% 0.21/0.50    inference(resolution,[],[f115,f33])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X0),X2) | ~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0) | k2_relat_1(X0) = k2_relset_1(X1,X2,X0)) )),
% 0.21/0.50    inference(resolution,[],[f34,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    k2_relat_1(sK2) != k1_relset_1(sK1,sK0,k4_relat_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))),
% 0.21/0.50    inference(backward_demodulation,[],[f94,f95])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f38,f26])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    k1_relat_1(sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2)) | k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k4_relat_1(sK2))),
% 0.21/0.50    inference(backward_demodulation,[],[f92,f93])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f37,f26])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k4_relat_1(sK2)) | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f91,f90])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f36,f26])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_relset_1(X0,X1,X2) = k4_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k3_relset_1(X0,X1,X2) = k4_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2)) | k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))),
% 0.21/0.50    inference(backward_demodulation,[],[f25,f90])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (18297)------------------------------
% 0.21/0.50  % (18297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (18297)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (18297)Memory used [KB]: 6396
% 0.21/0.50  % (18297)Time elapsed: 0.071 s
% 0.21/0.50  % (18297)------------------------------
% 0.21/0.50  % (18297)------------------------------
% 0.21/0.50  % (18283)Success in time 0.145 s
%------------------------------------------------------------------------------
