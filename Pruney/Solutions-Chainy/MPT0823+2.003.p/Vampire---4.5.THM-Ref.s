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
% DateTime   : Thu Dec  3 12:56:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 181 expanded)
%              Number of leaves         :   13 (  45 expanded)
%              Depth                    :   34
%              Number of atoms          :  274 ( 567 expanded)
%              Number of equality atoms :   63 ( 162 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f105,plain,(
    $false ),
    inference(subsumption_resolution,[],[f103,f36])).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f103,plain,(
    ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f102,f30])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))
      | k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X0,X1,X2) != k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
          | k2_relset_1(X0,X1,X2) != k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))
        | k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        | k2_relset_1(X0,X1,X2) != k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
          & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f101,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f101,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(trivial_inequality_removal,[],[f100])).

fof(f100,plain,(
    ! [X0] :
      ( k1_relat_1(sK2) != k1_relat_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f99,f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f99,plain,(
    ! [X0] :
      ( k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f97,f35])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f96,f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f96,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k4_relat_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f95,f35])).

fof(f95,plain,(
    ! [X0] :
      ( k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(k4_relat_1(sK2))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f94,f56])).

fof(f56,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f55,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f55,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f46,f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f94,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2),sK1)
      | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(k4_relat_1(sK2))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f92,f35])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(k4_relat_1(sK2))
      | ~ v1_relat_1(sK2)
      | ~ r1_tarski(k2_relat_1(sK2),sK1) ) ),
    inference(resolution,[],[f91,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k4_relat_1(X0)),X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(subsumption_resolution,[],[f61,f32])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(k4_relat_1(X0)),X1)
      | ~ v1_relat_1(k4_relat_1(X0)) ) ),
    inference(resolution,[],[f50,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( v4_relat_1(k4_relat_1(X0),X1)
      | ~ r1_tarski(k2_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f49,f32])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),X1)
      | v4_relat_1(k4_relat_1(X0),X1)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f40,f33])).

fof(f33,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(k4_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f90,f35])).

fof(f90,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
      | ~ r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1)
      | ~ v1_relat_1(k4_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f89,f52])).

fof(f52,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f51,f39])).

fof(f51,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f45,f30])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f89,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
      | ~ r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1)
      | ~ v1_relat_1(k4_relat_1(sK2)) ) ),
    inference(inner_rewriting,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
      | ~ r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1)
      | ~ v1_relat_1(k4_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f87,f30])).

fof(f87,plain,(
    ! [X0] :
      ( k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
      | ~ r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1)
      | ~ v1_relat_1(k4_relat_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(superposition,[],[f86,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f86,plain,(
    ! [X0] :
      ( k1_relset_1(sK0,sK1,sK2) != k2_relat_1(k4_relat_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
      | ~ r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1)
      | ~ v1_relat_1(k4_relat_1(sK2)) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | k1_relset_1(sK0,sK1,sK2) != k2_relat_1(k4_relat_1(sK2))
      | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
      | ~ r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1)
      | ~ v1_relat_1(k4_relat_1(sK2)) ) ),
    inference(resolution,[],[f84,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f84,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | k1_relset_1(sK0,sK1,sK2) != k2_relat_1(k4_relat_1(sK2)) ) ),
    inference(superposition,[],[f83,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f83,plain,(
    ! [X0] :
      ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))
      | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f82,f35])).

fof(f82,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f81,f32])).

fof(f81,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f80,f33])).

fof(f80,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f79,f56])).

fof(f79,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2)) ),
    inference(inner_rewriting,[],[f78])).

fof(f78,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2))
    | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | ~ r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1)
    | ~ v1_relat_1(k4_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f77,f30])).

fof(f77,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2))
    | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | ~ r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1)
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f75,f44])).

fof(f75,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k1_relat_1(k4_relat_1(sK2))
    | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | ~ r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1)
    | ~ v1_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f74,f41])).

fof(f74,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))
    | k2_relset_1(sK0,sK1,sK2) != k1_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[],[f73,f43])).

fof(f73,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k4_relat_1(sK2))
    | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f71,f30])).

fof(f71,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k4_relat_1(sK2))
    | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f31,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f31,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))
    | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:16:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.48  % (28250)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.49  % (28250)Refutation not found, incomplete strategy% (28250)------------------------------
% 0.20/0.49  % (28250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (28258)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.49  % (28250)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (28250)Memory used [KB]: 10618
% 0.20/0.49  % (28250)Time elapsed: 0.056 s
% 0.20/0.49  % (28250)------------------------------
% 0.20/0.49  % (28250)------------------------------
% 0.20/0.51  % (28254)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.51  % (28263)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.51  % (28265)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.52  % (28262)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.52  % (28255)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.52  % (28253)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.52  % (28252)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.52  % (28251)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.52  % (28252)Refutation not found, incomplete strategy% (28252)------------------------------
% 0.20/0.52  % (28252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (28252)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (28252)Memory used [KB]: 10618
% 0.20/0.52  % (28252)Time elapsed: 0.104 s
% 0.20/0.52  % (28252)------------------------------
% 0.20/0.52  % (28252)------------------------------
% 0.20/0.52  % (28257)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.52  % (28259)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.52  % (28264)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.52  % (28244)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.52  % (28256)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.52  % (28246)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.52  % (28247)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.52  % (28261)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.53  % (28243)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.53  % (28249)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (28245)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.53  % (28249)Refutation not found, incomplete strategy% (28249)------------------------------
% 0.20/0.53  % (28249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28249)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (28249)Memory used [KB]: 6140
% 0.20/0.53  % (28249)Time elapsed: 0.106 s
% 0.20/0.53  % (28249)------------------------------
% 0.20/0.53  % (28249)------------------------------
% 0.20/0.53  % (28245)Refutation not found, incomplete strategy% (28245)------------------------------
% 0.20/0.53  % (28245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28245)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (28245)Memory used [KB]: 10618
% 0.20/0.53  % (28245)Time elapsed: 0.107 s
% 0.20/0.53  % (28245)------------------------------
% 0.20/0.53  % (28245)------------------------------
% 0.20/0.53  % (28265)Refutation not found, incomplete strategy% (28265)------------------------------
% 0.20/0.53  % (28265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28265)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (28265)Memory used [KB]: 10618
% 0.20/0.53  % (28265)Time elapsed: 0.108 s
% 0.20/0.53  % (28265)------------------------------
% 0.20/0.53  % (28265)------------------------------
% 0.20/0.53  % (28248)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.53  % (28261)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f103,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.53    inference(resolution,[],[f102,f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    (k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) | k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) | k2_relset_1(X0,X1,X2) != k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) | k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) | k2_relset_1(X0,X1,X2) != k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))))),
% 0.20/0.53    inference(negated_conjecture,[],[f12])).
% 0.20/0.53  fof(f12,conjecture,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f101,f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f100])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    ( ! [X0] : (k1_relat_1(sK2) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 0.20/0.53    inference(superposition,[],[f99,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    ( ! [X0] : (k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f97,f35])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 0.20/0.53    inference(resolution,[],[f96,f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_relat_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f95,f35])).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    ( ! [X0] : (k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 0.20/0.53    inference(resolution,[],[f94,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(sK2)),
% 0.20/0.53    inference(resolution,[],[f55,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    v5_relat_1(sK2,sK1)),
% 0.20/0.53    inference(resolution,[],[f46,f30])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),sK1) | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f92,f35])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK1)) )),
% 0.20/0.53    inference(resolution,[],[f91,f62])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k4_relat_1(X0)),X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f61,f32])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),X1) | ~v1_relat_1(X0) | r1_tarski(k1_relat_1(k4_relat_1(X0)),X1) | ~v1_relat_1(k4_relat_1(X0))) )),
% 0.20/0.53    inference(resolution,[],[f50,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v4_relat_1(k4_relat_1(X0),X1) | ~r1_tarski(k2_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f49,f32])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),X1) | v4_relat_1(k4_relat_1(X0),X1) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(superposition,[],[f40,f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1) | ~v1_relat_1(X0) | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(k4_relat_1(sK2))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f90,f35])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | ~r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1) | ~v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 0.20/0.53    inference(resolution,[],[f89,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2)),
% 0.20/0.53    inference(resolution,[],[f51,f39])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    v4_relat_1(sK2,sK0)),
% 0.20/0.53    inference(resolution,[],[f45,f30])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | ~r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1) | ~v1_relat_1(k4_relat_1(sK2))) )),
% 0.20/0.53    inference(inner_rewriting,[],[f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X0] : (k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | ~r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1) | ~v1_relat_1(k4_relat_1(sK2))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f87,f30])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    ( ! [X0] : (k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | ~r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1) | ~v1_relat_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 0.20/0.53    inference(superposition,[],[f86,f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    ( ! [X0] : (k1_relset_1(sK0,sK1,sK2) != k2_relat_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | ~r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1) | ~v1_relat_1(k4_relat_1(sK2))) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f85])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | k1_relset_1(sK0,sK1,sK2) != k2_relat_1(k4_relat_1(sK2)) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | ~r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1) | ~v1_relat_1(k4_relat_1(sK2))) )),
% 0.20/0.53    inference(resolution,[],[f84,f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(flattening,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | k1_relset_1(sK0,sK1,sK2) != k2_relat_1(k4_relat_1(sK2))) )),
% 0.20/0.53    inference(superposition,[],[f83,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    ( ! [X0] : (k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2)) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(resolution,[],[f82,f35])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))),
% 0.20/0.53    inference(subsumption_resolution,[],[f81,f32])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2)) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | ~v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.53    inference(subsumption_resolution,[],[f80,f33])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2)) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.20/0.53    inference(resolution,[],[f79,f56])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    ~r1_tarski(k2_relat_1(sK2),sK1) | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2)) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2))),
% 0.20/0.53    inference(inner_rewriting,[],[f78])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2)) | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2)) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | ~r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1) | ~v1_relat_1(k4_relat_1(sK2))),
% 0.20/0.53    inference(subsumption_resolution,[],[f77,f30])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2)) | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2)) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | ~r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1) | ~v1_relat_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    inference(superposition,[],[f75,f44])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    k2_relset_1(sK0,sK1,sK2) != k1_relat_1(k4_relat_1(sK2)) | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2)) | ~r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | ~r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1) | ~v1_relat_1(k4_relat_1(sK2))),
% 0.20/0.53    inference(resolution,[],[f74,f41])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2)) | k2_relset_1(sK0,sK1,sK2) != k1_relat_1(k4_relat_1(sK2))),
% 0.20/0.53    inference(superposition,[],[f73,f43])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k4_relat_1(sK2)) | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))),
% 0.20/0.53    inference(subsumption_resolution,[],[f71,f30])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k4_relat_1(sK2)) | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    inference(superposition,[],[f31,f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k3_relset_1(X0,X1,X2) = k4_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (28261)------------------------------
% 0.20/0.53  % (28261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28261)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (28261)Memory used [KB]: 6140
% 0.20/0.53  % (28261)Time elapsed: 0.114 s
% 0.20/0.53  % (28261)------------------------------
% 0.20/0.53  % (28261)------------------------------
% 0.20/0.53  % (28241)Success in time 0.173 s
%------------------------------------------------------------------------------
