%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:22 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 274 expanded)
%              Number of leaves         :   10 (  66 expanded)
%              Depth                    :   33
%              Number of atoms          :  322 (1615 expanded)
%              Number of equality atoms :   27 ( 191 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(subsumption_resolution,[],[f95,f38])).

fof(f38,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f95,plain,(
    ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f94,f29])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f94,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f93,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f93,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f91,f27])).

fof(f27,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f91,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f90,f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_funct_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f88,f29])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
      | ~ v1_relat_1(k2_funct_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f87,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f87,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK2,sK0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k2_funct_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f86,f33])).

fof(f86,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k2_funct_1(sK2))
      | ~ v4_relat_1(sK2,sK0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f85,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f85,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k2_funct_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f84,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | ~ r1_tarski(k1_relat_1(sK2),X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f74,f33])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | ~ r1_tarski(k1_relat_1(sK2),X0) ) ),
    inference(forward_demodulation,[],[f73,f57])).

fof(f57,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f50,f54])).

fof(f54,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f53,f31])).

fof(f31,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f44,f29])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f50,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f49,f38])).

fof(f49,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f48,f29])).

fof(f48,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f47,f33])).

fof(f47,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f46,f27])).

fof(f46,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f36,f30])).

fof(f30,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0)))
      | ~ v1_relat_1(sK2)
      | ~ r1_tarski(k1_relat_1(sK2),X0) ) ),
    inference(subsumption_resolution,[],[f72,f27])).

fof(f72,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0)))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ r1_tarski(k1_relat_1(sK2),X0) ) ),
    inference(resolution,[],[f71,f30])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),X1)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),X1)
      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),X1)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f63,f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f63,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_relat_1(k2_funct_1(X1)),X2)
      | m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),X2)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f61,f34])).

fof(f61,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_relat_1(k2_funct_1(X1)),X2)
      | m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),X2)))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f43,f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f84,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_relat_1(k2_funct_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f83,f33])).

fof(f83,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_relat_1(k2_funct_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f82,f27])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_relat_1(k2_funct_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f81,f30])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_relat_1(k2_funct_1(sK2))
      | ~ v2_funct_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f80,f37])).

fof(f80,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_relat_1(k2_funct_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f79,f33])).

fof(f79,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_relat_1(k2_funct_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f78,f27])).

fof(f78,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_relat_1(k2_funct_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f77,f35])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k2_funct_1(sK2))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_relat_1(k2_funct_1(sK2)) ) ),
    inference(resolution,[],[f69,f32])).

fof(f32,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_1(sK2),sK1,X0)
      | ~ v1_relat_1(k2_funct_1(sK2))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f68,f33])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | v1_funct_2(k2_funct_1(sK2),sK1,X0)
      | ~ v1_relat_1(k2_funct_1(sK2))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) ) ),
    inference(subsumption_resolution,[],[f67,f27])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
      | v1_funct_2(k2_funct_1(sK2),sK1,X0)
      | ~ v1_relat_1(k2_funct_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f55,f35])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k2_funct_1(sK2))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
      | v1_funct_2(k2_funct_1(sK2),sK1,X0)
      | ~ v1_relat_1(k2_funct_1(sK2)) ) ),
    inference(backward_demodulation,[],[f52,f54])).

fof(f52,plain,(
    ! [X0] :
      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),X0)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
      | ~ v1_funct_1(k2_funct_1(sK2))
      | ~ v1_relat_1(k2_funct_1(sK2)) ) ),
    inference(superposition,[],[f42,f50])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 18:39:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.46  % (7861)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.23/0.48  % (7856)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.23/0.48  % (7878)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.23/0.48  % (7878)Refutation not found, incomplete strategy% (7878)------------------------------
% 0.23/0.48  % (7878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.48  % (7878)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.48  
% 0.23/0.48  % (7878)Memory used [KB]: 10618
% 0.23/0.48  % (7878)Time elapsed: 0.064 s
% 0.23/0.48  % (7878)------------------------------
% 0.23/0.48  % (7878)------------------------------
% 0.23/0.49  % (7858)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.23/0.49  % (7871)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.23/0.49  % (7858)Refutation not found, incomplete strategy% (7858)------------------------------
% 0.23/0.49  % (7858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (7858)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.49  
% 0.23/0.49  % (7858)Memory used [KB]: 10618
% 0.23/0.49  % (7858)Time elapsed: 0.071 s
% 0.23/0.49  % (7858)------------------------------
% 0.23/0.49  % (7858)------------------------------
% 0.23/0.49  % (7873)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.23/0.49  % (7874)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.23/0.49  % (7859)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.23/0.50  % (7874)Refutation found. Thanks to Tanya!
% 0.23/0.50  % SZS status Theorem for theBenchmark
% 0.23/0.50  % SZS output start Proof for theBenchmark
% 0.23/0.50  fof(f97,plain,(
% 0.23/0.50    $false),
% 0.23/0.50    inference(subsumption_resolution,[],[f95,f38])).
% 0.23/0.50  fof(f38,plain,(
% 0.23/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f3])).
% 0.23/0.50  fof(f3,axiom,(
% 0.23/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.23/0.50  fof(f95,plain,(
% 0.23/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.23/0.50    inference(resolution,[],[f94,f29])).
% 0.23/0.50  fof(f29,plain,(
% 0.23/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.23/0.50    inference(cnf_transformation,[],[f25])).
% 0.23/0.50  fof(f25,plain,(
% 0.23/0.50    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.23/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f24])).
% 0.23/0.50  fof(f24,plain,(
% 0.23/0.50    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f13,plain,(
% 0.23/0.50    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.23/0.50    inference(flattening,[],[f12])).
% 0.23/0.50  fof(f12,plain,(
% 0.23/0.50    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.23/0.50    inference(ennf_transformation,[],[f10])).
% 0.23/0.50  fof(f10,negated_conjecture,(
% 0.23/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.23/0.50    inference(negated_conjecture,[],[f9])).
% 0.23/0.50  fof(f9,conjecture,(
% 0.23/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.23/0.50  fof(f94,plain,(
% 0.23/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.23/0.50    inference(subsumption_resolution,[],[f93,f33])).
% 0.23/0.50  fof(f33,plain,(
% 0.23/0.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f14])).
% 0.23/0.50  fof(f14,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.23/0.50    inference(ennf_transformation,[],[f1])).
% 0.23/0.50  fof(f1,axiom,(
% 0.23/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.23/0.50  fof(f93,plain,(
% 0.23/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 0.23/0.50    inference(subsumption_resolution,[],[f91,f27])).
% 0.23/0.50  fof(f27,plain,(
% 0.23/0.50    v1_funct_1(sK2)),
% 0.23/0.50    inference(cnf_transformation,[],[f25])).
% 0.23/0.50  fof(f91,plain,(
% 0.23/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.23/0.50    inference(resolution,[],[f90,f34])).
% 0.23/0.50  fof(f34,plain,(
% 0.23/0.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f16])).
% 0.23/0.50  fof(f16,plain,(
% 0.23/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.50    inference(flattening,[],[f15])).
% 0.23/0.50  fof(f15,plain,(
% 0.23/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f4])).
% 0.23/0.50  fof(f4,axiom,(
% 0.23/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.23/0.50  fof(f90,plain,(
% 0.23/0.50    ( ! [X0] : (~v1_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.23/0.50    inference(resolution,[],[f88,f29])).
% 0.23/0.50  fof(f88,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.23/0.50    inference(resolution,[],[f87,f45])).
% 0.23/0.50  fof(f45,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f23])).
% 0.23/0.50  fof(f23,plain,(
% 0.23/0.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.50    inference(ennf_transformation,[],[f11])).
% 0.23/0.50  fof(f11,plain,(
% 0.23/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.23/0.50    inference(pure_predicate_removal,[],[f6])).
% 0.23/0.50  fof(f6,axiom,(
% 0.23/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.23/0.50  fof(f87,plain,(
% 0.23/0.50    ( ! [X0] : (~v4_relat_1(sK2,sK0) | ~v1_relat_1(X0) | ~v1_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 0.23/0.50    inference(subsumption_resolution,[],[f86,f33])).
% 0.23/0.50  fof(f86,plain,(
% 0.23/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k2_funct_1(sK2)) | ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2)) )),
% 0.23/0.50    inference(resolution,[],[f85,f39])).
% 0.23/0.50  fof(f39,plain,(
% 0.23/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f26])).
% 0.23/0.50  fof(f26,plain,(
% 0.23/0.50    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.23/0.50    inference(nnf_transformation,[],[f19])).
% 0.23/0.50  fof(f19,plain,(
% 0.23/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.23/0.50    inference(ennf_transformation,[],[f2])).
% 0.23/0.50  fof(f2,axiom,(
% 0.23/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.23/0.50  fof(f85,plain,(
% 0.23/0.50    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k2_funct_1(sK2))) )),
% 0.23/0.50    inference(subsumption_resolution,[],[f84,f75])).
% 0.23/0.50  fof(f75,plain,(
% 0.23/0.50    ( ! [X0,X1] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r1_tarski(k1_relat_1(sK2),X0) | ~m1_subset_1(sK2,k1_zfmisc_1(X1)) | ~v1_relat_1(X1)) )),
% 0.23/0.50    inference(resolution,[],[f74,f33])).
% 0.23/0.50  fof(f74,plain,(
% 0.23/0.50    ( ! [X0] : (~v1_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r1_tarski(k1_relat_1(sK2),X0)) )),
% 0.23/0.50    inference(forward_demodulation,[],[f73,f57])).
% 0.23/0.50  fof(f57,plain,(
% 0.23/0.50    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.23/0.50    inference(backward_demodulation,[],[f50,f54])).
% 0.23/0.50  fof(f54,plain,(
% 0.23/0.50    sK1 = k2_relat_1(sK2)),
% 0.23/0.50    inference(forward_demodulation,[],[f53,f31])).
% 0.23/0.50  fof(f31,plain,(
% 0.23/0.50    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.23/0.50    inference(cnf_transformation,[],[f25])).
% 0.23/0.50  fof(f53,plain,(
% 0.23/0.50    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.23/0.50    inference(resolution,[],[f44,f29])).
% 0.23/0.50  fof(f44,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f22])).
% 0.23/0.50  fof(f22,plain,(
% 0.23/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.50    inference(ennf_transformation,[],[f7])).
% 0.23/0.50  fof(f7,axiom,(
% 0.23/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.23/0.50  fof(f50,plain,(
% 0.23/0.50    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.23/0.50    inference(subsumption_resolution,[],[f49,f38])).
% 0.23/0.50  fof(f49,plain,(
% 0.23/0.50    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.23/0.50    inference(resolution,[],[f48,f29])).
% 0.23/0.50  fof(f48,plain,(
% 0.23/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(X0)) )),
% 0.23/0.50    inference(resolution,[],[f47,f33])).
% 0.23/0.50  fof(f47,plain,(
% 0.23/0.50    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.23/0.50    inference(subsumption_resolution,[],[f46,f27])).
% 0.23/0.50  fof(f46,plain,(
% 0.23/0.50    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.23/0.50    inference(resolution,[],[f36,f30])).
% 0.23/0.50  fof(f30,plain,(
% 0.23/0.50    v2_funct_1(sK2)),
% 0.23/0.50    inference(cnf_transformation,[],[f25])).
% 0.23/0.50  fof(f36,plain,(
% 0.23/0.50    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f18])).
% 0.23/0.50  fof(f18,plain,(
% 0.23/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.50    inference(flattening,[],[f17])).
% 0.23/0.50  fof(f17,plain,(
% 0.23/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f5])).
% 0.23/0.50  fof(f5,axiom,(
% 0.23/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.23/0.50  fof(f73,plain,(
% 0.23/0.50    ( ! [X0] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0))) | ~v1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),X0)) )),
% 0.23/0.50    inference(subsumption_resolution,[],[f72,f27])).
% 0.23/0.50  fof(f72,plain,(
% 0.23/0.50    ( ! [X0] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),X0)) )),
% 0.23/0.50    inference(resolution,[],[f71,f30])).
% 0.23/0.50  fof(f71,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~v2_funct_1(X0) | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),X1)) )),
% 0.23/0.50    inference(duplicate_literal_removal,[],[f70])).
% 0.23/0.50  fof(f70,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),X1) | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X0)),X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.50    inference(superposition,[],[f63,f37])).
% 0.23/0.50  fof(f37,plain,(
% 0.23/0.50    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f18])).
% 0.23/0.50  fof(f63,plain,(
% 0.23/0.50    ( ! [X2,X1] : (~r1_tarski(k2_relat_1(k2_funct_1(X1)),X2) | m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),X2))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.23/0.50    inference(subsumption_resolution,[],[f61,f34])).
% 0.23/0.50  fof(f61,plain,(
% 0.23/0.50    ( ! [X2,X1] : (~r1_tarski(k2_relat_1(k2_funct_1(X1)),X2) | m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),X2))) | ~v1_relat_1(k2_funct_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.23/0.50    inference(resolution,[],[f43,f35])).
% 0.23/0.50  fof(f35,plain,(
% 0.23/0.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f16])).
% 0.23/0.50  fof(f43,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f21])).
% 0.23/0.50  fof(f21,plain,(
% 0.23/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.23/0.50    inference(flattening,[],[f20])).
% 0.23/0.50  fof(f20,plain,(
% 0.23/0.50    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.23/0.50    inference(ennf_transformation,[],[f8])).
% 0.23/0.50  fof(f8,axiom,(
% 0.23/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.23/0.50  fof(f84,plain,(
% 0.23/0.50    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_relat_1(k2_funct_1(sK2))) )),
% 0.23/0.50    inference(subsumption_resolution,[],[f83,f33])).
% 0.23/0.50  fof(f83,plain,(
% 0.23/0.50    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)) )),
% 0.23/0.50    inference(subsumption_resolution,[],[f82,f27])).
% 0.23/0.50  fof(f82,plain,(
% 0.23/0.50    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.23/0.50    inference(subsumption_resolution,[],[f81,f30])).
% 0.23/0.50  fof(f81,plain,(
% 0.23/0.50    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.23/0.50    inference(superposition,[],[f80,f37])).
% 0.23/0.50  fof(f80,plain,(
% 0.23/0.50    ( ! [X0] : (~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_relat_1(k2_funct_1(sK2))) )),
% 0.23/0.50    inference(subsumption_resolution,[],[f79,f33])).
% 0.23/0.50  fof(f79,plain,(
% 0.23/0.50    ( ! [X0] : (~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)) )),
% 0.23/0.50    inference(subsumption_resolution,[],[f78,f27])).
% 0.23/0.50  fof(f78,plain,(
% 0.23/0.50    ( ! [X0] : (~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.23/0.50    inference(resolution,[],[f77,f35])).
% 0.23/0.50  fof(f77,plain,(
% 0.23/0.50    ( ! [X0] : (~v1_funct_1(k2_funct_1(sK2)) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_relat_1(k2_funct_1(sK2))) )),
% 0.23/0.50    inference(resolution,[],[f69,f32])).
% 0.23/0.50  fof(f32,plain,(
% 0.23/0.50    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.23/0.50    inference(cnf_transformation,[],[f25])).
% 0.23/0.50  fof(f69,plain,(
% 0.23/0.50    ( ! [X0,X1] : (v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~v1_relat_1(k2_funct_1(sK2)) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) | ~m1_subset_1(sK2,k1_zfmisc_1(X1)) | ~v1_relat_1(X1)) )),
% 0.23/0.50    inference(resolution,[],[f68,f33])).
% 0.23/0.50  fof(f68,plain,(
% 0.23/0.50    ( ! [X0] : (~v1_relat_1(sK2) | v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~v1_relat_1(k2_funct_1(sK2)) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)) )),
% 0.23/0.50    inference(subsumption_resolution,[],[f67,f27])).
% 0.23/0.50  fof(f67,plain,(
% 0.23/0.50    ( ! [X0] : (~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) | v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.23/0.50    inference(resolution,[],[f55,f35])).
% 0.23/0.50  fof(f55,plain,(
% 0.23/0.50    ( ! [X0] : (~v1_funct_1(k2_funct_1(sK2)) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) | v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~v1_relat_1(k2_funct_1(sK2))) )),
% 0.23/0.50    inference(backward_demodulation,[],[f52,f54])).
% 0.23/0.50  fof(f52,plain,(
% 0.23/0.50    ( ! [X0] : (v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),X0) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) )),
% 0.23/0.50    inference(superposition,[],[f42,f50])).
% 0.23/0.50  fof(f42,plain,(
% 0.23/0.50    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f21])).
% 0.23/0.50  % SZS output end Proof for theBenchmark
% 0.23/0.50  % (7874)------------------------------
% 0.23/0.50  % (7874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (7874)Termination reason: Refutation
% 0.23/0.50  
% 0.23/0.50  % (7874)Memory used [KB]: 6140
% 0.23/0.50  % (7874)Time elapsed: 0.077 s
% 0.23/0.50  % (7874)------------------------------
% 0.23/0.50  % (7874)------------------------------
% 0.23/0.50  % (7854)Success in time 0.125 s
%------------------------------------------------------------------------------
