%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:23 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  218 (6574 expanded)
%              Number of clauses        :  152 (2228 expanded)
%              Number of leaves         :   21 (1243 expanded)
%              Depth                    :   25
%              Number of atoms          :  684 (34369 expanded)
%              Number of equality atoms :  354 (7163 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f50,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f51,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f55,plain,
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
      & k2_relset_1(sK0,sK1,sK2) = sK1
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f51,f55])).

fof(f95,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f96,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f75,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f97,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f94,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f23,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f90,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f98,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f56])).

fof(f74,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f72,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f89,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f99,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f56])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f52])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f103,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f106,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f84])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_877,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_7802,plain,
    ( k2_funct_1(sK2) != X0
    | k2_relat_1(k2_funct_1(sK2)) = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_877])).

cnf(c_7804,plain,
    ( k2_funct_1(sK2) != k1_xboole_0
    | k2_relat_1(k2_funct_1(sK2)) = k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7802])).

cnf(c_869,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1926,plain,
    ( k2_relat_1(X0) != X1
    | k2_relat_1(X0) = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_869])).

cnf(c_4133,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != X0
    | k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1926])).

cnf(c_7801,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k2_relat_1(X0)
    | k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_4133])).

cnf(c_7803,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k2_relat_1(k1_xboole_0)
    | k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7801])).

cnf(c_868,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2465,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_868])).

cnf(c_7365,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_2465])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1843,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_6947,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_1843])).

cnf(c_6948,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6947])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_732,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_40])).

cnf(c_733,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_735,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_733,c_39])).

cnf(c_1476,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1480,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4538,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1476,c_1480])).

cnf(c_4605,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_735,c_4538])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1482,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2895,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1476,c_1482])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_38,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_461,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_38])).

cnf(c_462,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_464,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_462,c_41])).

cnf(c_1472,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_3118,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2895,c_1472])).

cnf(c_30,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1477,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5018,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3118,c_1477])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1479,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3021,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1476,c_1479])).

cnf(c_37,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3033,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3021,c_37])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_447,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_38])).

cnf(c_448,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_450,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_448,c_41])).

cnf(c_1473,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_3110,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3033,c_1473])).

cnf(c_44,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_1855,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1856,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1855])).

cnf(c_3398,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3110,c_44,c_1856])).

cnf(c_5037,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5018,c_3398])).

cnf(c_42,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2198,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2199,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2198])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3096,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3097,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3096])).

cnf(c_5462,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5037,c_42,c_44,c_1856,c_2199,c_3097])).

cnf(c_5468,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_5462,c_1480])).

cnf(c_5477,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_5468,c_3398])).

cnf(c_5499,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4605,c_5477])).

cnf(c_31,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_36,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_743,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k2_relat_1(X0) != sK0
    | k1_relat_1(X0) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_36])).

cnf(c_744,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_743])).

cnf(c_756,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_744,c_19])).

cnf(c_1460,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_756])).

cnf(c_3401,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3398,c_1460])).

cnf(c_3410,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3401])).

cnf(c_745,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_4278,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3410,c_42,c_44,c_745,c_1856,c_2199,c_3097,c_3110])).

cnf(c_4279,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4278])).

cnf(c_4282,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4279,c_3118])).

cnf(c_4701,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4605,c_4282])).

cnf(c_5467,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4605,c_5462])).

cnf(c_5500,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5499,c_4701,c_5467])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_33,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_419,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | X1 != X2
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_33])).

cnf(c_420,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_1474,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_4428,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3118,c_1474])).

cnf(c_4433,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4428,c_3398])).

cnf(c_4809,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4433,c_42,c_44,c_1856,c_2199,c_3097])).

cnf(c_5511,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5500,c_4809])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_5609,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5511,c_4])).

cnf(c_34,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_401,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | X1 != X2
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_34])).

cnf(c_402,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_762,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_402,c_36])).

cnf(c_763,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_762])).

cnf(c_775,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_763,c_19])).

cnf(c_1459,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_775])).

cnf(c_3402,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3398,c_1459])).

cnf(c_3403,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3402])).

cnf(c_764,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_4269,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3403,c_42,c_44,c_764,c_1856,c_2199,c_3097,c_3110])).

cnf(c_4270,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4269])).

cnf(c_4273,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4270,c_3118])).

cnf(c_5515,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5500,c_4273])).

cnf(c_5594,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5515,c_4])).

cnf(c_5612,plain,
    ( k1_relat_1(sK2) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5609,c_5594])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_536,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k2_relat_1(X2) != k1_xboole_0
    | k1_relat_1(X2) != X1
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_553,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_537,c_420])).

cnf(c_1469,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_553])).

cnf(c_3690,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3033,c_1469])).

cnf(c_3719,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3690])).

cnf(c_4070,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3690,c_41,c_39,c_1855,c_3719])).

cnf(c_5518,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5500,c_4070])).

cnf(c_5581,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5518])).

cnf(c_5615,plain,
    ( sK2 = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5612,c_5581])).

cnf(c_5523,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5500,c_3033])).

cnf(c_5625,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5615,c_5523])).

cnf(c_873,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1938,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_2464,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | X0 != k1_xboole_0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1938])).

cnf(c_4931,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k2_funct_1(sK2) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_2464])).

cnf(c_4932,plain,
    ( k2_funct_1(sK2) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4931])).

cnf(c_870,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2309,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(X1))
    | k1_relat_1(X1) != X0 ),
    inference(instantiation,[status(thm)],[c_870])).

cnf(c_4081,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(k2_funct_1(sK2)))
    | k1_relat_1(k2_funct_1(sK2)) != X0 ),
    inference(instantiation,[status(thm)],[c_2309])).

cnf(c_4083,plain,
    ( v1_xboole_0(k1_relat_1(k2_funct_1(sK2)))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4081])).

cnf(c_3634,plain,
    ( k2_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_869])).

cnf(c_3635,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3634])).

cnf(c_2946,plain,
    ( k2_relat_1(sK2) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_877])).

cnf(c_2948,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2946])).

cnf(c_2553,plain,
    ( k2_relat_1(sK2) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_869])).

cnf(c_2945,plain,
    ( k2_relat_1(sK2) != k2_relat_1(X0)
    | k1_xboole_0 != k2_relat_1(X0)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2553])).

cnf(c_2947,plain,
    ( k2_relat_1(sK2) != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK2)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2945])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2000,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2387,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | v1_xboole_0(k2_funct_1(sK2))
    | ~ v1_xboole_0(k1_relat_1(k2_funct_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_2000])).

cnf(c_2386,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_1894,plain,
    ( k1_relat_1(X0) != X1
    | k1_relat_1(X0) = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_869])).

cnf(c_2366,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1894])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2040,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_funct_1(sK2))
    | k2_funct_1(sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2042,plain,
    ( ~ v1_xboole_0(k2_funct_1(sK2))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_funct_1(sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2040])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_126,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_125,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7804,c_7803,c_7365,c_6948,c_5625,c_5615,c_4932,c_4083,c_3635,c_3110,c_3097,c_3096,c_2948,c_2947,c_2387,c_2386,c_2366,c_2199,c_2198,c_2042,c_1856,c_1855,c_764,c_448,c_0,c_126,c_125,c_44,c_39,c_42,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.22/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/0.99  
% 3.22/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.22/0.99  
% 3.22/0.99  ------  iProver source info
% 3.22/0.99  
% 3.22/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.22/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.22/0.99  git: non_committed_changes: false
% 3.22/0.99  git: last_make_outside_of_git: false
% 3.22/0.99  
% 3.22/0.99  ------ 
% 3.22/0.99  
% 3.22/0.99  ------ Input Options
% 3.22/0.99  
% 3.22/0.99  --out_options                           all
% 3.22/0.99  --tptp_safe_out                         true
% 3.22/0.99  --problem_path                          ""
% 3.22/0.99  --include_path                          ""
% 3.22/0.99  --clausifier                            res/vclausify_rel
% 3.22/0.99  --clausifier_options                    --mode clausify
% 3.22/0.99  --stdin                                 false
% 3.22/0.99  --stats_out                             all
% 3.22/0.99  
% 3.22/0.99  ------ General Options
% 3.22/0.99  
% 3.22/0.99  --fof                                   false
% 3.22/0.99  --time_out_real                         305.
% 3.22/0.99  --time_out_virtual                      -1.
% 3.22/0.99  --symbol_type_check                     false
% 3.22/0.99  --clausify_out                          false
% 3.22/0.99  --sig_cnt_out                           false
% 3.22/0.99  --trig_cnt_out                          false
% 3.22/0.99  --trig_cnt_out_tolerance                1.
% 3.22/0.99  --trig_cnt_out_sk_spl                   false
% 3.22/0.99  --abstr_cl_out                          false
% 3.22/0.99  
% 3.22/0.99  ------ Global Options
% 3.22/0.99  
% 3.22/0.99  --schedule                              default
% 3.22/0.99  --add_important_lit                     false
% 3.22/0.99  --prop_solver_per_cl                    1000
% 3.22/0.99  --min_unsat_core                        false
% 3.22/0.99  --soft_assumptions                      false
% 3.22/0.99  --soft_lemma_size                       3
% 3.22/0.99  --prop_impl_unit_size                   0
% 3.22/0.99  --prop_impl_unit                        []
% 3.22/0.99  --share_sel_clauses                     true
% 3.22/0.99  --reset_solvers                         false
% 3.22/0.99  --bc_imp_inh                            [conj_cone]
% 3.22/0.99  --conj_cone_tolerance                   3.
% 3.22/0.99  --extra_neg_conj                        none
% 3.22/0.99  --large_theory_mode                     true
% 3.22/0.99  --prolific_symb_bound                   200
% 3.22/0.99  --lt_threshold                          2000
% 3.22/0.99  --clause_weak_htbl                      true
% 3.22/0.99  --gc_record_bc_elim                     false
% 3.22/0.99  
% 3.22/0.99  ------ Preprocessing Options
% 3.22/0.99  
% 3.22/0.99  --preprocessing_flag                    true
% 3.22/0.99  --time_out_prep_mult                    0.1
% 3.22/0.99  --splitting_mode                        input
% 3.22/0.99  --splitting_grd                         true
% 3.22/0.99  --splitting_cvd                         false
% 3.22/0.99  --splitting_cvd_svl                     false
% 3.22/0.99  --splitting_nvd                         32
% 3.22/0.99  --sub_typing                            true
% 3.22/0.99  --prep_gs_sim                           true
% 3.22/0.99  --prep_unflatten                        true
% 3.22/0.99  --prep_res_sim                          true
% 3.22/0.99  --prep_upred                            true
% 3.22/0.99  --prep_sem_filter                       exhaustive
% 3.22/0.99  --prep_sem_filter_out                   false
% 3.22/0.99  --pred_elim                             true
% 3.22/0.99  --res_sim_input                         true
% 3.22/0.99  --eq_ax_congr_red                       true
% 3.22/0.99  --pure_diseq_elim                       true
% 3.22/0.99  --brand_transform                       false
% 3.22/0.99  --non_eq_to_eq                          false
% 3.22/0.99  --prep_def_merge                        true
% 3.22/0.99  --prep_def_merge_prop_impl              false
% 3.22/0.99  --prep_def_merge_mbd                    true
% 3.22/0.99  --prep_def_merge_tr_red                 false
% 3.22/0.99  --prep_def_merge_tr_cl                  false
% 3.22/0.99  --smt_preprocessing                     true
% 3.22/0.99  --smt_ac_axioms                         fast
% 3.22/0.99  --preprocessed_out                      false
% 3.22/0.99  --preprocessed_stats                    false
% 3.22/0.99  
% 3.22/0.99  ------ Abstraction refinement Options
% 3.22/0.99  
% 3.22/0.99  --abstr_ref                             []
% 3.22/0.99  --abstr_ref_prep                        false
% 3.22/0.99  --abstr_ref_until_sat                   false
% 3.22/0.99  --abstr_ref_sig_restrict                funpre
% 3.22/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.22/0.99  --abstr_ref_under                       []
% 3.22/0.99  
% 3.22/0.99  ------ SAT Options
% 3.22/0.99  
% 3.22/0.99  --sat_mode                              false
% 3.22/0.99  --sat_fm_restart_options                ""
% 3.22/0.99  --sat_gr_def                            false
% 3.22/0.99  --sat_epr_types                         true
% 3.22/0.99  --sat_non_cyclic_types                  false
% 3.22/0.99  --sat_finite_models                     false
% 3.22/0.99  --sat_fm_lemmas                         false
% 3.22/0.99  --sat_fm_prep                           false
% 3.22/0.99  --sat_fm_uc_incr                        true
% 3.22/0.99  --sat_out_model                         small
% 3.22/0.99  --sat_out_clauses                       false
% 3.22/0.99  
% 3.22/0.99  ------ QBF Options
% 3.22/0.99  
% 3.22/0.99  --qbf_mode                              false
% 3.22/0.99  --qbf_elim_univ                         false
% 3.22/0.99  --qbf_dom_inst                          none
% 3.22/0.99  --qbf_dom_pre_inst                      false
% 3.22/0.99  --qbf_sk_in                             false
% 3.22/0.99  --qbf_pred_elim                         true
% 3.22/0.99  --qbf_split                             512
% 3.22/0.99  
% 3.22/0.99  ------ BMC1 Options
% 3.22/0.99  
% 3.22/0.99  --bmc1_incremental                      false
% 3.22/0.99  --bmc1_axioms                           reachable_all
% 3.22/0.99  --bmc1_min_bound                        0
% 3.22/0.99  --bmc1_max_bound                        -1
% 3.22/0.99  --bmc1_max_bound_default                -1
% 3.22/0.99  --bmc1_symbol_reachability              true
% 3.22/0.99  --bmc1_property_lemmas                  false
% 3.22/0.99  --bmc1_k_induction                      false
% 3.22/0.99  --bmc1_non_equiv_states                 false
% 3.22/0.99  --bmc1_deadlock                         false
% 3.22/0.99  --bmc1_ucm                              false
% 3.22/0.99  --bmc1_add_unsat_core                   none
% 3.22/0.99  --bmc1_unsat_core_children              false
% 3.22/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.22/0.99  --bmc1_out_stat                         full
% 3.22/0.99  --bmc1_ground_init                      false
% 3.22/0.99  --bmc1_pre_inst_next_state              false
% 3.22/0.99  --bmc1_pre_inst_state                   false
% 3.22/0.99  --bmc1_pre_inst_reach_state             false
% 3.22/0.99  --bmc1_out_unsat_core                   false
% 3.22/0.99  --bmc1_aig_witness_out                  false
% 3.22/0.99  --bmc1_verbose                          false
% 3.22/0.99  --bmc1_dump_clauses_tptp                false
% 3.22/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.22/0.99  --bmc1_dump_file                        -
% 3.22/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.22/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.22/0.99  --bmc1_ucm_extend_mode                  1
% 3.22/0.99  --bmc1_ucm_init_mode                    2
% 3.22/0.99  --bmc1_ucm_cone_mode                    none
% 3.22/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.22/0.99  --bmc1_ucm_relax_model                  4
% 3.22/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.22/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.22/0.99  --bmc1_ucm_layered_model                none
% 3.22/0.99  --bmc1_ucm_max_lemma_size               10
% 3.22/0.99  
% 3.22/0.99  ------ AIG Options
% 3.22/0.99  
% 3.22/0.99  --aig_mode                              false
% 3.22/0.99  
% 3.22/0.99  ------ Instantiation Options
% 3.22/0.99  
% 3.22/0.99  --instantiation_flag                    true
% 3.22/0.99  --inst_sos_flag                         false
% 3.22/0.99  --inst_sos_phase                        true
% 3.22/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.22/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.22/0.99  --inst_lit_sel_side                     num_symb
% 3.22/0.99  --inst_solver_per_active                1400
% 3.22/0.99  --inst_solver_calls_frac                1.
% 3.22/0.99  --inst_passive_queue_type               priority_queues
% 3.22/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.22/0.99  --inst_passive_queues_freq              [25;2]
% 3.22/0.99  --inst_dismatching                      true
% 3.22/0.99  --inst_eager_unprocessed_to_passive     true
% 3.22/0.99  --inst_prop_sim_given                   true
% 3.22/0.99  --inst_prop_sim_new                     false
% 3.22/0.99  --inst_subs_new                         false
% 3.22/0.99  --inst_eq_res_simp                      false
% 3.22/0.99  --inst_subs_given                       false
% 3.22/0.99  --inst_orphan_elimination               true
% 3.22/0.99  --inst_learning_loop_flag               true
% 3.22/0.99  --inst_learning_start                   3000
% 3.22/0.99  --inst_learning_factor                  2
% 3.22/0.99  --inst_start_prop_sim_after_learn       3
% 3.22/0.99  --inst_sel_renew                        solver
% 3.22/0.99  --inst_lit_activity_flag                true
% 3.22/0.99  --inst_restr_to_given                   false
% 3.22/0.99  --inst_activity_threshold               500
% 3.22/0.99  --inst_out_proof                        true
% 3.22/0.99  
% 3.22/0.99  ------ Resolution Options
% 3.22/0.99  
% 3.22/0.99  --resolution_flag                       true
% 3.22/0.99  --res_lit_sel                           adaptive
% 3.22/0.99  --res_lit_sel_side                      none
% 3.22/0.99  --res_ordering                          kbo
% 3.22/0.99  --res_to_prop_solver                    active
% 3.22/0.99  --res_prop_simpl_new                    false
% 3.22/0.99  --res_prop_simpl_given                  true
% 3.22/0.99  --res_passive_queue_type                priority_queues
% 3.22/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.22/0.99  --res_passive_queues_freq               [15;5]
% 3.22/0.99  --res_forward_subs                      full
% 3.22/0.99  --res_backward_subs                     full
% 3.22/0.99  --res_forward_subs_resolution           true
% 3.22/0.99  --res_backward_subs_resolution          true
% 3.22/0.99  --res_orphan_elimination                true
% 3.22/0.99  --res_time_limit                        2.
% 3.22/0.99  --res_out_proof                         true
% 3.22/0.99  
% 3.22/0.99  ------ Superposition Options
% 3.22/0.99  
% 3.22/0.99  --superposition_flag                    true
% 3.22/0.99  --sup_passive_queue_type                priority_queues
% 3.22/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.22/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.22/0.99  --demod_completeness_check              fast
% 3.22/0.99  --demod_use_ground                      true
% 3.22/0.99  --sup_to_prop_solver                    passive
% 3.22/0.99  --sup_prop_simpl_new                    true
% 3.22/0.99  --sup_prop_simpl_given                  true
% 3.22/0.99  --sup_fun_splitting                     false
% 3.22/0.99  --sup_smt_interval                      50000
% 3.22/0.99  
% 3.22/0.99  ------ Superposition Simplification Setup
% 3.22/0.99  
% 3.22/0.99  --sup_indices_passive                   []
% 3.22/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.22/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.99  --sup_full_bw                           [BwDemod]
% 3.22/0.99  --sup_immed_triv                        [TrivRules]
% 3.22/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.99  --sup_immed_bw_main                     []
% 3.22/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.22/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.99  
% 3.22/0.99  ------ Combination Options
% 3.22/0.99  
% 3.22/0.99  --comb_res_mult                         3
% 3.22/0.99  --comb_sup_mult                         2
% 3.22/0.99  --comb_inst_mult                        10
% 3.22/0.99  
% 3.22/0.99  ------ Debug Options
% 3.22/0.99  
% 3.22/0.99  --dbg_backtrace                         false
% 3.22/0.99  --dbg_dump_prop_clauses                 false
% 3.22/0.99  --dbg_dump_prop_clauses_file            -
% 3.22/0.99  --dbg_out_stat                          false
% 3.22/0.99  ------ Parsing...
% 3.22/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.22/0.99  
% 3.22/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.22/0.99  
% 3.22/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.22/0.99  
% 3.22/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/0.99  ------ Proving...
% 3.22/0.99  ------ Problem Properties 
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  clauses                                 42
% 3.22/0.99  conjectures                             3
% 3.22/0.99  EPR                                     4
% 3.22/0.99  Horn                                    36
% 3.22/0.99  unary                                   11
% 3.22/0.99  binary                                  10
% 3.22/0.99  lits                                    112
% 3.22/0.99  lits eq                                 50
% 3.22/0.99  fd_pure                                 0
% 3.22/0.99  fd_pseudo                               0
% 3.22/0.99  fd_cond                                 3
% 3.22/0.99  fd_pseudo_cond                          1
% 3.22/0.99  AC symbols                              0
% 3.22/0.99  
% 3.22/0.99  ------ Schedule dynamic 5 is on 
% 3.22/0.99  
% 3.22/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  ------ 
% 3.22/0.99  Current options:
% 3.22/0.99  ------ 
% 3.22/0.99  
% 3.22/0.99  ------ Input Options
% 3.22/0.99  
% 3.22/0.99  --out_options                           all
% 3.22/0.99  --tptp_safe_out                         true
% 3.22/0.99  --problem_path                          ""
% 3.22/0.99  --include_path                          ""
% 3.22/0.99  --clausifier                            res/vclausify_rel
% 3.22/0.99  --clausifier_options                    --mode clausify
% 3.22/0.99  --stdin                                 false
% 3.22/0.99  --stats_out                             all
% 3.22/0.99  
% 3.22/0.99  ------ General Options
% 3.22/0.99  
% 3.22/0.99  --fof                                   false
% 3.22/0.99  --time_out_real                         305.
% 3.22/0.99  --time_out_virtual                      -1.
% 3.22/0.99  --symbol_type_check                     false
% 3.22/0.99  --clausify_out                          false
% 3.22/0.99  --sig_cnt_out                           false
% 3.22/0.99  --trig_cnt_out                          false
% 3.22/0.99  --trig_cnt_out_tolerance                1.
% 3.22/0.99  --trig_cnt_out_sk_spl                   false
% 3.22/0.99  --abstr_cl_out                          false
% 3.22/0.99  
% 3.22/0.99  ------ Global Options
% 3.22/0.99  
% 3.22/0.99  --schedule                              default
% 3.22/0.99  --add_important_lit                     false
% 3.22/0.99  --prop_solver_per_cl                    1000
% 3.22/0.99  --min_unsat_core                        false
% 3.22/0.99  --soft_assumptions                      false
% 3.22/0.99  --soft_lemma_size                       3
% 3.22/0.99  --prop_impl_unit_size                   0
% 3.22/0.99  --prop_impl_unit                        []
% 3.22/0.99  --share_sel_clauses                     true
% 3.22/0.99  --reset_solvers                         false
% 3.22/0.99  --bc_imp_inh                            [conj_cone]
% 3.22/0.99  --conj_cone_tolerance                   3.
% 3.22/0.99  --extra_neg_conj                        none
% 3.22/0.99  --large_theory_mode                     true
% 3.22/0.99  --prolific_symb_bound                   200
% 3.22/0.99  --lt_threshold                          2000
% 3.22/0.99  --clause_weak_htbl                      true
% 3.22/0.99  --gc_record_bc_elim                     false
% 3.22/0.99  
% 3.22/0.99  ------ Preprocessing Options
% 3.22/0.99  
% 3.22/0.99  --preprocessing_flag                    true
% 3.22/0.99  --time_out_prep_mult                    0.1
% 3.22/0.99  --splitting_mode                        input
% 3.22/0.99  --splitting_grd                         true
% 3.22/0.99  --splitting_cvd                         false
% 3.22/0.99  --splitting_cvd_svl                     false
% 3.22/0.99  --splitting_nvd                         32
% 3.22/0.99  --sub_typing                            true
% 3.22/0.99  --prep_gs_sim                           true
% 3.22/0.99  --prep_unflatten                        true
% 3.22/0.99  --prep_res_sim                          true
% 3.22/0.99  --prep_upred                            true
% 3.22/0.99  --prep_sem_filter                       exhaustive
% 3.22/0.99  --prep_sem_filter_out                   false
% 3.22/0.99  --pred_elim                             true
% 3.22/0.99  --res_sim_input                         true
% 3.22/0.99  --eq_ax_congr_red                       true
% 3.22/0.99  --pure_diseq_elim                       true
% 3.22/0.99  --brand_transform                       false
% 3.22/0.99  --non_eq_to_eq                          false
% 3.22/0.99  --prep_def_merge                        true
% 3.22/0.99  --prep_def_merge_prop_impl              false
% 3.22/0.99  --prep_def_merge_mbd                    true
% 3.22/0.99  --prep_def_merge_tr_red                 false
% 3.22/0.99  --prep_def_merge_tr_cl                  false
% 3.22/0.99  --smt_preprocessing                     true
% 3.22/0.99  --smt_ac_axioms                         fast
% 3.22/0.99  --preprocessed_out                      false
% 3.22/0.99  --preprocessed_stats                    false
% 3.22/0.99  
% 3.22/0.99  ------ Abstraction refinement Options
% 3.22/0.99  
% 3.22/0.99  --abstr_ref                             []
% 3.22/0.99  --abstr_ref_prep                        false
% 3.22/0.99  --abstr_ref_until_sat                   false
% 3.22/0.99  --abstr_ref_sig_restrict                funpre
% 3.22/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.22/0.99  --abstr_ref_under                       []
% 3.22/0.99  
% 3.22/0.99  ------ SAT Options
% 3.22/0.99  
% 3.22/0.99  --sat_mode                              false
% 3.22/0.99  --sat_fm_restart_options                ""
% 3.22/0.99  --sat_gr_def                            false
% 3.22/0.99  --sat_epr_types                         true
% 3.22/0.99  --sat_non_cyclic_types                  false
% 3.22/0.99  --sat_finite_models                     false
% 3.22/0.99  --sat_fm_lemmas                         false
% 3.22/0.99  --sat_fm_prep                           false
% 3.22/0.99  --sat_fm_uc_incr                        true
% 3.22/0.99  --sat_out_model                         small
% 3.22/0.99  --sat_out_clauses                       false
% 3.22/0.99  
% 3.22/0.99  ------ QBF Options
% 3.22/0.99  
% 3.22/0.99  --qbf_mode                              false
% 3.22/0.99  --qbf_elim_univ                         false
% 3.22/0.99  --qbf_dom_inst                          none
% 3.22/0.99  --qbf_dom_pre_inst                      false
% 3.22/0.99  --qbf_sk_in                             false
% 3.22/0.99  --qbf_pred_elim                         true
% 3.22/0.99  --qbf_split                             512
% 3.22/0.99  
% 3.22/0.99  ------ BMC1 Options
% 3.22/0.99  
% 3.22/0.99  --bmc1_incremental                      false
% 3.22/0.99  --bmc1_axioms                           reachable_all
% 3.22/0.99  --bmc1_min_bound                        0
% 3.22/0.99  --bmc1_max_bound                        -1
% 3.22/0.99  --bmc1_max_bound_default                -1
% 3.22/0.99  --bmc1_symbol_reachability              true
% 3.22/0.99  --bmc1_property_lemmas                  false
% 3.22/0.99  --bmc1_k_induction                      false
% 3.22/0.99  --bmc1_non_equiv_states                 false
% 3.22/0.99  --bmc1_deadlock                         false
% 3.22/0.99  --bmc1_ucm                              false
% 3.22/0.99  --bmc1_add_unsat_core                   none
% 3.22/0.99  --bmc1_unsat_core_children              false
% 3.22/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.22/0.99  --bmc1_out_stat                         full
% 3.22/0.99  --bmc1_ground_init                      false
% 3.22/0.99  --bmc1_pre_inst_next_state              false
% 3.22/0.99  --bmc1_pre_inst_state                   false
% 3.22/0.99  --bmc1_pre_inst_reach_state             false
% 3.22/0.99  --bmc1_out_unsat_core                   false
% 3.22/0.99  --bmc1_aig_witness_out                  false
% 3.22/0.99  --bmc1_verbose                          false
% 3.22/0.99  --bmc1_dump_clauses_tptp                false
% 3.22/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.22/0.99  --bmc1_dump_file                        -
% 3.22/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.22/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.22/0.99  --bmc1_ucm_extend_mode                  1
% 3.22/0.99  --bmc1_ucm_init_mode                    2
% 3.22/0.99  --bmc1_ucm_cone_mode                    none
% 3.22/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.22/0.99  --bmc1_ucm_relax_model                  4
% 3.22/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.22/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.22/0.99  --bmc1_ucm_layered_model                none
% 3.22/0.99  --bmc1_ucm_max_lemma_size               10
% 3.22/0.99  
% 3.22/0.99  ------ AIG Options
% 3.22/0.99  
% 3.22/0.99  --aig_mode                              false
% 3.22/0.99  
% 3.22/0.99  ------ Instantiation Options
% 3.22/0.99  
% 3.22/0.99  --instantiation_flag                    true
% 3.22/0.99  --inst_sos_flag                         false
% 3.22/0.99  --inst_sos_phase                        true
% 3.22/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.22/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.22/0.99  --inst_lit_sel_side                     none
% 3.22/0.99  --inst_solver_per_active                1400
% 3.22/0.99  --inst_solver_calls_frac                1.
% 3.22/0.99  --inst_passive_queue_type               priority_queues
% 3.22/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.22/0.99  --inst_passive_queues_freq              [25;2]
% 3.22/0.99  --inst_dismatching                      true
% 3.22/0.99  --inst_eager_unprocessed_to_passive     true
% 3.22/0.99  --inst_prop_sim_given                   true
% 3.22/0.99  --inst_prop_sim_new                     false
% 3.22/0.99  --inst_subs_new                         false
% 3.22/0.99  --inst_eq_res_simp                      false
% 3.22/0.99  --inst_subs_given                       false
% 3.22/0.99  --inst_orphan_elimination               true
% 3.22/0.99  --inst_learning_loop_flag               true
% 3.22/0.99  --inst_learning_start                   3000
% 3.22/0.99  --inst_learning_factor                  2
% 3.22/0.99  --inst_start_prop_sim_after_learn       3
% 3.22/0.99  --inst_sel_renew                        solver
% 3.22/0.99  --inst_lit_activity_flag                true
% 3.22/0.99  --inst_restr_to_given                   false
% 3.22/0.99  --inst_activity_threshold               500
% 3.22/0.99  --inst_out_proof                        true
% 3.22/0.99  
% 3.22/0.99  ------ Resolution Options
% 3.22/0.99  
% 3.22/0.99  --resolution_flag                       false
% 3.22/0.99  --res_lit_sel                           adaptive
% 3.22/0.99  --res_lit_sel_side                      none
% 3.22/0.99  --res_ordering                          kbo
% 3.22/0.99  --res_to_prop_solver                    active
% 3.22/0.99  --res_prop_simpl_new                    false
% 3.22/0.99  --res_prop_simpl_given                  true
% 3.22/0.99  --res_passive_queue_type                priority_queues
% 3.22/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.22/0.99  --res_passive_queues_freq               [15;5]
% 3.22/0.99  --res_forward_subs                      full
% 3.22/0.99  --res_backward_subs                     full
% 3.22/0.99  --res_forward_subs_resolution           true
% 3.22/0.99  --res_backward_subs_resolution          true
% 3.22/0.99  --res_orphan_elimination                true
% 3.22/0.99  --res_time_limit                        2.
% 3.22/0.99  --res_out_proof                         true
% 3.22/0.99  
% 3.22/0.99  ------ Superposition Options
% 3.22/0.99  
% 3.22/0.99  --superposition_flag                    true
% 3.22/0.99  --sup_passive_queue_type                priority_queues
% 3.22/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.22/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.22/0.99  --demod_completeness_check              fast
% 3.22/0.99  --demod_use_ground                      true
% 3.22/0.99  --sup_to_prop_solver                    passive
% 3.22/0.99  --sup_prop_simpl_new                    true
% 3.22/0.99  --sup_prop_simpl_given                  true
% 3.22/0.99  --sup_fun_splitting                     false
% 3.22/0.99  --sup_smt_interval                      50000
% 3.22/0.99  
% 3.22/0.99  ------ Superposition Simplification Setup
% 3.22/0.99  
% 3.22/0.99  --sup_indices_passive                   []
% 3.22/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.22/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.99  --sup_full_bw                           [BwDemod]
% 3.22/0.99  --sup_immed_triv                        [TrivRules]
% 3.22/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.99  --sup_immed_bw_main                     []
% 3.22/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.22/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.99  
% 3.22/0.99  ------ Combination Options
% 3.22/0.99  
% 3.22/0.99  --comb_res_mult                         3
% 3.22/0.99  --comb_sup_mult                         2
% 3.22/0.99  --comb_inst_mult                        10
% 3.22/0.99  
% 3.22/0.99  ------ Debug Options
% 3.22/0.99  
% 3.22/0.99  --dbg_backtrace                         false
% 3.22/0.99  --dbg_dump_prop_clauses                 false
% 3.22/0.99  --dbg_dump_prop_clauses_file            -
% 3.22/0.99  --dbg_out_stat                          false
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  ------ Proving...
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  % SZS status Theorem for theBenchmark.p
% 3.22/0.99  
% 3.22/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.22/0.99  
% 3.22/0.99  fof(f5,axiom,(
% 3.22/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f63,plain,(
% 3.22/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.22/0.99    inference(cnf_transformation,[],[f5])).
% 3.22/0.99  
% 3.22/0.99  fof(f20,axiom,(
% 3.22/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f44,plain,(
% 3.22/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/0.99    inference(ennf_transformation,[],[f20])).
% 3.22/0.99  
% 3.22/0.99  fof(f45,plain,(
% 3.22/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/0.99    inference(flattening,[],[f44])).
% 3.22/0.99  
% 3.22/0.99  fof(f54,plain,(
% 3.22/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/0.99    inference(nnf_transformation,[],[f45])).
% 3.22/0.99  
% 3.22/0.99  fof(f80,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/0.99    inference(cnf_transformation,[],[f54])).
% 3.22/0.99  
% 3.22/0.99  fof(f25,conjecture,(
% 3.22/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f26,negated_conjecture,(
% 3.22/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.22/0.99    inference(negated_conjecture,[],[f25])).
% 3.22/0.99  
% 3.22/0.99  fof(f50,plain,(
% 3.22/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.22/0.99    inference(ennf_transformation,[],[f26])).
% 3.22/0.99  
% 3.22/0.99  fof(f51,plain,(
% 3.22/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.22/0.99    inference(flattening,[],[f50])).
% 3.22/0.99  
% 3.22/0.99  fof(f55,plain,(
% 3.22/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.22/0.99    introduced(choice_axiom,[])).
% 3.22/0.99  
% 3.22/0.99  fof(f56,plain,(
% 3.22/0.99    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.22/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f51,f55])).
% 3.22/0.99  
% 3.22/0.99  fof(f95,plain,(
% 3.22/0.99    v1_funct_2(sK2,sK0,sK1)),
% 3.22/0.99    inference(cnf_transformation,[],[f56])).
% 3.22/0.99  
% 3.22/0.99  fof(f96,plain,(
% 3.22/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.22/0.99    inference(cnf_transformation,[],[f56])).
% 3.22/0.99  
% 3.22/0.99  fof(f18,axiom,(
% 3.22/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f42,plain,(
% 3.22/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/0.99    inference(ennf_transformation,[],[f18])).
% 3.22/0.99  
% 3.22/0.99  fof(f78,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/0.99    inference(cnf_transformation,[],[f42])).
% 3.22/0.99  
% 3.22/0.99  fof(f16,axiom,(
% 3.22/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f40,plain,(
% 3.22/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/0.99    inference(ennf_transformation,[],[f16])).
% 3.22/0.99  
% 3.22/0.99  fof(f76,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/0.99    inference(cnf_transformation,[],[f40])).
% 3.22/0.99  
% 3.22/0.99  fof(f15,axiom,(
% 3.22/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f38,plain,(
% 3.22/0.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.22/0.99    inference(ennf_transformation,[],[f15])).
% 3.22/0.99  
% 3.22/0.99  fof(f39,plain,(
% 3.22/0.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.22/0.99    inference(flattening,[],[f38])).
% 3.22/0.99  
% 3.22/0.99  fof(f75,plain,(
% 3.22/0.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f39])).
% 3.22/0.99  
% 3.22/0.99  fof(f97,plain,(
% 3.22/0.99    v2_funct_1(sK2)),
% 3.22/0.99    inference(cnf_transformation,[],[f56])).
% 3.22/0.99  
% 3.22/0.99  fof(f94,plain,(
% 3.22/0.99    v1_funct_1(sK2)),
% 3.22/0.99    inference(cnf_transformation,[],[f56])).
% 3.22/0.99  
% 3.22/0.99  fof(f23,axiom,(
% 3.22/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f46,plain,(
% 3.22/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.22/0.99    inference(ennf_transformation,[],[f23])).
% 3.22/0.99  
% 3.22/0.99  fof(f47,plain,(
% 3.22/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.22/0.99    inference(flattening,[],[f46])).
% 3.22/0.99  
% 3.22/0.99  fof(f90,plain,(
% 3.22/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f47])).
% 3.22/0.99  
% 3.22/0.99  fof(f19,axiom,(
% 3.22/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f43,plain,(
% 3.22/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/0.99    inference(ennf_transformation,[],[f19])).
% 3.22/0.99  
% 3.22/0.99  fof(f79,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/0.99    inference(cnf_transformation,[],[f43])).
% 3.22/0.99  
% 3.22/0.99  fof(f98,plain,(
% 3.22/0.99    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.22/0.99    inference(cnf_transformation,[],[f56])).
% 3.22/0.99  
% 3.22/0.99  fof(f74,plain,(
% 3.22/0.99    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f39])).
% 3.22/0.99  
% 3.22/0.99  fof(f13,axiom,(
% 3.22/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f34,plain,(
% 3.22/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.22/0.99    inference(ennf_transformation,[],[f13])).
% 3.22/0.99  
% 3.22/0.99  fof(f35,plain,(
% 3.22/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.22/0.99    inference(flattening,[],[f34])).
% 3.22/0.99  
% 3.22/0.99  fof(f72,plain,(
% 3.22/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f35])).
% 3.22/0.99  
% 3.22/0.99  fof(f71,plain,(
% 3.22/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f35])).
% 3.22/0.99  
% 3.22/0.99  fof(f89,plain,(
% 3.22/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f47])).
% 3.22/0.99  
% 3.22/0.99  fof(f99,plain,(
% 3.22/0.99    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.22/0.99    inference(cnf_transformation,[],[f56])).
% 3.22/0.99  
% 3.22/0.99  fof(f2,axiom,(
% 3.22/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f58,plain,(
% 3.22/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f2])).
% 3.22/0.99  
% 3.22/0.99  fof(f24,axiom,(
% 3.22/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f48,plain,(
% 3.22/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.22/0.99    inference(ennf_transformation,[],[f24])).
% 3.22/0.99  
% 3.22/0.99  fof(f49,plain,(
% 3.22/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.22/0.99    inference(flattening,[],[f48])).
% 3.22/0.99  
% 3.22/0.99  fof(f93,plain,(
% 3.22/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f49])).
% 3.22/0.99  
% 3.22/0.99  fof(f4,axiom,(
% 3.22/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f52,plain,(
% 3.22/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.22/0.99    inference(nnf_transformation,[],[f4])).
% 3.22/0.99  
% 3.22/0.99  fof(f53,plain,(
% 3.22/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.22/0.99    inference(flattening,[],[f52])).
% 3.22/0.99  
% 3.22/0.99  fof(f61,plain,(
% 3.22/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.22/0.99    inference(cnf_transformation,[],[f53])).
% 3.22/0.99  
% 3.22/0.99  fof(f103,plain,(
% 3.22/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.22/0.99    inference(equality_resolution,[],[f61])).
% 3.22/0.99  
% 3.22/0.99  fof(f92,plain,(
% 3.22/0.99    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f49])).
% 3.22/0.99  
% 3.22/0.99  fof(f84,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/0.99    inference(cnf_transformation,[],[f54])).
% 3.22/0.99  
% 3.22/0.99  fof(f106,plain,(
% 3.22/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.22/0.99    inference(equality_resolution,[],[f84])).
% 3.22/0.99  
% 3.22/0.99  fof(f17,axiom,(
% 3.22/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f41,plain,(
% 3.22/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.22/0.99    inference(ennf_transformation,[],[f17])).
% 3.22/0.99  
% 3.22/0.99  fof(f77,plain,(
% 3.22/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f41])).
% 3.22/0.99  
% 3.22/0.99  fof(f3,axiom,(
% 3.22/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f29,plain,(
% 3.22/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.22/0.99    inference(ennf_transformation,[],[f3])).
% 3.22/0.99  
% 3.22/0.99  fof(f59,plain,(
% 3.22/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f29])).
% 3.22/0.99  
% 3.22/0.99  fof(f1,axiom,(
% 3.22/0.99    v1_xboole_0(k1_xboole_0)),
% 3.22/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.99  
% 3.22/0.99  fof(f57,plain,(
% 3.22/0.99    v1_xboole_0(k1_xboole_0)),
% 3.22/0.99    inference(cnf_transformation,[],[f1])).
% 3.22/0.99  
% 3.22/0.99  fof(f60,plain,(
% 3.22/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.22/0.99    inference(cnf_transformation,[],[f53])).
% 3.22/0.99  
% 3.22/0.99  cnf(c_877,plain,
% 3.22/0.99      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 3.22/0.99      theory(equality) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_7802,plain,
% 3.22/0.99      ( k2_funct_1(sK2) != X0
% 3.22/0.99      | k2_relat_1(k2_funct_1(sK2)) = k2_relat_1(X0) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_877]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_7804,plain,
% 3.22/0.99      ( k2_funct_1(sK2) != k1_xboole_0
% 3.22/0.99      | k2_relat_1(k2_funct_1(sK2)) = k2_relat_1(k1_xboole_0) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_7802]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_869,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1926,plain,
% 3.22/0.99      ( k2_relat_1(X0) != X1
% 3.22/0.99      | k2_relat_1(X0) = k1_xboole_0
% 3.22/0.99      | k1_xboole_0 != X1 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_869]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4133,plain,
% 3.22/0.99      ( k2_relat_1(k2_funct_1(sK2)) != X0
% 3.22/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 3.22/0.99      | k1_xboole_0 != X0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1926]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_7801,plain,
% 3.22/0.99      ( k2_relat_1(k2_funct_1(sK2)) != k2_relat_1(X0)
% 3.22/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 3.22/0.99      | k1_xboole_0 != k2_relat_1(X0) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_4133]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_7803,plain,
% 3.22/0.99      ( k2_relat_1(k2_funct_1(sK2)) != k2_relat_1(k1_xboole_0)
% 3.22/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 3.22/0.99      | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_7801]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_868,plain,( X0 = X0 ),theory(equality) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2465,plain,
% 3.22/0.99      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_868]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_7365,plain,
% 3.22/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_2465]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_6,plain,
% 3.22/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.22/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1843,plain,
% 3.22/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_6947,plain,
% 3.22/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1843]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_6948,plain,
% 3.22/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_6947]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_28,plain,
% 3.22/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.22/0.99      | k1_xboole_0 = X2 ),
% 3.22/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_40,negated_conjecture,
% 3.22/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.22/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_732,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.22/0.99      | sK0 != X1
% 3.22/0.99      | sK1 != X2
% 3.22/0.99      | sK2 != X0
% 3.22/0.99      | k1_xboole_0 = X2 ),
% 3.22/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_40]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_733,plain,
% 3.22/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.22/0.99      | k1_relset_1(sK0,sK1,sK2) = sK0
% 3.22/0.99      | k1_xboole_0 = sK1 ),
% 3.22/0.99      inference(unflattening,[status(thm)],[c_732]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_39,negated_conjecture,
% 3.22/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.22/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_735,plain,
% 3.22/0.99      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_733,c_39]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1476,plain,
% 3.22/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_21,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1480,plain,
% 3.22/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.22/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4538,plain,
% 3.22/0.99      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_1476,c_1480]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4605,plain,
% 3.22/0.99      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_735,c_4538]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_19,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/0.99      | v1_relat_1(X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1482,plain,
% 3.22/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.22/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2895,plain,
% 3.22/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_1476,c_1482]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_17,plain,
% 3.22/0.99      ( ~ v2_funct_1(X0)
% 3.22/0.99      | ~ v1_funct_1(X0)
% 3.22/0.99      | ~ v1_relat_1(X0)
% 3.22/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_38,negated_conjecture,
% 3.22/0.99      ( v2_funct_1(sK2) ),
% 3.22/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_461,plain,
% 3.22/0.99      ( ~ v1_funct_1(X0)
% 3.22/0.99      | ~ v1_relat_1(X0)
% 3.22/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.22/0.99      | sK2 != X0 ),
% 3.22/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_38]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_462,plain,
% 3.22/0.99      ( ~ v1_funct_1(sK2)
% 3.22/0.99      | ~ v1_relat_1(sK2)
% 3.22/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.22/0.99      inference(unflattening,[status(thm)],[c_461]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_41,negated_conjecture,
% 3.22/0.99      ( v1_funct_1(sK2) ),
% 3.22/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_464,plain,
% 3.22/0.99      ( ~ v1_relat_1(sK2)
% 3.22/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_462,c_41]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1472,plain,
% 3.22/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.22/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_3118,plain,
% 3.22/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_2895,c_1472]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_30,plain,
% 3.22/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.22/0.99      | ~ v1_funct_1(X0)
% 3.22/0.99      | ~ v1_relat_1(X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1477,plain,
% 3.22/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.22/0.99      | v1_funct_1(X0) != iProver_top
% 3.22/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5018,plain,
% 3.22/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 3.22/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.22/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_3118,c_1477]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_22,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1479,plain,
% 3.22/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.22/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_3021,plain,
% 3.22/0.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_1476,c_1479]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_37,negated_conjecture,
% 3.22/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.22/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_3033,plain,
% 3.22/0.99      ( k2_relat_1(sK2) = sK1 ),
% 3.22/0.99      inference(light_normalisation,[status(thm)],[c_3021,c_37]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_18,plain,
% 3.22/0.99      ( ~ v2_funct_1(X0)
% 3.22/0.99      | ~ v1_funct_1(X0)
% 3.22/0.99      | ~ v1_relat_1(X0)
% 3.22/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_447,plain,
% 3.22/0.99      ( ~ v1_funct_1(X0)
% 3.22/0.99      | ~ v1_relat_1(X0)
% 3.22/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.22/0.99      | sK2 != X0 ),
% 3.22/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_38]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_448,plain,
% 3.22/0.99      ( ~ v1_funct_1(sK2)
% 3.22/0.99      | ~ v1_relat_1(sK2)
% 3.22/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.22/0.99      inference(unflattening,[status(thm)],[c_447]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_450,plain,
% 3.22/0.99      ( ~ v1_relat_1(sK2)
% 3.22/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_448,c_41]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1473,plain,
% 3.22/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.22/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_450]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_3110,plain,
% 3.22/0.99      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 3.22/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.22/0.99      inference(demodulation,[status(thm)],[c_3033,c_1473]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_44,plain,
% 3.22/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1855,plain,
% 3.22/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.22/0.99      | v1_relat_1(sK2) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1856,plain,
% 3.22/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.22/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_1855]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_3398,plain,
% 3.22/0.99      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_3110,c_44,c_1856]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5037,plain,
% 3.22/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 3.22/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.22/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.22/0.99      inference(light_normalisation,[status(thm)],[c_5018,c_3398]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_42,plain,
% 3.22/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_14,plain,
% 3.22/0.99      ( ~ v1_funct_1(X0)
% 3.22/0.99      | v1_funct_1(k2_funct_1(X0))
% 3.22/0.99      | ~ v1_relat_1(X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2198,plain,
% 3.22/0.99      ( v1_funct_1(k2_funct_1(sK2))
% 3.22/0.99      | ~ v1_funct_1(sK2)
% 3.22/0.99      | ~ v1_relat_1(sK2) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2199,plain,
% 3.22/0.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.22/0.99      | v1_funct_1(sK2) != iProver_top
% 3.22/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_2198]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_15,plain,
% 3.22/0.99      ( ~ v1_funct_1(X0)
% 3.22/0.99      | ~ v1_relat_1(X0)
% 3.22/0.99      | v1_relat_1(k2_funct_1(X0)) ),
% 3.22/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_3096,plain,
% 3.22/0.99      ( ~ v1_funct_1(sK2)
% 3.22/0.99      | v1_relat_1(k2_funct_1(sK2))
% 3.22/0.99      | ~ v1_relat_1(sK2) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_3097,plain,
% 3.22/0.99      ( v1_funct_1(sK2) != iProver_top
% 3.22/0.99      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.22/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_3096]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5462,plain,
% 3.22/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_5037,c_42,c_44,c_1856,c_2199,c_3097]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5468,plain,
% 3.22/0.99      ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_5462,c_1480]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5477,plain,
% 3.22/0.99      ( k1_relset_1(sK1,k1_relat_1(sK2),k2_funct_1(sK2)) = sK1 ),
% 3.22/0.99      inference(light_normalisation,[status(thm)],[c_5468,c_3398]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5499,plain,
% 3.22/0.99      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1 | sK1 = k1_xboole_0 ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_4605,c_5477]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_31,plain,
% 3.22/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.22/0.99      | ~ v1_funct_1(X0)
% 3.22/0.99      | ~ v1_relat_1(X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_36,negated_conjecture,
% 3.22/0.99      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 3.22/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.22/0.99      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 3.22/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_743,plain,
% 3.22/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.22/0.99      | ~ v1_funct_1(X0)
% 3.22/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.22/0.99      | ~ v1_relat_1(X0)
% 3.22/0.99      | k2_funct_1(sK2) != X0
% 3.22/0.99      | k2_relat_1(X0) != sK0
% 3.22/0.99      | k1_relat_1(X0) != sK1 ),
% 3.22/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_36]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_744,plain,
% 3.22/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.22/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.22/0.99      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.22/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.22/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.22/0.99      inference(unflattening,[status(thm)],[c_743]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_756,plain,
% 3.22/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.22/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.22/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.22/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.22/0.99      inference(forward_subsumption_resolution,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_744,c_19]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1460,plain,
% 3.22/0.99      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.22/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.22/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_756]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_3401,plain,
% 3.22/0.99      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.22/0.99      | sK1 != sK1
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.22/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.22/0.99      inference(demodulation,[status(thm)],[c_3398,c_1460]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_3410,plain,
% 3.22/0.99      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.22/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.22/0.99      inference(equality_resolution_simp,[status(thm)],[c_3401]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_745,plain,
% 3.22/0.99      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.22/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.22/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.22/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4278,plain,
% 3.22/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.22/0.99      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_3410,c_42,c_44,c_745,c_1856,c_2199,c_3097,c_3110]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4279,plain,
% 3.22/0.99      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.22/0.99      inference(renaming,[status(thm)],[c_4278]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4282,plain,
% 3.22/0.99      ( k1_relat_1(sK2) != sK0
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.22/0.99      inference(light_normalisation,[status(thm)],[c_4279,c_3118]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4701,plain,
% 3.22/0.99      ( sK1 = k1_xboole_0
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_4605,c_4282]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5467,plain,
% 3.22/0.99      ( sK1 = k1_xboole_0
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_4605,c_5462]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5500,plain,
% 3.22/0.99      ( sK1 = k1_xboole_0 ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_5499,c_4701,c_5467]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1,plain,
% 3.22/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_33,plain,
% 3.22/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.22/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.22/0.99      | ~ v1_funct_1(X0)
% 3.22/0.99      | ~ v1_relat_1(X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_419,plain,
% 3.22/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.22/0.99      | ~ v1_funct_1(X0)
% 3.22/0.99      | ~ v1_relat_1(X0)
% 3.22/0.99      | X1 != X2
% 3.22/0.99      | k2_relat_1(X0) != k1_xboole_0 ),
% 3.22/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_33]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_420,plain,
% 3.22/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.22/0.99      | ~ v1_funct_1(X0)
% 3.22/0.99      | ~ v1_relat_1(X0)
% 3.22/0.99      | k2_relat_1(X0) != k1_xboole_0 ),
% 3.22/0.99      inference(unflattening,[status(thm)],[c_419]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1474,plain,
% 3.22/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 3.22/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.22/0.99      | v1_funct_1(X0) != iProver_top
% 3.22/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_420]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4428,plain,
% 3.22/0.99      ( k1_relat_1(sK2) != k1_xboole_0
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0))) = iProver_top
% 3.22/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.22/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_3118,c_1474]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4433,plain,
% 3.22/0.99      ( k1_relat_1(sK2) != k1_xboole_0
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.22/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.22/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.22/0.99      inference(light_normalisation,[status(thm)],[c_4428,c_3398]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4809,plain,
% 3.22/0.99      ( k1_relat_1(sK2) != k1_xboole_0
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_4433,c_42,c_44,c_1856,c_2199,c_3097]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5511,plain,
% 3.22/0.99      ( k1_relat_1(sK2) != k1_xboole_0
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top ),
% 3.22/0.99      inference(demodulation,[status(thm)],[c_5500,c_4809]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4,plain,
% 3.22/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.22/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5609,plain,
% 3.22/0.99      ( k1_relat_1(sK2) != k1_xboole_0
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.22/0.99      inference(light_normalisation,[status(thm)],[c_5511,c_4]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_34,plain,
% 3.22/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.22/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.22/0.99      | ~ v1_funct_1(X0)
% 3.22/0.99      | ~ v1_relat_1(X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_401,plain,
% 3.22/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.22/0.99      | ~ v1_funct_1(X0)
% 3.22/0.99      | ~ v1_relat_1(X0)
% 3.22/0.99      | X1 != X2
% 3.22/0.99      | k2_relat_1(X0) != k1_xboole_0 ),
% 3.22/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_34]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_402,plain,
% 3.22/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.22/0.99      | ~ v1_funct_1(X0)
% 3.22/0.99      | ~ v1_relat_1(X0)
% 3.22/0.99      | k2_relat_1(X0) != k1_xboole_0 ),
% 3.22/0.99      inference(unflattening,[status(thm)],[c_401]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_762,plain,
% 3.22/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.22/0.99      | ~ v1_funct_1(X0)
% 3.22/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.22/0.99      | ~ v1_relat_1(X0)
% 3.22/0.99      | k2_funct_1(sK2) != X0
% 3.22/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.22/0.99      | k1_relat_1(X0) != sK1
% 3.22/0.99      | sK0 != X1 ),
% 3.22/0.99      inference(resolution_lifted,[status(thm)],[c_402,c_36]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_763,plain,
% 3.22/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.22/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.22/0.99      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.22/0.99      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 3.22/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.22/0.99      inference(unflattening,[status(thm)],[c_762]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_775,plain,
% 3.22/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.22/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.22/0.99      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 3.22/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.22/0.99      inference(forward_subsumption_resolution,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_763,c_19]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1459,plain,
% 3.22/0.99      ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 3.22/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.22/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_775]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_3402,plain,
% 3.22/0.99      ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 3.22/0.99      | sK1 != sK1
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.22/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.22/0.99      inference(demodulation,[status(thm)],[c_3398,c_1459]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_3403,plain,
% 3.22/0.99      ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.22/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.22/0.99      inference(equality_resolution_simp,[status(thm)],[c_3402]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_764,plain,
% 3.22/0.99      ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 3.22/0.99      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.22/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.22/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_763]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4269,plain,
% 3.22/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.22/0.99      | k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0 ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_3403,c_42,c_44,c_764,c_1856,c_2199,c_3097,c_3110]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4270,plain,
% 3.22/0.99      ( k2_relat_1(k2_funct_1(sK2)) != k1_xboole_0
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.22/0.99      inference(renaming,[status(thm)],[c_4269]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4273,plain,
% 3.22/0.99      ( k1_relat_1(sK2) != k1_xboole_0
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.22/0.99      inference(light_normalisation,[status(thm)],[c_4270,c_3118]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5515,plain,
% 3.22/0.99      ( k1_relat_1(sK2) != k1_xboole_0
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 3.22/0.99      inference(demodulation,[status(thm)],[c_5500,c_4273]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5594,plain,
% 3.22/0.99      ( k1_relat_1(sK2) != k1_xboole_0
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.22/0.99      inference(demodulation,[status(thm)],[c_5515,c_4]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5612,plain,
% 3.22/0.99      ( k1_relat_1(sK2) != k1_xboole_0 ),
% 3.22/0.99      inference(backward_subsumption_resolution,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_5609,c_5594]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_24,plain,
% 3.22/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.22/0.99      | k1_xboole_0 = X1
% 3.22/0.99      | k1_xboole_0 = X0 ),
% 3.22/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_536,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.22/0.99      | ~ v1_funct_1(X2)
% 3.22/0.99      | ~ v1_relat_1(X2)
% 3.22/0.99      | X2 != X0
% 3.22/0.99      | k2_relat_1(X2) != k1_xboole_0
% 3.22/0.99      | k1_relat_1(X2) != X1
% 3.22/0.99      | k1_xboole_0 = X1
% 3.22/0.99      | k1_xboole_0 = X0 ),
% 3.22/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_537,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.22/0.99      | ~ v1_funct_1(X0)
% 3.22/0.99      | ~ v1_relat_1(X0)
% 3.22/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.22/0.99      | k1_xboole_0 = X0
% 3.22/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.22/0.99      inference(unflattening,[status(thm)],[c_536]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_553,plain,
% 3.22/0.99      ( ~ v1_funct_1(X0)
% 3.22/0.99      | ~ v1_relat_1(X0)
% 3.22/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.22/0.99      | k1_xboole_0 = X0
% 3.22/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.22/0.99      inference(forward_subsumption_resolution,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_537,c_420]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1469,plain,
% 3.22/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 3.22/0.99      | k1_xboole_0 = X0
% 3.22/0.99      | k1_xboole_0 = k1_relat_1(X0)
% 3.22/0.99      | v1_funct_1(X0) != iProver_top
% 3.22/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_553]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_3690,plain,
% 3.22/0.99      ( k1_relat_1(sK2) = k1_xboole_0
% 3.22/0.99      | sK1 != k1_xboole_0
% 3.22/0.99      | sK2 = k1_xboole_0
% 3.22/0.99      | v1_funct_1(sK2) != iProver_top
% 3.22/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_3033,c_1469]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_3719,plain,
% 3.22/0.99      ( ~ v1_funct_1(sK2)
% 3.22/0.99      | ~ v1_relat_1(sK2)
% 3.22/0.99      | k1_relat_1(sK2) = k1_xboole_0
% 3.22/0.99      | sK1 != k1_xboole_0
% 3.22/0.99      | sK2 = k1_xboole_0 ),
% 3.22/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3690]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4070,plain,
% 3.22/0.99      ( k1_relat_1(sK2) = k1_xboole_0
% 3.22/0.99      | sK1 != k1_xboole_0
% 3.22/0.99      | sK2 = k1_xboole_0 ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_3690,c_41,c_39,c_1855,c_3719]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5518,plain,
% 3.22/0.99      ( k1_relat_1(sK2) = k1_xboole_0
% 3.22/0.99      | sK2 = k1_xboole_0
% 3.22/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.22/0.99      inference(demodulation,[status(thm)],[c_5500,c_4070]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5581,plain,
% 3.22/0.99      ( k1_relat_1(sK2) = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.22/0.99      inference(equality_resolution_simp,[status(thm)],[c_5518]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5615,plain,
% 3.22/0.99      ( sK2 = k1_xboole_0 ),
% 3.22/0.99      inference(backward_subsumption_resolution,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_5612,c_5581]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5523,plain,
% 3.22/0.99      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 3.22/0.99      inference(demodulation,[status(thm)],[c_5500,c_3033]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5625,plain,
% 3.22/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.22/0.99      inference(demodulation,[status(thm)],[c_5615,c_5523]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_873,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.22/0.99      theory(equality) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1938,plain,
% 3.22/0.99      ( m1_subset_1(X0,X1)
% 3.22/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
% 3.22/0.99      | X1 != k1_zfmisc_1(X2)
% 3.22/0.99      | X0 != k1_xboole_0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_873]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2464,plain,
% 3.22/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.22/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
% 3.22/0.99      | X0 != k1_xboole_0
% 3.22/0.99      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1938]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4931,plain,
% 3.22/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.22/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.22/0.99      | k2_funct_1(sK2) != k1_xboole_0
% 3.22/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_2464]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4932,plain,
% 3.22/0.99      ( k2_funct_1(sK2) != k1_xboole_0
% 3.22/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 3.22/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 3.22/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_4931]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_870,plain,
% 3.22/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.22/0.99      theory(equality) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2309,plain,
% 3.22/0.99      ( ~ v1_xboole_0(X0)
% 3.22/0.99      | v1_xboole_0(k1_relat_1(X1))
% 3.22/0.99      | k1_relat_1(X1) != X0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_870]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4081,plain,
% 3.22/0.99      ( ~ v1_xboole_0(X0)
% 3.22/0.99      | v1_xboole_0(k1_relat_1(k2_funct_1(sK2)))
% 3.22/0.99      | k1_relat_1(k2_funct_1(sK2)) != X0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_2309]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_4083,plain,
% 3.22/0.99      ( v1_xboole_0(k1_relat_1(k2_funct_1(sK2)))
% 3.22/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.22/0.99      | k1_relat_1(k2_funct_1(sK2)) != k1_xboole_0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_4081]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_3634,plain,
% 3.22/0.99      ( k2_relat_1(X0) != X1
% 3.22/0.99      | k1_xboole_0 != X1
% 3.22/0.99      | k1_xboole_0 = k2_relat_1(X0) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_869]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_3635,plain,
% 3.22/0.99      ( k2_relat_1(k1_xboole_0) != k1_xboole_0
% 3.22/0.99      | k1_xboole_0 = k2_relat_1(k1_xboole_0)
% 3.22/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_3634]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2946,plain,
% 3.22/0.99      ( k2_relat_1(sK2) = k2_relat_1(X0) | sK2 != X0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_877]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2948,plain,
% 3.22/0.99      ( k2_relat_1(sK2) = k2_relat_1(k1_xboole_0) | sK2 != k1_xboole_0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_2946]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2553,plain,
% 3.22/0.99      ( k2_relat_1(sK2) != X0
% 3.22/0.99      | k1_xboole_0 != X0
% 3.22/0.99      | k1_xboole_0 = k2_relat_1(sK2) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_869]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2945,plain,
% 3.22/0.99      ( k2_relat_1(sK2) != k2_relat_1(X0)
% 3.22/0.99      | k1_xboole_0 != k2_relat_1(X0)
% 3.22/0.99      | k1_xboole_0 = k2_relat_1(sK2) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_2553]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2947,plain,
% 3.22/0.99      ( k2_relat_1(sK2) != k2_relat_1(k1_xboole_0)
% 3.22/0.99      | k1_xboole_0 = k2_relat_1(sK2)
% 3.22/0.99      | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_2945]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_20,plain,
% 3.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/0.99      | ~ v1_xboole_0(X1)
% 3.22/0.99      | v1_xboole_0(X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2000,plain,
% 3.22/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.22/0.99      | ~ v1_xboole_0(X0)
% 3.22/0.99      | v1_xboole_0(k2_funct_1(sK2)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2387,plain,
% 3.22/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
% 3.22/0.99      | v1_xboole_0(k2_funct_1(sK2))
% 3.22/0.99      | ~ v1_xboole_0(k1_relat_1(k2_funct_1(sK2))) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_2000]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2386,plain,
% 3.22/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
% 3.22/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.22/0.99      | ~ v1_relat_1(k2_funct_1(sK2)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_30]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1894,plain,
% 3.22/0.99      ( k1_relat_1(X0) != X1
% 3.22/0.99      | k1_relat_1(X0) = k1_xboole_0
% 3.22/0.99      | k1_xboole_0 != X1 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_869]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2366,plain,
% 3.22/0.99      ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 3.22/0.99      | k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 3.22/0.99      | k1_xboole_0 != k2_relat_1(sK2) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1894]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2,plain,
% 3.22/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 3.22/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2040,plain,
% 3.22/0.99      ( ~ v1_xboole_0(X0)
% 3.22/0.99      | ~ v1_xboole_0(k2_funct_1(sK2))
% 3.22/0.99      | k2_funct_1(sK2) = X0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_2042,plain,
% 3.22/0.99      ( ~ v1_xboole_0(k2_funct_1(sK2))
% 3.22/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.22/0.99      | k2_funct_1(sK2) = k1_xboole_0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_2040]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_0,plain,
% 3.22/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_126,plain,
% 3.22/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_5,plain,
% 3.22/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.22/0.99      | k1_xboole_0 = X1
% 3.22/0.99      | k1_xboole_0 = X0 ),
% 3.22/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_125,plain,
% 3.22/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.22/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(contradiction,plain,
% 3.22/0.99      ( $false ),
% 3.22/0.99      inference(minisat,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_7804,c_7803,c_7365,c_6948,c_5625,c_5615,c_4932,c_4083,
% 3.22/0.99                 c_3635,c_3110,c_3097,c_3096,c_2948,c_2947,c_2387,c_2386,
% 3.22/0.99                 c_2366,c_2199,c_2198,c_2042,c_1856,c_1855,c_764,c_448,
% 3.22/0.99                 c_0,c_126,c_125,c_44,c_39,c_42,c_41]) ).
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.22/0.99  
% 3.22/0.99  ------                               Statistics
% 3.22/0.99  
% 3.22/0.99  ------ General
% 3.22/0.99  
% 3.22/0.99  abstr_ref_over_cycles:                  0
% 3.22/0.99  abstr_ref_under_cycles:                 0
% 3.22/0.99  gc_basic_clause_elim:                   0
% 3.22/0.99  forced_gc_time:                         0
% 3.22/0.99  parsing_time:                           0.012
% 3.22/0.99  unif_index_cands_time:                  0.
% 3.22/0.99  unif_index_add_time:                    0.
% 3.22/0.99  orderings_time:                         0.
% 3.22/0.99  out_proof_time:                         0.013
% 3.22/0.99  total_time:                             0.231
% 3.22/0.99  num_of_symbols:                         52
% 3.22/0.99  num_of_terms:                           5217
% 3.22/0.99  
% 3.22/0.99  ------ Preprocessing
% 3.22/0.99  
% 3.22/0.99  num_of_splits:                          0
% 3.22/0.99  num_of_split_atoms:                     0
% 3.22/0.99  num_of_reused_defs:                     0
% 3.22/0.99  num_eq_ax_congr_red:                    6
% 3.22/0.99  num_of_sem_filtered_clauses:            1
% 3.22/0.99  num_of_subtypes:                        0
% 3.22/0.99  monotx_restored_types:                  0
% 3.22/0.99  sat_num_of_epr_types:                   0
% 3.22/0.99  sat_num_of_non_cyclic_types:            0
% 3.22/0.99  sat_guarded_non_collapsed_types:        0
% 3.22/0.99  num_pure_diseq_elim:                    0
% 3.22/0.99  simp_replaced_by:                       0
% 3.22/0.99  res_preprocessed:                       155
% 3.22/0.99  prep_upred:                             0
% 3.22/0.99  prep_unflattend:                        56
% 3.22/0.99  smt_new_axioms:                         0
% 3.22/0.99  pred_elim_cands:                        7
% 3.22/0.99  pred_elim:                              3
% 3.22/0.99  pred_elim_cl:                           -2
% 3.22/0.99  pred_elim_cycles:                       4
% 3.22/0.99  merged_defs:                            0
% 3.22/0.99  merged_defs_ncl:                        0
% 3.22/0.99  bin_hyper_res:                          0
% 3.22/0.99  prep_cycles:                            3
% 3.22/0.99  pred_elim_time:                         0.011
% 3.22/0.99  splitting_time:                         0.
% 3.22/0.99  sem_filter_time:                        0.
% 3.22/0.99  monotx_time:                            0.
% 3.22/0.99  subtype_inf_time:                       0.
% 3.22/0.99  
% 3.22/0.99  ------ Problem properties
% 3.22/0.99  
% 3.22/0.99  clauses:                                42
% 3.22/0.99  conjectures:                            3
% 3.22/0.99  epr:                                    4
% 3.22/0.99  horn:                                   36
% 3.22/0.99  ground:                                 15
% 3.22/0.99  unary:                                  11
% 3.22/0.99  binary:                                 10
% 3.22/0.99  lits:                                   112
% 3.22/0.99  lits_eq:                                50
% 3.22/0.99  fd_pure:                                0
% 3.22/0.99  fd_pseudo:                              0
% 3.22/0.99  fd_cond:                                3
% 3.22/0.99  fd_pseudo_cond:                         1
% 3.22/0.99  ac_symbols:                             0
% 3.22/0.99  
% 3.22/0.99  ------ Propositional Solver
% 3.22/0.99  
% 3.22/0.99  prop_solver_calls:                      24
% 3.22/0.99  prop_fast_solver_calls:                 1196
% 3.22/0.99  smt_solver_calls:                       0
% 3.22/0.99  smt_fast_solver_calls:                  0
% 3.22/0.99  prop_num_of_clauses:                    3027
% 3.22/0.99  prop_preprocess_simplified:             9162
% 3.22/0.99  prop_fo_subsumed:                       37
% 3.22/0.99  prop_solver_time:                       0.
% 3.22/0.99  smt_solver_time:                        0.
% 3.22/0.99  smt_fast_solver_time:                   0.
% 3.22/0.99  prop_fast_solver_time:                  0.
% 3.22/0.99  prop_unsat_core_time:                   0.
% 3.22/0.99  
% 3.22/0.99  ------ QBF
% 3.22/0.99  
% 3.22/0.99  qbf_q_res:                              0
% 3.22/0.99  qbf_num_tautologies:                    0
% 3.22/0.99  qbf_prep_cycles:                        0
% 3.22/0.99  
% 3.22/0.99  ------ BMC1
% 3.22/0.99  
% 3.22/0.99  bmc1_current_bound:                     -1
% 3.22/0.99  bmc1_last_solved_bound:                 -1
% 3.22/0.99  bmc1_unsat_core_size:                   -1
% 3.22/0.99  bmc1_unsat_core_parents_size:           -1
% 3.22/0.99  bmc1_merge_next_fun:                    0
% 3.22/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.22/0.99  
% 3.22/0.99  ------ Instantiation
% 3.22/0.99  
% 3.22/0.99  inst_num_of_clauses:                    1058
% 3.22/0.99  inst_num_in_passive:                    564
% 3.22/0.99  inst_num_in_active:                     396
% 3.22/0.99  inst_num_in_unprocessed:                97
% 3.22/1.00  inst_num_of_loops:                      549
% 3.22/1.00  inst_num_of_learning_restarts:          0
% 3.22/1.00  inst_num_moves_active_passive:          150
% 3.22/1.00  inst_lit_activity:                      0
% 3.22/1.00  inst_lit_activity_moves:                0
% 3.22/1.00  inst_num_tautologies:                   0
% 3.22/1.00  inst_num_prop_implied:                  0
% 3.22/1.00  inst_num_existing_simplified:           0
% 3.22/1.00  inst_num_eq_res_simplified:             0
% 3.22/1.00  inst_num_child_elim:                    0
% 3.22/1.00  inst_num_of_dismatching_blockings:      356
% 3.22/1.00  inst_num_of_non_proper_insts:           1036
% 3.22/1.00  inst_num_of_duplicates:                 0
% 3.22/1.00  inst_inst_num_from_inst_to_res:         0
% 3.22/1.00  inst_dismatching_checking_time:         0.
% 3.22/1.00  
% 3.22/1.00  ------ Resolution
% 3.22/1.00  
% 3.22/1.00  res_num_of_clauses:                     0
% 3.22/1.00  res_num_in_passive:                     0
% 3.22/1.00  res_num_in_active:                      0
% 3.22/1.00  res_num_of_loops:                       158
% 3.22/1.00  res_forward_subset_subsumed:            27
% 3.22/1.00  res_backward_subset_subsumed:           2
% 3.22/1.00  res_forward_subsumed:                   0
% 3.22/1.00  res_backward_subsumed:                  0
% 3.22/1.00  res_forward_subsumption_resolution:     6
% 3.22/1.00  res_backward_subsumption_resolution:    0
% 3.22/1.00  res_clause_to_clause_subsumption:       271
% 3.22/1.00  res_orphan_elimination:                 0
% 3.22/1.00  res_tautology_del:                      67
% 3.22/1.00  res_num_eq_res_simplified:              0
% 3.22/1.00  res_num_sel_changes:                    0
% 3.22/1.00  res_moves_from_active_to_pass:          0
% 3.22/1.00  
% 3.22/1.00  ------ Superposition
% 3.22/1.00  
% 3.22/1.00  sup_time_total:                         0.
% 3.22/1.00  sup_time_generating:                    0.
% 3.22/1.00  sup_time_sim_full:                      0.
% 3.22/1.00  sup_time_sim_immed:                     0.
% 3.22/1.00  
% 3.22/1.00  sup_num_of_clauses:                     102
% 3.22/1.00  sup_num_in_active:                      60
% 3.22/1.00  sup_num_in_passive:                     42
% 3.22/1.00  sup_num_of_loops:                       108
% 3.22/1.00  sup_fw_superposition:                   78
% 3.22/1.00  sup_bw_superposition:                   43
% 3.22/1.00  sup_immediate_simplified:               91
% 3.22/1.00  sup_given_eliminated:                   0
% 3.22/1.00  comparisons_done:                       0
% 3.22/1.00  comparisons_avoided:                    8
% 3.22/1.00  
% 3.22/1.00  ------ Simplifications
% 3.22/1.00  
% 3.22/1.00  
% 3.22/1.00  sim_fw_subset_subsumed:                 13
% 3.22/1.00  sim_bw_subset_subsumed:                 6
% 3.22/1.00  sim_fw_subsumed:                        12
% 3.22/1.00  sim_bw_subsumed:                        4
% 3.22/1.00  sim_fw_subsumption_res:                 1
% 3.22/1.00  sim_bw_subsumption_res:                 5
% 3.22/1.00  sim_tautology_del:                      2
% 3.22/1.00  sim_eq_tautology_del:                   10
% 3.22/1.00  sim_eq_res_simp:                        6
% 3.22/1.00  sim_fw_demodulated:                     23
% 3.22/1.00  sim_bw_demodulated:                     58
% 3.22/1.00  sim_light_normalised:                   38
% 3.22/1.00  sim_joinable_taut:                      0
% 3.22/1.00  sim_joinable_simp:                      0
% 3.22/1.00  sim_ac_normalised:                      0
% 3.22/1.00  sim_smt_subsumption:                    0
% 3.22/1.00  
%------------------------------------------------------------------------------
