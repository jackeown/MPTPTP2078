%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:32 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  243 (6554 expanded)
%              Number of clauses        :  159 (2399 expanded)
%              Number of leaves         :   27 (1730 expanded)
%              Depth                    :   27
%              Number of atoms          :  816 (38783 expanded)
%              Number of equality atoms :  316 (6944 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2)
        & v2_funct_1(sK2)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2)
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_struct_0(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f54,f53,f52])).

fof(f80,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f76,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f83,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f84,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f33])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f81,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f72])).

fof(f88,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k4_relat_1(X2) = k3_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f58,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_32,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_659,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1182,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_20,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_668,plain,
    ( ~ l1_struct_0(X0_56)
    | u1_struct_0(X0_56) = k2_struct_0(X0_56) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1174,plain,
    ( u1_struct_0(X0_56) = k2_struct_0(X0_56)
    | l1_struct_0(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_668])).

cnf(c_1563,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1182,c_1174])).

cnf(c_30,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_660,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1181,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_1562,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1181,c_1174])).

cnf(c_26,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_664,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1614,plain,
    ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1562,c_664])).

cnf(c_1695,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1563,c_1614])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_663,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1178,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_675,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1167,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_675])).

cnf(c_1609,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1178,c_1167])).

cnf(c_1764,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1609,c_1562,c_1563])).

cnf(c_1766,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1695,c_1764])).

cnf(c_1768,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1766,c_1764])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_667,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1175,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54)
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_2468,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1768,c_1175])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_36,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_39,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_662,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1179,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_1613,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1562,c_1179])).

cnf(c_1729,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1613,c_1563])).

cnf(c_1770,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1766,c_1729])).

cnf(c_1612,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1562,c_1178])).

cnf(c_1840,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1612,c_1563,c_1766])).

cnf(c_6538,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2468,c_36,c_39,c_1770,c_1840])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_21,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_358,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_359,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_48,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_361,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_31,c_30,c_48])).

cnf(c_371,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_361])).

cnf(c_372,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_14,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_433,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_372,c_14])).

cnf(c_4,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_449,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_433,c_4])).

cnf(c_658,plain,
    ( ~ v1_funct_2(X0_54,X0_55,k2_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | k1_relat_1(X0_54) = X0_55 ),
    inference(subtyping,[status(esa)],[c_449])).

cnf(c_1183,plain,
    ( k1_relat_1(X0_54) = X0_55
    | v1_funct_2(X0_54,X0_55,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_658])).

cnf(c_3659,plain,
    ( k1_relat_1(X0_54) = X0_55
    | v1_funct_2(X0_54,X0_55,k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1183,c_1766])).

cnf(c_3669,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1840,c_3659])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_681,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ v1_relat_1(X1_54)
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1161,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
    | v1_relat_1(X1_54) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_681])).

cnf(c_1507,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1178,c_1161])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_680,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1573,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_680])).

cnf(c_1574,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1573])).

cnf(c_4059,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3669,c_36,c_1507,c_1574,c_1770])).

cnf(c_6540,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_6538,c_4059])).

cnf(c_15,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_24,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_468,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_469,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_657,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_469])).

cnf(c_1184,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_657])).

cnf(c_1611,plain,
    ( k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1562,c_1184])).

cnf(c_2192,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1611,c_1563,c_1766])).

cnf(c_4077,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4059,c_2192])).

cnf(c_6542,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6540,c_4077])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X2,X1,k3_relset_1(X1,X2,X0)) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_673,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k2_relset_1(X1_55,X0_55,k3_relset_1(X0_55,X1_55,X0_54)) = k1_relset_1(X0_55,X1_55,X0_54) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1169,plain,
    ( k2_relset_1(X0_55,X1_55,k3_relset_1(X1_55,X0_55,X0_54)) = k1_relset_1(X1_55,X0_55,X0_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_673])).

cnf(c_2047,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(superposition,[status(thm)],[c_1840,c_1169])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_676,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k1_relset_1(X0_55,X1_55,X0_54) = k1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1166,plain,
    ( k1_relset_1(X0_55,X1_55,X0_54) = k1_relat_1(X0_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_1571,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1178,c_1166])).

cnf(c_1732,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1571,c_1562,c_1563])).

cnf(c_1769,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1766,c_1732])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_674,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k3_relset_1(X0_55,X1_55,X0_54) = k4_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1168,plain,
    ( k3_relset_1(X0_55,X1_55,X0_54) = k4_relat_1(X0_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_1929,plain,
    ( k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1840,c_1168])).

cnf(c_661,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1180,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_661])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k4_relat_1(X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_679,plain,
    ( ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | k4_relat_1(X0_54) = k2_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1163,plain,
    ( k4_relat_1(X0_54) = k2_funct_1(X0_54)
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_679])).

cnf(c_1856,plain,
    ( k4_relat_1(sK2) = k2_funct_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1180,c_1163])).

cnf(c_719,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_679])).

cnf(c_1508,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1507])).

cnf(c_2140,plain,
    ( k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1856,c_29,c_25,c_719,c_1508,c_1573])).

cnf(c_2263,plain,
    ( k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1929,c_2140])).

cnf(c_2617,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2047,c_1769,c_2263])).

cnf(c_4072,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4059,c_2617])).

cnf(c_5703,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4072,c_1175])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_678,plain,
    ( ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | k2_funct_1(k2_funct_1(X0_54)) = X0_54 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1164,plain,
    ( k2_funct_1(k2_funct_1(X0_54)) = X0_54
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_2353,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1180,c_1164])).

cnf(c_722,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_2535,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2353,c_29,c_25,c_722,c_1508,c_1573])).

cnf(c_5723,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5703,c_2535])).

cnf(c_692,plain,
    ( X0_54 != X1_54
    | k2_funct_1(X0_54) = k2_funct_1(X1_54) ),
    theory(equality)).

cnf(c_703,plain,
    ( k2_funct_1(sK2) = k2_funct_1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_683,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_711,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_683])).

cnf(c_752,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_668])).

cnf(c_1464,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_666,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ l1_struct_0(X1_56)
    | ~ l1_struct_0(X0_56)
    | ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_54))
    | k2_relset_1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_54) != k2_struct_0(X1_56) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1474,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_687,plain,
    ( X0_55 != X1_55
    | X2_55 != X1_55
    | X2_55 = X0_55 ),
    theory(equality)).

cnf(c_1500,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_55
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0_55 ),
    inference(instantiation,[status(thm)],[c_687])).

cnf(c_1634,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1500])).

cnf(c_2620,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2617,c_1175])).

cnf(c_2643,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2620,c_2535])).

cnf(c_37,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_669,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k2_funct_1(X0_54))
    | ~ v2_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1455,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_1456,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1455])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_677,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | m1_subset_1(k3_relset_1(X0_55,X1_55,X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1165,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(k3_relset_1(X0_55,X1_55,X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_677])).

cnf(c_2265,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2263,c_1165])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_670,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1172,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_670])).

cnf(c_2459,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1768,c_1172])).

cnf(c_2659,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2643,c_30,c_36,c_37,c_38,c_39,c_752,c_664,c_1456,c_1634,c_1770,c_1840,c_2265,c_2459])).

cnf(c_2660,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2659])).

cnf(c_4071,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4059,c_2660])).

cnf(c_4102,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4071])).

cnf(c_4199,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4102])).

cnf(c_686,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_2475,plain,
    ( X0_54 != X1_54
    | k2_funct_1(sK2) != X1_54
    | k2_funct_1(sK2) = X0_54 ),
    inference(instantiation,[status(thm)],[c_686])).

cnf(c_3704,plain,
    ( X0_54 != k2_funct_1(sK2)
    | k2_funct_1(sK2) = X0_54
    | k2_funct_1(sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2475])).

cnf(c_5353,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_funct_1(sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3704])).

cnf(c_693,plain,
    ( ~ v2_funct_1(X0_54)
    | v2_funct_1(X1_54)
    | X1_54 != X0_54 ),
    theory(equality)).

cnf(c_2034,plain,
    ( ~ v2_funct_1(X0_54)
    | v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != X0_54 ),
    inference(instantiation,[status(thm)],[c_693])).

cnf(c_5682,plain,
    ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_2034])).

cnf(c_5747,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5723,c_32,c_30,c_29,c_28,c_27,c_25,c_703,c_711,c_752,c_664,c_1464,c_1474,c_1634,c_4199,c_5353,c_5682])).

cnf(c_6543,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6542,c_5747])).

cnf(c_6544,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6543])).

cnf(c_4078,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4059,c_1840])).

cnf(c_4076,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4059,c_1770])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6544,c_4078,c_4076,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:48:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.13/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/0.99  
% 3.13/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.13/0.99  
% 3.13/0.99  ------  iProver source info
% 3.13/0.99  
% 3.13/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.13/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.13/0.99  git: non_committed_changes: false
% 3.13/0.99  git: last_make_outside_of_git: false
% 3.13/0.99  
% 3.13/0.99  ------ 
% 3.13/0.99  
% 3.13/0.99  ------ Input Options
% 3.13/0.99  
% 3.13/0.99  --out_options                           all
% 3.13/0.99  --tptp_safe_out                         true
% 3.13/0.99  --problem_path                          ""
% 3.13/0.99  --include_path                          ""
% 3.13/0.99  --clausifier                            res/vclausify_rel
% 3.13/0.99  --clausifier_options                    --mode clausify
% 3.13/0.99  --stdin                                 false
% 3.13/0.99  --stats_out                             all
% 3.13/0.99  
% 3.13/0.99  ------ General Options
% 3.13/0.99  
% 3.13/0.99  --fof                                   false
% 3.13/0.99  --time_out_real                         305.
% 3.13/0.99  --time_out_virtual                      -1.
% 3.13/0.99  --symbol_type_check                     false
% 3.13/0.99  --clausify_out                          false
% 3.13/0.99  --sig_cnt_out                           false
% 3.13/0.99  --trig_cnt_out                          false
% 3.13/0.99  --trig_cnt_out_tolerance                1.
% 3.13/0.99  --trig_cnt_out_sk_spl                   false
% 3.13/0.99  --abstr_cl_out                          false
% 3.13/0.99  
% 3.13/0.99  ------ Global Options
% 3.13/0.99  
% 3.13/0.99  --schedule                              default
% 3.13/0.99  --add_important_lit                     false
% 3.13/0.99  --prop_solver_per_cl                    1000
% 3.13/0.99  --min_unsat_core                        false
% 3.13/0.99  --soft_assumptions                      false
% 3.13/0.99  --soft_lemma_size                       3
% 3.13/0.99  --prop_impl_unit_size                   0
% 3.13/0.99  --prop_impl_unit                        []
% 3.13/0.99  --share_sel_clauses                     true
% 3.13/0.99  --reset_solvers                         false
% 3.13/0.99  --bc_imp_inh                            [conj_cone]
% 3.13/0.99  --conj_cone_tolerance                   3.
% 3.13/0.99  --extra_neg_conj                        none
% 3.13/0.99  --large_theory_mode                     true
% 3.13/0.99  --prolific_symb_bound                   200
% 3.13/0.99  --lt_threshold                          2000
% 3.13/0.99  --clause_weak_htbl                      true
% 3.13/0.99  --gc_record_bc_elim                     false
% 3.13/0.99  
% 3.13/0.99  ------ Preprocessing Options
% 3.13/0.99  
% 3.13/0.99  --preprocessing_flag                    true
% 3.13/0.99  --time_out_prep_mult                    0.1
% 3.13/0.99  --splitting_mode                        input
% 3.13/0.99  --splitting_grd                         true
% 3.13/0.99  --splitting_cvd                         false
% 3.13/0.99  --splitting_cvd_svl                     false
% 3.13/0.99  --splitting_nvd                         32
% 3.13/0.99  --sub_typing                            true
% 3.13/0.99  --prep_gs_sim                           true
% 3.13/0.99  --prep_unflatten                        true
% 3.13/0.99  --prep_res_sim                          true
% 3.13/0.99  --prep_upred                            true
% 3.13/0.99  --prep_sem_filter                       exhaustive
% 3.13/0.99  --prep_sem_filter_out                   false
% 3.13/0.99  --pred_elim                             true
% 3.13/0.99  --res_sim_input                         true
% 3.13/0.99  --eq_ax_congr_red                       true
% 3.13/0.99  --pure_diseq_elim                       true
% 3.13/0.99  --brand_transform                       false
% 3.13/0.99  --non_eq_to_eq                          false
% 3.13/0.99  --prep_def_merge                        true
% 3.13/0.99  --prep_def_merge_prop_impl              false
% 3.13/0.99  --prep_def_merge_mbd                    true
% 3.13/0.99  --prep_def_merge_tr_red                 false
% 3.13/0.99  --prep_def_merge_tr_cl                  false
% 3.13/0.99  --smt_preprocessing                     true
% 3.13/0.99  --smt_ac_axioms                         fast
% 3.13/0.99  --preprocessed_out                      false
% 3.13/0.99  --preprocessed_stats                    false
% 3.13/0.99  
% 3.13/0.99  ------ Abstraction refinement Options
% 3.13/0.99  
% 3.13/0.99  --abstr_ref                             []
% 3.13/0.99  --abstr_ref_prep                        false
% 3.13/0.99  --abstr_ref_until_sat                   false
% 3.13/0.99  --abstr_ref_sig_restrict                funpre
% 3.13/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.13/0.99  --abstr_ref_under                       []
% 3.13/0.99  
% 3.13/0.99  ------ SAT Options
% 3.13/0.99  
% 3.13/0.99  --sat_mode                              false
% 3.13/0.99  --sat_fm_restart_options                ""
% 3.13/0.99  --sat_gr_def                            false
% 3.13/0.99  --sat_epr_types                         true
% 3.13/0.99  --sat_non_cyclic_types                  false
% 3.13/0.99  --sat_finite_models                     false
% 3.13/0.99  --sat_fm_lemmas                         false
% 3.13/0.99  --sat_fm_prep                           false
% 3.13/0.99  --sat_fm_uc_incr                        true
% 3.13/0.99  --sat_out_model                         small
% 3.13/0.99  --sat_out_clauses                       false
% 3.13/0.99  
% 3.13/0.99  ------ QBF Options
% 3.13/0.99  
% 3.13/0.99  --qbf_mode                              false
% 3.13/0.99  --qbf_elim_univ                         false
% 3.13/0.99  --qbf_dom_inst                          none
% 3.13/0.99  --qbf_dom_pre_inst                      false
% 3.13/0.99  --qbf_sk_in                             false
% 3.13/0.99  --qbf_pred_elim                         true
% 3.13/0.99  --qbf_split                             512
% 3.13/0.99  
% 3.13/0.99  ------ BMC1 Options
% 3.13/0.99  
% 3.13/0.99  --bmc1_incremental                      false
% 3.13/0.99  --bmc1_axioms                           reachable_all
% 3.13/0.99  --bmc1_min_bound                        0
% 3.13/0.99  --bmc1_max_bound                        -1
% 3.13/0.99  --bmc1_max_bound_default                -1
% 3.13/0.99  --bmc1_symbol_reachability              true
% 3.13/0.99  --bmc1_property_lemmas                  false
% 3.13/0.99  --bmc1_k_induction                      false
% 3.13/0.99  --bmc1_non_equiv_states                 false
% 3.13/0.99  --bmc1_deadlock                         false
% 3.13/0.99  --bmc1_ucm                              false
% 3.13/0.99  --bmc1_add_unsat_core                   none
% 3.13/0.99  --bmc1_unsat_core_children              false
% 3.13/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.13/0.99  --bmc1_out_stat                         full
% 3.13/0.99  --bmc1_ground_init                      false
% 3.13/0.99  --bmc1_pre_inst_next_state              false
% 3.13/0.99  --bmc1_pre_inst_state                   false
% 3.13/0.99  --bmc1_pre_inst_reach_state             false
% 3.13/0.99  --bmc1_out_unsat_core                   false
% 3.13/0.99  --bmc1_aig_witness_out                  false
% 3.13/0.99  --bmc1_verbose                          false
% 3.13/0.99  --bmc1_dump_clauses_tptp                false
% 3.13/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.13/0.99  --bmc1_dump_file                        -
% 3.13/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.13/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.13/0.99  --bmc1_ucm_extend_mode                  1
% 3.13/0.99  --bmc1_ucm_init_mode                    2
% 3.13/0.99  --bmc1_ucm_cone_mode                    none
% 3.13/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.13/0.99  --bmc1_ucm_relax_model                  4
% 3.13/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.13/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.13/0.99  --bmc1_ucm_layered_model                none
% 3.13/0.99  --bmc1_ucm_max_lemma_size               10
% 3.13/0.99  
% 3.13/0.99  ------ AIG Options
% 3.13/0.99  
% 3.13/0.99  --aig_mode                              false
% 3.13/0.99  
% 3.13/0.99  ------ Instantiation Options
% 3.13/0.99  
% 3.13/0.99  --instantiation_flag                    true
% 3.13/0.99  --inst_sos_flag                         false
% 3.13/0.99  --inst_sos_phase                        true
% 3.13/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.13/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.13/0.99  --inst_lit_sel_side                     num_symb
% 3.13/0.99  --inst_solver_per_active                1400
% 3.13/0.99  --inst_solver_calls_frac                1.
% 3.13/0.99  --inst_passive_queue_type               priority_queues
% 3.13/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.13/0.99  --inst_passive_queues_freq              [25;2]
% 3.13/0.99  --inst_dismatching                      true
% 3.13/0.99  --inst_eager_unprocessed_to_passive     true
% 3.13/0.99  --inst_prop_sim_given                   true
% 3.13/0.99  --inst_prop_sim_new                     false
% 3.13/0.99  --inst_subs_new                         false
% 3.13/0.99  --inst_eq_res_simp                      false
% 3.13/0.99  --inst_subs_given                       false
% 3.13/0.99  --inst_orphan_elimination               true
% 3.13/0.99  --inst_learning_loop_flag               true
% 3.13/0.99  --inst_learning_start                   3000
% 3.13/0.99  --inst_learning_factor                  2
% 3.13/0.99  --inst_start_prop_sim_after_learn       3
% 3.13/0.99  --inst_sel_renew                        solver
% 3.13/0.99  --inst_lit_activity_flag                true
% 3.13/0.99  --inst_restr_to_given                   false
% 3.13/0.99  --inst_activity_threshold               500
% 3.13/0.99  --inst_out_proof                        true
% 3.13/0.99  
% 3.13/0.99  ------ Resolution Options
% 3.13/0.99  
% 3.13/0.99  --resolution_flag                       true
% 3.13/0.99  --res_lit_sel                           adaptive
% 3.13/0.99  --res_lit_sel_side                      none
% 3.13/0.99  --res_ordering                          kbo
% 3.13/0.99  --res_to_prop_solver                    active
% 3.13/0.99  --res_prop_simpl_new                    false
% 3.13/0.99  --res_prop_simpl_given                  true
% 3.13/0.99  --res_passive_queue_type                priority_queues
% 3.13/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.13/0.99  --res_passive_queues_freq               [15;5]
% 3.13/0.99  --res_forward_subs                      full
% 3.13/0.99  --res_backward_subs                     full
% 3.13/0.99  --res_forward_subs_resolution           true
% 3.13/0.99  --res_backward_subs_resolution          true
% 3.13/0.99  --res_orphan_elimination                true
% 3.13/0.99  --res_time_limit                        2.
% 3.13/0.99  --res_out_proof                         true
% 3.13/0.99  
% 3.13/0.99  ------ Superposition Options
% 3.13/0.99  
% 3.13/0.99  --superposition_flag                    true
% 3.13/0.99  --sup_passive_queue_type                priority_queues
% 3.13/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.13/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.13/0.99  --demod_completeness_check              fast
% 3.13/0.99  --demod_use_ground                      true
% 3.13/0.99  --sup_to_prop_solver                    passive
% 3.13/0.99  --sup_prop_simpl_new                    true
% 3.13/0.99  --sup_prop_simpl_given                  true
% 3.13/0.99  --sup_fun_splitting                     false
% 3.13/0.99  --sup_smt_interval                      50000
% 3.13/0.99  
% 3.13/0.99  ------ Superposition Simplification Setup
% 3.13/0.99  
% 3.13/0.99  --sup_indices_passive                   []
% 3.13/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.13/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/0.99  --sup_full_bw                           [BwDemod]
% 3.13/0.99  --sup_immed_triv                        [TrivRules]
% 3.13/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.13/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/0.99  --sup_immed_bw_main                     []
% 3.13/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.13/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/0.99  
% 3.13/0.99  ------ Combination Options
% 3.13/0.99  
% 3.13/0.99  --comb_res_mult                         3
% 3.13/0.99  --comb_sup_mult                         2
% 3.13/0.99  --comb_inst_mult                        10
% 3.13/0.99  
% 3.13/0.99  ------ Debug Options
% 3.13/0.99  
% 3.13/0.99  --dbg_backtrace                         false
% 3.13/0.99  --dbg_dump_prop_clauses                 false
% 3.13/0.99  --dbg_dump_prop_clauses_file            -
% 3.13/0.99  --dbg_out_stat                          false
% 3.13/0.99  ------ Parsing...
% 3.13/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.13/0.99  
% 3.13/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.13/0.99  
% 3.13/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.13/0.99  
% 3.13/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.13/0.99  ------ Proving...
% 3.13/0.99  ------ Problem Properties 
% 3.13/0.99  
% 3.13/0.99  
% 3.13/0.99  clauses                                 25
% 3.13/0.99  conjectures                             7
% 3.13/0.99  EPR                                     4
% 3.13/0.99  Horn                                    25
% 3.13/0.99  unary                                   8
% 3.13/0.99  binary                                  7
% 3.13/0.99  lits                                    74
% 3.13/0.99  lits eq                                 17
% 3.13/0.99  fd_pure                                 0
% 3.13/0.99  fd_pseudo                               0
% 3.13/0.99  fd_cond                                 0
% 3.13/0.99  fd_pseudo_cond                          1
% 3.13/0.99  AC symbols                              0
% 3.13/0.99  
% 3.13/0.99  ------ Schedule dynamic 5 is on 
% 3.13/0.99  
% 3.13/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.13/0.99  
% 3.13/0.99  
% 3.13/0.99  ------ 
% 3.13/0.99  Current options:
% 3.13/0.99  ------ 
% 3.13/0.99  
% 3.13/0.99  ------ Input Options
% 3.13/0.99  
% 3.13/0.99  --out_options                           all
% 3.13/0.99  --tptp_safe_out                         true
% 3.13/0.99  --problem_path                          ""
% 3.13/0.99  --include_path                          ""
% 3.13/0.99  --clausifier                            res/vclausify_rel
% 3.13/0.99  --clausifier_options                    --mode clausify
% 3.13/0.99  --stdin                                 false
% 3.13/0.99  --stats_out                             all
% 3.13/0.99  
% 3.13/0.99  ------ General Options
% 3.13/0.99  
% 3.13/0.99  --fof                                   false
% 3.13/0.99  --time_out_real                         305.
% 3.13/0.99  --time_out_virtual                      -1.
% 3.13/0.99  --symbol_type_check                     false
% 3.13/0.99  --clausify_out                          false
% 3.13/0.99  --sig_cnt_out                           false
% 3.13/0.99  --trig_cnt_out                          false
% 3.13/0.99  --trig_cnt_out_tolerance                1.
% 3.13/0.99  --trig_cnt_out_sk_spl                   false
% 3.13/0.99  --abstr_cl_out                          false
% 3.13/0.99  
% 3.13/0.99  ------ Global Options
% 3.13/0.99  
% 3.13/0.99  --schedule                              default
% 3.13/0.99  --add_important_lit                     false
% 3.13/0.99  --prop_solver_per_cl                    1000
% 3.13/0.99  --min_unsat_core                        false
% 3.13/0.99  --soft_assumptions                      false
% 3.13/0.99  --soft_lemma_size                       3
% 3.13/0.99  --prop_impl_unit_size                   0
% 3.13/0.99  --prop_impl_unit                        []
% 3.13/0.99  --share_sel_clauses                     true
% 3.13/0.99  --reset_solvers                         false
% 3.13/0.99  --bc_imp_inh                            [conj_cone]
% 3.13/0.99  --conj_cone_tolerance                   3.
% 3.13/0.99  --extra_neg_conj                        none
% 3.13/0.99  --large_theory_mode                     true
% 3.13/0.99  --prolific_symb_bound                   200
% 3.13/0.99  --lt_threshold                          2000
% 3.13/0.99  --clause_weak_htbl                      true
% 3.13/0.99  --gc_record_bc_elim                     false
% 3.13/0.99  
% 3.13/0.99  ------ Preprocessing Options
% 3.13/0.99  
% 3.13/0.99  --preprocessing_flag                    true
% 3.13/0.99  --time_out_prep_mult                    0.1
% 3.13/0.99  --splitting_mode                        input
% 3.13/0.99  --splitting_grd                         true
% 3.13/0.99  --splitting_cvd                         false
% 3.13/0.99  --splitting_cvd_svl                     false
% 3.13/0.99  --splitting_nvd                         32
% 3.13/0.99  --sub_typing                            true
% 3.13/0.99  --prep_gs_sim                           true
% 3.13/0.99  --prep_unflatten                        true
% 3.13/0.99  --prep_res_sim                          true
% 3.13/0.99  --prep_upred                            true
% 3.13/0.99  --prep_sem_filter                       exhaustive
% 3.13/0.99  --prep_sem_filter_out                   false
% 3.13/0.99  --pred_elim                             true
% 3.13/0.99  --res_sim_input                         true
% 3.13/0.99  --eq_ax_congr_red                       true
% 3.13/0.99  --pure_diseq_elim                       true
% 3.13/0.99  --brand_transform                       false
% 3.13/0.99  --non_eq_to_eq                          false
% 3.13/0.99  --prep_def_merge                        true
% 3.13/0.99  --prep_def_merge_prop_impl              false
% 3.13/0.99  --prep_def_merge_mbd                    true
% 3.13/0.99  --prep_def_merge_tr_red                 false
% 3.13/0.99  --prep_def_merge_tr_cl                  false
% 3.13/0.99  --smt_preprocessing                     true
% 3.13/0.99  --smt_ac_axioms                         fast
% 3.13/0.99  --preprocessed_out                      false
% 3.13/0.99  --preprocessed_stats                    false
% 3.13/0.99  
% 3.13/0.99  ------ Abstraction refinement Options
% 3.13/0.99  
% 3.13/0.99  --abstr_ref                             []
% 3.13/0.99  --abstr_ref_prep                        false
% 3.13/0.99  --abstr_ref_until_sat                   false
% 3.13/0.99  --abstr_ref_sig_restrict                funpre
% 3.13/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.13/0.99  --abstr_ref_under                       []
% 3.13/0.99  
% 3.13/0.99  ------ SAT Options
% 3.13/0.99  
% 3.13/0.99  --sat_mode                              false
% 3.13/0.99  --sat_fm_restart_options                ""
% 3.13/0.99  --sat_gr_def                            false
% 3.13/0.99  --sat_epr_types                         true
% 3.13/0.99  --sat_non_cyclic_types                  false
% 3.13/0.99  --sat_finite_models                     false
% 3.13/0.99  --sat_fm_lemmas                         false
% 3.13/0.99  --sat_fm_prep                           false
% 3.13/0.99  --sat_fm_uc_incr                        true
% 3.13/0.99  --sat_out_model                         small
% 3.13/0.99  --sat_out_clauses                       false
% 3.13/0.99  
% 3.13/0.99  ------ QBF Options
% 3.13/0.99  
% 3.13/0.99  --qbf_mode                              false
% 3.13/0.99  --qbf_elim_univ                         false
% 3.13/0.99  --qbf_dom_inst                          none
% 3.13/0.99  --qbf_dom_pre_inst                      false
% 3.13/0.99  --qbf_sk_in                             false
% 3.13/0.99  --qbf_pred_elim                         true
% 3.13/0.99  --qbf_split                             512
% 3.13/0.99  
% 3.13/0.99  ------ BMC1 Options
% 3.13/0.99  
% 3.13/0.99  --bmc1_incremental                      false
% 3.13/0.99  --bmc1_axioms                           reachable_all
% 3.13/0.99  --bmc1_min_bound                        0
% 3.13/0.99  --bmc1_max_bound                        -1
% 3.13/0.99  --bmc1_max_bound_default                -1
% 3.13/0.99  --bmc1_symbol_reachability              true
% 3.13/0.99  --bmc1_property_lemmas                  false
% 3.13/0.99  --bmc1_k_induction                      false
% 3.13/0.99  --bmc1_non_equiv_states                 false
% 3.13/0.99  --bmc1_deadlock                         false
% 3.13/0.99  --bmc1_ucm                              false
% 3.13/0.99  --bmc1_add_unsat_core                   none
% 3.13/0.99  --bmc1_unsat_core_children              false
% 3.13/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.13/0.99  --bmc1_out_stat                         full
% 3.13/0.99  --bmc1_ground_init                      false
% 3.13/0.99  --bmc1_pre_inst_next_state              false
% 3.13/0.99  --bmc1_pre_inst_state                   false
% 3.13/0.99  --bmc1_pre_inst_reach_state             false
% 3.13/0.99  --bmc1_out_unsat_core                   false
% 3.13/0.99  --bmc1_aig_witness_out                  false
% 3.13/0.99  --bmc1_verbose                          false
% 3.13/0.99  --bmc1_dump_clauses_tptp                false
% 3.13/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.13/0.99  --bmc1_dump_file                        -
% 3.13/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.13/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.13/0.99  --bmc1_ucm_extend_mode                  1
% 3.13/0.99  --bmc1_ucm_init_mode                    2
% 3.13/0.99  --bmc1_ucm_cone_mode                    none
% 3.13/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.13/0.99  --bmc1_ucm_relax_model                  4
% 3.13/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.13/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.13/0.99  --bmc1_ucm_layered_model                none
% 3.13/0.99  --bmc1_ucm_max_lemma_size               10
% 3.13/0.99  
% 3.13/0.99  ------ AIG Options
% 3.13/0.99  
% 3.13/0.99  --aig_mode                              false
% 3.13/0.99  
% 3.13/0.99  ------ Instantiation Options
% 3.13/0.99  
% 3.13/0.99  --instantiation_flag                    true
% 3.13/0.99  --inst_sos_flag                         false
% 3.13/0.99  --inst_sos_phase                        true
% 3.13/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.13/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.13/0.99  --inst_lit_sel_side                     none
% 3.13/0.99  --inst_solver_per_active                1400
% 3.13/0.99  --inst_solver_calls_frac                1.
% 3.13/0.99  --inst_passive_queue_type               priority_queues
% 3.13/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.13/0.99  --inst_passive_queues_freq              [25;2]
% 3.13/0.99  --inst_dismatching                      true
% 3.13/0.99  --inst_eager_unprocessed_to_passive     true
% 3.13/0.99  --inst_prop_sim_given                   true
% 3.13/0.99  --inst_prop_sim_new                     false
% 3.13/0.99  --inst_subs_new                         false
% 3.13/0.99  --inst_eq_res_simp                      false
% 3.13/0.99  --inst_subs_given                       false
% 3.13/0.99  --inst_orphan_elimination               true
% 3.13/0.99  --inst_learning_loop_flag               true
% 3.13/0.99  --inst_learning_start                   3000
% 3.13/0.99  --inst_learning_factor                  2
% 3.13/0.99  --inst_start_prop_sim_after_learn       3
% 3.13/0.99  --inst_sel_renew                        solver
% 3.13/0.99  --inst_lit_activity_flag                true
% 3.13/0.99  --inst_restr_to_given                   false
% 3.13/0.99  --inst_activity_threshold               500
% 3.13/0.99  --inst_out_proof                        true
% 3.13/0.99  
% 3.13/0.99  ------ Resolution Options
% 3.13/0.99  
% 3.13/0.99  --resolution_flag                       false
% 3.13/0.99  --res_lit_sel                           adaptive
% 3.13/0.99  --res_lit_sel_side                      none
% 3.13/0.99  --res_ordering                          kbo
% 3.13/0.99  --res_to_prop_solver                    active
% 3.13/0.99  --res_prop_simpl_new                    false
% 3.13/0.99  --res_prop_simpl_given                  true
% 3.13/0.99  --res_passive_queue_type                priority_queues
% 3.13/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.13/0.99  --res_passive_queues_freq               [15;5]
% 3.13/0.99  --res_forward_subs                      full
% 3.13/0.99  --res_backward_subs                     full
% 3.13/0.99  --res_forward_subs_resolution           true
% 3.13/0.99  --res_backward_subs_resolution          true
% 3.13/0.99  --res_orphan_elimination                true
% 3.13/0.99  --res_time_limit                        2.
% 3.13/0.99  --res_out_proof                         true
% 3.13/0.99  
% 3.13/0.99  ------ Superposition Options
% 3.13/0.99  
% 3.13/0.99  --superposition_flag                    true
% 3.13/0.99  --sup_passive_queue_type                priority_queues
% 3.13/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.13/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.13/0.99  --demod_completeness_check              fast
% 3.13/0.99  --demod_use_ground                      true
% 3.13/0.99  --sup_to_prop_solver                    passive
% 3.13/0.99  --sup_prop_simpl_new                    true
% 3.13/0.99  --sup_prop_simpl_given                  true
% 3.13/0.99  --sup_fun_splitting                     false
% 3.13/0.99  --sup_smt_interval                      50000
% 3.13/0.99  
% 3.13/0.99  ------ Superposition Simplification Setup
% 3.13/0.99  
% 3.13/0.99  --sup_indices_passive                   []
% 3.13/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.13/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/0.99  --sup_full_bw                           [BwDemod]
% 3.13/0.99  --sup_immed_triv                        [TrivRules]
% 3.13/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.13/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/0.99  --sup_immed_bw_main                     []
% 3.13/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.13/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/0.99  
% 3.13/0.99  ------ Combination Options
% 3.13/0.99  
% 3.13/0.99  --comb_res_mult                         3
% 3.13/0.99  --comb_sup_mult                         2
% 3.13/0.99  --comb_inst_mult                        10
% 3.13/0.99  
% 3.13/0.99  ------ Debug Options
% 3.13/0.99  
% 3.13/0.99  --dbg_backtrace                         false
% 3.13/0.99  --dbg_dump_prop_clauses                 false
% 3.13/0.99  --dbg_dump_prop_clauses_file            -
% 3.13/0.99  --dbg_out_stat                          false
% 3.13/0.99  
% 3.13/0.99  
% 3.13/0.99  
% 3.13/0.99  
% 3.13/0.99  ------ Proving...
% 3.13/0.99  
% 3.13/0.99  
% 3.13/0.99  % SZS status Theorem for theBenchmark.p
% 3.13/0.99  
% 3.13/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.13/0.99  
% 3.13/0.99  fof(f19,conjecture,(
% 3.13/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f20,negated_conjecture,(
% 3.13/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.13/1.00    inference(negated_conjecture,[],[f19])).
% 3.13/1.00  
% 3.13/1.00  fof(f48,plain,(
% 3.13/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.13/1.00    inference(ennf_transformation,[],[f20])).
% 3.13/1.00  
% 3.13/1.00  fof(f49,plain,(
% 3.13/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.13/1.00    inference(flattening,[],[f48])).
% 3.13/1.00  
% 3.13/1.00  fof(f54,plain,(
% 3.13/1.00    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.13/1.00    introduced(choice_axiom,[])).
% 3.13/1.00  
% 3.13/1.00  fof(f53,plain,(
% 3.13/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 3.13/1.00    introduced(choice_axiom,[])).
% 3.13/1.00  
% 3.13/1.00  fof(f52,plain,(
% 3.13/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 3.13/1.00    introduced(choice_axiom,[])).
% 3.13/1.00  
% 3.13/1.00  fof(f55,plain,(
% 3.13/1.00    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 3.13/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f54,f53,f52])).
% 3.13/1.00  
% 3.13/1.00  fof(f80,plain,(
% 3.13/1.00    l1_struct_0(sK0)),
% 3.13/1.00    inference(cnf_transformation,[],[f55])).
% 3.13/1.00  
% 3.13/1.00  fof(f15,axiom,(
% 3.13/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f41,plain,(
% 3.13/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.13/1.00    inference(ennf_transformation,[],[f15])).
% 3.13/1.00  
% 3.13/1.00  fof(f76,plain,(
% 3.13/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f41])).
% 3.13/1.00  
% 3.13/1.00  fof(f82,plain,(
% 3.13/1.00    l1_struct_0(sK1)),
% 3.13/1.00    inference(cnf_transformation,[],[f55])).
% 3.13/1.00  
% 3.13/1.00  fof(f86,plain,(
% 3.13/1.00    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 3.13/1.00    inference(cnf_transformation,[],[f55])).
% 3.13/1.00  
% 3.13/1.00  fof(f85,plain,(
% 3.13/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.13/1.00    inference(cnf_transformation,[],[f55])).
% 3.13/1.00  
% 3.13/1.00  fof(f8,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f30,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.00    inference(ennf_transformation,[],[f8])).
% 3.13/1.00  
% 3.13/1.00  fof(f63,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f30])).
% 3.13/1.00  
% 3.13/1.00  fof(f17,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f44,plain,(
% 3.13/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.13/1.00    inference(ennf_transformation,[],[f17])).
% 3.13/1.00  
% 3.13/1.00  fof(f45,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.13/1.00    inference(flattening,[],[f44])).
% 3.13/1.00  
% 3.13/1.00  fof(f78,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f45])).
% 3.13/1.00  
% 3.13/1.00  fof(f83,plain,(
% 3.13/1.00    v1_funct_1(sK2)),
% 3.13/1.00    inference(cnf_transformation,[],[f55])).
% 3.13/1.00  
% 3.13/1.00  fof(f87,plain,(
% 3.13/1.00    v2_funct_1(sK2)),
% 3.13/1.00    inference(cnf_transformation,[],[f55])).
% 3.13/1.00  
% 3.13/1.00  fof(f84,plain,(
% 3.13/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.13/1.00    inference(cnf_transformation,[],[f55])).
% 3.13/1.00  
% 3.13/1.00  fof(f11,axiom,(
% 3.13/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f33,plain,(
% 3.13/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.13/1.00    inference(ennf_transformation,[],[f11])).
% 3.13/1.00  
% 3.13/1.00  fof(f34,plain,(
% 3.13/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.13/1.00    inference(flattening,[],[f33])).
% 3.13/1.00  
% 3.13/1.00  fof(f68,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f34])).
% 3.13/1.00  
% 3.13/1.00  fof(f16,axiom,(
% 3.13/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f42,plain,(
% 3.13/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.13/1.00    inference(ennf_transformation,[],[f16])).
% 3.13/1.00  
% 3.13/1.00  fof(f43,plain,(
% 3.13/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.13/1.00    inference(flattening,[],[f42])).
% 3.13/1.00  
% 3.13/1.00  fof(f77,plain,(
% 3.13/1.00    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f43])).
% 3.13/1.00  
% 3.13/1.00  fof(f81,plain,(
% 3.13/1.00    ~v2_struct_0(sK1)),
% 3.13/1.00    inference(cnf_transformation,[],[f55])).
% 3.13/1.00  
% 3.13/1.00  fof(f12,axiom,(
% 3.13/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f35,plain,(
% 3.13/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.13/1.00    inference(ennf_transformation,[],[f12])).
% 3.13/1.00  
% 3.13/1.00  fof(f36,plain,(
% 3.13/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.13/1.00    inference(flattening,[],[f35])).
% 3.13/1.00  
% 3.13/1.00  fof(f50,plain,(
% 3.13/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.13/1.00    inference(nnf_transformation,[],[f36])).
% 3.13/1.00  
% 3.13/1.00  fof(f69,plain,(
% 3.13/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f50])).
% 3.13/1.00  
% 3.13/1.00  fof(f5,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f21,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.13/1.00    inference(pure_predicate_removal,[],[f5])).
% 3.13/1.00  
% 3.13/1.00  fof(f27,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.00    inference(ennf_transformation,[],[f21])).
% 3.13/1.00  
% 3.13/1.00  fof(f60,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f27])).
% 3.13/1.00  
% 3.13/1.00  fof(f1,axiom,(
% 3.13/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f22,plain,(
% 3.13/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.13/1.00    inference(ennf_transformation,[],[f1])).
% 3.13/1.00  
% 3.13/1.00  fof(f56,plain,(
% 3.13/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f22])).
% 3.13/1.00  
% 3.13/1.00  fof(f2,axiom,(
% 3.13/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f57,plain,(
% 3.13/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f2])).
% 3.13/1.00  
% 3.13/1.00  fof(f13,axiom,(
% 3.13/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f37,plain,(
% 3.13/1.00    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.13/1.00    inference(ennf_transformation,[],[f13])).
% 3.13/1.00  
% 3.13/1.00  fof(f38,plain,(
% 3.13/1.00    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.13/1.00    inference(flattening,[],[f37])).
% 3.13/1.00  
% 3.13/1.00  fof(f51,plain,(
% 3.13/1.00    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.13/1.00    inference(nnf_transformation,[],[f38])).
% 3.13/1.00  
% 3.13/1.00  fof(f72,plain,(
% 3.13/1.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f51])).
% 3.13/1.00  
% 3.13/1.00  fof(f90,plain,(
% 3.13/1.00    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.13/1.00    inference(equality_resolution,[],[f72])).
% 3.13/1.00  
% 3.13/1.00  fof(f88,plain,(
% 3.13/1.00    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 3.13/1.00    inference(cnf_transformation,[],[f55])).
% 3.13/1.00  
% 3.13/1.00  fof(f10,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f32,plain,(
% 3.13/1.00    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.00    inference(ennf_transformation,[],[f10])).
% 3.13/1.00  
% 3.13/1.00  fof(f66,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f32])).
% 3.13/1.00  
% 3.13/1.00  fof(f7,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f29,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.00    inference(ennf_transformation,[],[f7])).
% 3.13/1.00  
% 3.13/1.00  fof(f62,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f29])).
% 3.13/1.00  
% 3.13/1.00  fof(f9,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k4_relat_1(X2) = k3_relset_1(X0,X1,X2))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f31,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.00    inference(ennf_transformation,[],[f9])).
% 3.13/1.00  
% 3.13/1.00  fof(f64,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f31])).
% 3.13/1.00  
% 3.13/1.00  fof(f3,axiom,(
% 3.13/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(X0) = k4_relat_1(X0)))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f23,plain,(
% 3.13/1.00    ! [X0] : ((k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.13/1.00    inference(ennf_transformation,[],[f3])).
% 3.13/1.00  
% 3.13/1.00  fof(f24,plain,(
% 3.13/1.00    ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.13/1.00    inference(flattening,[],[f23])).
% 3.13/1.00  
% 3.13/1.00  fof(f58,plain,(
% 3.13/1.00    ( ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f24])).
% 3.13/1.00  
% 3.13/1.00  fof(f4,axiom,(
% 3.13/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f25,plain,(
% 3.13/1.00    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.13/1.00    inference(ennf_transformation,[],[f4])).
% 3.13/1.00  
% 3.13/1.00  fof(f26,plain,(
% 3.13/1.00    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.13/1.00    inference(flattening,[],[f25])).
% 3.13/1.00  
% 3.13/1.00  fof(f59,plain,(
% 3.13/1.00    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f26])).
% 3.13/1.00  
% 3.13/1.00  fof(f18,axiom,(
% 3.13/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f46,plain,(
% 3.13/1.00    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.13/1.00    inference(ennf_transformation,[],[f18])).
% 3.13/1.00  
% 3.13/1.00  fof(f47,plain,(
% 3.13/1.00    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.13/1.00    inference(flattening,[],[f46])).
% 3.13/1.00  
% 3.13/1.00  fof(f79,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f47])).
% 3.13/1.00  
% 3.13/1.00  fof(f14,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f39,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.13/1.00    inference(ennf_transformation,[],[f14])).
% 3.13/1.00  
% 3.13/1.00  fof(f40,plain,(
% 3.13/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.13/1.00    inference(flattening,[],[f39])).
% 3.13/1.00  
% 3.13/1.00  fof(f73,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f40])).
% 3.13/1.00  
% 3.13/1.00  fof(f6,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f28,plain,(
% 3.13/1.00    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.00    inference(ennf_transformation,[],[f6])).
% 3.13/1.00  
% 3.13/1.00  fof(f61,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f28])).
% 3.13/1.00  
% 3.13/1.00  fof(f74,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f40])).
% 3.13/1.00  
% 3.13/1.00  cnf(c_32,negated_conjecture,
% 3.13/1.00      ( l1_struct_0(sK0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_659,negated_conjecture,
% 3.13/1.00      ( l1_struct_0(sK0) ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_32]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1182,plain,
% 3.13/1.00      ( l1_struct_0(sK0) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_659]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_20,plain,
% 3.13/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_668,plain,
% 3.13/1.00      ( ~ l1_struct_0(X0_56) | u1_struct_0(X0_56) = k2_struct_0(X0_56) ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1174,plain,
% 3.13/1.00      ( u1_struct_0(X0_56) = k2_struct_0(X0_56)
% 3.13/1.00      | l1_struct_0(X0_56) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_668]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1563,plain,
% 3.13/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1182,c_1174]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_30,negated_conjecture,
% 3.13/1.00      ( l1_struct_0(sK1) ),
% 3.13/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_660,negated_conjecture,
% 3.13/1.00      ( l1_struct_0(sK1) ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_30]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1181,plain,
% 3.13/1.00      ( l1_struct_0(sK1) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1562,plain,
% 3.13/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1181,c_1174]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_26,negated_conjecture,
% 3.13/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.13/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_664,negated_conjecture,
% 3.13/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_26]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1614,plain,
% 3.13/1.00      ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_1562,c_664]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1695,plain,
% 3.13/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_1563,c_1614]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_27,negated_conjecture,
% 3.13/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.13/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_663,negated_conjecture,
% 3.13/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_27]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1178,plain,
% 3.13/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_663]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_7,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_675,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.13/1.00      | k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54) ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1167,plain,
% 3.13/1.00      ( k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54)
% 3.13/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_675]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1609,plain,
% 3.13/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1178,c_1167]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1764,plain,
% 3.13/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 3.13/1.00      inference(light_normalisation,[status(thm)],[c_1609,c_1562,c_1563]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1766,plain,
% 3.13/1.00      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 3.13/1.00      inference(light_normalisation,[status(thm)],[c_1695,c_1764]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1768,plain,
% 3.13/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_1766,c_1764]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_22,plain,
% 3.13/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | ~ v1_funct_1(X0)
% 3.13/1.00      | ~ v2_funct_1(X0)
% 3.13/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.13/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.13/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_667,plain,
% 3.13/1.00      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 3.13/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.13/1.00      | ~ v1_funct_1(X0_54)
% 3.13/1.00      | ~ v2_funct_1(X0_54)
% 3.13/1.00      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 3.13/1.00      | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54) ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1175,plain,
% 3.13/1.00      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 3.13/1.00      | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54)
% 3.13/1.00      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 3.13/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.13/1.00      | v1_funct_1(X0_54) != iProver_top
% 3.13/1.00      | v2_funct_1(X0_54) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_667]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2468,plain,
% 3.13/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 3.13/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.13/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.13/1.00      | v1_funct_1(sK2) != iProver_top
% 3.13/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1768,c_1175]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_29,negated_conjecture,
% 3.13/1.00      ( v1_funct_1(sK2) ),
% 3.13/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_36,plain,
% 3.13/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_25,negated_conjecture,
% 3.13/1.00      ( v2_funct_1(sK2) ),
% 3.13/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_39,plain,
% 3.13/1.00      ( v2_funct_1(sK2) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_28,negated_conjecture,
% 3.13/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.13/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_662,negated_conjecture,
% 3.13/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_28]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1179,plain,
% 3.13/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_662]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1613,plain,
% 3.13/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_1562,c_1179]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1729,plain,
% 3.13/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.13/1.00      inference(light_normalisation,[status(thm)],[c_1613,c_1563]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1770,plain,
% 3.13/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_1766,c_1729]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1612,plain,
% 3.13/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_1562,c_1178]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1840,plain,
% 3.13/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 3.13/1.00      inference(light_normalisation,[status(thm)],[c_1612,c_1563,c_1766]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_6538,plain,
% 3.13/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_2468,c_36,c_39,c_1770,c_1840]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_11,plain,
% 3.13/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.13/1.00      | v1_partfun1(X0,X1)
% 3.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | v1_xboole_0(X2)
% 3.13/1.00      | ~ v1_funct_1(X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_21,plain,
% 3.13/1.00      ( v2_struct_0(X0)
% 3.13/1.00      | ~ l1_struct_0(X0)
% 3.13/1.00      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 3.13/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_31,negated_conjecture,
% 3.13/1.00      ( ~ v2_struct_0(sK1) ),
% 3.13/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_358,plain,
% 3.13/1.00      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 3.13/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_359,plain,
% 3.13/1.00      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 3.13/1.00      inference(unflattening,[status(thm)],[c_358]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_48,plain,
% 3.13/1.00      ( v2_struct_0(sK1)
% 3.13/1.00      | ~ l1_struct_0(sK1)
% 3.13/1.00      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_361,plain,
% 3.13/1.00      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_359,c_31,c_30,c_48]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_371,plain,
% 3.13/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.13/1.00      | v1_partfun1(X0,X1)
% 3.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | ~ v1_funct_1(X0)
% 3.13/1.00      | k2_struct_0(sK1) != X2 ),
% 3.13/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_361]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_372,plain,
% 3.13/1.00      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 3.13/1.00      | v1_partfun1(X0,X1)
% 3.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 3.13/1.00      | ~ v1_funct_1(X0) ),
% 3.13/1.00      inference(unflattening,[status(thm)],[c_371]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_14,plain,
% 3.13/1.00      ( ~ v1_partfun1(X0,X1)
% 3.13/1.00      | ~ v4_relat_1(X0,X1)
% 3.13/1.00      | ~ v1_relat_1(X0)
% 3.13/1.00      | k1_relat_1(X0) = X1 ),
% 3.13/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_433,plain,
% 3.13/1.00      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 3.13/1.00      | ~ v4_relat_1(X0,X1)
% 3.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 3.13/1.00      | ~ v1_funct_1(X0)
% 3.13/1.00      | ~ v1_relat_1(X0)
% 3.13/1.00      | k1_relat_1(X0) = X1 ),
% 3.13/1.00      inference(resolution,[status(thm)],[c_372,c_14]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4,plain,
% 3.13/1.00      ( v4_relat_1(X0,X1)
% 3.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.13/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_449,plain,
% 3.13/1.00      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 3.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 3.13/1.00      | ~ v1_funct_1(X0)
% 3.13/1.00      | ~ v1_relat_1(X0)
% 3.13/1.00      | k1_relat_1(X0) = X1 ),
% 3.13/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_433,c_4]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_658,plain,
% 3.13/1.00      ( ~ v1_funct_2(X0_54,X0_55,k2_struct_0(sK1))
% 3.13/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_struct_0(sK1))))
% 3.13/1.00      | ~ v1_funct_1(X0_54)
% 3.13/1.00      | ~ v1_relat_1(X0_54)
% 3.13/1.00      | k1_relat_1(X0_54) = X0_55 ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_449]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1183,plain,
% 3.13/1.00      ( k1_relat_1(X0_54) = X0_55
% 3.13/1.00      | v1_funct_2(X0_54,X0_55,k2_struct_0(sK1)) != iProver_top
% 3.13/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_struct_0(sK1)))) != iProver_top
% 3.13/1.00      | v1_funct_1(X0_54) != iProver_top
% 3.13/1.00      | v1_relat_1(X0_54) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_658]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3659,plain,
% 3.13/1.00      ( k1_relat_1(X0_54) = X0_55
% 3.13/1.00      | v1_funct_2(X0_54,X0_55,k2_relat_1(sK2)) != iProver_top
% 3.13/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_relat_1(sK2)))) != iProver_top
% 3.13/1.00      | v1_funct_1(X0_54) != iProver_top
% 3.13/1.00      | v1_relat_1(X0_54) != iProver_top ),
% 3.13/1.00      inference(light_normalisation,[status(thm)],[c_1183,c_1766]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3669,plain,
% 3.13/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.13/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.13/1.00      | v1_funct_1(sK2) != iProver_top
% 3.13/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1840,c_3659]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_0,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.13/1.00      | ~ v1_relat_1(X1)
% 3.13/1.00      | v1_relat_1(X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_681,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 3.13/1.00      | ~ v1_relat_1(X1_54)
% 3.13/1.00      | v1_relat_1(X0_54) ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1161,plain,
% 3.13/1.00      ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
% 3.13/1.00      | v1_relat_1(X1_54) != iProver_top
% 3.13/1.00      | v1_relat_1(X0_54) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_681]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1507,plain,
% 3.13/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 3.13/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1178,c_1161]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1,plain,
% 3.13/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.13/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_680,plain,
% 3.13/1.00      ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1573,plain,
% 3.13/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_680]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1574,plain,
% 3.13/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_1573]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4059,plain,
% 3.13/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_3669,c_36,c_1507,c_1574,c_1770]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_6540,plain,
% 3.13/1.00      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 3.13/1.00      inference(light_normalisation,[status(thm)],[c_6538,c_4059]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_15,plain,
% 3.13/1.00      ( r2_funct_2(X0,X1,X2,X2)
% 3.13/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.13/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.13/1.00      | ~ v1_funct_1(X2) ),
% 3.13/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_24,negated_conjecture,
% 3.13/1.00      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 3.13/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_468,plain,
% 3.13/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | ~ v1_funct_1(X0)
% 3.13/1.00      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 3.13/1.00      | u1_struct_0(sK1) != X2
% 3.13/1.00      | u1_struct_0(sK0) != X1
% 3.13/1.00      | sK2 != X0 ),
% 3.13/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_469,plain,
% 3.13/1.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.13/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.13/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.13/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.13/1.00      inference(unflattening,[status(thm)],[c_468]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_657,plain,
% 3.13/1.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.13/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.13/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.13/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_469]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1184,plain,
% 3.13/1.00      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.13/1.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.13/1.00      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.13/1.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_657]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1611,plain,
% 3.13/1.00      ( k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 3.13/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.13/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.13/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_1562,c_1184]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2192,plain,
% 3.13/1.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 3.13/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.13/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.13/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 3.13/1.00      inference(light_normalisation,[status(thm)],[c_1611,c_1563,c_1766]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4077,plain,
% 3.13/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
% 3.13/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.13/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.13/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_4059,c_2192]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_6542,plain,
% 3.13/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 3.13/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.13/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.13/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_6540,c_4077]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_9,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | k2_relset_1(X2,X1,k3_relset_1(X1,X2,X0)) = k1_relset_1(X1,X2,X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_673,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.13/1.00      | k2_relset_1(X1_55,X0_55,k3_relset_1(X0_55,X1_55,X0_54)) = k1_relset_1(X0_55,X1_55,X0_54) ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1169,plain,
% 3.13/1.00      ( k2_relset_1(X0_55,X1_55,k3_relset_1(X1_55,X0_55,X0_54)) = k1_relset_1(X1_55,X0_55,X0_54)
% 3.13/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_673]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2047,plain,
% 3.13/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1840,c_1169]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_6,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_676,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.13/1.00      | k1_relset_1(X0_55,X1_55,X0_54) = k1_relat_1(X0_54) ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1166,plain,
% 3.13/1.00      ( k1_relset_1(X0_55,X1_55,X0_54) = k1_relat_1(X0_54)
% 3.13/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1571,plain,
% 3.13/1.00      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1178,c_1166]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1732,plain,
% 3.13/1.00      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 3.13/1.00      inference(light_normalisation,[status(thm)],[c_1571,c_1562,c_1563]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1769,plain,
% 3.13/1.00      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_1766,c_1732]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_8,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_674,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.13/1.00      | k3_relset_1(X0_55,X1_55,X0_54) = k4_relat_1(X0_54) ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1168,plain,
% 3.13/1.00      ( k3_relset_1(X0_55,X1_55,X0_54) = k4_relat_1(X0_54)
% 3.13/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1929,plain,
% 3.13/1.00      ( k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k4_relat_1(sK2) ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1840,c_1168]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_661,negated_conjecture,
% 3.13/1.00      ( v1_funct_1(sK2) ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_29]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1180,plain,
% 3.13/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_661]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2,plain,
% 3.13/1.00      ( ~ v1_funct_1(X0)
% 3.13/1.00      | ~ v2_funct_1(X0)
% 3.13/1.00      | ~ v1_relat_1(X0)
% 3.13/1.00      | k4_relat_1(X0) = k2_funct_1(X0) ),
% 3.13/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_679,plain,
% 3.13/1.00      ( ~ v1_funct_1(X0_54)
% 3.13/1.00      | ~ v2_funct_1(X0_54)
% 3.13/1.00      | ~ v1_relat_1(X0_54)
% 3.13/1.00      | k4_relat_1(X0_54) = k2_funct_1(X0_54) ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1163,plain,
% 3.13/1.00      ( k4_relat_1(X0_54) = k2_funct_1(X0_54)
% 3.13/1.00      | v1_funct_1(X0_54) != iProver_top
% 3.13/1.00      | v2_funct_1(X0_54) != iProver_top
% 3.13/1.00      | v1_relat_1(X0_54) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_679]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1856,plain,
% 3.13/1.00      ( k4_relat_1(sK2) = k2_funct_1(sK2)
% 3.13/1.00      | v2_funct_1(sK2) != iProver_top
% 3.13/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1180,c_1163]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_719,plain,
% 3.13/1.00      ( ~ v1_funct_1(sK2)
% 3.13/1.00      | ~ v2_funct_1(sK2)
% 3.13/1.00      | ~ v1_relat_1(sK2)
% 3.13/1.00      | k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_679]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1508,plain,
% 3.13/1.00      ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 3.13/1.00      | v1_relat_1(sK2) ),
% 3.13/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1507]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2140,plain,
% 3.13/1.00      ( k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_1856,c_29,c_25,c_719,c_1508,c_1573]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2263,plain,
% 3.13/1.00      ( k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 3.13/1.00      inference(light_normalisation,[status(thm)],[c_1929,c_2140]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2617,plain,
% 3.13/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.13/1.00      inference(light_normalisation,[status(thm)],[c_2047,c_1769,c_2263]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4072,plain,
% 3.13/1.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_4059,c_2617]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_5703,plain,
% 3.13/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 3.13/1.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.13/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.13/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.13/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_4072,c_1175]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3,plain,
% 3.13/1.00      ( ~ v1_funct_1(X0)
% 3.13/1.00      | ~ v2_funct_1(X0)
% 3.13/1.00      | ~ v1_relat_1(X0)
% 3.13/1.00      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.13/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_678,plain,
% 3.13/1.00      ( ~ v1_funct_1(X0_54)
% 3.13/1.00      | ~ v2_funct_1(X0_54)
% 3.13/1.00      | ~ v1_relat_1(X0_54)
% 3.13/1.00      | k2_funct_1(k2_funct_1(X0_54)) = X0_54 ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1164,plain,
% 3.13/1.00      ( k2_funct_1(k2_funct_1(X0_54)) = X0_54
% 3.13/1.00      | v1_funct_1(X0_54) != iProver_top
% 3.13/1.00      | v2_funct_1(X0_54) != iProver_top
% 3.13/1.00      | v1_relat_1(X0_54) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2353,plain,
% 3.13/1.00      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.13/1.00      | v2_funct_1(sK2) != iProver_top
% 3.13/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1180,c_1164]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_722,plain,
% 3.13/1.00      ( ~ v1_funct_1(sK2)
% 3.13/1.00      | ~ v2_funct_1(sK2)
% 3.13/1.00      | ~ v1_relat_1(sK2)
% 3.13/1.00      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_678]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2535,plain,
% 3.13/1.00      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_2353,c_29,c_25,c_722,c_1508,c_1573]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_5723,plain,
% 3.13/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 3.13/1.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.13/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.13/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.13/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.13/1.00      inference(light_normalisation,[status(thm)],[c_5703,c_2535]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_692,plain,
% 3.13/1.00      ( X0_54 != X1_54 | k2_funct_1(X0_54) = k2_funct_1(X1_54) ),
% 3.13/1.00      theory(equality) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_703,plain,
% 3.13/1.00      ( k2_funct_1(sK2) = k2_funct_1(sK2) | sK2 != sK2 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_692]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_683,plain,( X0_54 = X0_54 ),theory(equality) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_711,plain,
% 3.13/1.00      ( sK2 = sK2 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_683]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_752,plain,
% 3.13/1.00      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_668]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1464,plain,
% 3.13/1.00      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.13/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.13/1.00      | ~ v1_funct_1(sK2)
% 3.13/1.00      | ~ v2_funct_1(sK2)
% 3.13/1.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 3.13/1.00      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_667]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_23,plain,
% 3.13/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.13/1.00      | ~ l1_struct_0(X1)
% 3.13/1.00      | ~ l1_struct_0(X2)
% 3.13/1.00      | ~ v1_funct_1(X0)
% 3.13/1.00      | ~ v2_funct_1(X0)
% 3.13/1.00      | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
% 3.13/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 3.13/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_666,plain,
% 3.13/1.00      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_56),u1_struct_0(X1_56))
% 3.13/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 3.13/1.00      | ~ l1_struct_0(X1_56)
% 3.13/1.00      | ~ l1_struct_0(X0_56)
% 3.13/1.00      | ~ v1_funct_1(X0_54)
% 3.13/1.00      | ~ v2_funct_1(X0_54)
% 3.13/1.00      | v2_funct_1(k2_tops_2(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_54))
% 3.13/1.00      | k2_relset_1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_54) != k2_struct_0(X1_56) ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1474,plain,
% 3.13/1.00      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.13/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.13/1.00      | ~ l1_struct_0(sK1)
% 3.13/1.00      | ~ l1_struct_0(sK0)
% 3.13/1.00      | ~ v1_funct_1(sK2)
% 3.13/1.00      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.13/1.00      | ~ v2_funct_1(sK2)
% 3.13/1.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_666]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_687,plain,
% 3.13/1.00      ( X0_55 != X1_55 | X2_55 != X1_55 | X2_55 = X0_55 ),
% 3.13/1.00      theory(equality) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1500,plain,
% 3.13/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_55
% 3.13/1.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 3.13/1.00      | u1_struct_0(sK1) != X0_55 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_687]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1634,plain,
% 3.13/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 3.13/1.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 3.13/1.00      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_1500]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2620,plain,
% 3.13/1.00      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 3.13/1.00      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 3.13/1.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 3.13/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 3.13/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.13/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_2617,c_1175]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2643,plain,
% 3.13/1.00      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 3.13/1.00      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 3.13/1.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 3.13/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 3.13/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.13/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.13/1.00      inference(light_normalisation,[status(thm)],[c_2620,c_2535]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_37,plain,
% 3.13/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_38,plain,
% 3.13/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_19,plain,
% 3.13/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | ~ v1_funct_1(X0)
% 3.13/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.13/1.00      | ~ v2_funct_1(X0)
% 3.13/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.13/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_669,plain,
% 3.13/1.00      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 3.13/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.13/1.00      | ~ v1_funct_1(X0_54)
% 3.13/1.00      | v1_funct_1(k2_funct_1(X0_54))
% 3.13/1.00      | ~ v2_funct_1(X0_54)
% 3.13/1.00      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1455,plain,
% 3.13/1.00      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.13/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.13/1.00      | v1_funct_1(k2_funct_1(sK2))
% 3.13/1.00      | ~ v1_funct_1(sK2)
% 3.13/1.00      | ~ v2_funct_1(sK2)
% 3.13/1.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_669]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1456,plain,
% 3.13/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 3.13/1.00      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.13/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.13/1.00      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.13/1.00      | v1_funct_1(sK2) != iProver_top
% 3.13/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_1455]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_5,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.13/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_677,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.13/1.00      | m1_subset_1(k3_relset_1(X0_55,X1_55,X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1165,plain,
% 3.13/1.00      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.13/1.00      | m1_subset_1(k3_relset_1(X0_55,X1_55,X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_677]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2265,plain,
% 3.13/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 3.13/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_2263,c_1165]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_18,plain,
% 3.13/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.13/1.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.00      | ~ v1_funct_1(X0)
% 3.13/1.00      | ~ v2_funct_1(X0)
% 3.13/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.13/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_670,plain,
% 3.13/1.00      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 3.13/1.00      | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55)
% 3.13/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.13/1.00      | ~ v1_funct_1(X0_54)
% 3.13/1.00      | ~ v2_funct_1(X0_54)
% 3.13/1.00      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
% 3.13/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1172,plain,
% 3.13/1.00      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 3.13/1.00      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 3.13/1.00      | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55) = iProver_top
% 3.13/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.13/1.00      | v1_funct_1(X0_54) != iProver_top
% 3.13/1.00      | v2_funct_1(X0_54) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_670]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2459,plain,
% 3.13/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 3.13/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.13/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.13/1.00      | v1_funct_1(sK2) != iProver_top
% 3.13/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1768,c_1172]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2659,plain,
% 3.13/1.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 3.13/1.00      | k2_struct_0(sK0) != k1_relat_1(sK2)
% 3.13/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_2643,c_30,c_36,c_37,c_38,c_39,c_752,c_664,c_1456,
% 3.13/1.00                 c_1634,c_1770,c_1840,c_2265,c_2459]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2660,plain,
% 3.13/1.00      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 3.13/1.00      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 3.13/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.13/1.00      inference(renaming,[status(thm)],[c_2659]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4071,plain,
% 3.13/1.00      ( k1_relat_1(sK2) != k1_relat_1(sK2)
% 3.13/1.00      | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 3.13/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_4059,c_2660]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4102,plain,
% 3.13/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 3.13/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.13/1.00      inference(equality_resolution_simp,[status(thm)],[c_4071]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4199,plain,
% 3.13/1.00      ( ~ v2_funct_1(k2_funct_1(sK2))
% 3.13/1.00      | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 3.13/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4102]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_686,plain,
% 3.13/1.00      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 3.13/1.00      theory(equality) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2475,plain,
% 3.13/1.00      ( X0_54 != X1_54
% 3.13/1.00      | k2_funct_1(sK2) != X1_54
% 3.13/1.00      | k2_funct_1(sK2) = X0_54 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_686]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3704,plain,
% 3.13/1.00      ( X0_54 != k2_funct_1(sK2)
% 3.13/1.00      | k2_funct_1(sK2) = X0_54
% 3.13/1.00      | k2_funct_1(sK2) != k2_funct_1(sK2) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_2475]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_5353,plain,
% 3.13/1.00      ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2)
% 3.13/1.00      | k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
% 3.13/1.00      | k2_funct_1(sK2) != k2_funct_1(sK2) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_3704]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_693,plain,
% 3.13/1.00      ( ~ v2_funct_1(X0_54) | v2_funct_1(X1_54) | X1_54 != X0_54 ),
% 3.13/1.00      theory(equality) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2034,plain,
% 3.13/1.00      ( ~ v2_funct_1(X0_54)
% 3.13/1.00      | v2_funct_1(k2_funct_1(sK2))
% 3.13/1.00      | k2_funct_1(sK2) != X0_54 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_693]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_5682,plain,
% 3.13/1.00      ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.13/1.00      | v2_funct_1(k2_funct_1(sK2))
% 3.13/1.00      | k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_2034]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_5747,plain,
% 3.13/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_5723,c_32,c_30,c_29,c_28,c_27,c_25,c_703,c_711,c_752,
% 3.13/1.00                 c_664,c_1464,c_1474,c_1634,c_4199,c_5353,c_5682]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_6543,plain,
% 3.13/1.00      ( sK2 != sK2
% 3.13/1.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.13/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.13/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.13/1.00      inference(light_normalisation,[status(thm)],[c_6542,c_5747]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_6544,plain,
% 3.13/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.13/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.13/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.13/1.00      inference(equality_resolution_simp,[status(thm)],[c_6543]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4078,plain,
% 3.13/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_4059,c_1840]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4076,plain,
% 3.13/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_4059,c_1770]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(contradiction,plain,
% 3.13/1.00      ( $false ),
% 3.13/1.00      inference(minisat,[status(thm)],[c_6544,c_4078,c_4076,c_36]) ).
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.13/1.00  
% 3.13/1.00  ------                               Statistics
% 3.13/1.00  
% 3.13/1.00  ------ General
% 3.13/1.00  
% 3.13/1.00  abstr_ref_over_cycles:                  0
% 3.13/1.00  abstr_ref_under_cycles:                 0
% 3.13/1.00  gc_basic_clause_elim:                   0
% 3.13/1.00  forced_gc_time:                         0
% 3.13/1.00  parsing_time:                           0.01
% 3.13/1.00  unif_index_cands_time:                  0.
% 3.13/1.00  unif_index_add_time:                    0.
% 3.13/1.00  orderings_time:                         0.
% 3.13/1.00  out_proof_time:                         0.013
% 3.13/1.00  total_time:                             0.242
% 3.13/1.00  num_of_symbols:                         58
% 3.13/1.00  num_of_terms:                           5973
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing
% 3.13/1.00  
% 3.13/1.00  num_of_splits:                          0
% 3.13/1.00  num_of_split_atoms:                     0
% 3.13/1.00  num_of_reused_defs:                     0
% 3.13/1.00  num_eq_ax_congr_red:                    29
% 3.13/1.00  num_of_sem_filtered_clauses:            1
% 3.13/1.00  num_of_subtypes:                        4
% 3.13/1.00  monotx_restored_types:                  1
% 3.13/1.00  sat_num_of_epr_types:                   0
% 3.13/1.00  sat_num_of_non_cyclic_types:            0
% 3.13/1.00  sat_guarded_non_collapsed_types:        1
% 3.13/1.00  num_pure_diseq_elim:                    0
% 3.13/1.00  simp_replaced_by:                       0
% 3.13/1.00  res_preprocessed:                       140
% 3.13/1.00  prep_upred:                             0
% 3.13/1.00  prep_unflattend:                        13
% 3.13/1.00  smt_new_axioms:                         0
% 3.13/1.00  pred_elim_cands:                        6
% 3.13/1.00  pred_elim:                              5
% 3.13/1.00  pred_elim_cl:                           7
% 3.13/1.00  pred_elim_cycles:                       8
% 3.13/1.00  merged_defs:                            0
% 3.13/1.00  merged_defs_ncl:                        0
% 3.13/1.00  bin_hyper_res:                          0
% 3.13/1.00  prep_cycles:                            4
% 3.13/1.00  pred_elim_time:                         0.005
% 3.13/1.00  splitting_time:                         0.
% 3.13/1.00  sem_filter_time:                        0.
% 3.13/1.00  monotx_time:                            0.001
% 3.13/1.00  subtype_inf_time:                       0.002
% 3.13/1.00  
% 3.13/1.00  ------ Problem properties
% 3.13/1.00  
% 3.13/1.00  clauses:                                25
% 3.13/1.00  conjectures:                            7
% 3.13/1.00  epr:                                    4
% 3.13/1.00  horn:                                   25
% 3.13/1.00  ground:                                 8
% 3.13/1.00  unary:                                  8
% 3.13/1.00  binary:                                 7
% 3.13/1.00  lits:                                   74
% 3.13/1.00  lits_eq:                                17
% 3.13/1.00  fd_pure:                                0
% 3.13/1.00  fd_pseudo:                              0
% 3.13/1.00  fd_cond:                                0
% 3.13/1.00  fd_pseudo_cond:                         1
% 3.13/1.00  ac_symbols:                             0
% 3.13/1.00  
% 3.13/1.00  ------ Propositional Solver
% 3.13/1.00  
% 3.13/1.00  prop_solver_calls:                      32
% 3.13/1.00  prop_fast_solver_calls:                 1294
% 3.13/1.00  smt_solver_calls:                       0
% 3.13/1.00  smt_fast_solver_calls:                  0
% 3.13/1.00  prop_num_of_clauses:                    2186
% 3.13/1.00  prop_preprocess_simplified:             6419
% 3.13/1.00  prop_fo_subsumed:                       48
% 3.13/1.00  prop_solver_time:                       0.
% 3.13/1.00  smt_solver_time:                        0.
% 3.13/1.00  smt_fast_solver_time:                   0.
% 3.13/1.00  prop_fast_solver_time:                  0.
% 3.13/1.00  prop_unsat_core_time:                   0.
% 3.13/1.00  
% 3.13/1.00  ------ QBF
% 3.13/1.00  
% 3.13/1.00  qbf_q_res:                              0
% 3.13/1.00  qbf_num_tautologies:                    0
% 3.13/1.00  qbf_prep_cycles:                        0
% 3.13/1.00  
% 3.13/1.00  ------ BMC1
% 3.13/1.00  
% 3.13/1.00  bmc1_current_bound:                     -1
% 3.13/1.00  bmc1_last_solved_bound:                 -1
% 3.13/1.00  bmc1_unsat_core_size:                   -1
% 3.13/1.00  bmc1_unsat_core_parents_size:           -1
% 3.13/1.00  bmc1_merge_next_fun:                    0
% 3.13/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.13/1.00  
% 3.13/1.00  ------ Instantiation
% 3.13/1.00  
% 3.13/1.00  inst_num_of_clauses:                    791
% 3.13/1.00  inst_num_in_passive:                    219
% 3.13/1.00  inst_num_in_active:                     474
% 3.13/1.00  inst_num_in_unprocessed:                98
% 3.13/1.00  inst_num_of_loops:                      500
% 3.13/1.00  inst_num_of_learning_restarts:          0
% 3.13/1.00  inst_num_moves_active_passive:          20
% 3.13/1.00  inst_lit_activity:                      0
% 3.13/1.00  inst_lit_activity_moves:                0
% 3.13/1.00  inst_num_tautologies:                   0
% 3.13/1.00  inst_num_prop_implied:                  0
% 3.13/1.00  inst_num_existing_simplified:           0
% 3.13/1.00  inst_num_eq_res_simplified:             0
% 3.13/1.00  inst_num_child_elim:                    0
% 3.13/1.00  inst_num_of_dismatching_blockings:      300
% 3.13/1.00  inst_num_of_non_proper_insts:           845
% 3.13/1.00  inst_num_of_duplicates:                 0
% 3.13/1.00  inst_inst_num_from_inst_to_res:         0
% 3.13/1.00  inst_dismatching_checking_time:         0.
% 3.13/1.00  
% 3.13/1.00  ------ Resolution
% 3.13/1.00  
% 3.13/1.00  res_num_of_clauses:                     0
% 3.13/1.00  res_num_in_passive:                     0
% 3.13/1.00  res_num_in_active:                      0
% 3.13/1.00  res_num_of_loops:                       144
% 3.13/1.00  res_forward_subset_subsumed:            85
% 3.13/1.00  res_backward_subset_subsumed:           0
% 3.13/1.00  res_forward_subsumed:                   0
% 3.13/1.00  res_backward_subsumed:                  0
% 3.13/1.00  res_forward_subsumption_resolution:     1
% 3.13/1.00  res_backward_subsumption_resolution:    0
% 3.13/1.00  res_clause_to_clause_subsumption:       310
% 3.13/1.00  res_orphan_elimination:                 0
% 3.13/1.00  res_tautology_del:                      138
% 3.13/1.00  res_num_eq_res_simplified:              0
% 3.13/1.00  res_num_sel_changes:                    0
% 3.13/1.00  res_moves_from_active_to_pass:          0
% 3.13/1.00  
% 3.13/1.00  ------ Superposition
% 3.13/1.00  
% 3.13/1.00  sup_time_total:                         0.
% 3.13/1.00  sup_time_generating:                    0.
% 3.13/1.00  sup_time_sim_full:                      0.
% 3.13/1.00  sup_time_sim_immed:                     0.
% 3.13/1.00  
% 3.13/1.00  sup_num_of_clauses:                     137
% 3.13/1.00  sup_num_in_active:                      67
% 3.13/1.00  sup_num_in_passive:                     70
% 3.13/1.00  sup_num_of_loops:                       99
% 3.13/1.00  sup_fw_superposition:                   64
% 3.13/1.00  sup_bw_superposition:                   121
% 3.13/1.00  sup_immediate_simplified:               109
% 3.13/1.00  sup_given_eliminated:                   0
% 3.13/1.00  comparisons_done:                       0
% 3.13/1.00  comparisons_avoided:                    0
% 3.13/1.00  
% 3.13/1.00  ------ Simplifications
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  sim_fw_subset_subsumed:                 11
% 3.13/1.00  sim_bw_subset_subsumed:                 4
% 3.13/1.00  sim_fw_subsumed:                        10
% 3.13/1.00  sim_bw_subsumed:                        0
% 3.13/1.00  sim_fw_subsumption_res:                 1
% 3.13/1.00  sim_bw_subsumption_res:                 0
% 3.13/1.00  sim_tautology_del:                      0
% 3.13/1.00  sim_eq_tautology_del:                   11
% 3.13/1.00  sim_eq_res_simp:                        2
% 3.13/1.00  sim_fw_demodulated:                     0
% 3.13/1.00  sim_bw_demodulated:                     50
% 3.13/1.00  sim_light_normalised:                   101
% 3.13/1.00  sim_joinable_taut:                      0
% 3.13/1.00  sim_joinable_simp:                      0
% 3.13/1.00  sim_ac_normalised:                      0
% 3.13/1.00  sim_smt_subsumption:                    0
% 3.13/1.00  
%------------------------------------------------------------------------------
