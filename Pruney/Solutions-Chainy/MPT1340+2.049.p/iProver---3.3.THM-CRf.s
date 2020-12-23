%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:31 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  209 (6036 expanded)
%              Number of clauses        :  121 (1688 expanded)
%              Number of leaves         :   23 (1790 expanded)
%              Depth                    :   27
%              Number of atoms          :  752 (39235 expanded)
%              Number of equality atoms :  276 (6465 expanded)
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

fof(f56,plain,(
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

fof(f55,plain,(
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

fof(f54,plain,
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

fof(f57,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f56,f55,f54])).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f57])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f84,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f89,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f93,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f35])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f88,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f15,axiom,(
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

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f94,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f69,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f72,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f64,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f71,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
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

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f80])).

fof(f95,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1193,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_26,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_35,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_419,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_35])).

cnf(c_420,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_37,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_424,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_37])).

cnf(c_425,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_1236,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1193,c_420,c_425])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1199,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1741,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1236,c_1199])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1233,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_31,c_420,c_425])).

cnf(c_1743,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1741,c_1233])).

cnf(c_1793,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1743,c_1236])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1211,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2083,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1793,c_1211])).

cnf(c_43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1459,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1829,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_1830,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1829])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1869,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1870,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1869])).

cnf(c_2227,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2083,c_43,c_1830,c_1870])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_27,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_406,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_36])).

cnf(c_407,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_50,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_409,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_407,c_36,c_35,c_50])).

cnf(c_431,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_409])).

cnf(c_432,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_20,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_493,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_432,c_20])).

cnf(c_15,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_509,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_493,c_15])).

cnf(c_1190,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_1641,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1236,c_1190])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_41,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1192,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1230,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1192,c_420,c_425])).

cnf(c_1720,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1641,c_41,c_1230])).

cnf(c_2232,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2227,c_1720])).

cnf(c_1790,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1743,c_1741])).

cnf(c_2236,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2232,c_1790])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1198,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3364,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2236,c_1198])).

cnf(c_30,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_44,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2235,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2232,c_1793])).

cnf(c_1794,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1743,c_1230])).

cnf(c_2237,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2232,c_1794])).

cnf(c_3775,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3364,c_41,c_44,c_2235,c_2237])).

cnf(c_3781,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3775,c_1199])).

cnf(c_1194,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1204,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2733,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1194,c_1204])).

cnf(c_1486,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2911,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2733,c_34,c_32,c_30,c_1486,c_1829,c_1869])).

cnf(c_3783,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3781,c_2911])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1195,plain,
    ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3880,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3783,c_1195])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1200,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2614,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1194,c_1200])).

cnf(c_1507,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2831,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2614,c_34,c_32,c_30,c_1507,c_1829,c_1869])).

cnf(c_3886,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3880,c_2831])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1453,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1454,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1453])).

cnf(c_7,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2378,plain,
    ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2379,plain,
    ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2378])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1197,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3197,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2236,c_1197])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1212,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1205,plain,
    ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3321,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) != iProver_top
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2911,c_1205])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1456,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1457,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1456])).

cnf(c_3560,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) != iProver_top
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3321,c_41,c_43,c_1454,c_1457,c_1830,c_1870])).

cnf(c_3561,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) != iProver_top
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3560])).

cnf(c_3571,plain,
    ( v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_3561])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1202,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3205,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1194,c_1202])).

cnf(c_1518,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3492,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3205,c_34,c_32,c_30,c_1518,c_1829,c_1869])).

cnf(c_3587,plain,
    ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3571,c_3492])).

cnf(c_4085,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3886,c_41,c_43,c_44,c_1454,c_1830,c_1870,c_2235,c_2237,c_2379,c_3197,c_3364,c_3587])).

cnf(c_21,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_29,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_528,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_529,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_1189,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_529])).

cnf(c_1379,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1189,c_420,c_425])).

cnf(c_1792,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1743,c_1379])).

cnf(c_2234,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2232,c_1792])).

cnf(c_1943,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1790,c_1195])).

cnf(c_3040,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1943,c_41,c_44,c_1793,c_1794])).

cnf(c_3042,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3040,c_2232])).

cnf(c_3093,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2234,c_3042])).

cnf(c_4088,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4085,c_3093])).

cnf(c_721,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1662,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4088,c_2237,c_2235,c_1662,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:38:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.81/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.03  
% 1.81/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.81/1.03  
% 1.81/1.03  ------  iProver source info
% 1.81/1.03  
% 1.81/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.81/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.81/1.03  git: non_committed_changes: false
% 1.81/1.03  git: last_make_outside_of_git: false
% 1.81/1.03  
% 1.81/1.03  ------ 
% 1.81/1.03  
% 1.81/1.03  ------ Input Options
% 1.81/1.03  
% 1.81/1.03  --out_options                           all
% 1.81/1.03  --tptp_safe_out                         true
% 1.81/1.03  --problem_path                          ""
% 1.81/1.03  --include_path                          ""
% 1.81/1.03  --clausifier                            res/vclausify_rel
% 1.81/1.03  --clausifier_options                    --mode clausify
% 1.81/1.03  --stdin                                 false
% 1.81/1.03  --stats_out                             all
% 1.81/1.03  
% 1.81/1.03  ------ General Options
% 1.81/1.03  
% 1.81/1.03  --fof                                   false
% 1.81/1.03  --time_out_real                         305.
% 1.81/1.03  --time_out_virtual                      -1.
% 1.81/1.03  --symbol_type_check                     false
% 1.81/1.03  --clausify_out                          false
% 1.81/1.03  --sig_cnt_out                           false
% 1.81/1.03  --trig_cnt_out                          false
% 1.81/1.03  --trig_cnt_out_tolerance                1.
% 1.81/1.03  --trig_cnt_out_sk_spl                   false
% 1.81/1.03  --abstr_cl_out                          false
% 1.81/1.03  
% 1.81/1.03  ------ Global Options
% 1.81/1.03  
% 1.81/1.03  --schedule                              default
% 1.81/1.03  --add_important_lit                     false
% 1.81/1.03  --prop_solver_per_cl                    1000
% 1.81/1.03  --min_unsat_core                        false
% 1.81/1.03  --soft_assumptions                      false
% 1.81/1.03  --soft_lemma_size                       3
% 1.81/1.03  --prop_impl_unit_size                   0
% 1.81/1.03  --prop_impl_unit                        []
% 1.81/1.03  --share_sel_clauses                     true
% 1.81/1.03  --reset_solvers                         false
% 1.81/1.03  --bc_imp_inh                            [conj_cone]
% 1.81/1.03  --conj_cone_tolerance                   3.
% 1.81/1.03  --extra_neg_conj                        none
% 1.81/1.03  --large_theory_mode                     true
% 1.81/1.03  --prolific_symb_bound                   200
% 1.81/1.03  --lt_threshold                          2000
% 1.81/1.03  --clause_weak_htbl                      true
% 1.81/1.03  --gc_record_bc_elim                     false
% 1.81/1.03  
% 1.81/1.03  ------ Preprocessing Options
% 1.81/1.03  
% 1.81/1.03  --preprocessing_flag                    true
% 1.81/1.03  --time_out_prep_mult                    0.1
% 1.81/1.03  --splitting_mode                        input
% 1.81/1.03  --splitting_grd                         true
% 1.81/1.03  --splitting_cvd                         false
% 1.81/1.03  --splitting_cvd_svl                     false
% 1.81/1.03  --splitting_nvd                         32
% 1.81/1.03  --sub_typing                            true
% 1.81/1.03  --prep_gs_sim                           true
% 1.81/1.03  --prep_unflatten                        true
% 1.81/1.03  --prep_res_sim                          true
% 1.81/1.03  --prep_upred                            true
% 1.81/1.03  --prep_sem_filter                       exhaustive
% 1.81/1.03  --prep_sem_filter_out                   false
% 1.81/1.03  --pred_elim                             true
% 1.81/1.03  --res_sim_input                         true
% 1.81/1.03  --eq_ax_congr_red                       true
% 1.81/1.03  --pure_diseq_elim                       true
% 1.81/1.03  --brand_transform                       false
% 1.81/1.03  --non_eq_to_eq                          false
% 1.81/1.03  --prep_def_merge                        true
% 1.81/1.03  --prep_def_merge_prop_impl              false
% 1.81/1.03  --prep_def_merge_mbd                    true
% 1.81/1.03  --prep_def_merge_tr_red                 false
% 1.81/1.03  --prep_def_merge_tr_cl                  false
% 1.81/1.03  --smt_preprocessing                     true
% 1.81/1.03  --smt_ac_axioms                         fast
% 1.81/1.03  --preprocessed_out                      false
% 1.81/1.03  --preprocessed_stats                    false
% 1.81/1.03  
% 1.81/1.03  ------ Abstraction refinement Options
% 1.81/1.03  
% 1.81/1.03  --abstr_ref                             []
% 1.81/1.03  --abstr_ref_prep                        false
% 1.81/1.03  --abstr_ref_until_sat                   false
% 1.81/1.03  --abstr_ref_sig_restrict                funpre
% 1.81/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.81/1.03  --abstr_ref_under                       []
% 1.81/1.03  
% 1.81/1.03  ------ SAT Options
% 1.81/1.03  
% 1.81/1.03  --sat_mode                              false
% 1.81/1.03  --sat_fm_restart_options                ""
% 1.81/1.03  --sat_gr_def                            false
% 1.81/1.03  --sat_epr_types                         true
% 1.81/1.03  --sat_non_cyclic_types                  false
% 1.81/1.03  --sat_finite_models                     false
% 1.81/1.03  --sat_fm_lemmas                         false
% 1.81/1.03  --sat_fm_prep                           false
% 1.81/1.03  --sat_fm_uc_incr                        true
% 1.81/1.03  --sat_out_model                         small
% 1.81/1.03  --sat_out_clauses                       false
% 1.81/1.03  
% 1.81/1.03  ------ QBF Options
% 1.81/1.03  
% 1.81/1.03  --qbf_mode                              false
% 1.81/1.03  --qbf_elim_univ                         false
% 1.81/1.03  --qbf_dom_inst                          none
% 1.81/1.03  --qbf_dom_pre_inst                      false
% 1.81/1.03  --qbf_sk_in                             false
% 1.81/1.03  --qbf_pred_elim                         true
% 1.81/1.03  --qbf_split                             512
% 1.81/1.03  
% 1.81/1.03  ------ BMC1 Options
% 1.81/1.03  
% 1.81/1.03  --bmc1_incremental                      false
% 1.81/1.03  --bmc1_axioms                           reachable_all
% 1.81/1.03  --bmc1_min_bound                        0
% 1.81/1.03  --bmc1_max_bound                        -1
% 1.81/1.03  --bmc1_max_bound_default                -1
% 1.81/1.03  --bmc1_symbol_reachability              true
% 1.81/1.03  --bmc1_property_lemmas                  false
% 1.81/1.03  --bmc1_k_induction                      false
% 1.81/1.03  --bmc1_non_equiv_states                 false
% 1.81/1.03  --bmc1_deadlock                         false
% 1.81/1.03  --bmc1_ucm                              false
% 1.81/1.03  --bmc1_add_unsat_core                   none
% 1.81/1.03  --bmc1_unsat_core_children              false
% 1.81/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.81/1.03  --bmc1_out_stat                         full
% 1.81/1.03  --bmc1_ground_init                      false
% 1.81/1.03  --bmc1_pre_inst_next_state              false
% 1.81/1.03  --bmc1_pre_inst_state                   false
% 1.81/1.03  --bmc1_pre_inst_reach_state             false
% 1.81/1.03  --bmc1_out_unsat_core                   false
% 1.81/1.03  --bmc1_aig_witness_out                  false
% 1.81/1.03  --bmc1_verbose                          false
% 1.81/1.03  --bmc1_dump_clauses_tptp                false
% 1.81/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.81/1.03  --bmc1_dump_file                        -
% 1.81/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.81/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.81/1.03  --bmc1_ucm_extend_mode                  1
% 1.81/1.03  --bmc1_ucm_init_mode                    2
% 1.81/1.03  --bmc1_ucm_cone_mode                    none
% 1.81/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.81/1.03  --bmc1_ucm_relax_model                  4
% 1.81/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.81/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.81/1.03  --bmc1_ucm_layered_model                none
% 1.81/1.03  --bmc1_ucm_max_lemma_size               10
% 1.81/1.03  
% 1.81/1.03  ------ AIG Options
% 1.81/1.03  
% 1.81/1.03  --aig_mode                              false
% 1.81/1.03  
% 1.81/1.03  ------ Instantiation Options
% 1.81/1.03  
% 1.81/1.03  --instantiation_flag                    true
% 1.81/1.03  --inst_sos_flag                         false
% 1.81/1.03  --inst_sos_phase                        true
% 1.81/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.81/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.81/1.03  --inst_lit_sel_side                     num_symb
% 1.81/1.03  --inst_solver_per_active                1400
% 1.81/1.03  --inst_solver_calls_frac                1.
% 1.81/1.03  --inst_passive_queue_type               priority_queues
% 1.81/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.81/1.03  --inst_passive_queues_freq              [25;2]
% 1.81/1.03  --inst_dismatching                      true
% 1.81/1.03  --inst_eager_unprocessed_to_passive     true
% 1.81/1.03  --inst_prop_sim_given                   true
% 1.81/1.03  --inst_prop_sim_new                     false
% 1.81/1.03  --inst_subs_new                         false
% 1.81/1.03  --inst_eq_res_simp                      false
% 1.81/1.03  --inst_subs_given                       false
% 1.81/1.03  --inst_orphan_elimination               true
% 1.81/1.03  --inst_learning_loop_flag               true
% 1.81/1.03  --inst_learning_start                   3000
% 1.81/1.03  --inst_learning_factor                  2
% 1.81/1.03  --inst_start_prop_sim_after_learn       3
% 1.81/1.03  --inst_sel_renew                        solver
% 1.81/1.03  --inst_lit_activity_flag                true
% 1.81/1.03  --inst_restr_to_given                   false
% 1.81/1.03  --inst_activity_threshold               500
% 1.81/1.03  --inst_out_proof                        true
% 1.81/1.03  
% 1.81/1.03  ------ Resolution Options
% 1.81/1.03  
% 1.81/1.03  --resolution_flag                       true
% 1.81/1.03  --res_lit_sel                           adaptive
% 1.81/1.03  --res_lit_sel_side                      none
% 1.81/1.03  --res_ordering                          kbo
% 1.81/1.03  --res_to_prop_solver                    active
% 1.81/1.03  --res_prop_simpl_new                    false
% 1.81/1.03  --res_prop_simpl_given                  true
% 1.81/1.03  --res_passive_queue_type                priority_queues
% 1.81/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.81/1.03  --res_passive_queues_freq               [15;5]
% 1.81/1.03  --res_forward_subs                      full
% 1.81/1.03  --res_backward_subs                     full
% 1.81/1.03  --res_forward_subs_resolution           true
% 1.81/1.03  --res_backward_subs_resolution          true
% 1.81/1.03  --res_orphan_elimination                true
% 1.81/1.03  --res_time_limit                        2.
% 1.81/1.03  --res_out_proof                         true
% 1.81/1.03  
% 1.81/1.03  ------ Superposition Options
% 1.81/1.03  
% 1.81/1.03  --superposition_flag                    true
% 1.81/1.03  --sup_passive_queue_type                priority_queues
% 1.81/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.81/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.81/1.03  --demod_completeness_check              fast
% 1.81/1.03  --demod_use_ground                      true
% 1.81/1.03  --sup_to_prop_solver                    passive
% 1.81/1.03  --sup_prop_simpl_new                    true
% 1.81/1.03  --sup_prop_simpl_given                  true
% 1.81/1.03  --sup_fun_splitting                     false
% 1.81/1.03  --sup_smt_interval                      50000
% 1.81/1.03  
% 1.81/1.03  ------ Superposition Simplification Setup
% 1.81/1.03  
% 1.81/1.03  --sup_indices_passive                   []
% 1.81/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.81/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.03  --sup_full_bw                           [BwDemod]
% 1.81/1.03  --sup_immed_triv                        [TrivRules]
% 1.81/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.81/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.03  --sup_immed_bw_main                     []
% 1.81/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.81/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/1.03  
% 1.81/1.03  ------ Combination Options
% 1.81/1.03  
% 1.81/1.03  --comb_res_mult                         3
% 1.81/1.03  --comb_sup_mult                         2
% 1.81/1.03  --comb_inst_mult                        10
% 1.81/1.03  
% 1.81/1.03  ------ Debug Options
% 1.81/1.03  
% 1.81/1.03  --dbg_backtrace                         false
% 1.81/1.03  --dbg_dump_prop_clauses                 false
% 1.81/1.03  --dbg_dump_prop_clauses_file            -
% 1.81/1.03  --dbg_out_stat                          false
% 1.81/1.03  ------ Parsing...
% 1.81/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.81/1.03  
% 1.81/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.81/1.03  
% 1.81/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.81/1.03  
% 1.81/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.81/1.03  ------ Proving...
% 1.81/1.03  ------ Problem Properties 
% 1.81/1.03  
% 1.81/1.03  
% 1.81/1.03  clauses                                 28
% 1.81/1.03  conjectures                             5
% 1.81/1.03  EPR                                     4
% 1.81/1.03  Horn                                    28
% 1.81/1.03  unary                                   11
% 1.81/1.03  binary                                  1
% 1.81/1.03  lits                                    85
% 1.81/1.03  lits eq                                 17
% 1.81/1.03  fd_pure                                 0
% 1.81/1.03  fd_pseudo                               0
% 1.81/1.03  fd_cond                                 0
% 1.81/1.03  fd_pseudo_cond                          2
% 1.81/1.03  AC symbols                              0
% 1.81/1.03  
% 1.81/1.03  ------ Schedule dynamic 5 is on 
% 1.81/1.03  
% 1.81/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.81/1.03  
% 1.81/1.03  
% 1.81/1.03  ------ 
% 1.81/1.03  Current options:
% 1.81/1.03  ------ 
% 1.81/1.03  
% 1.81/1.03  ------ Input Options
% 1.81/1.03  
% 1.81/1.03  --out_options                           all
% 1.81/1.03  --tptp_safe_out                         true
% 1.81/1.03  --problem_path                          ""
% 1.81/1.03  --include_path                          ""
% 1.81/1.03  --clausifier                            res/vclausify_rel
% 1.81/1.03  --clausifier_options                    --mode clausify
% 1.81/1.03  --stdin                                 false
% 1.81/1.03  --stats_out                             all
% 1.81/1.03  
% 1.81/1.03  ------ General Options
% 1.81/1.03  
% 1.81/1.03  --fof                                   false
% 1.81/1.03  --time_out_real                         305.
% 1.81/1.03  --time_out_virtual                      -1.
% 1.81/1.03  --symbol_type_check                     false
% 1.81/1.03  --clausify_out                          false
% 1.81/1.03  --sig_cnt_out                           false
% 1.81/1.03  --trig_cnt_out                          false
% 1.81/1.03  --trig_cnt_out_tolerance                1.
% 1.81/1.03  --trig_cnt_out_sk_spl                   false
% 1.81/1.03  --abstr_cl_out                          false
% 1.81/1.03  
% 1.81/1.03  ------ Global Options
% 1.81/1.03  
% 1.81/1.03  --schedule                              default
% 1.81/1.03  --add_important_lit                     false
% 1.81/1.03  --prop_solver_per_cl                    1000
% 1.81/1.03  --min_unsat_core                        false
% 1.81/1.03  --soft_assumptions                      false
% 1.81/1.03  --soft_lemma_size                       3
% 1.81/1.03  --prop_impl_unit_size                   0
% 1.81/1.03  --prop_impl_unit                        []
% 1.81/1.03  --share_sel_clauses                     true
% 1.81/1.03  --reset_solvers                         false
% 1.81/1.03  --bc_imp_inh                            [conj_cone]
% 1.81/1.03  --conj_cone_tolerance                   3.
% 1.81/1.03  --extra_neg_conj                        none
% 1.81/1.03  --large_theory_mode                     true
% 1.81/1.03  --prolific_symb_bound                   200
% 1.81/1.03  --lt_threshold                          2000
% 1.81/1.03  --clause_weak_htbl                      true
% 1.81/1.03  --gc_record_bc_elim                     false
% 1.81/1.03  
% 1.81/1.03  ------ Preprocessing Options
% 1.81/1.03  
% 1.81/1.03  --preprocessing_flag                    true
% 1.81/1.03  --time_out_prep_mult                    0.1
% 1.81/1.03  --splitting_mode                        input
% 1.81/1.03  --splitting_grd                         true
% 1.81/1.03  --splitting_cvd                         false
% 1.81/1.03  --splitting_cvd_svl                     false
% 1.81/1.03  --splitting_nvd                         32
% 1.81/1.03  --sub_typing                            true
% 1.81/1.03  --prep_gs_sim                           true
% 1.81/1.03  --prep_unflatten                        true
% 1.81/1.03  --prep_res_sim                          true
% 1.81/1.03  --prep_upred                            true
% 1.81/1.03  --prep_sem_filter                       exhaustive
% 1.81/1.03  --prep_sem_filter_out                   false
% 1.81/1.03  --pred_elim                             true
% 1.81/1.03  --res_sim_input                         true
% 1.81/1.03  --eq_ax_congr_red                       true
% 1.81/1.03  --pure_diseq_elim                       true
% 1.81/1.03  --brand_transform                       false
% 1.81/1.03  --non_eq_to_eq                          false
% 1.81/1.03  --prep_def_merge                        true
% 1.81/1.03  --prep_def_merge_prop_impl              false
% 1.81/1.03  --prep_def_merge_mbd                    true
% 1.81/1.03  --prep_def_merge_tr_red                 false
% 1.81/1.03  --prep_def_merge_tr_cl                  false
% 1.81/1.03  --smt_preprocessing                     true
% 1.81/1.03  --smt_ac_axioms                         fast
% 1.81/1.03  --preprocessed_out                      false
% 1.81/1.03  --preprocessed_stats                    false
% 1.81/1.03  
% 1.81/1.03  ------ Abstraction refinement Options
% 1.81/1.03  
% 1.81/1.03  --abstr_ref                             []
% 1.81/1.03  --abstr_ref_prep                        false
% 1.81/1.03  --abstr_ref_until_sat                   false
% 1.81/1.03  --abstr_ref_sig_restrict                funpre
% 1.81/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.81/1.03  --abstr_ref_under                       []
% 1.81/1.03  
% 1.81/1.03  ------ SAT Options
% 1.81/1.03  
% 1.81/1.03  --sat_mode                              false
% 1.81/1.03  --sat_fm_restart_options                ""
% 1.81/1.03  --sat_gr_def                            false
% 1.81/1.03  --sat_epr_types                         true
% 1.81/1.03  --sat_non_cyclic_types                  false
% 1.81/1.03  --sat_finite_models                     false
% 1.81/1.03  --sat_fm_lemmas                         false
% 1.81/1.03  --sat_fm_prep                           false
% 1.81/1.03  --sat_fm_uc_incr                        true
% 1.81/1.03  --sat_out_model                         small
% 1.81/1.03  --sat_out_clauses                       false
% 1.81/1.03  
% 1.81/1.03  ------ QBF Options
% 1.81/1.03  
% 1.81/1.03  --qbf_mode                              false
% 1.81/1.03  --qbf_elim_univ                         false
% 1.81/1.03  --qbf_dom_inst                          none
% 1.81/1.03  --qbf_dom_pre_inst                      false
% 1.81/1.03  --qbf_sk_in                             false
% 1.81/1.03  --qbf_pred_elim                         true
% 1.81/1.03  --qbf_split                             512
% 1.81/1.03  
% 1.81/1.03  ------ BMC1 Options
% 1.81/1.03  
% 1.81/1.03  --bmc1_incremental                      false
% 1.81/1.03  --bmc1_axioms                           reachable_all
% 1.81/1.03  --bmc1_min_bound                        0
% 1.81/1.03  --bmc1_max_bound                        -1
% 1.81/1.03  --bmc1_max_bound_default                -1
% 1.81/1.03  --bmc1_symbol_reachability              true
% 1.81/1.03  --bmc1_property_lemmas                  false
% 1.81/1.03  --bmc1_k_induction                      false
% 1.81/1.03  --bmc1_non_equiv_states                 false
% 1.81/1.03  --bmc1_deadlock                         false
% 1.81/1.03  --bmc1_ucm                              false
% 1.81/1.03  --bmc1_add_unsat_core                   none
% 1.81/1.03  --bmc1_unsat_core_children              false
% 1.81/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.81/1.03  --bmc1_out_stat                         full
% 1.81/1.03  --bmc1_ground_init                      false
% 1.81/1.03  --bmc1_pre_inst_next_state              false
% 1.81/1.03  --bmc1_pre_inst_state                   false
% 1.81/1.03  --bmc1_pre_inst_reach_state             false
% 1.81/1.03  --bmc1_out_unsat_core                   false
% 1.81/1.03  --bmc1_aig_witness_out                  false
% 1.81/1.03  --bmc1_verbose                          false
% 1.81/1.03  --bmc1_dump_clauses_tptp                false
% 1.81/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.81/1.03  --bmc1_dump_file                        -
% 1.81/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.81/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.81/1.03  --bmc1_ucm_extend_mode                  1
% 1.81/1.03  --bmc1_ucm_init_mode                    2
% 1.81/1.03  --bmc1_ucm_cone_mode                    none
% 1.81/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.81/1.03  --bmc1_ucm_relax_model                  4
% 1.81/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.81/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.81/1.03  --bmc1_ucm_layered_model                none
% 1.81/1.03  --bmc1_ucm_max_lemma_size               10
% 1.81/1.03  
% 1.81/1.03  ------ AIG Options
% 1.81/1.03  
% 1.81/1.03  --aig_mode                              false
% 1.81/1.03  
% 1.81/1.03  ------ Instantiation Options
% 1.81/1.03  
% 1.81/1.03  --instantiation_flag                    true
% 1.81/1.03  --inst_sos_flag                         false
% 1.81/1.03  --inst_sos_phase                        true
% 1.81/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.81/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.81/1.03  --inst_lit_sel_side                     none
% 1.81/1.03  --inst_solver_per_active                1400
% 1.81/1.03  --inst_solver_calls_frac                1.
% 1.81/1.03  --inst_passive_queue_type               priority_queues
% 1.81/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.81/1.03  --inst_passive_queues_freq              [25;2]
% 1.81/1.03  --inst_dismatching                      true
% 1.81/1.03  --inst_eager_unprocessed_to_passive     true
% 1.81/1.03  --inst_prop_sim_given                   true
% 1.81/1.03  --inst_prop_sim_new                     false
% 1.81/1.03  --inst_subs_new                         false
% 1.81/1.03  --inst_eq_res_simp                      false
% 1.81/1.03  --inst_subs_given                       false
% 1.81/1.03  --inst_orphan_elimination               true
% 1.81/1.03  --inst_learning_loop_flag               true
% 1.81/1.03  --inst_learning_start                   3000
% 1.81/1.03  --inst_learning_factor                  2
% 1.81/1.03  --inst_start_prop_sim_after_learn       3
% 1.81/1.03  --inst_sel_renew                        solver
% 1.81/1.03  --inst_lit_activity_flag                true
% 1.81/1.03  --inst_restr_to_given                   false
% 1.81/1.03  --inst_activity_threshold               500
% 1.81/1.03  --inst_out_proof                        true
% 1.81/1.03  
% 1.81/1.03  ------ Resolution Options
% 1.81/1.03  
% 1.81/1.03  --resolution_flag                       false
% 1.81/1.03  --res_lit_sel                           adaptive
% 1.81/1.03  --res_lit_sel_side                      none
% 1.81/1.03  --res_ordering                          kbo
% 1.81/1.03  --res_to_prop_solver                    active
% 1.81/1.03  --res_prop_simpl_new                    false
% 1.81/1.03  --res_prop_simpl_given                  true
% 1.81/1.03  --res_passive_queue_type                priority_queues
% 1.81/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.81/1.03  --res_passive_queues_freq               [15;5]
% 1.81/1.03  --res_forward_subs                      full
% 1.81/1.03  --res_backward_subs                     full
% 1.81/1.03  --res_forward_subs_resolution           true
% 1.81/1.03  --res_backward_subs_resolution          true
% 1.81/1.03  --res_orphan_elimination                true
% 1.81/1.03  --res_time_limit                        2.
% 1.81/1.03  --res_out_proof                         true
% 1.81/1.03  
% 1.81/1.03  ------ Superposition Options
% 1.81/1.03  
% 1.81/1.03  --superposition_flag                    true
% 1.81/1.03  --sup_passive_queue_type                priority_queues
% 1.81/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.81/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.81/1.03  --demod_completeness_check              fast
% 1.81/1.03  --demod_use_ground                      true
% 1.81/1.03  --sup_to_prop_solver                    passive
% 1.81/1.03  --sup_prop_simpl_new                    true
% 1.81/1.03  --sup_prop_simpl_given                  true
% 1.81/1.03  --sup_fun_splitting                     false
% 1.81/1.03  --sup_smt_interval                      50000
% 1.81/1.03  
% 1.81/1.03  ------ Superposition Simplification Setup
% 1.81/1.03  
% 1.81/1.03  --sup_indices_passive                   []
% 1.81/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.81/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.03  --sup_full_bw                           [BwDemod]
% 1.81/1.03  --sup_immed_triv                        [TrivRules]
% 1.81/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.81/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.03  --sup_immed_bw_main                     []
% 1.81/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.81/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/1.03  
% 1.81/1.03  ------ Combination Options
% 1.81/1.03  
% 1.81/1.03  --comb_res_mult                         3
% 1.81/1.03  --comb_sup_mult                         2
% 1.81/1.03  --comb_inst_mult                        10
% 1.81/1.03  
% 1.81/1.03  ------ Debug Options
% 1.81/1.03  
% 1.81/1.03  --dbg_backtrace                         false
% 1.81/1.03  --dbg_dump_prop_clauses                 false
% 1.81/1.03  --dbg_dump_prop_clauses_file            -
% 1.81/1.03  --dbg_out_stat                          false
% 1.81/1.03  
% 1.81/1.03  
% 1.81/1.03  
% 1.81/1.03  
% 1.81/1.03  ------ Proving...
% 1.81/1.03  
% 1.81/1.03  
% 1.81/1.03  % SZS status Theorem for theBenchmark.p
% 1.81/1.03  
% 1.81/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.81/1.03  
% 1.81/1.03  fof(f19,conjecture,(
% 1.81/1.03    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.03  
% 1.81/1.03  fof(f20,negated_conjecture,(
% 1.81/1.03    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.81/1.03    inference(negated_conjecture,[],[f19])).
% 1.81/1.03  
% 1.81/1.03  fof(f48,plain,(
% 1.81/1.03    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 1.81/1.03    inference(ennf_transformation,[],[f20])).
% 1.81/1.03  
% 1.81/1.03  fof(f49,plain,(
% 1.81/1.03    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 1.81/1.03    inference(flattening,[],[f48])).
% 1.81/1.03  
% 1.81/1.03  fof(f56,plain,(
% 1.81/1.03    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 1.81/1.03    introduced(choice_axiom,[])).
% 1.81/1.03  
% 1.81/1.03  fof(f55,plain,(
% 1.81/1.03    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 1.81/1.03    introduced(choice_axiom,[])).
% 1.81/1.03  
% 1.81/1.03  fof(f54,plain,(
% 1.81/1.03    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 1.81/1.03    introduced(choice_axiom,[])).
% 1.81/1.03  
% 1.81/1.03  fof(f57,plain,(
% 1.81/1.03    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 1.81/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f56,f55,f54])).
% 1.81/1.03  
% 1.81/1.03  fof(f92,plain,(
% 1.81/1.03    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.81/1.03    inference(cnf_transformation,[],[f57])).
% 1.81/1.03  
% 1.81/1.03  fof(f16,axiom,(
% 1.81/1.03    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.03  
% 1.81/1.03  fof(f43,plain,(
% 1.81/1.03    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.81/1.03    inference(ennf_transformation,[],[f16])).
% 1.81/1.03  
% 1.81/1.03  fof(f84,plain,(
% 1.81/1.03    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.81/1.03    inference(cnf_transformation,[],[f43])).
% 1.81/1.03  
% 1.81/1.03  fof(f89,plain,(
% 1.81/1.03    l1_struct_0(sK1)),
% 1.81/1.03    inference(cnf_transformation,[],[f57])).
% 1.81/1.03  
% 1.81/1.03  fof(f87,plain,(
% 1.81/1.03    l1_struct_0(sK0)),
% 1.81/1.03    inference(cnf_transformation,[],[f57])).
% 1.81/1.03  
% 1.81/1.03  fof(f11,axiom,(
% 1.81/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.03  
% 1.81/1.03  fof(f34,plain,(
% 1.81/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/1.03    inference(ennf_transformation,[],[f11])).
% 1.81/1.03  
% 1.81/1.03  fof(f74,plain,(
% 1.81/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.81/1.03    inference(cnf_transformation,[],[f34])).
% 1.81/1.03  
% 1.81/1.03  fof(f93,plain,(
% 1.81/1.03    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 1.81/1.03    inference(cnf_transformation,[],[f57])).
% 1.81/1.03  
% 1.81/1.03  fof(f2,axiom,(
% 1.81/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.03  
% 1.81/1.03  fof(f22,plain,(
% 1.81/1.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.81/1.03    inference(ennf_transformation,[],[f2])).
% 1.81/1.03  
% 1.81/1.03  fof(f61,plain,(
% 1.81/1.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.81/1.03    inference(cnf_transformation,[],[f22])).
% 1.81/1.03  
% 1.81/1.03  fof(f3,axiom,(
% 1.81/1.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.03  
% 1.81/1.03  fof(f62,plain,(
% 1.81/1.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.81/1.03    inference(cnf_transformation,[],[f3])).
% 1.81/1.03  
% 1.81/1.03  fof(f12,axiom,(
% 1.81/1.03    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.03  
% 1.81/1.03  fof(f35,plain,(
% 1.81/1.03    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.81/1.03    inference(ennf_transformation,[],[f12])).
% 1.81/1.03  
% 1.81/1.03  fof(f36,plain,(
% 1.81/1.03    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.81/1.03    inference(flattening,[],[f35])).
% 1.81/1.03  
% 1.81/1.03  fof(f76,plain,(
% 1.81/1.03    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.81/1.03    inference(cnf_transformation,[],[f36])).
% 1.81/1.03  
% 1.81/1.03  fof(f17,axiom,(
% 1.81/1.03    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.03  
% 1.81/1.03  fof(f44,plain,(
% 1.81/1.03    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.81/1.03    inference(ennf_transformation,[],[f17])).
% 1.81/1.03  
% 1.81/1.03  fof(f45,plain,(
% 1.81/1.03    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.81/1.03    inference(flattening,[],[f44])).
% 1.81/1.03  
% 1.81/1.03  fof(f85,plain,(
% 1.81/1.03    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.81/1.03    inference(cnf_transformation,[],[f45])).
% 1.81/1.03  
% 1.81/1.03  fof(f88,plain,(
% 1.81/1.03    ~v2_struct_0(sK1)),
% 1.81/1.03    inference(cnf_transformation,[],[f57])).
% 1.81/1.03  
% 1.81/1.03  fof(f13,axiom,(
% 1.81/1.03    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.03  
% 1.81/1.03  fof(f37,plain,(
% 1.81/1.03    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.81/1.03    inference(ennf_transformation,[],[f13])).
% 1.81/1.03  
% 1.81/1.03  fof(f38,plain,(
% 1.81/1.03    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.81/1.03    inference(flattening,[],[f37])).
% 1.81/1.03  
% 1.81/1.03  fof(f52,plain,(
% 1.81/1.03    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.81/1.03    inference(nnf_transformation,[],[f38])).
% 1.81/1.03  
% 1.81/1.03  fof(f77,plain,(
% 1.81/1.03    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.81/1.03    inference(cnf_transformation,[],[f52])).
% 1.81/1.03  
% 1.81/1.03  fof(f10,axiom,(
% 1.81/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.03  
% 1.81/1.03  fof(f21,plain,(
% 1.81/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.81/1.03    inference(pure_predicate_removal,[],[f10])).
% 1.81/1.03  
% 1.81/1.03  fof(f33,plain,(
% 1.81/1.03    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/1.03    inference(ennf_transformation,[],[f21])).
% 1.81/1.03  
% 1.81/1.03  fof(f73,plain,(
% 1.81/1.03    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.81/1.03    inference(cnf_transformation,[],[f33])).
% 1.81/1.03  
% 1.81/1.03  fof(f90,plain,(
% 1.81/1.03    v1_funct_1(sK2)),
% 1.81/1.03    inference(cnf_transformation,[],[f57])).
% 1.81/1.03  
% 1.81/1.03  fof(f91,plain,(
% 1.81/1.03    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.81/1.03    inference(cnf_transformation,[],[f57])).
% 1.81/1.03  
% 1.81/1.03  fof(f15,axiom,(
% 1.81/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.03  
% 1.81/1.03  fof(f41,plain,(
% 1.81/1.03    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.81/1.03    inference(ennf_transformation,[],[f15])).
% 1.81/1.03  
% 1.81/1.03  fof(f42,plain,(
% 1.81/1.03    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.81/1.03    inference(flattening,[],[f41])).
% 1.81/1.03  
% 1.81/1.03  fof(f83,plain,(
% 1.81/1.03    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.81/1.03    inference(cnf_transformation,[],[f42])).
% 1.81/1.03  
% 1.81/1.03  fof(f94,plain,(
% 1.81/1.03    v2_funct_1(sK2)),
% 1.81/1.03    inference(cnf_transformation,[],[f57])).
% 1.81/1.03  
% 1.81/1.03  fof(f7,axiom,(
% 1.81/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.03  
% 1.81/1.03  fof(f27,plain,(
% 1.81/1.03    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.81/1.03    inference(ennf_transformation,[],[f7])).
% 1.81/1.03  
% 1.81/1.03  fof(f28,plain,(
% 1.81/1.03    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.81/1.03    inference(flattening,[],[f27])).
% 1.81/1.03  
% 1.81/1.03  fof(f69,plain,(
% 1.81/1.03    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/1.03    inference(cnf_transformation,[],[f28])).
% 1.81/1.03  
% 1.81/1.03  fof(f18,axiom,(
% 1.81/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.03  
% 1.81/1.03  fof(f46,plain,(
% 1.81/1.03    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.81/1.03    inference(ennf_transformation,[],[f18])).
% 1.81/1.03  
% 1.81/1.03  fof(f47,plain,(
% 1.81/1.03    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.81/1.03    inference(flattening,[],[f46])).
% 1.81/1.03  
% 1.81/1.03  fof(f86,plain,(
% 1.81/1.03    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.81/1.03    inference(cnf_transformation,[],[f47])).
% 1.81/1.03  
% 1.81/1.03  fof(f9,axiom,(
% 1.81/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.03  
% 1.81/1.03  fof(f31,plain,(
% 1.81/1.03    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.81/1.03    inference(ennf_transformation,[],[f9])).
% 1.81/1.03  
% 1.81/1.03  fof(f32,plain,(
% 1.81/1.03    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.81/1.03    inference(flattening,[],[f31])).
% 1.81/1.03  
% 1.81/1.03  fof(f72,plain,(
% 1.81/1.03    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/1.03    inference(cnf_transformation,[],[f32])).
% 1.81/1.03  
% 1.81/1.03  fof(f4,axiom,(
% 1.81/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.03  
% 1.81/1.03  fof(f23,plain,(
% 1.81/1.03    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.81/1.03    inference(ennf_transformation,[],[f4])).
% 1.81/1.03  
% 1.81/1.03  fof(f24,plain,(
% 1.81/1.03    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.81/1.03    inference(flattening,[],[f23])).
% 1.81/1.03  
% 1.81/1.03  fof(f64,plain,(
% 1.81/1.03    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/1.03    inference(cnf_transformation,[],[f24])).
% 1.81/1.03  
% 1.81/1.03  fof(f5,axiom,(
% 1.81/1.03    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.03  
% 1.81/1.03  fof(f66,plain,(
% 1.81/1.03    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.81/1.03    inference(cnf_transformation,[],[f5])).
% 1.81/1.03  
% 1.81/1.03  fof(f82,plain,(
% 1.81/1.03    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.81/1.03    inference(cnf_transformation,[],[f42])).
% 1.81/1.03  
% 1.81/1.03  fof(f1,axiom,(
% 1.81/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.03  
% 1.81/1.03  fof(f50,plain,(
% 1.81/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/1.03    inference(nnf_transformation,[],[f1])).
% 1.81/1.03  
% 1.81/1.03  fof(f51,plain,(
% 1.81/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/1.03    inference(flattening,[],[f50])).
% 1.81/1.03  
% 1.81/1.03  fof(f59,plain,(
% 1.81/1.03    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.81/1.03    inference(cnf_transformation,[],[f51])).
% 1.81/1.03  
% 1.81/1.03  fof(f96,plain,(
% 1.81/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.81/1.03    inference(equality_resolution,[],[f59])).
% 1.81/1.03  
% 1.81/1.03  fof(f6,axiom,(
% 1.81/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 1.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.03  
% 1.81/1.03  fof(f25,plain,(
% 1.81/1.03    ! [X0] : (! [X1] : ((v2_funct_1(X1) | (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.81/1.03    inference(ennf_transformation,[],[f6])).
% 1.81/1.03  
% 1.81/1.03  fof(f26,plain,(
% 1.81/1.03    ! [X0] : (! [X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.81/1.03    inference(flattening,[],[f25])).
% 1.81/1.03  
% 1.81/1.03  fof(f67,plain,(
% 1.81/1.03    ( ! [X0,X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/1.03    inference(cnf_transformation,[],[f26])).
% 1.81/1.03  
% 1.81/1.03  fof(f63,plain,(
% 1.81/1.03    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/1.03    inference(cnf_transformation,[],[f24])).
% 1.81/1.03  
% 1.81/1.03  fof(f8,axiom,(
% 1.81/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 1.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.03  
% 1.81/1.03  fof(f29,plain,(
% 1.81/1.03    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.81/1.03    inference(ennf_transformation,[],[f8])).
% 1.81/1.03  
% 1.81/1.03  fof(f30,plain,(
% 1.81/1.03    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.81/1.03    inference(flattening,[],[f29])).
% 1.81/1.03  
% 1.81/1.03  fof(f71,plain,(
% 1.81/1.03    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.81/1.03    inference(cnf_transformation,[],[f30])).
% 1.81/1.03  
% 1.81/1.03  fof(f14,axiom,(
% 1.81/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.03  
% 1.81/1.03  fof(f39,plain,(
% 1.81/1.03    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.81/1.03    inference(ennf_transformation,[],[f14])).
% 1.81/1.03  
% 1.81/1.03  fof(f40,plain,(
% 1.81/1.03    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.81/1.03    inference(flattening,[],[f39])).
% 1.81/1.03  
% 1.81/1.03  fof(f53,plain,(
% 1.81/1.03    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.81/1.03    inference(nnf_transformation,[],[f40])).
% 1.81/1.03  
% 1.81/1.03  fof(f80,plain,(
% 1.81/1.03    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.81/1.03    inference(cnf_transformation,[],[f53])).
% 1.81/1.03  
% 1.81/1.03  fof(f99,plain,(
% 1.81/1.03    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.81/1.03    inference(equality_resolution,[],[f80])).
% 1.81/1.03  
% 1.81/1.03  fof(f95,plain,(
% 1.81/1.03    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 1.81/1.03    inference(cnf_transformation,[],[f57])).
% 1.81/1.03  
% 1.81/1.03  cnf(c_32,negated_conjecture,
% 1.81/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 1.81/1.03      inference(cnf_transformation,[],[f92]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1193,plain,
% 1.81/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_26,plain,
% 1.81/1.03      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.81/1.03      inference(cnf_transformation,[],[f84]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_35,negated_conjecture,
% 1.81/1.03      ( l1_struct_0(sK1) ),
% 1.81/1.03      inference(cnf_transformation,[],[f89]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_419,plain,
% 1.81/1.03      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 1.81/1.03      inference(resolution_lifted,[status(thm)],[c_26,c_35]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_420,plain,
% 1.81/1.03      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.81/1.03      inference(unflattening,[status(thm)],[c_419]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_37,negated_conjecture,
% 1.81/1.03      ( l1_struct_0(sK0) ),
% 1.81/1.03      inference(cnf_transformation,[],[f87]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_424,plain,
% 1.81/1.03      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 1.81/1.03      inference(resolution_lifted,[status(thm)],[c_26,c_37]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_425,plain,
% 1.81/1.03      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.81/1.03      inference(unflattening,[status(thm)],[c_424]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1236,plain,
% 1.81/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 1.81/1.03      inference(light_normalisation,[status(thm)],[c_1193,c_420,c_425]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_16,plain,
% 1.81/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.81/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.81/1.03      inference(cnf_transformation,[],[f74]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1199,plain,
% 1.81/1.03      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.81/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1741,plain,
% 1.81/1.03      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 1.81/1.03      inference(superposition,[status(thm)],[c_1236,c_1199]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_31,negated_conjecture,
% 1.81/1.03      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 1.81/1.03      inference(cnf_transformation,[],[f93]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1233,plain,
% 1.81/1.03      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 1.81/1.03      inference(light_normalisation,[status(thm)],[c_31,c_420,c_425]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1743,plain,
% 1.81/1.03      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 1.81/1.03      inference(demodulation,[status(thm)],[c_1741,c_1233]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1793,plain,
% 1.81/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 1.81/1.03      inference(demodulation,[status(thm)],[c_1743,c_1236]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_3,plain,
% 1.81/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.81/1.03      | ~ v1_relat_1(X1)
% 1.81/1.03      | v1_relat_1(X0) ),
% 1.81/1.03      inference(cnf_transformation,[],[f61]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1211,plain,
% 1.81/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.81/1.03      | v1_relat_1(X1) != iProver_top
% 1.81/1.03      | v1_relat_1(X0) = iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_2083,plain,
% 1.81/1.03      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) != iProver_top
% 1.81/1.03      | v1_relat_1(sK2) = iProver_top ),
% 1.81/1.03      inference(superposition,[status(thm)],[c_1793,c_1211]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_43,plain,
% 1.81/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1459,plain,
% 1.81/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.81/1.03      | v1_relat_1(X0)
% 1.81/1.03      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 1.81/1.03      inference(instantiation,[status(thm)],[c_3]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1829,plain,
% 1.81/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.81/1.03      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 1.81/1.03      | v1_relat_1(sK2) ),
% 1.81/1.03      inference(instantiation,[status(thm)],[c_1459]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1830,plain,
% 1.81/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 1.81/1.03      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 1.81/1.03      | v1_relat_1(sK2) = iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_1829]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_4,plain,
% 1.81/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.81/1.03      inference(cnf_transformation,[],[f62]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1869,plain,
% 1.81/1.03      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 1.81/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1870,plain,
% 1.81/1.03      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_1869]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_2227,plain,
% 1.81/1.03      ( v1_relat_1(sK2) = iProver_top ),
% 1.81/1.03      inference(global_propositional_subsumption,
% 1.81/1.03                [status(thm)],
% 1.81/1.03                [c_2083,c_43,c_1830,c_1870]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_17,plain,
% 1.81/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 1.81/1.03      | v1_partfun1(X0,X1)
% 1.81/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.81/1.03      | v1_xboole_0(X2)
% 1.81/1.03      | ~ v1_funct_1(X0) ),
% 1.81/1.03      inference(cnf_transformation,[],[f76]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_27,plain,
% 1.81/1.03      ( v2_struct_0(X0)
% 1.81/1.03      | ~ l1_struct_0(X0)
% 1.81/1.03      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 1.81/1.03      inference(cnf_transformation,[],[f85]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_36,negated_conjecture,
% 1.81/1.03      ( ~ v2_struct_0(sK1) ),
% 1.81/1.03      inference(cnf_transformation,[],[f88]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_406,plain,
% 1.81/1.03      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 1.81/1.03      inference(resolution_lifted,[status(thm)],[c_27,c_36]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_407,plain,
% 1.81/1.03      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 1.81/1.03      inference(unflattening,[status(thm)],[c_406]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_50,plain,
% 1.81/1.03      ( v2_struct_0(sK1)
% 1.81/1.03      | ~ l1_struct_0(sK1)
% 1.81/1.03      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 1.81/1.03      inference(instantiation,[status(thm)],[c_27]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_409,plain,
% 1.81/1.03      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 1.81/1.03      inference(global_propositional_subsumption,
% 1.81/1.03                [status(thm)],
% 1.81/1.03                [c_407,c_36,c_35,c_50]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_431,plain,
% 1.81/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 1.81/1.03      | v1_partfun1(X0,X1)
% 1.81/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.81/1.03      | ~ v1_funct_1(X0)
% 1.81/1.03      | k2_struct_0(sK1) != X2 ),
% 1.81/1.03      inference(resolution_lifted,[status(thm)],[c_17,c_409]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_432,plain,
% 1.81/1.03      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 1.81/1.03      | v1_partfun1(X0,X1)
% 1.81/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 1.81/1.03      | ~ v1_funct_1(X0) ),
% 1.81/1.03      inference(unflattening,[status(thm)],[c_431]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_20,plain,
% 1.81/1.03      ( ~ v1_partfun1(X0,X1)
% 1.81/1.03      | ~ v4_relat_1(X0,X1)
% 1.81/1.03      | ~ v1_relat_1(X0)
% 1.81/1.03      | k1_relat_1(X0) = X1 ),
% 1.81/1.03      inference(cnf_transformation,[],[f77]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_493,plain,
% 1.81/1.03      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 1.81/1.03      | ~ v4_relat_1(X0,X1)
% 1.81/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 1.81/1.03      | ~ v1_funct_1(X0)
% 1.81/1.03      | ~ v1_relat_1(X0)
% 1.81/1.03      | k1_relat_1(X0) = X1 ),
% 1.81/1.03      inference(resolution,[status(thm)],[c_432,c_20]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_15,plain,
% 1.81/1.03      ( v4_relat_1(X0,X1)
% 1.81/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.81/1.03      inference(cnf_transformation,[],[f73]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_509,plain,
% 1.81/1.03      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 1.81/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 1.81/1.03      | ~ v1_funct_1(X0)
% 1.81/1.03      | ~ v1_relat_1(X0)
% 1.81/1.03      | k1_relat_1(X0) = X1 ),
% 1.81/1.03      inference(forward_subsumption_resolution,
% 1.81/1.03                [status(thm)],
% 1.81/1.03                [c_493,c_15]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1190,plain,
% 1.81/1.03      ( k1_relat_1(X0) = X1
% 1.81/1.03      | v1_funct_2(X0,X1,k2_struct_0(sK1)) != iProver_top
% 1.81/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1)))) != iProver_top
% 1.81/1.03      | v1_funct_1(X0) != iProver_top
% 1.81/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1641,plain,
% 1.81/1.03      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 1.81/1.03      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 1.81/1.03      | v1_funct_1(sK2) != iProver_top
% 1.81/1.03      | v1_relat_1(sK2) != iProver_top ),
% 1.81/1.03      inference(superposition,[status(thm)],[c_1236,c_1190]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_34,negated_conjecture,
% 1.81/1.03      ( v1_funct_1(sK2) ),
% 1.81/1.03      inference(cnf_transformation,[],[f90]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_41,plain,
% 1.81/1.03      ( v1_funct_1(sK2) = iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_33,negated_conjecture,
% 1.81/1.03      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 1.81/1.03      inference(cnf_transformation,[],[f91]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1192,plain,
% 1.81/1.03      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1230,plain,
% 1.81/1.03      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 1.81/1.03      inference(light_normalisation,[status(thm)],[c_1192,c_420,c_425]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1720,plain,
% 1.81/1.03      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 1.81/1.03      | v1_relat_1(sK2) != iProver_top ),
% 1.81/1.03      inference(global_propositional_subsumption,
% 1.81/1.03                [status(thm)],
% 1.81/1.03                [c_1641,c_41,c_1230]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_2232,plain,
% 1.81/1.03      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 1.81/1.03      inference(superposition,[status(thm)],[c_2227,c_1720]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1790,plain,
% 1.81/1.03      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 1.81/1.03      inference(demodulation,[status(thm)],[c_1743,c_1741]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_2236,plain,
% 1.81/1.03      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 1.81/1.03      inference(demodulation,[status(thm)],[c_2232,c_1790]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_23,plain,
% 1.81/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 1.81/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.81/1.03      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.81/1.03      | ~ v2_funct_1(X0)
% 1.81/1.03      | ~ v1_funct_1(X0)
% 1.81/1.03      | k2_relset_1(X1,X2,X0) != X2 ),
% 1.81/1.03      inference(cnf_transformation,[],[f83]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1198,plain,
% 1.81/1.03      ( k2_relset_1(X0,X1,X2) != X1
% 1.81/1.03      | v1_funct_2(X2,X0,X1) != iProver_top
% 1.81/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.81/1.03      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 1.81/1.03      | v2_funct_1(X2) != iProver_top
% 1.81/1.03      | v1_funct_1(X2) != iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_3364,plain,
% 1.81/1.03      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 1.81/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 1.81/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 1.81/1.03      | v2_funct_1(sK2) != iProver_top
% 1.81/1.03      | v1_funct_1(sK2) != iProver_top ),
% 1.81/1.03      inference(superposition,[status(thm)],[c_2236,c_1198]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_30,negated_conjecture,
% 1.81/1.03      ( v2_funct_1(sK2) ),
% 1.81/1.03      inference(cnf_transformation,[],[f94]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_44,plain,
% 1.81/1.03      ( v2_funct_1(sK2) = iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_2235,plain,
% 1.81/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 1.81/1.03      inference(demodulation,[status(thm)],[c_2232,c_1793]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1794,plain,
% 1.81/1.03      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 1.81/1.03      inference(demodulation,[status(thm)],[c_1743,c_1230]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_2237,plain,
% 1.81/1.03      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 1.81/1.03      inference(demodulation,[status(thm)],[c_2232,c_1794]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_3775,plain,
% 1.81/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 1.81/1.03      inference(global_propositional_subsumption,
% 1.81/1.03                [status(thm)],
% 1.81/1.03                [c_3364,c_41,c_44,c_2235,c_2237]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_3781,plain,
% 1.81/1.03      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 1.81/1.03      inference(superposition,[status(thm)],[c_3775,c_1199]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1194,plain,
% 1.81/1.03      ( v2_funct_1(sK2) = iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_10,plain,
% 1.81/1.03      ( ~ v2_funct_1(X0)
% 1.81/1.03      | ~ v1_funct_1(X0)
% 1.81/1.03      | ~ v1_relat_1(X0)
% 1.81/1.03      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 1.81/1.03      inference(cnf_transformation,[],[f69]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1204,plain,
% 1.81/1.03      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 1.81/1.03      | v2_funct_1(X0) != iProver_top
% 1.81/1.03      | v1_funct_1(X0) != iProver_top
% 1.81/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_2733,plain,
% 1.81/1.03      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 1.81/1.03      | v1_funct_1(sK2) != iProver_top
% 1.81/1.03      | v1_relat_1(sK2) != iProver_top ),
% 1.81/1.03      inference(superposition,[status(thm)],[c_1194,c_1204]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1486,plain,
% 1.81/1.03      ( ~ v2_funct_1(sK2)
% 1.81/1.03      | ~ v1_funct_1(sK2)
% 1.81/1.03      | ~ v1_relat_1(sK2)
% 1.81/1.03      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.81/1.03      inference(instantiation,[status(thm)],[c_10]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_2911,plain,
% 1.81/1.03      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.81/1.03      inference(global_propositional_subsumption,
% 1.81/1.03                [status(thm)],
% 1.81/1.03                [c_2733,c_34,c_32,c_30,c_1486,c_1829,c_1869]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_3783,plain,
% 1.81/1.03      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.81/1.03      inference(light_normalisation,[status(thm)],[c_3781,c_2911]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_28,plain,
% 1.81/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 1.81/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.81/1.03      | ~ v2_funct_1(X0)
% 1.81/1.03      | ~ v1_funct_1(X0)
% 1.81/1.03      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 1.81/1.03      | k2_relset_1(X1,X2,X0) != X2 ),
% 1.81/1.03      inference(cnf_transformation,[],[f86]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1195,plain,
% 1.81/1.03      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
% 1.81/1.03      | k2_relset_1(X0,X1,X2) != X1
% 1.81/1.03      | v1_funct_2(X2,X0,X1) != iProver_top
% 1.81/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.81/1.03      | v2_funct_1(X2) != iProver_top
% 1.81/1.03      | v1_funct_1(X2) != iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_3880,plain,
% 1.81/1.03      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 1.81/1.03      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 1.81/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 1.81/1.03      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.81/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 1.81/1.03      inference(superposition,[status(thm)],[c_3783,c_1195]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_14,plain,
% 1.81/1.03      ( ~ v2_funct_1(X0)
% 1.81/1.03      | ~ v1_funct_1(X0)
% 1.81/1.03      | ~ v1_relat_1(X0)
% 1.81/1.03      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 1.81/1.03      inference(cnf_transformation,[],[f72]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1200,plain,
% 1.81/1.03      ( k2_funct_1(k2_funct_1(X0)) = X0
% 1.81/1.03      | v2_funct_1(X0) != iProver_top
% 1.81/1.03      | v1_funct_1(X0) != iProver_top
% 1.81/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_2614,plain,
% 1.81/1.03      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 1.81/1.03      | v1_funct_1(sK2) != iProver_top
% 1.81/1.03      | v1_relat_1(sK2) != iProver_top ),
% 1.81/1.03      inference(superposition,[status(thm)],[c_1194,c_1200]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1507,plain,
% 1.81/1.03      ( ~ v2_funct_1(sK2)
% 1.81/1.03      | ~ v1_funct_1(sK2)
% 1.81/1.03      | ~ v1_relat_1(sK2)
% 1.81/1.03      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 1.81/1.03      inference(instantiation,[status(thm)],[c_14]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_2831,plain,
% 1.81/1.03      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 1.81/1.03      inference(global_propositional_subsumption,
% 1.81/1.03                [status(thm)],
% 1.81/1.03                [c_2614,c_34,c_32,c_30,c_1507,c_1829,c_1869]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_3886,plain,
% 1.81/1.03      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 1.81/1.03      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 1.81/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 1.81/1.03      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.81/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 1.81/1.03      inference(light_normalisation,[status(thm)],[c_3880,c_2831]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_5,plain,
% 1.81/1.03      ( ~ v1_funct_1(X0)
% 1.81/1.03      | v1_funct_1(k2_funct_1(X0))
% 1.81/1.03      | ~ v1_relat_1(X0) ),
% 1.81/1.03      inference(cnf_transformation,[],[f64]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1453,plain,
% 1.81/1.03      ( v1_funct_1(k2_funct_1(sK2))
% 1.81/1.03      | ~ v1_funct_1(sK2)
% 1.81/1.03      | ~ v1_relat_1(sK2) ),
% 1.81/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1454,plain,
% 1.81/1.03      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 1.81/1.03      | v1_funct_1(sK2) != iProver_top
% 1.81/1.03      | v1_relat_1(sK2) != iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_1453]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_7,plain,
% 1.81/1.03      ( v2_funct_1(k6_relat_1(X0)) ),
% 1.81/1.03      inference(cnf_transformation,[],[f66]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_2378,plain,
% 1.81/1.03      ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) ),
% 1.81/1.03      inference(instantiation,[status(thm)],[c_7]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_2379,plain,
% 1.81/1.03      ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) = iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_2378]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_24,plain,
% 1.81/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 1.81/1.03      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 1.81/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.81/1.03      | ~ v2_funct_1(X0)
% 1.81/1.03      | ~ v1_funct_1(X0)
% 1.81/1.03      | k2_relset_1(X1,X2,X0) != X2 ),
% 1.81/1.03      inference(cnf_transformation,[],[f82]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1197,plain,
% 1.81/1.03      ( k2_relset_1(X0,X1,X2) != X1
% 1.81/1.03      | v1_funct_2(X2,X0,X1) != iProver_top
% 1.81/1.03      | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
% 1.81/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.81/1.03      | v2_funct_1(X2) != iProver_top
% 1.81/1.03      | v1_funct_1(X2) != iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_3197,plain,
% 1.81/1.03      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 1.81/1.03      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 1.81/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 1.81/1.03      | v2_funct_1(sK2) != iProver_top
% 1.81/1.03      | v1_funct_1(sK2) != iProver_top ),
% 1.81/1.03      inference(superposition,[status(thm)],[c_2236,c_1197]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1,plain,
% 1.81/1.03      ( r1_tarski(X0,X0) ),
% 1.81/1.03      inference(cnf_transformation,[],[f96]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1212,plain,
% 1.81/1.03      ( r1_tarski(X0,X0) = iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_9,plain,
% 1.81/1.03      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 1.81/1.03      | v2_funct_1(X0)
% 1.81/1.03      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 1.81/1.03      | ~ v1_funct_1(X1)
% 1.81/1.03      | ~ v1_funct_1(X0)
% 1.81/1.03      | ~ v1_relat_1(X1)
% 1.81/1.03      | ~ v1_relat_1(X0) ),
% 1.81/1.03      inference(cnf_transformation,[],[f67]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1205,plain,
% 1.81/1.03      ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 1.81/1.03      | v2_funct_1(X0) = iProver_top
% 1.81/1.03      | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
% 1.81/1.03      | v1_funct_1(X0) != iProver_top
% 1.81/1.03      | v1_funct_1(X1) != iProver_top
% 1.81/1.03      | v1_relat_1(X0) != iProver_top
% 1.81/1.03      | v1_relat_1(X1) != iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_3321,plain,
% 1.81/1.03      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) != iProver_top
% 1.81/1.03      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) != iProver_top
% 1.81/1.03      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 1.81/1.03      | v1_funct_1(X0) != iProver_top
% 1.81/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.81/1.03      | v1_relat_1(X0) != iProver_top
% 1.81/1.03      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 1.81/1.03      inference(superposition,[status(thm)],[c_2911,c_1205]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_6,plain,
% 1.81/1.03      ( ~ v1_funct_1(X0)
% 1.81/1.03      | ~ v1_relat_1(X0)
% 1.81/1.03      | v1_relat_1(k2_funct_1(X0)) ),
% 1.81/1.03      inference(cnf_transformation,[],[f63]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1456,plain,
% 1.81/1.03      ( ~ v1_funct_1(sK2)
% 1.81/1.03      | v1_relat_1(k2_funct_1(sK2))
% 1.81/1.03      | ~ v1_relat_1(sK2) ),
% 1.81/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1457,plain,
% 1.81/1.03      ( v1_funct_1(sK2) != iProver_top
% 1.81/1.03      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 1.81/1.03      | v1_relat_1(sK2) != iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_1456]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_3560,plain,
% 1.81/1.03      ( v1_relat_1(X0) != iProver_top
% 1.81/1.03      | r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) != iProver_top
% 1.81/1.03      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) != iProver_top
% 1.81/1.03      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 1.81/1.03      | v1_funct_1(X0) != iProver_top ),
% 1.81/1.03      inference(global_propositional_subsumption,
% 1.81/1.03                [status(thm)],
% 1.81/1.03                [c_3321,c_41,c_43,c_1454,c_1457,c_1830,c_1870]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_3561,plain,
% 1.81/1.03      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(X0)) != iProver_top
% 1.81/1.03      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) != iProver_top
% 1.81/1.03      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 1.81/1.03      | v1_funct_1(X0) != iProver_top
% 1.81/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.81/1.03      inference(renaming,[status(thm)],[c_3560]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_3571,plain,
% 1.81/1.03      ( v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
% 1.81/1.03      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 1.81/1.03      | v1_funct_1(sK2) != iProver_top
% 1.81/1.03      | v1_relat_1(sK2) != iProver_top ),
% 1.81/1.03      inference(superposition,[status(thm)],[c_1212,c_3561]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_12,plain,
% 1.81/1.03      ( ~ v2_funct_1(X0)
% 1.81/1.03      | ~ v1_funct_1(X0)
% 1.81/1.03      | ~ v1_relat_1(X0)
% 1.81/1.03      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
% 1.81/1.03      inference(cnf_transformation,[],[f71]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1202,plain,
% 1.81/1.03      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
% 1.81/1.03      | v2_funct_1(X0) != iProver_top
% 1.81/1.03      | v1_funct_1(X0) != iProver_top
% 1.81/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_3205,plain,
% 1.81/1.03      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
% 1.81/1.03      | v1_funct_1(sK2) != iProver_top
% 1.81/1.03      | v1_relat_1(sK2) != iProver_top ),
% 1.81/1.03      inference(superposition,[status(thm)],[c_1194,c_1202]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1518,plain,
% 1.81/1.03      ( ~ v2_funct_1(sK2)
% 1.81/1.03      | ~ v1_funct_1(sK2)
% 1.81/1.03      | ~ v1_relat_1(sK2)
% 1.81/1.03      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
% 1.81/1.03      inference(instantiation,[status(thm)],[c_12]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_3492,plain,
% 1.81/1.03      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
% 1.81/1.03      inference(global_propositional_subsumption,
% 1.81/1.03                [status(thm)],
% 1.81/1.03                [c_3205,c_34,c_32,c_30,c_1518,c_1829,c_1869]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_3587,plain,
% 1.81/1.03      ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top
% 1.81/1.03      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 1.81/1.03      | v1_funct_1(sK2) != iProver_top
% 1.81/1.03      | v1_relat_1(sK2) != iProver_top ),
% 1.81/1.03      inference(light_normalisation,[status(thm)],[c_3571,c_3492]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_4085,plain,
% 1.81/1.03      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 1.81/1.03      inference(global_propositional_subsumption,
% 1.81/1.03                [status(thm)],
% 1.81/1.03                [c_3886,c_41,c_43,c_44,c_1454,c_1830,c_1870,c_2235,
% 1.81/1.03                 c_2237,c_2379,c_3197,c_3364,c_3587]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_21,plain,
% 1.81/1.03      ( r2_funct_2(X0,X1,X2,X2)
% 1.81/1.03      | ~ v1_funct_2(X2,X0,X1)
% 1.81/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.81/1.03      | ~ v1_funct_1(X2) ),
% 1.81/1.03      inference(cnf_transformation,[],[f99]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_29,negated_conjecture,
% 1.81/1.03      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 1.81/1.03      inference(cnf_transformation,[],[f95]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_528,plain,
% 1.81/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 1.81/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.81/1.03      | ~ v1_funct_1(X0)
% 1.81/1.03      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 1.81/1.03      | u1_struct_0(sK1) != X2
% 1.81/1.03      | u1_struct_0(sK0) != X1
% 1.81/1.03      | sK2 != X0 ),
% 1.81/1.03      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_529,plain,
% 1.81/1.03      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 1.81/1.03      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.81/1.03      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 1.81/1.03      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 1.81/1.03      inference(unflattening,[status(thm)],[c_528]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1189,plain,
% 1.81/1.03      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 1.81/1.03      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 1.81/1.03      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 1.81/1.03      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 1.81/1.03      inference(predicate_to_equality,[status(thm)],[c_529]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1379,plain,
% 1.81/1.03      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 1.81/1.03      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 1.81/1.03      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 1.81/1.03      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 1.81/1.03      inference(light_normalisation,[status(thm)],[c_1189,c_420,c_425]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1792,plain,
% 1.81/1.03      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 1.81/1.03      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 1.81/1.03      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 1.81/1.03      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 1.81/1.03      inference(demodulation,[status(thm)],[c_1743,c_1379]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_2234,plain,
% 1.81/1.03      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
% 1.81/1.03      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 1.81/1.03      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 1.81/1.03      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
% 1.81/1.03      inference(demodulation,[status(thm)],[c_2232,c_1792]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1943,plain,
% 1.81/1.03      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 1.81/1.03      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 1.81/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 1.81/1.03      | v2_funct_1(sK2) != iProver_top
% 1.81/1.03      | v1_funct_1(sK2) != iProver_top ),
% 1.81/1.03      inference(superposition,[status(thm)],[c_1790,c_1195]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_3040,plain,
% 1.81/1.03      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 1.81/1.03      inference(global_propositional_subsumption,
% 1.81/1.03                [status(thm)],
% 1.81/1.03                [c_1943,c_41,c_44,c_1793,c_1794]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_3042,plain,
% 1.81/1.03      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 1.81/1.03      inference(light_normalisation,[status(thm)],[c_3040,c_2232]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_3093,plain,
% 1.81/1.03      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 1.81/1.03      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 1.81/1.03      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 1.81/1.03      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 1.81/1.03      inference(light_normalisation,[status(thm)],[c_2234,c_3042]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_4088,plain,
% 1.81/1.03      ( sK2 != sK2
% 1.81/1.03      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 1.81/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 1.81/1.03      | v1_funct_1(sK2) != iProver_top ),
% 1.81/1.03      inference(demodulation,[status(thm)],[c_4085,c_3093]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_721,plain,( X0 = X0 ),theory(equality) ).
% 1.81/1.03  
% 1.81/1.03  cnf(c_1662,plain,
% 1.81/1.03      ( sK2 = sK2 ),
% 1.81/1.03      inference(instantiation,[status(thm)],[c_721]) ).
% 1.81/1.03  
% 1.81/1.03  cnf(contradiction,plain,
% 1.81/1.03      ( $false ),
% 1.81/1.03      inference(minisat,[status(thm)],[c_4088,c_2237,c_2235,c_1662,c_41]) ).
% 1.81/1.03  
% 1.81/1.03  
% 1.81/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.81/1.03  
% 1.81/1.03  ------                               Statistics
% 1.81/1.03  
% 1.81/1.03  ------ General
% 1.81/1.03  
% 1.81/1.03  abstr_ref_over_cycles:                  0
% 1.81/1.03  abstr_ref_under_cycles:                 0
% 1.81/1.03  gc_basic_clause_elim:                   0
% 1.81/1.03  forced_gc_time:                         0
% 1.81/1.03  parsing_time:                           0.021
% 1.81/1.03  unif_index_cands_time:                  0.
% 1.81/1.03  unif_index_add_time:                    0.
% 1.81/1.03  orderings_time:                         0.
% 1.81/1.03  out_proof_time:                         0.012
% 1.81/1.03  total_time:                             0.239
% 1.81/1.03  num_of_symbols:                         57
% 1.81/1.03  num_of_terms:                           3597
% 1.81/1.03  
% 1.81/1.03  ------ Preprocessing
% 1.81/1.03  
% 1.81/1.03  num_of_splits:                          0
% 1.81/1.03  num_of_split_atoms:                     0
% 1.81/1.03  num_of_reused_defs:                     0
% 1.81/1.03  num_eq_ax_congr_red:                    2
% 1.81/1.03  num_of_sem_filtered_clauses:            1
% 1.81/1.03  num_of_subtypes:                        0
% 1.81/1.03  monotx_restored_types:                  0
% 1.81/1.03  sat_num_of_epr_types:                   0
% 1.81/1.03  sat_num_of_non_cyclic_types:            0
% 1.81/1.03  sat_guarded_non_collapsed_types:        0
% 1.81/1.03  num_pure_diseq_elim:                    0
% 1.81/1.03  simp_replaced_by:                       0
% 1.81/1.03  res_preprocessed:                       159
% 1.81/1.03  prep_upred:                             0
% 1.81/1.03  prep_unflattend:                        15
% 1.81/1.03  smt_new_axioms:                         0
% 1.81/1.03  pred_elim_cands:                        6
% 1.81/1.03  pred_elim:                              6
% 1.81/1.03  pred_elim_cl:                           8
% 1.81/1.03  pred_elim_cycles:                       9
% 1.81/1.03  merged_defs:                            0
% 1.81/1.03  merged_defs_ncl:                        0
% 1.81/1.03  bin_hyper_res:                          0
% 1.81/1.03  prep_cycles:                            4
% 1.81/1.03  pred_elim_time:                         0.005
% 1.81/1.03  splitting_time:                         0.
% 1.81/1.03  sem_filter_time:                        0.
% 1.81/1.03  monotx_time:                            0.
% 1.81/1.03  subtype_inf_time:                       0.
% 1.81/1.03  
% 1.81/1.03  ------ Problem properties
% 1.81/1.03  
% 1.81/1.03  clauses:                                28
% 1.81/1.03  conjectures:                            5
% 1.81/1.03  epr:                                    4
% 1.81/1.03  horn:                                   28
% 1.81/1.03  ground:                                 8
% 1.81/1.03  unary:                                  11
% 1.81/1.03  binary:                                 1
% 1.81/1.03  lits:                                   85
% 1.81/1.03  lits_eq:                                17
% 1.81/1.03  fd_pure:                                0
% 1.81/1.03  fd_pseudo:                              0
% 1.81/1.03  fd_cond:                                0
% 1.81/1.03  fd_pseudo_cond:                         2
% 1.81/1.03  ac_symbols:                             0
% 1.81/1.03  
% 1.81/1.03  ------ Propositional Solver
% 1.81/1.03  
% 1.81/1.03  prop_solver_calls:                      29
% 1.81/1.03  prop_fast_solver_calls:                 1205
% 1.81/1.03  smt_solver_calls:                       0
% 1.81/1.03  smt_fast_solver_calls:                  0
% 1.81/1.03  prop_num_of_clauses:                    1386
% 1.81/1.03  prop_preprocess_simplified:             5564
% 1.81/1.03  prop_fo_subsumed:                       50
% 1.81/1.03  prop_solver_time:                       0.
% 1.81/1.03  smt_solver_time:                        0.
% 1.81/1.03  smt_fast_solver_time:                   0.
% 1.81/1.03  prop_fast_solver_time:                  0.
% 1.81/1.03  prop_unsat_core_time:                   0.
% 1.81/1.03  
% 1.81/1.03  ------ QBF
% 1.81/1.03  
% 1.81/1.03  qbf_q_res:                              0
% 1.81/1.03  qbf_num_tautologies:                    0
% 1.81/1.03  qbf_prep_cycles:                        0
% 1.81/1.03  
% 1.81/1.03  ------ BMC1
% 1.81/1.03  
% 1.81/1.03  bmc1_current_bound:                     -1
% 1.81/1.03  bmc1_last_solved_bound:                 -1
% 1.81/1.03  bmc1_unsat_core_size:                   -1
% 1.81/1.03  bmc1_unsat_core_parents_size:           -1
% 1.81/1.03  bmc1_merge_next_fun:                    0
% 1.81/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.81/1.03  
% 1.81/1.03  ------ Instantiation
% 1.81/1.03  
% 1.81/1.03  inst_num_of_clauses:                    459
% 1.81/1.03  inst_num_in_passive:                    115
% 1.81/1.03  inst_num_in_active:                     286
% 1.81/1.03  inst_num_in_unprocessed:                58
% 1.81/1.03  inst_num_of_loops:                      320
% 1.81/1.03  inst_num_of_learning_restarts:          0
% 1.81/1.03  inst_num_moves_active_passive:          30
% 1.81/1.03  inst_lit_activity:                      0
% 1.81/1.03  inst_lit_activity_moves:                0
% 1.81/1.03  inst_num_tautologies:                   0
% 1.81/1.03  inst_num_prop_implied:                  0
% 1.81/1.03  inst_num_existing_simplified:           0
% 1.81/1.03  inst_num_eq_res_simplified:             0
% 1.81/1.03  inst_num_child_elim:                    0
% 1.81/1.03  inst_num_of_dismatching_blockings:      87
% 1.81/1.03  inst_num_of_non_proper_insts:           493
% 1.81/1.03  inst_num_of_duplicates:                 0
% 1.81/1.03  inst_inst_num_from_inst_to_res:         0
% 1.81/1.03  inst_dismatching_checking_time:         0.
% 1.81/1.03  
% 1.81/1.03  ------ Resolution
% 1.81/1.03  
% 1.81/1.03  res_num_of_clauses:                     0
% 1.81/1.03  res_num_in_passive:                     0
% 1.81/1.03  res_num_in_active:                      0
% 1.81/1.03  res_num_of_loops:                       163
% 1.81/1.03  res_forward_subset_subsumed:            79
% 1.81/1.03  res_backward_subset_subsumed:           0
% 1.81/1.03  res_forward_subsumed:                   0
% 1.81/1.03  res_backward_subsumed:                  0
% 1.81/1.03  res_forward_subsumption_resolution:     1
% 1.81/1.03  res_backward_subsumption_resolution:    0
% 1.81/1.03  res_clause_to_clause_subsumption:       75
% 1.81/1.03  res_orphan_elimination:                 0
% 1.81/1.03  res_tautology_del:                      69
% 1.81/1.03  res_num_eq_res_simplified:              0
% 1.81/1.03  res_num_sel_changes:                    0
% 1.81/1.03  res_moves_from_active_to_pass:          0
% 1.81/1.03  
% 1.81/1.03  ------ Superposition
% 1.81/1.03  
% 1.81/1.03  sup_time_total:                         0.
% 1.81/1.03  sup_time_generating:                    0.
% 1.81/1.03  sup_time_sim_full:                      0.
% 1.81/1.03  sup_time_sim_immed:                     0.
% 1.81/1.03  
% 1.81/1.03  sup_num_of_clauses:                     52
% 1.81/1.03  sup_num_in_active:                      48
% 1.81/1.03  sup_num_in_passive:                     4
% 1.81/1.03  sup_num_of_loops:                       62
% 1.81/1.03  sup_fw_superposition:                   24
% 1.81/1.03  sup_bw_superposition:                   19
% 1.81/1.03  sup_immediate_simplified:               16
% 1.81/1.03  sup_given_eliminated:                   0
% 1.81/1.03  comparisons_done:                       0
% 1.81/1.03  comparisons_avoided:                    0
% 1.81/1.03  
% 1.81/1.03  ------ Simplifications
% 1.81/1.03  
% 1.81/1.03  
% 1.81/1.03  sim_fw_subset_subsumed:                 4
% 1.81/1.03  sim_bw_subset_subsumed:                 2
% 1.81/1.03  sim_fw_subsumed:                        4
% 1.81/1.03  sim_bw_subsumed:                        0
% 1.81/1.03  sim_fw_subsumption_res:                 0
% 1.81/1.03  sim_bw_subsumption_res:                 0
% 1.81/1.03  sim_tautology_del:                      0
% 1.81/1.03  sim_eq_tautology_del:                   7
% 1.81/1.03  sim_eq_res_simp:                        0
% 1.81/1.03  sim_fw_demodulated:                     0
% 1.81/1.03  sim_bw_demodulated:                     13
% 1.81/1.03  sim_light_normalised:                   17
% 1.81/1.03  sim_joinable_taut:                      0
% 1.81/1.03  sim_joinable_simp:                      0
% 1.81/1.03  sim_ac_normalised:                      0
% 1.81/1.03  sim_smt_subsumption:                    0
% 1.81/1.03  
%------------------------------------------------------------------------------
