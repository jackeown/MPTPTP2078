%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:24 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  296 (10881 expanded)
%              Number of clauses        :  203 (3490 expanded)
%              Number of leaves         :   29 (3032 expanded)
%              Depth                    :   25
%              Number of atoms          : 1153 (68631 expanded)
%              Number of equality atoms :  530 (12227 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f52,f56,f55,f54])).

fof(f93,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f57])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f85,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f88,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f90,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f91,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f95,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f89,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f66,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f60,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f65,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f97,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f62,f73])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f67,f73])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f84,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f83,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f40])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f49])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f96,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_777,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1338,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_777])).

cnf(c_26,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_37,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_447,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_37])).

cnf(c_448,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_771,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_448])).

cnf(c_35,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_442,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_35])).

cnf(c_443,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_772,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_443])).

cnf(c_1369,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1338,c_771,c_772])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_787,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1329,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_787])).

cnf(c_1947,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1369,c_1329])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_778,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1366,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_778,c_771,c_772])).

cnf(c_1949,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1947,c_1366])).

cnf(c_1986,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1949,c_1947])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_784,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k1_xboole_0 = X1_55
    | k5_relat_1(k2_funct_1(X0_54),X0_54) = k6_partfun1(X1_55) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1332,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k1_xboole_0 = X1_55
    | k5_relat_1(k2_funct_1(X0_54),X0_54) = k6_partfun1(X1_55)
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_784])).

cnf(c_2881,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1986,c_1332])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_41,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_30,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_44,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1988,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1949,c_1369])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_776,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_1339,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_776])).

cnf(c_1363,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1339,c_771,c_772])).

cnf(c_1989,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1949,c_1363])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_415,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_27])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_433,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_415,c_36])).

cnf(c_434,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_417,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_436,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_434,c_36,c_35,c_417])).

cnf(c_773,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_436])).

cnf(c_1357,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_772,c_773])).

cnf(c_1990,plain,
    ( k2_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1949,c_1357])).

cnf(c_4880,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2881,c_41,c_44,c_1988,c_1989,c_1990])).

cnf(c_779,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1337,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_779])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_791,plain,
    ( ~ v2_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relat_1(k2_funct_1(X0_54)) = k1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1325,plain,
    ( k2_relat_1(k2_funct_1(X0_54)) = k1_relat_1(X0_54)
    | v2_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_791])).

cnf(c_2246,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_1325])).

cnf(c_853,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_788,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1636,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_2333,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2246,c_34,c_32,c_30,c_853,c_1636])).

cnf(c_6,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_792,plain,
    ( v2_funct_1(X0_54)
    | ~ v2_funct_1(k5_relat_1(X0_54,X1_54))
    | ~ v1_relat_1(X0_54)
    | ~ v1_relat_1(X1_54)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54)
    | k1_relat_1(X1_54) != k2_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1324,plain,
    ( k1_relat_1(X0_54) != k2_relat_1(X1_54)
    | v2_funct_1(X1_54) = iProver_top
    | v2_funct_1(k5_relat_1(X1_54,X0_54)) != iProver_top
    | v1_relat_1(X1_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_792])).

cnf(c_2645,plain,
    ( k1_relat_1(X0_54) != k1_relat_1(sK2)
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_54)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2333,c_1324])).

cnf(c_43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_797,plain,
    ( ~ v1_relat_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k2_funct_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_838,plain,
    ( v1_relat_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_funct_1(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_797])).

cnf(c_840,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_838])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_796,plain,
    ( ~ v1_relat_1(X0_54)
    | v1_relat_1(k2_funct_1(X0_54))
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_841,plain,
    ( v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(k2_funct_1(X0_54)) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_796])).

cnf(c_843,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_1637,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1636])).

cnf(c_3449,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | k1_relat_1(X0_54) != k1_relat_1(sK2)
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_54)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2645,c_41,c_43,c_840,c_843,c_1637])).

cnf(c_3450,plain,
    ( k1_relat_1(X0_54) != k1_relat_1(sK2)
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_54)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_3449])).

cnf(c_3461,plain,
    ( v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3450])).

cnf(c_812,plain,
    ( k1_relat_1(X0_54) = k1_relat_1(X1_54)
    | X0_54 != X1_54 ),
    theory(equality)).

cnf(c_825,plain,
    ( k1_relat_1(sK2) = k1_relat_1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_801,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_834,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_3452,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3450])).

cnf(c_4040,plain,
    ( v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3461,c_41,c_43,c_825,c_834,c_1637,c_3452])).

cnf(c_4883,plain,
    ( v2_funct_1(k6_partfun1(k2_relat_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4880,c_4040])).

cnf(c_802,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_1757,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_806,plain,
    ( X0_55 != X1_55
    | X2_55 != X1_55
    | X2_55 = X0_55 ),
    theory(equality)).

cnf(c_1649,plain,
    ( u1_struct_0(sK1) != X0_55
    | u1_struct_0(sK1) = k1_xboole_0
    | k1_xboole_0 != X0_55 ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_1849,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK1) = k1_xboole_0
    | k1_xboole_0 != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1649])).

cnf(c_1724,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_55
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0_55 ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_1877,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1724])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_783,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k1_xboole_0 = X1_55
    | k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_partfun1(X0_55) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1740,plain,
    ( ~ v1_funct_2(X0_54,X0_55,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,u1_struct_0(sK1))))
    | ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(X0_55,u1_struct_0(sK1),X0_54) != u1_struct_0(sK1)
    | k1_xboole_0 = u1_struct_0(sK1)
    | k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_partfun1(X0_55) ),
    inference(instantiation,[status(thm)],[c_783])).

cnf(c_1953,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | k1_xboole_0 = u1_struct_0(sK1)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1740])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_790,plain,
    ( ~ v2_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k1_relat_1(k2_funct_1(X0_54)) = k2_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1326,plain,
    ( k1_relat_1(k2_funct_1(X0_54)) = k2_relat_1(X0_54)
    | v2_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_790])).

cnf(c_2269,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_1326])).

cnf(c_856,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_790])).

cnf(c_2369,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2269,c_34,c_32,c_30,c_856,c_1636])).

cnf(c_5,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X1,X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_793,plain,
    ( v2_funct_1(X0_54)
    | ~ v2_funct_1(k5_relat_1(X1_54,X0_54))
    | ~ v1_relat_1(X0_54)
    | ~ v1_relat_1(X1_54)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54)
    | k1_relat_1(X0_54) != k2_relat_1(X1_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1323,plain,
    ( k1_relat_1(X0_54) != k2_relat_1(X1_54)
    | v2_funct_1(X0_54) = iProver_top
    | v2_funct_1(k5_relat_1(X1_54,X0_54)) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(X1_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_793])).

cnf(c_2374,plain,
    ( k2_relat_1(X0_54) != k2_relat_1(sK2)
    | v2_funct_1(k5_relat_1(X0_54,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2369,c_1323])).

cnf(c_3426,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | k2_relat_1(X0_54) != k2_relat_1(sK2)
    | v2_funct_1(k5_relat_1(X0_54,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2374,c_41,c_43,c_840,c_843,c_1637])).

cnf(c_3427,plain,
    ( k2_relat_1(X0_54) != k2_relat_1(sK2)
    | v2_funct_1(k5_relat_1(X0_54,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_3426])).

cnf(c_3438,plain,
    ( v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3427])).

cnf(c_811,plain,
    ( k2_relat_1(X0_54) = k2_relat_1(X1_54)
    | X0_54 != X1_54 ),
    theory(equality)).

cnf(c_824,plain,
    ( k2_relat_1(sK2) = k2_relat_1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_3429,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3427])).

cnf(c_3961,plain,
    ( v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3438,c_41,c_43,c_824,c_834,c_1637,c_3429])).

cnf(c_810,plain,
    ( ~ v2_funct_1(X0_54)
    | v2_funct_1(X1_54)
    | X1_54 != X0_54 ),
    theory(equality)).

cnf(c_3278,plain,
    ( ~ v2_funct_1(X0_54)
    | v2_funct_1(k5_relat_1(X1_54,k2_funct_1(X2_54)))
    | k5_relat_1(X1_54,k2_funct_1(X2_54)) != X0_54 ),
    inference(instantiation,[status(thm)],[c_810])).

cnf(c_5486,plain,
    ( v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ v2_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_partfun1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_3278])).

cnf(c_5487,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) != k6_partfun1(u1_struct_0(sK0))
    | v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) = iProver_top
    | v2_funct_1(k6_partfun1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5486])).

cnf(c_3,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_795,plain,
    ( v2_funct_1(k6_partfun1(X0_55)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_6643,plain,
    ( v2_funct_1(k6_partfun1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_6644,plain,
    ( v2_funct_1(k6_partfun1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6643])).

cnf(c_6677,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4883,c_34,c_41,c_33,c_32,c_43,c_30,c_824,c_834,c_778,c_773,c_772,c_1637,c_1757,c_1849,c_1877,c_1953,c_3429,c_5487,c_6644])).

cnf(c_1333,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k1_xboole_0 = X1_55
    | k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_partfun1(X0_55)
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_783])).

cnf(c_3709,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0))
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1986,c_1333])).

cnf(c_5557,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3709,c_41,c_44,c_1988,c_1989,c_1990])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_11,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_14,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_489,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_11,c_14])).

cnf(c_493,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_489,c_14,c_11,c_10])).

cnf(c_494,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_493])).

cnf(c_533,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_17,c_494])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_533,c_17,c_494])).

cnf(c_538,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_537])).

cnf(c_769,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_54)
    | k1_relat_1(X0_54) = X0_55
    | k1_xboole_0 = X1_55 ),
    inference(subtyping,[status(esa)],[c_538])).

cnf(c_1344,plain,
    ( k1_relat_1(X0_54) = X0_55
    | k1_xboole_0 = X1_55
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_769])).

cnf(c_4895,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1988,c_1344])).

cnf(c_5291,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4895,c_41,c_1989,c_1990])).

cnf(c_5559,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_5557,c_5291])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k1_relat_1(X0) != k2_relat_1(X1)
    | k2_funct_1(X0) = X1 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_789,plain,
    ( ~ v2_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | ~ v1_relat_1(X1_54)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54)
    | k1_relat_1(X0_54) != k2_relat_1(X1_54)
    | k5_relat_1(X1_54,X0_54) != k6_partfun1(k2_relat_1(X0_54))
    | k2_funct_1(X0_54) = X1_54 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1327,plain,
    ( k1_relat_1(X0_54) != k2_relat_1(X1_54)
    | k5_relat_1(X1_54,X0_54) != k6_partfun1(k2_relat_1(X0_54))
    | k2_funct_1(X0_54) = X1_54
    | v2_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(X1_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_5563,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(k2_funct_1(sK2))) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5559,c_1327])).

cnf(c_5564,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5563,c_2333,c_2369])).

cnf(c_5565,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5564])).

cnf(c_5619,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5565,c_41,c_43,c_840,c_843,c_1637])).

cnf(c_6686,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_6677,c_5619])).

cnf(c_23,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_782,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_54),k2_relat_1(X0_54))))
    | ~ v1_relat_1(X0_54)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1334,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_54),k2_relat_1(X0_54)))) = iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_782])).

cnf(c_2372,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2369,c_1334])).

cnf(c_2399,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2372,c_2333])).

cnf(c_876,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_782])).

cnf(c_875,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_54),k2_relat_1(X0_54)))) = iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_782])).

cnf(c_877,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_875])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_781,plain,
    ( v1_funct_2(X0_54,k1_relat_1(X0_54),k2_relat_1(X0_54))
    | ~ v1_relat_1(X0_54)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_878,plain,
    ( v1_funct_2(X0_54,k1_relat_1(X0_54),k2_relat_1(X0_54)) = iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_781])).

cnf(c_880,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_878])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_786,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55)))
    | ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1789,plain,
    ( ~ v1_funct_2(X0_54,k1_relat_1(X0_54),k2_relat_1(X0_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_54),k2_relat_1(X0_54))))
    | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0_54),k1_relat_1(X0_54))))
    | ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(k1_relat_1(X0_54),k2_relat_1(X0_54),X0_54) != k2_relat_1(X0_54) ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_1800,plain,
    ( k2_relset_1(k1_relat_1(X0_54),k2_relat_1(X0_54),X0_54) != k2_relat_1(X0_54)
    | v1_funct_2(X0_54,k1_relat_1(X0_54),k2_relat_1(X0_54)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_54),k2_relat_1(X0_54)))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0_54),k1_relat_1(X0_54)))) = iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1789])).

cnf(c_1802,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1800])).

cnf(c_1808,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_54),k2_relat_1(X0_54))))
    | k2_relset_1(k1_relat_1(X0_54),k2_relat_1(X0_54),X0_54) = k2_relat_1(X0_54) ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(c_1818,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1808])).

cnf(c_2623,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2399,c_34,c_41,c_32,c_43,c_44,c_876,c_877,c_880,c_1636,c_1637,c_1802,c_1818])).

cnf(c_2628,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2623,c_1329])).

cnf(c_2633,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2628,c_2333])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_780,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1336,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54)
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_780])).

cnf(c_3052,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2633,c_1336])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_785,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1790,plain,
    ( ~ v1_funct_2(X0_54,k1_relat_1(X0_54),k2_relat_1(X0_54))
    | v1_funct_2(k2_funct_1(X0_54),k2_relat_1(X0_54),k1_relat_1(X0_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_54),k2_relat_1(X0_54))))
    | ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(k1_relat_1(X0_54),k2_relat_1(X0_54),X0_54) != k2_relat_1(X0_54) ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(c_1796,plain,
    ( k2_relset_1(k1_relat_1(X0_54),k2_relat_1(X0_54),X0_54) != k2_relat_1(X0_54)
    | v1_funct_2(X0_54,k1_relat_1(X0_54),k2_relat_1(X0_54)) != iProver_top
    | v1_funct_2(k2_funct_1(X0_54),k2_relat_1(X0_54),k1_relat_1(X0_54)) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_54),k2_relat_1(X0_54)))) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1790])).

cnf(c_1798,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1796])).

cnf(c_2098,plain,
    ( ~ v1_funct_2(k2_funct_1(X0_54),k2_relat_1(X0_54),k1_relat_1(X0_54))
    | ~ m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0_54),k1_relat_1(X0_54))))
    | ~ v2_funct_1(k2_funct_1(X0_54))
    | ~ v1_funct_1(k2_funct_1(X0_54))
    | k2_relset_1(k2_relat_1(X0_54),k1_relat_1(X0_54),k2_funct_1(X0_54)) != k1_relat_1(X0_54)
    | k2_tops_2(k2_relat_1(X0_54),k1_relat_1(X0_54),k2_funct_1(X0_54)) = k2_funct_1(k2_funct_1(X0_54)) ),
    inference(instantiation,[status(thm)],[c_780])).

cnf(c_2114,plain,
    ( k2_relset_1(k2_relat_1(X0_54),k1_relat_1(X0_54),k2_funct_1(X0_54)) != k1_relat_1(X0_54)
    | k2_tops_2(k2_relat_1(X0_54),k1_relat_1(X0_54),k2_funct_1(X0_54)) = k2_funct_1(k2_funct_1(X0_54))
    | v1_funct_2(k2_funct_1(X0_54),k2_relat_1(X0_54),k1_relat_1(X0_54)) != iProver_top
    | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0_54),k1_relat_1(X0_54)))) != iProver_top
    | v2_funct_1(k2_funct_1(X0_54)) != iProver_top
    | v1_funct_1(k2_funct_1(X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2098])).

cnf(c_2116,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2114])).

cnf(c_4627,plain,
    ( v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3052,c_34,c_41,c_32,c_43,c_44,c_840,c_876,c_877,c_880,c_1636,c_1637,c_1798,c_1802,c_1818,c_2116,c_2633])).

cnf(c_4628,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4627])).

cnf(c_6688,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_6677,c_4628])).

cnf(c_6695,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_6686,c_6688])).

cnf(c_2821,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1986,c_1336])).

cnf(c_4113,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2821,c_41,c_44,c_1988,c_1989])).

cnf(c_15,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_29,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_454,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X3
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_455,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_770,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_455])).

cnf(c_799,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sP0_iProver_split
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_770])).

cnf(c_1342,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_1563,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1342,c_771,c_772])).

cnf(c_798,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_770])).

cnf(c_1343,plain,
    ( v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_798])).

cnf(c_1426,plain,
    ( v1_funct_2(X0_54,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1343,c_771,c_772])).

cnf(c_1569,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1563,c_1426])).

cnf(c_1987,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1949,c_1569])).

cnf(c_4116,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4113,c_1987])).

cnf(c_5296,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5291,c_4116])).

cnf(c_7713,plain,
    ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5296,c_6695])).

cnf(c_8843,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6695,c_7713])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8843,c_1637,c_880,c_877,c_43,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:51:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.18/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.01  
% 2.18/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.18/1.01  
% 2.18/1.01  ------  iProver source info
% 2.18/1.01  
% 2.18/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.18/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.18/1.01  git: non_committed_changes: false
% 2.18/1.01  git: last_make_outside_of_git: false
% 2.18/1.01  
% 2.18/1.01  ------ 
% 2.18/1.01  
% 2.18/1.01  ------ Input Options
% 2.18/1.01  
% 2.18/1.01  --out_options                           all
% 2.18/1.01  --tptp_safe_out                         true
% 2.18/1.01  --problem_path                          ""
% 2.18/1.01  --include_path                          ""
% 2.18/1.01  --clausifier                            res/vclausify_rel
% 2.18/1.01  --clausifier_options                    --mode clausify
% 2.18/1.01  --stdin                                 false
% 2.18/1.01  --stats_out                             all
% 2.18/1.01  
% 2.18/1.01  ------ General Options
% 2.18/1.01  
% 2.18/1.01  --fof                                   false
% 2.18/1.01  --time_out_real                         305.
% 2.18/1.01  --time_out_virtual                      -1.
% 2.18/1.01  --symbol_type_check                     false
% 2.18/1.01  --clausify_out                          false
% 2.18/1.01  --sig_cnt_out                           false
% 2.18/1.01  --trig_cnt_out                          false
% 2.18/1.01  --trig_cnt_out_tolerance                1.
% 2.18/1.01  --trig_cnt_out_sk_spl                   false
% 2.18/1.01  --abstr_cl_out                          false
% 2.18/1.01  
% 2.18/1.01  ------ Global Options
% 2.18/1.01  
% 2.18/1.01  --schedule                              default
% 2.18/1.01  --add_important_lit                     false
% 2.18/1.01  --prop_solver_per_cl                    1000
% 2.18/1.01  --min_unsat_core                        false
% 2.18/1.01  --soft_assumptions                      false
% 2.18/1.01  --soft_lemma_size                       3
% 2.18/1.01  --prop_impl_unit_size                   0
% 2.18/1.01  --prop_impl_unit                        []
% 2.18/1.01  --share_sel_clauses                     true
% 2.18/1.01  --reset_solvers                         false
% 2.18/1.01  --bc_imp_inh                            [conj_cone]
% 2.18/1.01  --conj_cone_tolerance                   3.
% 2.18/1.01  --extra_neg_conj                        none
% 2.18/1.01  --large_theory_mode                     true
% 2.18/1.01  --prolific_symb_bound                   200
% 2.18/1.01  --lt_threshold                          2000
% 2.18/1.01  --clause_weak_htbl                      true
% 2.18/1.01  --gc_record_bc_elim                     false
% 2.18/1.01  
% 2.18/1.01  ------ Preprocessing Options
% 2.18/1.01  
% 2.18/1.01  --preprocessing_flag                    true
% 2.18/1.01  --time_out_prep_mult                    0.1
% 2.18/1.01  --splitting_mode                        input
% 2.18/1.01  --splitting_grd                         true
% 2.18/1.01  --splitting_cvd                         false
% 2.18/1.01  --splitting_cvd_svl                     false
% 2.18/1.01  --splitting_nvd                         32
% 2.18/1.01  --sub_typing                            true
% 2.18/1.01  --prep_gs_sim                           true
% 2.18/1.01  --prep_unflatten                        true
% 2.18/1.01  --prep_res_sim                          true
% 2.18/1.01  --prep_upred                            true
% 2.18/1.01  --prep_sem_filter                       exhaustive
% 2.18/1.01  --prep_sem_filter_out                   false
% 2.18/1.01  --pred_elim                             true
% 2.18/1.01  --res_sim_input                         true
% 2.18/1.01  --eq_ax_congr_red                       true
% 2.18/1.01  --pure_diseq_elim                       true
% 2.18/1.01  --brand_transform                       false
% 2.18/1.01  --non_eq_to_eq                          false
% 2.18/1.01  --prep_def_merge                        true
% 2.18/1.01  --prep_def_merge_prop_impl              false
% 2.18/1.01  --prep_def_merge_mbd                    true
% 2.18/1.01  --prep_def_merge_tr_red                 false
% 2.18/1.01  --prep_def_merge_tr_cl                  false
% 2.18/1.01  --smt_preprocessing                     true
% 2.18/1.01  --smt_ac_axioms                         fast
% 2.18/1.01  --preprocessed_out                      false
% 2.18/1.01  --preprocessed_stats                    false
% 2.18/1.01  
% 2.18/1.01  ------ Abstraction refinement Options
% 2.18/1.01  
% 2.18/1.01  --abstr_ref                             []
% 2.18/1.01  --abstr_ref_prep                        false
% 2.18/1.01  --abstr_ref_until_sat                   false
% 2.18/1.01  --abstr_ref_sig_restrict                funpre
% 2.18/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/1.01  --abstr_ref_under                       []
% 2.18/1.01  
% 2.18/1.01  ------ SAT Options
% 2.18/1.01  
% 2.18/1.01  --sat_mode                              false
% 2.18/1.01  --sat_fm_restart_options                ""
% 2.18/1.01  --sat_gr_def                            false
% 2.18/1.01  --sat_epr_types                         true
% 2.18/1.01  --sat_non_cyclic_types                  false
% 2.18/1.01  --sat_finite_models                     false
% 2.18/1.01  --sat_fm_lemmas                         false
% 2.18/1.01  --sat_fm_prep                           false
% 2.18/1.01  --sat_fm_uc_incr                        true
% 2.18/1.01  --sat_out_model                         small
% 2.18/1.01  --sat_out_clauses                       false
% 2.18/1.01  
% 2.18/1.01  ------ QBF Options
% 2.18/1.01  
% 2.18/1.01  --qbf_mode                              false
% 2.18/1.01  --qbf_elim_univ                         false
% 2.18/1.01  --qbf_dom_inst                          none
% 2.18/1.01  --qbf_dom_pre_inst                      false
% 2.18/1.01  --qbf_sk_in                             false
% 2.18/1.01  --qbf_pred_elim                         true
% 2.18/1.01  --qbf_split                             512
% 2.18/1.01  
% 2.18/1.01  ------ BMC1 Options
% 2.18/1.01  
% 2.18/1.01  --bmc1_incremental                      false
% 2.18/1.01  --bmc1_axioms                           reachable_all
% 2.18/1.01  --bmc1_min_bound                        0
% 2.18/1.01  --bmc1_max_bound                        -1
% 2.18/1.01  --bmc1_max_bound_default                -1
% 2.18/1.01  --bmc1_symbol_reachability              true
% 2.18/1.01  --bmc1_property_lemmas                  false
% 2.18/1.01  --bmc1_k_induction                      false
% 2.18/1.01  --bmc1_non_equiv_states                 false
% 2.18/1.01  --bmc1_deadlock                         false
% 2.18/1.01  --bmc1_ucm                              false
% 2.18/1.01  --bmc1_add_unsat_core                   none
% 2.18/1.01  --bmc1_unsat_core_children              false
% 2.18/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/1.01  --bmc1_out_stat                         full
% 2.18/1.01  --bmc1_ground_init                      false
% 2.18/1.01  --bmc1_pre_inst_next_state              false
% 2.18/1.01  --bmc1_pre_inst_state                   false
% 2.18/1.01  --bmc1_pre_inst_reach_state             false
% 2.18/1.01  --bmc1_out_unsat_core                   false
% 2.18/1.01  --bmc1_aig_witness_out                  false
% 2.18/1.01  --bmc1_verbose                          false
% 2.18/1.01  --bmc1_dump_clauses_tptp                false
% 2.18/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.18/1.01  --bmc1_dump_file                        -
% 2.18/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.18/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.18/1.01  --bmc1_ucm_extend_mode                  1
% 2.18/1.01  --bmc1_ucm_init_mode                    2
% 2.18/1.01  --bmc1_ucm_cone_mode                    none
% 2.18/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.18/1.01  --bmc1_ucm_relax_model                  4
% 2.18/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.18/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/1.01  --bmc1_ucm_layered_model                none
% 2.18/1.01  --bmc1_ucm_max_lemma_size               10
% 2.18/1.01  
% 2.18/1.01  ------ AIG Options
% 2.18/1.01  
% 2.18/1.01  --aig_mode                              false
% 2.18/1.01  
% 2.18/1.01  ------ Instantiation Options
% 2.18/1.01  
% 2.18/1.01  --instantiation_flag                    true
% 2.18/1.01  --inst_sos_flag                         false
% 2.18/1.01  --inst_sos_phase                        true
% 2.18/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/1.01  --inst_lit_sel_side                     num_symb
% 2.18/1.01  --inst_solver_per_active                1400
% 2.18/1.01  --inst_solver_calls_frac                1.
% 2.18/1.01  --inst_passive_queue_type               priority_queues
% 2.18/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/1.01  --inst_passive_queues_freq              [25;2]
% 2.18/1.01  --inst_dismatching                      true
% 2.18/1.01  --inst_eager_unprocessed_to_passive     true
% 2.18/1.01  --inst_prop_sim_given                   true
% 2.18/1.01  --inst_prop_sim_new                     false
% 2.18/1.01  --inst_subs_new                         false
% 2.18/1.01  --inst_eq_res_simp                      false
% 2.18/1.01  --inst_subs_given                       false
% 2.18/1.01  --inst_orphan_elimination               true
% 2.18/1.01  --inst_learning_loop_flag               true
% 2.18/1.01  --inst_learning_start                   3000
% 2.18/1.01  --inst_learning_factor                  2
% 2.18/1.01  --inst_start_prop_sim_after_learn       3
% 2.18/1.01  --inst_sel_renew                        solver
% 2.18/1.01  --inst_lit_activity_flag                true
% 2.18/1.01  --inst_restr_to_given                   false
% 2.18/1.01  --inst_activity_threshold               500
% 2.18/1.01  --inst_out_proof                        true
% 2.18/1.01  
% 2.18/1.01  ------ Resolution Options
% 2.18/1.01  
% 2.18/1.01  --resolution_flag                       true
% 2.18/1.01  --res_lit_sel                           adaptive
% 2.18/1.01  --res_lit_sel_side                      none
% 2.18/1.01  --res_ordering                          kbo
% 2.18/1.01  --res_to_prop_solver                    active
% 2.18/1.01  --res_prop_simpl_new                    false
% 2.18/1.01  --res_prop_simpl_given                  true
% 2.18/1.01  --res_passive_queue_type                priority_queues
% 2.18/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/1.01  --res_passive_queues_freq               [15;5]
% 2.18/1.01  --res_forward_subs                      full
% 2.18/1.01  --res_backward_subs                     full
% 2.18/1.01  --res_forward_subs_resolution           true
% 2.18/1.01  --res_backward_subs_resolution          true
% 2.18/1.01  --res_orphan_elimination                true
% 2.18/1.01  --res_time_limit                        2.
% 2.18/1.01  --res_out_proof                         true
% 2.18/1.01  
% 2.18/1.01  ------ Superposition Options
% 2.18/1.01  
% 2.18/1.01  --superposition_flag                    true
% 2.18/1.01  --sup_passive_queue_type                priority_queues
% 2.18/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.18/1.01  --demod_completeness_check              fast
% 2.18/1.01  --demod_use_ground                      true
% 2.18/1.01  --sup_to_prop_solver                    passive
% 2.18/1.01  --sup_prop_simpl_new                    true
% 2.18/1.01  --sup_prop_simpl_given                  true
% 2.18/1.01  --sup_fun_splitting                     false
% 2.18/1.01  --sup_smt_interval                      50000
% 2.18/1.01  
% 2.18/1.01  ------ Superposition Simplification Setup
% 2.18/1.01  
% 2.18/1.01  --sup_indices_passive                   []
% 2.18/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.01  --sup_full_bw                           [BwDemod]
% 2.18/1.01  --sup_immed_triv                        [TrivRules]
% 2.18/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.01  --sup_immed_bw_main                     []
% 2.18/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.01  
% 2.18/1.01  ------ Combination Options
% 2.18/1.01  
% 2.18/1.01  --comb_res_mult                         3
% 2.18/1.01  --comb_sup_mult                         2
% 2.18/1.01  --comb_inst_mult                        10
% 2.18/1.01  
% 2.18/1.01  ------ Debug Options
% 2.18/1.01  
% 2.18/1.01  --dbg_backtrace                         false
% 2.18/1.01  --dbg_dump_prop_clauses                 false
% 2.18/1.01  --dbg_dump_prop_clauses_file            -
% 2.18/1.01  --dbg_out_stat                          false
% 2.18/1.01  ------ Parsing...
% 2.18/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.18/1.01  
% 2.18/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.18/1.01  
% 2.18/1.01  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.18/1.01  
% 2.18/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.18/1.01  ------ Proving...
% 2.18/1.01  ------ Problem Properties 
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  clauses                                 31
% 2.18/1.01  conjectures                             5
% 2.18/1.01  EPR                                     2
% 2.18/1.01  Horn                                    28
% 2.18/1.01  unary                                   10
% 2.18/1.01  binary                                  2
% 2.18/1.01  lits                                    110
% 2.18/1.01  lits eq                                 26
% 2.18/1.01  fd_pure                                 0
% 2.18/1.01  fd_pseudo                               0
% 2.18/1.01  fd_cond                                 2
% 2.18/1.01  fd_pseudo_cond                          2
% 2.18/1.01  AC symbols                              0
% 2.18/1.01  
% 2.18/1.01  ------ Schedule dynamic 5 is on 
% 2.18/1.01  
% 2.18/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  ------ 
% 2.18/1.01  Current options:
% 2.18/1.01  ------ 
% 2.18/1.01  
% 2.18/1.01  ------ Input Options
% 2.18/1.01  
% 2.18/1.01  --out_options                           all
% 2.18/1.01  --tptp_safe_out                         true
% 2.18/1.01  --problem_path                          ""
% 2.18/1.01  --include_path                          ""
% 2.18/1.01  --clausifier                            res/vclausify_rel
% 2.18/1.01  --clausifier_options                    --mode clausify
% 2.18/1.01  --stdin                                 false
% 2.18/1.01  --stats_out                             all
% 2.18/1.01  
% 2.18/1.01  ------ General Options
% 2.18/1.01  
% 2.18/1.01  --fof                                   false
% 2.18/1.01  --time_out_real                         305.
% 2.18/1.01  --time_out_virtual                      -1.
% 2.18/1.01  --symbol_type_check                     false
% 2.18/1.01  --clausify_out                          false
% 2.18/1.01  --sig_cnt_out                           false
% 2.18/1.01  --trig_cnt_out                          false
% 2.18/1.01  --trig_cnt_out_tolerance                1.
% 2.18/1.01  --trig_cnt_out_sk_spl                   false
% 2.18/1.01  --abstr_cl_out                          false
% 2.18/1.01  
% 2.18/1.01  ------ Global Options
% 2.18/1.01  
% 2.18/1.01  --schedule                              default
% 2.18/1.01  --add_important_lit                     false
% 2.18/1.01  --prop_solver_per_cl                    1000
% 2.18/1.01  --min_unsat_core                        false
% 2.18/1.01  --soft_assumptions                      false
% 2.18/1.01  --soft_lemma_size                       3
% 2.18/1.01  --prop_impl_unit_size                   0
% 2.18/1.01  --prop_impl_unit                        []
% 2.18/1.01  --share_sel_clauses                     true
% 2.18/1.01  --reset_solvers                         false
% 2.18/1.01  --bc_imp_inh                            [conj_cone]
% 2.18/1.01  --conj_cone_tolerance                   3.
% 2.18/1.01  --extra_neg_conj                        none
% 2.18/1.01  --large_theory_mode                     true
% 2.18/1.01  --prolific_symb_bound                   200
% 2.18/1.01  --lt_threshold                          2000
% 2.18/1.01  --clause_weak_htbl                      true
% 2.18/1.01  --gc_record_bc_elim                     false
% 2.18/1.01  
% 2.18/1.01  ------ Preprocessing Options
% 2.18/1.01  
% 2.18/1.01  --preprocessing_flag                    true
% 2.18/1.01  --time_out_prep_mult                    0.1
% 2.18/1.01  --splitting_mode                        input
% 2.18/1.01  --splitting_grd                         true
% 2.18/1.01  --splitting_cvd                         false
% 2.18/1.01  --splitting_cvd_svl                     false
% 2.18/1.01  --splitting_nvd                         32
% 2.18/1.01  --sub_typing                            true
% 2.18/1.01  --prep_gs_sim                           true
% 2.18/1.01  --prep_unflatten                        true
% 2.18/1.01  --prep_res_sim                          true
% 2.18/1.01  --prep_upred                            true
% 2.18/1.01  --prep_sem_filter                       exhaustive
% 2.18/1.01  --prep_sem_filter_out                   false
% 2.18/1.01  --pred_elim                             true
% 2.18/1.01  --res_sim_input                         true
% 2.18/1.01  --eq_ax_congr_red                       true
% 2.18/1.01  --pure_diseq_elim                       true
% 2.18/1.01  --brand_transform                       false
% 2.18/1.01  --non_eq_to_eq                          false
% 2.18/1.01  --prep_def_merge                        true
% 2.18/1.01  --prep_def_merge_prop_impl              false
% 2.18/1.01  --prep_def_merge_mbd                    true
% 2.18/1.01  --prep_def_merge_tr_red                 false
% 2.18/1.01  --prep_def_merge_tr_cl                  false
% 2.18/1.01  --smt_preprocessing                     true
% 2.18/1.01  --smt_ac_axioms                         fast
% 2.18/1.01  --preprocessed_out                      false
% 2.18/1.01  --preprocessed_stats                    false
% 2.18/1.01  
% 2.18/1.01  ------ Abstraction refinement Options
% 2.18/1.01  
% 2.18/1.01  --abstr_ref                             []
% 2.18/1.01  --abstr_ref_prep                        false
% 2.18/1.01  --abstr_ref_until_sat                   false
% 2.18/1.01  --abstr_ref_sig_restrict                funpre
% 2.18/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/1.01  --abstr_ref_under                       []
% 2.18/1.01  
% 2.18/1.01  ------ SAT Options
% 2.18/1.01  
% 2.18/1.01  --sat_mode                              false
% 2.18/1.01  --sat_fm_restart_options                ""
% 2.18/1.01  --sat_gr_def                            false
% 2.18/1.01  --sat_epr_types                         true
% 2.18/1.01  --sat_non_cyclic_types                  false
% 2.18/1.01  --sat_finite_models                     false
% 2.18/1.01  --sat_fm_lemmas                         false
% 2.18/1.01  --sat_fm_prep                           false
% 2.18/1.01  --sat_fm_uc_incr                        true
% 2.18/1.01  --sat_out_model                         small
% 2.18/1.01  --sat_out_clauses                       false
% 2.18/1.01  
% 2.18/1.01  ------ QBF Options
% 2.18/1.01  
% 2.18/1.01  --qbf_mode                              false
% 2.18/1.01  --qbf_elim_univ                         false
% 2.18/1.01  --qbf_dom_inst                          none
% 2.18/1.01  --qbf_dom_pre_inst                      false
% 2.18/1.01  --qbf_sk_in                             false
% 2.18/1.01  --qbf_pred_elim                         true
% 2.18/1.01  --qbf_split                             512
% 2.18/1.01  
% 2.18/1.01  ------ BMC1 Options
% 2.18/1.01  
% 2.18/1.01  --bmc1_incremental                      false
% 2.18/1.01  --bmc1_axioms                           reachable_all
% 2.18/1.01  --bmc1_min_bound                        0
% 2.18/1.01  --bmc1_max_bound                        -1
% 2.18/1.01  --bmc1_max_bound_default                -1
% 2.18/1.01  --bmc1_symbol_reachability              true
% 2.18/1.01  --bmc1_property_lemmas                  false
% 2.18/1.01  --bmc1_k_induction                      false
% 2.18/1.01  --bmc1_non_equiv_states                 false
% 2.18/1.01  --bmc1_deadlock                         false
% 2.18/1.01  --bmc1_ucm                              false
% 2.18/1.01  --bmc1_add_unsat_core                   none
% 2.18/1.01  --bmc1_unsat_core_children              false
% 2.18/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/1.01  --bmc1_out_stat                         full
% 2.18/1.01  --bmc1_ground_init                      false
% 2.18/1.01  --bmc1_pre_inst_next_state              false
% 2.18/1.01  --bmc1_pre_inst_state                   false
% 2.18/1.01  --bmc1_pre_inst_reach_state             false
% 2.18/1.01  --bmc1_out_unsat_core                   false
% 2.18/1.01  --bmc1_aig_witness_out                  false
% 2.18/1.01  --bmc1_verbose                          false
% 2.18/1.01  --bmc1_dump_clauses_tptp                false
% 2.18/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.18/1.01  --bmc1_dump_file                        -
% 2.18/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.18/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.18/1.01  --bmc1_ucm_extend_mode                  1
% 2.18/1.01  --bmc1_ucm_init_mode                    2
% 2.18/1.01  --bmc1_ucm_cone_mode                    none
% 2.18/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.18/1.01  --bmc1_ucm_relax_model                  4
% 2.18/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.18/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/1.01  --bmc1_ucm_layered_model                none
% 2.18/1.01  --bmc1_ucm_max_lemma_size               10
% 2.18/1.01  
% 2.18/1.01  ------ AIG Options
% 2.18/1.01  
% 2.18/1.01  --aig_mode                              false
% 2.18/1.01  
% 2.18/1.01  ------ Instantiation Options
% 2.18/1.01  
% 2.18/1.01  --instantiation_flag                    true
% 2.18/1.01  --inst_sos_flag                         false
% 2.18/1.01  --inst_sos_phase                        true
% 2.18/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/1.01  --inst_lit_sel_side                     none
% 2.18/1.01  --inst_solver_per_active                1400
% 2.18/1.01  --inst_solver_calls_frac                1.
% 2.18/1.01  --inst_passive_queue_type               priority_queues
% 2.18/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/1.01  --inst_passive_queues_freq              [25;2]
% 2.18/1.01  --inst_dismatching                      true
% 2.18/1.01  --inst_eager_unprocessed_to_passive     true
% 2.18/1.01  --inst_prop_sim_given                   true
% 2.18/1.01  --inst_prop_sim_new                     false
% 2.18/1.01  --inst_subs_new                         false
% 2.18/1.01  --inst_eq_res_simp                      false
% 2.18/1.01  --inst_subs_given                       false
% 2.18/1.01  --inst_orphan_elimination               true
% 2.18/1.01  --inst_learning_loop_flag               true
% 2.18/1.01  --inst_learning_start                   3000
% 2.18/1.01  --inst_learning_factor                  2
% 2.18/1.01  --inst_start_prop_sim_after_learn       3
% 2.18/1.01  --inst_sel_renew                        solver
% 2.18/1.01  --inst_lit_activity_flag                true
% 2.18/1.01  --inst_restr_to_given                   false
% 2.18/1.01  --inst_activity_threshold               500
% 2.18/1.01  --inst_out_proof                        true
% 2.18/1.01  
% 2.18/1.01  ------ Resolution Options
% 2.18/1.01  
% 2.18/1.01  --resolution_flag                       false
% 2.18/1.01  --res_lit_sel                           adaptive
% 2.18/1.01  --res_lit_sel_side                      none
% 2.18/1.01  --res_ordering                          kbo
% 2.18/1.01  --res_to_prop_solver                    active
% 2.18/1.01  --res_prop_simpl_new                    false
% 2.18/1.01  --res_prop_simpl_given                  true
% 2.18/1.01  --res_passive_queue_type                priority_queues
% 2.18/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/1.01  --res_passive_queues_freq               [15;5]
% 2.18/1.01  --res_forward_subs                      full
% 2.18/1.01  --res_backward_subs                     full
% 2.18/1.01  --res_forward_subs_resolution           true
% 2.18/1.01  --res_backward_subs_resolution          true
% 2.18/1.01  --res_orphan_elimination                true
% 2.18/1.01  --res_time_limit                        2.
% 2.18/1.01  --res_out_proof                         true
% 2.18/1.01  
% 2.18/1.01  ------ Superposition Options
% 2.18/1.01  
% 2.18/1.01  --superposition_flag                    true
% 2.18/1.01  --sup_passive_queue_type                priority_queues
% 2.18/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.18/1.01  --demod_completeness_check              fast
% 2.18/1.01  --demod_use_ground                      true
% 2.18/1.01  --sup_to_prop_solver                    passive
% 2.18/1.01  --sup_prop_simpl_new                    true
% 2.18/1.01  --sup_prop_simpl_given                  true
% 2.18/1.01  --sup_fun_splitting                     false
% 2.18/1.01  --sup_smt_interval                      50000
% 2.18/1.01  
% 2.18/1.01  ------ Superposition Simplification Setup
% 2.18/1.01  
% 2.18/1.01  --sup_indices_passive                   []
% 2.18/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.01  --sup_full_bw                           [BwDemod]
% 2.18/1.01  --sup_immed_triv                        [TrivRules]
% 2.18/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.01  --sup_immed_bw_main                     []
% 2.18/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.01  
% 2.18/1.01  ------ Combination Options
% 2.18/1.01  
% 2.18/1.01  --comb_res_mult                         3
% 2.18/1.01  --comb_sup_mult                         2
% 2.18/1.01  --comb_inst_mult                        10
% 2.18/1.01  
% 2.18/1.01  ------ Debug Options
% 2.18/1.01  
% 2.18/1.01  --dbg_backtrace                         false
% 2.18/1.01  --dbg_dump_prop_clauses                 false
% 2.18/1.01  --dbg_dump_prop_clauses_file            -
% 2.18/1.01  --dbg_out_stat                          false
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  ------ Proving...
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  % SZS status Theorem for theBenchmark.p
% 2.18/1.01  
% 2.18/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.18/1.01  
% 2.18/1.01  fof(f20,conjecture,(
% 2.18/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f21,negated_conjecture,(
% 2.18/1.01    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.18/1.01    inference(negated_conjecture,[],[f20])).
% 2.18/1.01  
% 2.18/1.01  fof(f51,plain,(
% 2.18/1.01    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.18/1.01    inference(ennf_transformation,[],[f21])).
% 2.18/1.01  
% 2.18/1.01  fof(f52,plain,(
% 2.18/1.01    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.18/1.01    inference(flattening,[],[f51])).
% 2.18/1.01  
% 2.18/1.01  fof(f56,plain,(
% 2.18/1.01    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.18/1.01    introduced(choice_axiom,[])).
% 2.18/1.01  
% 2.18/1.01  fof(f55,plain,(
% 2.18/1.01    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.18/1.01    introduced(choice_axiom,[])).
% 2.18/1.01  
% 2.18/1.01  fof(f54,plain,(
% 2.18/1.01    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.18/1.01    introduced(choice_axiom,[])).
% 2.18/1.01  
% 2.18/1.01  fof(f57,plain,(
% 2.18/1.01    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.18/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f52,f56,f55,f54])).
% 2.18/1.01  
% 2.18/1.01  fof(f93,plain,(
% 2.18/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.18/1.01    inference(cnf_transformation,[],[f57])).
% 2.18/1.01  
% 2.18/1.01  fof(f17,axiom,(
% 2.18/1.01    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f46,plain,(
% 2.18/1.01    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.18/1.01    inference(ennf_transformation,[],[f17])).
% 2.18/1.01  
% 2.18/1.01  fof(f85,plain,(
% 2.18/1.01    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f46])).
% 2.18/1.01  
% 2.18/1.01  fof(f88,plain,(
% 2.18/1.01    l1_struct_0(sK0)),
% 2.18/1.01    inference(cnf_transformation,[],[f57])).
% 2.18/1.01  
% 2.18/1.01  fof(f90,plain,(
% 2.18/1.01    l1_struct_0(sK1)),
% 2.18/1.01    inference(cnf_transformation,[],[f57])).
% 2.18/1.01  
% 2.18/1.01  fof(f9,axiom,(
% 2.18/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f33,plain,(
% 2.18/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/1.01    inference(ennf_transformation,[],[f9])).
% 2.18/1.01  
% 2.18/1.01  fof(f70,plain,(
% 2.18/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/1.01    inference(cnf_transformation,[],[f33])).
% 2.18/1.01  
% 2.18/1.01  fof(f94,plain,(
% 2.18/1.01    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.18/1.01    inference(cnf_transformation,[],[f57])).
% 2.18/1.01  
% 2.18/1.01  fof(f15,axiom,(
% 2.18/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f42,plain,(
% 2.18/1.01    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.18/1.01    inference(ennf_transformation,[],[f15])).
% 2.18/1.01  
% 2.18/1.01  fof(f43,plain,(
% 2.18/1.01    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.18/1.01    inference(flattening,[],[f42])).
% 2.18/1.01  
% 2.18/1.01  fof(f81,plain,(
% 2.18/1.01    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f43])).
% 2.18/1.01  
% 2.18/1.01  fof(f91,plain,(
% 2.18/1.01    v1_funct_1(sK2)),
% 2.18/1.01    inference(cnf_transformation,[],[f57])).
% 2.18/1.01  
% 2.18/1.01  fof(f95,plain,(
% 2.18/1.01    v2_funct_1(sK2)),
% 2.18/1.01    inference(cnf_transformation,[],[f57])).
% 2.18/1.01  
% 2.18/1.01  fof(f92,plain,(
% 2.18/1.01    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.18/1.01    inference(cnf_transformation,[],[f57])).
% 2.18/1.01  
% 2.18/1.01  fof(f1,axiom,(
% 2.18/1.01    v1_xboole_0(k1_xboole_0)),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f58,plain,(
% 2.18/1.01    v1_xboole_0(k1_xboole_0)),
% 2.18/1.01    inference(cnf_transformation,[],[f1])).
% 2.18/1.01  
% 2.18/1.01  fof(f18,axiom,(
% 2.18/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f47,plain,(
% 2.18/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.18/1.01    inference(ennf_transformation,[],[f18])).
% 2.18/1.01  
% 2.18/1.01  fof(f48,plain,(
% 2.18/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.18/1.01    inference(flattening,[],[f47])).
% 2.18/1.01  
% 2.18/1.01  fof(f86,plain,(
% 2.18/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f48])).
% 2.18/1.01  
% 2.18/1.01  fof(f89,plain,(
% 2.18/1.01    ~v2_struct_0(sK1)),
% 2.18/1.01    inference(cnf_transformation,[],[f57])).
% 2.18/1.01  
% 2.18/1.01  fof(f5,axiom,(
% 2.18/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f27,plain,(
% 2.18/1.01    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.18/1.01    inference(ennf_transformation,[],[f5])).
% 2.18/1.01  
% 2.18/1.01  fof(f28,plain,(
% 2.18/1.01    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.18/1.01    inference(flattening,[],[f27])).
% 2.18/1.01  
% 2.18/1.01  fof(f66,plain,(
% 2.18/1.01    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f28])).
% 2.18/1.01  
% 2.18/1.01  fof(f7,axiom,(
% 2.18/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f31,plain,(
% 2.18/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/1.01    inference(ennf_transformation,[],[f7])).
% 2.18/1.01  
% 2.18/1.01  fof(f68,plain,(
% 2.18/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/1.01    inference(cnf_transformation,[],[f31])).
% 2.18/1.01  
% 2.18/1.01  fof(f4,axiom,(
% 2.18/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f25,plain,(
% 2.18/1.01    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.18/1.01    inference(ennf_transformation,[],[f4])).
% 2.18/1.01  
% 2.18/1.01  fof(f26,plain,(
% 2.18/1.01    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.18/1.01    inference(flattening,[],[f25])).
% 2.18/1.01  
% 2.18/1.01  fof(f63,plain,(
% 2.18/1.01    ( ! [X0,X1] : (v2_funct_1(X1) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f26])).
% 2.18/1.01  
% 2.18/1.01  fof(f2,axiom,(
% 2.18/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f23,plain,(
% 2.18/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.18/1.01    inference(ennf_transformation,[],[f2])).
% 2.18/1.01  
% 2.18/1.01  fof(f24,plain,(
% 2.18/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.18/1.01    inference(flattening,[],[f23])).
% 2.18/1.01  
% 2.18/1.01  fof(f60,plain,(
% 2.18/1.01    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f24])).
% 2.18/1.01  
% 2.18/1.01  fof(f59,plain,(
% 2.18/1.01    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f24])).
% 2.18/1.01  
% 2.18/1.01  fof(f80,plain,(
% 2.18/1.01    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f43])).
% 2.18/1.01  
% 2.18/1.01  fof(f65,plain,(
% 2.18/1.01    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f28])).
% 2.18/1.01  
% 2.18/1.01  fof(f64,plain,(
% 2.18/1.01    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f26])).
% 2.18/1.01  
% 2.18/1.01  fof(f3,axiom,(
% 2.18/1.01    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f62,plain,(
% 2.18/1.01    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.18/1.01    inference(cnf_transformation,[],[f3])).
% 2.18/1.01  
% 2.18/1.01  fof(f11,axiom,(
% 2.18/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f73,plain,(
% 2.18/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f11])).
% 2.18/1.01  
% 2.18/1.01  fof(f97,plain,(
% 2.18/1.01    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.18/1.01    inference(definition_unfolding,[],[f62,f73])).
% 2.18/1.01  
% 2.18/1.01  fof(f13,axiom,(
% 2.18/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f38,plain,(
% 2.18/1.01    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.18/1.01    inference(ennf_transformation,[],[f13])).
% 2.18/1.01  
% 2.18/1.01  fof(f39,plain,(
% 2.18/1.01    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.18/1.01    inference(flattening,[],[f38])).
% 2.18/1.01  
% 2.18/1.01  fof(f75,plain,(
% 2.18/1.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f39])).
% 2.18/1.01  
% 2.18/1.01  fof(f8,axiom,(
% 2.18/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f22,plain,(
% 2.18/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.18/1.01    inference(pure_predicate_removal,[],[f8])).
% 2.18/1.01  
% 2.18/1.01  fof(f32,plain,(
% 2.18/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/1.01    inference(ennf_transformation,[],[f22])).
% 2.18/1.01  
% 2.18/1.01  fof(f69,plain,(
% 2.18/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/1.01    inference(cnf_transformation,[],[f32])).
% 2.18/1.01  
% 2.18/1.01  fof(f10,axiom,(
% 2.18/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f34,plain,(
% 2.18/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.18/1.01    inference(ennf_transformation,[],[f10])).
% 2.18/1.01  
% 2.18/1.01  fof(f35,plain,(
% 2.18/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.18/1.01    inference(flattening,[],[f34])).
% 2.18/1.01  
% 2.18/1.01  fof(f53,plain,(
% 2.18/1.01    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.18/1.01    inference(nnf_transformation,[],[f35])).
% 2.18/1.01  
% 2.18/1.01  fof(f71,plain,(
% 2.18/1.01    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f53])).
% 2.18/1.01  
% 2.18/1.01  fof(f6,axiom,(
% 2.18/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f29,plain,(
% 2.18/1.01    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.18/1.01    inference(ennf_transformation,[],[f6])).
% 2.18/1.01  
% 2.18/1.01  fof(f30,plain,(
% 2.18/1.01    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.18/1.01    inference(flattening,[],[f29])).
% 2.18/1.01  
% 2.18/1.01  fof(f67,plain,(
% 2.18/1.01    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f30])).
% 2.18/1.01  
% 2.18/1.01  fof(f99,plain,(
% 2.18/1.01    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/1.01    inference(definition_unfolding,[],[f67,f73])).
% 2.18/1.01  
% 2.18/1.01  fof(f16,axiom,(
% 2.18/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f44,plain,(
% 2.18/1.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.18/1.01    inference(ennf_transformation,[],[f16])).
% 2.18/1.01  
% 2.18/1.01  fof(f45,plain,(
% 2.18/1.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.18/1.01    inference(flattening,[],[f44])).
% 2.18/1.01  
% 2.18/1.01  fof(f84,plain,(
% 2.18/1.01    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f45])).
% 2.18/1.01  
% 2.18/1.01  fof(f83,plain,(
% 2.18/1.01    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f45])).
% 2.18/1.01  
% 2.18/1.01  fof(f14,axiom,(
% 2.18/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f40,plain,(
% 2.18/1.01    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.18/1.01    inference(ennf_transformation,[],[f14])).
% 2.18/1.01  
% 2.18/1.01  fof(f41,plain,(
% 2.18/1.01    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.18/1.01    inference(flattening,[],[f40])).
% 2.18/1.01  
% 2.18/1.01  fof(f79,plain,(
% 2.18/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f41])).
% 2.18/1.01  
% 2.18/1.01  fof(f19,axiom,(
% 2.18/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f49,plain,(
% 2.18/1.01    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.18/1.01    inference(ennf_transformation,[],[f19])).
% 2.18/1.01  
% 2.18/1.01  fof(f50,plain,(
% 2.18/1.01    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.18/1.01    inference(flattening,[],[f49])).
% 2.18/1.01  
% 2.18/1.01  fof(f87,plain,(
% 2.18/1.01    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f50])).
% 2.18/1.01  
% 2.18/1.01  fof(f78,plain,(
% 2.18/1.01    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f41])).
% 2.18/1.01  
% 2.18/1.01  fof(f12,axiom,(
% 2.18/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f36,plain,(
% 2.18/1.01    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.18/1.01    inference(ennf_transformation,[],[f12])).
% 2.18/1.01  
% 2.18/1.01  fof(f37,plain,(
% 2.18/1.01    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.18/1.01    inference(flattening,[],[f36])).
% 2.18/1.01  
% 2.18/1.01  fof(f74,plain,(
% 2.18/1.01    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f37])).
% 2.18/1.01  
% 2.18/1.01  fof(f96,plain,(
% 2.18/1.01    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.18/1.01    inference(cnf_transformation,[],[f57])).
% 2.18/1.01  
% 2.18/1.01  cnf(c_32,negated_conjecture,
% 2.18/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.18/1.01      inference(cnf_transformation,[],[f93]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_777,negated_conjecture,
% 2.18/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_32]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1338,plain,
% 2.18/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_777]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_26,plain,
% 2.18/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f85]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_37,negated_conjecture,
% 2.18/1.01      ( l1_struct_0(sK0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f88]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_447,plain,
% 2.18/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_26,c_37]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_448,plain,
% 2.18/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_447]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_771,plain,
% 2.18/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_448]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_35,negated_conjecture,
% 2.18/1.01      ( l1_struct_0(sK1) ),
% 2.18/1.01      inference(cnf_transformation,[],[f90]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_442,plain,
% 2.18/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_26,c_35]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_443,plain,
% 2.18/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_442]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_772,plain,
% 2.18/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_443]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1369,plain,
% 2.18/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.18/1.01      inference(light_normalisation,[status(thm)],[c_1338,c_771,c_772]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_12,plain,
% 2.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_787,plain,
% 2.18/1.01      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.18/1.01      | k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1329,plain,
% 2.18/1.01      ( k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54)
% 2.18/1.01      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_787]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1947,plain,
% 2.18/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_1369,c_1329]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_31,negated_conjecture,
% 2.18/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.18/1.01      inference(cnf_transformation,[],[f94]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_778,negated_conjecture,
% 2.18/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_31]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1366,plain,
% 2.18/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.18/1.01      inference(light_normalisation,[status(thm)],[c_778,c_771,c_772]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1949,plain,
% 2.18/1.01      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.18/1.01      inference(demodulation,[status(thm)],[c_1947,c_1366]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1986,plain,
% 2.18/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.18/1.01      inference(demodulation,[status(thm)],[c_1949,c_1947]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_21,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.01      | ~ v2_funct_1(X0)
% 2.18/1.01      | ~ v1_funct_1(X0)
% 2.18/1.01      | k2_relset_1(X1,X2,X0) != X2
% 2.18/1.01      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 2.18/1.01      | k1_xboole_0 = X2 ),
% 2.18/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_784,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 2.18/1.01      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.18/1.01      | ~ v2_funct_1(X0_54)
% 2.18/1.01      | ~ v1_funct_1(X0_54)
% 2.18/1.01      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.18/1.01      | k1_xboole_0 = X1_55
% 2.18/1.01      | k5_relat_1(k2_funct_1(X0_54),X0_54) = k6_partfun1(X1_55) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_21]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1332,plain,
% 2.18/1.01      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.18/1.01      | k1_xboole_0 = X1_55
% 2.18/1.01      | k5_relat_1(k2_funct_1(X0_54),X0_54) = k6_partfun1(X1_55)
% 2.18/1.01      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.18/1.01      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.18/1.01      | v2_funct_1(X0_54) != iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_784]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2881,plain,
% 2.18/1.01      ( k2_relat_1(sK2) = k1_xboole_0
% 2.18/1.01      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 2.18/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.18/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.18/1.01      | v2_funct_1(sK2) != iProver_top
% 2.18/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_1986,c_1332]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_34,negated_conjecture,
% 2.18/1.01      ( v1_funct_1(sK2) ),
% 2.18/1.01      inference(cnf_transformation,[],[f91]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_41,plain,
% 2.18/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_30,negated_conjecture,
% 2.18/1.01      ( v2_funct_1(sK2) ),
% 2.18/1.01      inference(cnf_transformation,[],[f95]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_44,plain,
% 2.18/1.01      ( v2_funct_1(sK2) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1988,plain,
% 2.18/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.18/1.01      inference(demodulation,[status(thm)],[c_1949,c_1369]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_33,negated_conjecture,
% 2.18/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.18/1.01      inference(cnf_transformation,[],[f92]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_776,negated_conjecture,
% 2.18/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_33]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1339,plain,
% 2.18/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_776]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1363,plain,
% 2.18/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.18/1.01      inference(light_normalisation,[status(thm)],[c_1339,c_771,c_772]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1989,plain,
% 2.18/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.18/1.01      inference(demodulation,[status(thm)],[c_1949,c_1363]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_0,plain,
% 2.18/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_27,plain,
% 2.18/1.01      ( v2_struct_0(X0)
% 2.18/1.01      | ~ l1_struct_0(X0)
% 2.18/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.18/1.01      inference(cnf_transformation,[],[f86]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_415,plain,
% 2.18/1.01      ( v2_struct_0(X0)
% 2.18/1.01      | ~ l1_struct_0(X0)
% 2.18/1.01      | u1_struct_0(X0) != k1_xboole_0 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_27]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_36,negated_conjecture,
% 2.18/1.01      ( ~ v2_struct_0(sK1) ),
% 2.18/1.01      inference(cnf_transformation,[],[f89]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_433,plain,
% 2.18/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_415,c_36]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_434,plain,
% 2.18/1.01      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_433]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_417,plain,
% 2.18/1.01      ( v2_struct_0(sK1)
% 2.18/1.01      | ~ l1_struct_0(sK1)
% 2.18/1.01      | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_415]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_436,plain,
% 2.18/1.01      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_434,c_36,c_35,c_417]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_773,plain,
% 2.18/1.01      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_436]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1357,plain,
% 2.18/1.01      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 2.18/1.01      inference(demodulation,[status(thm)],[c_772,c_773]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1990,plain,
% 2.18/1.01      ( k2_relat_1(sK2) != k1_xboole_0 ),
% 2.18/1.01      inference(demodulation,[status(thm)],[c_1949,c_1357]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4880,plain,
% 2.18/1.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_2881,c_41,c_44,c_1988,c_1989,c_1990]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_779,negated_conjecture,
% 2.18/1.01      ( v2_funct_1(sK2) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_30]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1337,plain,
% 2.18/1.01      ( v2_funct_1(sK2) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_779]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_7,plain,
% 2.18/1.01      ( ~ v2_funct_1(X0)
% 2.18/1.01      | ~ v1_relat_1(X0)
% 2.18/1.01      | ~ v1_funct_1(X0)
% 2.18/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_791,plain,
% 2.18/1.01      ( ~ v2_funct_1(X0_54)
% 2.18/1.01      | ~ v1_relat_1(X0_54)
% 2.18/1.01      | ~ v1_funct_1(X0_54)
% 2.18/1.01      | k2_relat_1(k2_funct_1(X0_54)) = k1_relat_1(X0_54) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1325,plain,
% 2.18/1.01      ( k2_relat_1(k2_funct_1(X0_54)) = k1_relat_1(X0_54)
% 2.18/1.01      | v2_funct_1(X0_54) != iProver_top
% 2.18/1.01      | v1_relat_1(X0_54) != iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_791]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2246,plain,
% 2.18/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.18/1.01      | v1_relat_1(sK2) != iProver_top
% 2.18/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_1337,c_1325]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_853,plain,
% 2.18/1.01      ( ~ v2_funct_1(sK2)
% 2.18/1.01      | ~ v1_relat_1(sK2)
% 2.18/1.01      | ~ v1_funct_1(sK2)
% 2.18/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_791]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_10,plain,
% 2.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.01      | v1_relat_1(X0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_788,plain,
% 2.18/1.01      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.18/1.01      | v1_relat_1(X0_54) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_10]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1636,plain,
% 2.18/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.18/1.01      | v1_relat_1(sK2) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_788]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2333,plain,
% 2.18/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_2246,c_34,c_32,c_30,c_853,c_1636]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_6,plain,
% 2.18/1.01      ( v2_funct_1(X0)
% 2.18/1.01      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 2.18/1.01      | ~ v1_relat_1(X1)
% 2.18/1.01      | ~ v1_relat_1(X0)
% 2.18/1.01      | ~ v1_funct_1(X1)
% 2.18/1.01      | ~ v1_funct_1(X0)
% 2.18/1.01      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_792,plain,
% 2.18/1.01      ( v2_funct_1(X0_54)
% 2.18/1.01      | ~ v2_funct_1(k5_relat_1(X0_54,X1_54))
% 2.18/1.01      | ~ v1_relat_1(X0_54)
% 2.18/1.01      | ~ v1_relat_1(X1_54)
% 2.18/1.01      | ~ v1_funct_1(X0_54)
% 2.18/1.01      | ~ v1_funct_1(X1_54)
% 2.18/1.01      | k1_relat_1(X1_54) != k2_relat_1(X0_54) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1324,plain,
% 2.18/1.01      ( k1_relat_1(X0_54) != k2_relat_1(X1_54)
% 2.18/1.01      | v2_funct_1(X1_54) = iProver_top
% 2.18/1.01      | v2_funct_1(k5_relat_1(X1_54,X0_54)) != iProver_top
% 2.18/1.01      | v1_relat_1(X1_54) != iProver_top
% 2.18/1.01      | v1_relat_1(X0_54) != iProver_top
% 2.18/1.01      | v1_funct_1(X1_54) != iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_792]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2645,plain,
% 2.18/1.01      ( k1_relat_1(X0_54) != k1_relat_1(sK2)
% 2.18/1.01      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_54)) != iProver_top
% 2.18/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.18/1.01      | v1_relat_1(X0_54) != iProver_top
% 2.18/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top
% 2.18/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_2333,c_1324]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_43,plain,
% 2.18/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1,plain,
% 2.18/1.01      ( ~ v1_relat_1(X0)
% 2.18/1.01      | ~ v1_funct_1(X0)
% 2.18/1.01      | v1_funct_1(k2_funct_1(X0)) ),
% 2.18/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_797,plain,
% 2.18/1.01      ( ~ v1_relat_1(X0_54)
% 2.18/1.01      | ~ v1_funct_1(X0_54)
% 2.18/1.01      | v1_funct_1(k2_funct_1(X0_54)) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_838,plain,
% 2.18/1.01      ( v1_relat_1(X0_54) != iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top
% 2.18/1.01      | v1_funct_1(k2_funct_1(X0_54)) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_797]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_840,plain,
% 2.18/1.01      ( v1_relat_1(sK2) != iProver_top
% 2.18/1.01      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.18/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_838]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2,plain,
% 2.18/1.01      ( ~ v1_relat_1(X0)
% 2.18/1.01      | v1_relat_1(k2_funct_1(X0))
% 2.18/1.01      | ~ v1_funct_1(X0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_796,plain,
% 2.18/1.01      ( ~ v1_relat_1(X0_54)
% 2.18/1.01      | v1_relat_1(k2_funct_1(X0_54))
% 2.18/1.01      | ~ v1_funct_1(X0_54) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_841,plain,
% 2.18/1.01      ( v1_relat_1(X0_54) != iProver_top
% 2.18/1.01      | v1_relat_1(k2_funct_1(X0_54)) = iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_796]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_843,plain,
% 2.18/1.01      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 2.18/1.01      | v1_relat_1(sK2) != iProver_top
% 2.18/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_841]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1637,plain,
% 2.18/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.18/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_1636]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3449,plain,
% 2.18/1.01      ( v1_funct_1(X0_54) != iProver_top
% 2.18/1.01      | k1_relat_1(X0_54) != k1_relat_1(sK2)
% 2.18/1.01      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_54)) != iProver_top
% 2.18/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.18/1.01      | v1_relat_1(X0_54) != iProver_top ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_2645,c_41,c_43,c_840,c_843,c_1637]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3450,plain,
% 2.18/1.01      ( k1_relat_1(X0_54) != k1_relat_1(sK2)
% 2.18/1.01      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_54)) != iProver_top
% 2.18/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.18/1.01      | v1_relat_1(X0_54) != iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top ),
% 2.18/1.01      inference(renaming,[status(thm)],[c_3449]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3461,plain,
% 2.18/1.01      ( v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
% 2.18/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.18/1.01      | v1_relat_1(sK2) != iProver_top
% 2.18/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.18/1.01      inference(equality_resolution,[status(thm)],[c_3450]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_812,plain,
% 2.18/1.01      ( k1_relat_1(X0_54) = k1_relat_1(X1_54) | X0_54 != X1_54 ),
% 2.18/1.01      theory(equality) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_825,plain,
% 2.18/1.01      ( k1_relat_1(sK2) = k1_relat_1(sK2) | sK2 != sK2 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_812]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_801,plain,( X0_54 = X0_54 ),theory(equality) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_834,plain,
% 2.18/1.01      ( sK2 = sK2 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_801]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3452,plain,
% 2.18/1.01      ( k1_relat_1(sK2) != k1_relat_1(sK2)
% 2.18/1.01      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
% 2.18/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.18/1.01      | v1_relat_1(sK2) != iProver_top
% 2.18/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_3450]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4040,plain,
% 2.18/1.01      ( v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
% 2.18/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_3461,c_41,c_43,c_825,c_834,c_1637,c_3452]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4883,plain,
% 2.18/1.01      ( v2_funct_1(k6_partfun1(k2_relat_1(sK2))) != iProver_top
% 2.18/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.18/1.01      inference(demodulation,[status(thm)],[c_4880,c_4040]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_802,plain,( X0_55 = X0_55 ),theory(equality) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1757,plain,
% 2.18/1.01      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_802]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_806,plain,
% 2.18/1.01      ( X0_55 != X1_55 | X2_55 != X1_55 | X2_55 = X0_55 ),
% 2.18/1.01      theory(equality) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1649,plain,
% 2.18/1.01      ( u1_struct_0(sK1) != X0_55
% 2.18/1.01      | u1_struct_0(sK1) = k1_xboole_0
% 2.18/1.01      | k1_xboole_0 != X0_55 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_806]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1849,plain,
% 2.18/1.01      ( u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.18/1.01      | u1_struct_0(sK1) = k1_xboole_0
% 2.18/1.01      | k1_xboole_0 != u1_struct_0(sK1) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_1649]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1724,plain,
% 2.18/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_55
% 2.18/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 2.18/1.01      | u1_struct_0(sK1) != X0_55 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_806]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1877,plain,
% 2.18/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 2.18/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 2.18/1.01      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_1724]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_22,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.01      | ~ v2_funct_1(X0)
% 2.18/1.01      | ~ v1_funct_1(X0)
% 2.18/1.01      | k2_relset_1(X1,X2,X0) != X2
% 2.18/1.01      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 2.18/1.01      | k1_xboole_0 = X2 ),
% 2.18/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_783,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 2.18/1.01      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.18/1.01      | ~ v2_funct_1(X0_54)
% 2.18/1.01      | ~ v1_funct_1(X0_54)
% 2.18/1.01      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.18/1.01      | k1_xboole_0 = X1_55
% 2.18/1.01      | k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_partfun1(X0_55) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_22]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1740,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0_54,X0_55,u1_struct_0(sK1))
% 2.18/1.01      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,u1_struct_0(sK1))))
% 2.18/1.01      | ~ v2_funct_1(X0_54)
% 2.18/1.01      | ~ v1_funct_1(X0_54)
% 2.18/1.01      | k2_relset_1(X0_55,u1_struct_0(sK1),X0_54) != u1_struct_0(sK1)
% 2.18/1.01      | k1_xboole_0 = u1_struct_0(sK1)
% 2.18/1.01      | k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_partfun1(X0_55) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_783]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1953,plain,
% 2.18/1.01      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.18/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.18/1.01      | ~ v2_funct_1(sK2)
% 2.18/1.01      | ~ v1_funct_1(sK2)
% 2.18/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 2.18/1.01      | k1_xboole_0 = u1_struct_0(sK1)
% 2.18/1.01      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(u1_struct_0(sK0)) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_1740]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_8,plain,
% 2.18/1.01      ( ~ v2_funct_1(X0)
% 2.18/1.01      | ~ v1_relat_1(X0)
% 2.18/1.01      | ~ v1_funct_1(X0)
% 2.18/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_790,plain,
% 2.18/1.01      ( ~ v2_funct_1(X0_54)
% 2.18/1.01      | ~ v1_relat_1(X0_54)
% 2.18/1.01      | ~ v1_funct_1(X0_54)
% 2.18/1.01      | k1_relat_1(k2_funct_1(X0_54)) = k2_relat_1(X0_54) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1326,plain,
% 2.18/1.01      ( k1_relat_1(k2_funct_1(X0_54)) = k2_relat_1(X0_54)
% 2.18/1.01      | v2_funct_1(X0_54) != iProver_top
% 2.18/1.01      | v1_relat_1(X0_54) != iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_790]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2269,plain,
% 2.18/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.18/1.01      | v1_relat_1(sK2) != iProver_top
% 2.18/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_1337,c_1326]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_856,plain,
% 2.18/1.01      ( ~ v2_funct_1(sK2)
% 2.18/1.01      | ~ v1_relat_1(sK2)
% 2.18/1.01      | ~ v1_funct_1(sK2)
% 2.18/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_790]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2369,plain,
% 2.18/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_2269,c_34,c_32,c_30,c_856,c_1636]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_5,plain,
% 2.18/1.01      ( v2_funct_1(X0)
% 2.18/1.01      | ~ v2_funct_1(k5_relat_1(X1,X0))
% 2.18/1.01      | ~ v1_relat_1(X0)
% 2.18/1.01      | ~ v1_relat_1(X1)
% 2.18/1.01      | ~ v1_funct_1(X0)
% 2.18/1.01      | ~ v1_funct_1(X1)
% 2.18/1.01      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 2.18/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_793,plain,
% 2.18/1.01      ( v2_funct_1(X0_54)
% 2.18/1.01      | ~ v2_funct_1(k5_relat_1(X1_54,X0_54))
% 2.18/1.01      | ~ v1_relat_1(X0_54)
% 2.18/1.01      | ~ v1_relat_1(X1_54)
% 2.18/1.01      | ~ v1_funct_1(X0_54)
% 2.18/1.01      | ~ v1_funct_1(X1_54)
% 2.18/1.01      | k1_relat_1(X0_54) != k2_relat_1(X1_54) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1323,plain,
% 2.18/1.01      ( k1_relat_1(X0_54) != k2_relat_1(X1_54)
% 2.18/1.01      | v2_funct_1(X0_54) = iProver_top
% 2.18/1.01      | v2_funct_1(k5_relat_1(X1_54,X0_54)) != iProver_top
% 2.18/1.01      | v1_relat_1(X0_54) != iProver_top
% 2.18/1.01      | v1_relat_1(X1_54) != iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top
% 2.18/1.01      | v1_funct_1(X1_54) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_793]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2374,plain,
% 2.18/1.01      ( k2_relat_1(X0_54) != k2_relat_1(sK2)
% 2.18/1.01      | v2_funct_1(k5_relat_1(X0_54,k2_funct_1(sK2))) != iProver_top
% 2.18/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.18/1.01      | v1_relat_1(X0_54) != iProver_top
% 2.18/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top
% 2.18/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_2369,c_1323]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3426,plain,
% 2.18/1.01      ( v1_funct_1(X0_54) != iProver_top
% 2.18/1.01      | k2_relat_1(X0_54) != k2_relat_1(sK2)
% 2.18/1.01      | v2_funct_1(k5_relat_1(X0_54,k2_funct_1(sK2))) != iProver_top
% 2.18/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.18/1.01      | v1_relat_1(X0_54) != iProver_top ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_2374,c_41,c_43,c_840,c_843,c_1637]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3427,plain,
% 2.18/1.01      ( k2_relat_1(X0_54) != k2_relat_1(sK2)
% 2.18/1.01      | v2_funct_1(k5_relat_1(X0_54,k2_funct_1(sK2))) != iProver_top
% 2.18/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.18/1.01      | v1_relat_1(X0_54) != iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top ),
% 2.18/1.01      inference(renaming,[status(thm)],[c_3426]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3438,plain,
% 2.18/1.01      ( v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top
% 2.18/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.18/1.01      | v1_relat_1(sK2) != iProver_top
% 2.18/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.18/1.01      inference(equality_resolution,[status(thm)],[c_3427]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_811,plain,
% 2.18/1.01      ( k2_relat_1(X0_54) = k2_relat_1(X1_54) | X0_54 != X1_54 ),
% 2.18/1.01      theory(equality) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_824,plain,
% 2.18/1.01      ( k2_relat_1(sK2) = k2_relat_1(sK2) | sK2 != sK2 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_811]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3429,plain,
% 2.18/1.01      ( k2_relat_1(sK2) != k2_relat_1(sK2)
% 2.18/1.01      | v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top
% 2.18/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.18/1.01      | v1_relat_1(sK2) != iProver_top
% 2.18/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_3427]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3961,plain,
% 2.18/1.01      ( v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top
% 2.18/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_3438,c_41,c_43,c_824,c_834,c_1637,c_3429]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_810,plain,
% 2.18/1.01      ( ~ v2_funct_1(X0_54) | v2_funct_1(X1_54) | X1_54 != X0_54 ),
% 2.18/1.01      theory(equality) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3278,plain,
% 2.18/1.01      ( ~ v2_funct_1(X0_54)
% 2.18/1.01      | v2_funct_1(k5_relat_1(X1_54,k2_funct_1(X2_54)))
% 2.18/1.01      | k5_relat_1(X1_54,k2_funct_1(X2_54)) != X0_54 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_810]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_5486,plain,
% 2.18/1.01      ( v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2)))
% 2.18/1.01      | ~ v2_funct_1(k6_partfun1(u1_struct_0(sK0)))
% 2.18/1.01      | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_partfun1(u1_struct_0(sK0)) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_3278]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_5487,plain,
% 2.18/1.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) != k6_partfun1(u1_struct_0(sK0))
% 2.18/1.01      | v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) = iProver_top
% 2.18/1.01      | v2_funct_1(k6_partfun1(u1_struct_0(sK0))) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_5486]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3,plain,
% 2.18/1.01      ( v2_funct_1(k6_partfun1(X0)) ),
% 2.18/1.01      inference(cnf_transformation,[],[f97]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_795,plain,
% 2.18/1.01      ( v2_funct_1(k6_partfun1(X0_55)) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_6643,plain,
% 2.18/1.01      ( v2_funct_1(k6_partfun1(u1_struct_0(sK0))) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_795]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_6644,plain,
% 2.18/1.01      ( v2_funct_1(k6_partfun1(u1_struct_0(sK0))) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_6643]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_6677,plain,
% 2.18/1.01      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_4883,c_34,c_41,c_33,c_32,c_43,c_30,c_824,c_834,c_778,
% 2.18/1.01                 c_773,c_772,c_1637,c_1757,c_1849,c_1877,c_1953,c_3429,
% 2.18/1.01                 c_5487,c_6644]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1333,plain,
% 2.18/1.01      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.18/1.01      | k1_xboole_0 = X1_55
% 2.18/1.01      | k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_partfun1(X0_55)
% 2.18/1.01      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.18/1.01      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.18/1.01      | v2_funct_1(X0_54) != iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_783]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3709,plain,
% 2.18/1.01      ( k2_relat_1(sK2) = k1_xboole_0
% 2.18/1.01      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0))
% 2.18/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.18/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.18/1.01      | v2_funct_1(sK2) != iProver_top
% 2.18/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_1986,c_1333]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_5557,plain,
% 2.18/1.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0)) ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_3709,c_41,c_44,c_1988,c_1989,c_1990]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_17,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.18/1.01      | v1_partfun1(X0,X1)
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.01      | ~ v1_funct_1(X0)
% 2.18/1.01      | k1_xboole_0 = X2 ),
% 2.18/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_11,plain,
% 2.18/1.01      ( v4_relat_1(X0,X1)
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.18/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_14,plain,
% 2.18/1.01      ( ~ v1_partfun1(X0,X1)
% 2.18/1.01      | ~ v4_relat_1(X0,X1)
% 2.18/1.01      | ~ v1_relat_1(X0)
% 2.18/1.01      | k1_relat_1(X0) = X1 ),
% 2.18/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_489,plain,
% 2.18/1.01      ( ~ v1_partfun1(X0,X1)
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.01      | ~ v1_relat_1(X0)
% 2.18/1.01      | k1_relat_1(X0) = X1 ),
% 2.18/1.01      inference(resolution,[status(thm)],[c_11,c_14]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_493,plain,
% 2.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.01      | ~ v1_partfun1(X0,X1)
% 2.18/1.01      | k1_relat_1(X0) = X1 ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_489,c_14,c_11,c_10]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_494,plain,
% 2.18/1.01      ( ~ v1_partfun1(X0,X1)
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.01      | k1_relat_1(X0) = X1 ),
% 2.18/1.01      inference(renaming,[status(thm)],[c_493]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_533,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.18/1.01      | ~ v1_funct_1(X0)
% 2.18/1.01      | k1_relat_1(X0) = X1
% 2.18/1.01      | k1_xboole_0 = X2 ),
% 2.18/1.01      inference(resolution,[status(thm)],[c_17,c_494]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_537,plain,
% 2.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.01      | ~ v1_funct_2(X0,X1,X2)
% 2.18/1.01      | ~ v1_funct_1(X0)
% 2.18/1.01      | k1_relat_1(X0) = X1
% 2.18/1.01      | k1_xboole_0 = X2 ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_533,c_17,c_494]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_538,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.01      | ~ v1_funct_1(X0)
% 2.18/1.01      | k1_relat_1(X0) = X1
% 2.18/1.01      | k1_xboole_0 = X2 ),
% 2.18/1.01      inference(renaming,[status(thm)],[c_537]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_769,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 2.18/1.01      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.18/1.01      | ~ v1_funct_1(X0_54)
% 2.18/1.01      | k1_relat_1(X0_54) = X0_55
% 2.18/1.01      | k1_xboole_0 = X1_55 ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_538]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1344,plain,
% 2.18/1.01      ( k1_relat_1(X0_54) = X0_55
% 2.18/1.01      | k1_xboole_0 = X1_55
% 2.18/1.01      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.18/1.01      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_769]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4895,plain,
% 2.18/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.18/1.01      | k2_relat_1(sK2) = k1_xboole_0
% 2.18/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.18/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_1988,c_1344]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_5291,plain,
% 2.18/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_4895,c_41,c_1989,c_1990]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_5559,plain,
% 2.18/1.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.18/1.01      inference(light_normalisation,[status(thm)],[c_5557,c_5291]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_9,plain,
% 2.18/1.01      ( ~ v2_funct_1(X0)
% 2.18/1.01      | ~ v1_relat_1(X0)
% 2.18/1.01      | ~ v1_relat_1(X1)
% 2.18/1.01      | ~ v1_funct_1(X0)
% 2.18/1.01      | ~ v1_funct_1(X1)
% 2.18/1.01      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 2.18/1.01      | k1_relat_1(X0) != k2_relat_1(X1)
% 2.18/1.01      | k2_funct_1(X0) = X1 ),
% 2.18/1.01      inference(cnf_transformation,[],[f99]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_789,plain,
% 2.18/1.01      ( ~ v2_funct_1(X0_54)
% 2.18/1.01      | ~ v1_relat_1(X0_54)
% 2.18/1.01      | ~ v1_relat_1(X1_54)
% 2.18/1.01      | ~ v1_funct_1(X0_54)
% 2.18/1.01      | ~ v1_funct_1(X1_54)
% 2.18/1.01      | k1_relat_1(X0_54) != k2_relat_1(X1_54)
% 2.18/1.01      | k5_relat_1(X1_54,X0_54) != k6_partfun1(k2_relat_1(X0_54))
% 2.18/1.01      | k2_funct_1(X0_54) = X1_54 ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_9]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1327,plain,
% 2.18/1.01      ( k1_relat_1(X0_54) != k2_relat_1(X1_54)
% 2.18/1.01      | k5_relat_1(X1_54,X0_54) != k6_partfun1(k2_relat_1(X0_54))
% 2.18/1.01      | k2_funct_1(X0_54) = X1_54
% 2.18/1.01      | v2_funct_1(X0_54) != iProver_top
% 2.18/1.01      | v1_relat_1(X0_54) != iProver_top
% 2.18/1.01      | v1_relat_1(X1_54) != iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top
% 2.18/1.01      | v1_funct_1(X1_54) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_5563,plain,
% 2.18/1.01      ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 2.18/1.01      | k6_partfun1(k2_relat_1(k2_funct_1(sK2))) != k6_partfun1(k1_relat_1(sK2))
% 2.18/1.01      | k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.18/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.18/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.18/1.01      | v1_relat_1(sK2) != iProver_top
% 2.18/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.18/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_5559,c_1327]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_5564,plain,
% 2.18/1.01      ( k2_relat_1(sK2) != k2_relat_1(sK2)
% 2.18/1.01      | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(k1_relat_1(sK2))
% 2.18/1.01      | k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.18/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.18/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.18/1.01      | v1_relat_1(sK2) != iProver_top
% 2.18/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.18/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.18/1.01      inference(light_normalisation,[status(thm)],[c_5563,c_2333,c_2369]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_5565,plain,
% 2.18/1.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.18/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.18/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.18/1.01      | v1_relat_1(sK2) != iProver_top
% 2.18/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.18/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.18/1.01      inference(equality_resolution_simp,[status(thm)],[c_5564]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_5619,plain,
% 2.18/1.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.18/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_5565,c_41,c_43,c_840,c_843,c_1637]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_6686,plain,
% 2.18/1.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_6677,c_5619]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_23,plain,
% 2.18/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.18/1.01      | ~ v1_relat_1(X0)
% 2.18/1.01      | ~ v1_funct_1(X0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f84]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_782,plain,
% 2.18/1.01      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_54),k2_relat_1(X0_54))))
% 2.18/1.01      | ~ v1_relat_1(X0_54)
% 2.18/1.01      | ~ v1_funct_1(X0_54) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_23]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1334,plain,
% 2.18/1.01      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_54),k2_relat_1(X0_54)))) = iProver_top
% 2.18/1.01      | v1_relat_1(X0_54) != iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_782]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2372,plain,
% 2.18/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) = iProver_top
% 2.18/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.18/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_2369,c_1334]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2399,plain,
% 2.18/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.18/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.18/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.18/1.01      inference(light_normalisation,[status(thm)],[c_2372,c_2333]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_876,plain,
% 2.18/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 2.18/1.01      | ~ v1_relat_1(sK2)
% 2.18/1.01      | ~ v1_funct_1(sK2) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_782]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_875,plain,
% 2.18/1.01      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_54),k2_relat_1(X0_54)))) = iProver_top
% 2.18/1.01      | v1_relat_1(X0_54) != iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_782]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_877,plain,
% 2.18/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 2.18/1.01      | v1_relat_1(sK2) != iProver_top
% 2.18/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_875]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_24,plain,
% 2.18/1.01      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.18/1.01      | ~ v1_relat_1(X0)
% 2.18/1.01      | ~ v1_funct_1(X0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_781,plain,
% 2.18/1.01      ( v1_funct_2(X0_54,k1_relat_1(X0_54),k2_relat_1(X0_54))
% 2.18/1.01      | ~ v1_relat_1(X0_54)
% 2.18/1.01      | ~ v1_funct_1(X0_54) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_24]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_878,plain,
% 2.18/1.01      ( v1_funct_2(X0_54,k1_relat_1(X0_54),k2_relat_1(X0_54)) = iProver_top
% 2.18/1.01      | v1_relat_1(X0_54) != iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_781]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_880,plain,
% 2.18/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
% 2.18/1.01      | v1_relat_1(sK2) != iProver_top
% 2.18/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_878]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_18,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.01      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.18/1.01      | ~ v2_funct_1(X0)
% 2.18/1.01      | ~ v1_funct_1(X0)
% 2.18/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.18/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_786,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 2.18/1.01      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.18/1.01      | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55)))
% 2.18/1.01      | ~ v2_funct_1(X0_54)
% 2.18/1.01      | ~ v1_funct_1(X0_54)
% 2.18/1.01      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1789,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0_54,k1_relat_1(X0_54),k2_relat_1(X0_54))
% 2.18/1.01      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_54),k2_relat_1(X0_54))))
% 2.18/1.01      | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0_54),k1_relat_1(X0_54))))
% 2.18/1.01      | ~ v2_funct_1(X0_54)
% 2.18/1.01      | ~ v1_funct_1(X0_54)
% 2.18/1.01      | k2_relset_1(k1_relat_1(X0_54),k2_relat_1(X0_54),X0_54) != k2_relat_1(X0_54) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_786]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1800,plain,
% 2.18/1.01      ( k2_relset_1(k1_relat_1(X0_54),k2_relat_1(X0_54),X0_54) != k2_relat_1(X0_54)
% 2.18/1.01      | v1_funct_2(X0_54,k1_relat_1(X0_54),k2_relat_1(X0_54)) != iProver_top
% 2.18/1.01      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_54),k2_relat_1(X0_54)))) != iProver_top
% 2.18/1.01      | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0_54),k1_relat_1(X0_54)))) = iProver_top
% 2.18/1.01      | v2_funct_1(X0_54) != iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_1789]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1802,plain,
% 2.18/1.01      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
% 2.18/1.01      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.18/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.18/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.18/1.01      | v2_funct_1(sK2) != iProver_top
% 2.18/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_1800]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1808,plain,
% 2.18/1.01      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_54),k2_relat_1(X0_54))))
% 2.18/1.01      | k2_relset_1(k1_relat_1(X0_54),k2_relat_1(X0_54),X0_54) = k2_relat_1(X0_54) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_787]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1818,plain,
% 2.18/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 2.18/1.01      | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_1808]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2623,plain,
% 2.18/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_2399,c_34,c_41,c_32,c_43,c_44,c_876,c_877,c_880,
% 2.18/1.01                 c_1636,c_1637,c_1802,c_1818]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2628,plain,
% 2.18/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_2623,c_1329]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2633,plain,
% 2.18/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.18/1.01      inference(light_normalisation,[status(thm)],[c_2628,c_2333]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_28,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.01      | ~ v2_funct_1(X0)
% 2.18/1.01      | ~ v1_funct_1(X0)
% 2.18/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.18/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.18/1.01      inference(cnf_transformation,[],[f87]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_780,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 2.18/1.01      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.18/1.01      | ~ v2_funct_1(X0_54)
% 2.18/1.01      | ~ v1_funct_1(X0_54)
% 2.18/1.01      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.18/1.01      | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_28]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1336,plain,
% 2.18/1.01      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.18/1.01      | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54)
% 2.18/1.01      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.18/1.01      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.18/1.01      | v2_funct_1(X0_54) != iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_780]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3052,plain,
% 2.18/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.18/1.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.18/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.18/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.18/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_2633,c_1336]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_19,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.18/1.01      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.01      | ~ v2_funct_1(X0)
% 2.18/1.01      | ~ v1_funct_1(X0)
% 2.18/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.18/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_785,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 2.18/1.01      | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55)
% 2.18/1.01      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.18/1.01      | ~ v2_funct_1(X0_54)
% 2.18/1.01      | ~ v1_funct_1(X0_54)
% 2.18/1.01      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_19]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1790,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0_54,k1_relat_1(X0_54),k2_relat_1(X0_54))
% 2.18/1.01      | v1_funct_2(k2_funct_1(X0_54),k2_relat_1(X0_54),k1_relat_1(X0_54))
% 2.18/1.01      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_54),k2_relat_1(X0_54))))
% 2.18/1.01      | ~ v2_funct_1(X0_54)
% 2.18/1.01      | ~ v1_funct_1(X0_54)
% 2.18/1.01      | k2_relset_1(k1_relat_1(X0_54),k2_relat_1(X0_54),X0_54) != k2_relat_1(X0_54) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_785]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1796,plain,
% 2.18/1.01      ( k2_relset_1(k1_relat_1(X0_54),k2_relat_1(X0_54),X0_54) != k2_relat_1(X0_54)
% 2.18/1.01      | v1_funct_2(X0_54,k1_relat_1(X0_54),k2_relat_1(X0_54)) != iProver_top
% 2.18/1.01      | v1_funct_2(k2_funct_1(X0_54),k2_relat_1(X0_54),k1_relat_1(X0_54)) = iProver_top
% 2.18/1.01      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_54),k2_relat_1(X0_54)))) != iProver_top
% 2.18/1.01      | v2_funct_1(X0_54) != iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_1790]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1798,plain,
% 2.18/1.01      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
% 2.18/1.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 2.18/1.01      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.18/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.18/1.01      | v2_funct_1(sK2) != iProver_top
% 2.18/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_1796]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2098,plain,
% 2.18/1.01      ( ~ v1_funct_2(k2_funct_1(X0_54),k2_relat_1(X0_54),k1_relat_1(X0_54))
% 2.18/1.01      | ~ m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0_54),k1_relat_1(X0_54))))
% 2.18/1.01      | ~ v2_funct_1(k2_funct_1(X0_54))
% 2.18/1.01      | ~ v1_funct_1(k2_funct_1(X0_54))
% 2.18/1.01      | k2_relset_1(k2_relat_1(X0_54),k1_relat_1(X0_54),k2_funct_1(X0_54)) != k1_relat_1(X0_54)
% 2.18/1.01      | k2_tops_2(k2_relat_1(X0_54),k1_relat_1(X0_54),k2_funct_1(X0_54)) = k2_funct_1(k2_funct_1(X0_54)) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_780]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2114,plain,
% 2.18/1.01      ( k2_relset_1(k2_relat_1(X0_54),k1_relat_1(X0_54),k2_funct_1(X0_54)) != k1_relat_1(X0_54)
% 2.18/1.01      | k2_tops_2(k2_relat_1(X0_54),k1_relat_1(X0_54),k2_funct_1(X0_54)) = k2_funct_1(k2_funct_1(X0_54))
% 2.18/1.01      | v1_funct_2(k2_funct_1(X0_54),k2_relat_1(X0_54),k1_relat_1(X0_54)) != iProver_top
% 2.18/1.01      | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0_54),k1_relat_1(X0_54)))) != iProver_top
% 2.18/1.01      | v2_funct_1(k2_funct_1(X0_54)) != iProver_top
% 2.18/1.01      | v1_funct_1(k2_funct_1(X0_54)) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_2098]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2116,plain,
% 2.18/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
% 2.18/1.01      | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.18/1.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.18/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.18/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.18/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_2114]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4627,plain,
% 2.18/1.01      ( v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.18/1.01      | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2)) ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_3052,c_34,c_41,c_32,c_43,c_44,c_840,c_876,c_877,c_880,
% 2.18/1.01                 c_1636,c_1637,c_1798,c_1802,c_1818,c_2116,c_2633]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4628,plain,
% 2.18/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.18/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.18/1.01      inference(renaming,[status(thm)],[c_4627]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_6688,plain,
% 2.18/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2)) ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_6677,c_4628]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_6695,plain,
% 2.18/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.18/1.01      inference(demodulation,[status(thm)],[c_6686,c_6688]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2821,plain,
% 2.18/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.18/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.18/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.18/1.01      | v2_funct_1(sK2) != iProver_top
% 2.18/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_1986,c_1336]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4113,plain,
% 2.18/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_2821,c_41,c_44,c_1988,c_1989]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_15,plain,
% 2.18/1.01      ( r2_funct_2(X0,X1,X2,X2)
% 2.18/1.01      | ~ v1_funct_2(X3,X0,X1)
% 2.18/1.01      | ~ v1_funct_2(X2,X0,X1)
% 2.18/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.18/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.18/1.01      | ~ v1_funct_1(X3)
% 2.18/1.01      | ~ v1_funct_1(X2) ),
% 2.18/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_29,negated_conjecture,
% 2.18/1.01      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.18/1.01      inference(cnf_transformation,[],[f96]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_454,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.18/1.01      | ~ v1_funct_2(X3,X1,X2)
% 2.18/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.01      | ~ v1_funct_1(X0)
% 2.18/1.01      | ~ v1_funct_1(X3)
% 2.18/1.01      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X3
% 2.18/1.01      | u1_struct_0(sK1) != X2
% 2.18/1.01      | u1_struct_0(sK0) != X1
% 2.18/1.01      | sK2 != X3 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_455,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.18/1.01      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.18/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.18/1.01      | ~ v1_funct_1(X0)
% 2.18/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.18/1.01      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_454]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_770,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.18/1.01      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.18/1.01      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.18/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.18/1.01      | ~ v1_funct_1(X0_54)
% 2.18/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.18/1.01      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.18/1.01      inference(subtyping,[status(esa)],[c_455]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_799,plain,
% 2.18/1.01      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.18/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.18/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.18/1.01      | sP0_iProver_split
% 2.18/1.01      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.18/1.01      inference(splitting,
% 2.18/1.01                [splitting(split),new_symbols(definition,[])],
% 2.18/1.01                [c_770]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1342,plain,
% 2.18/1.01      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.18/1.01      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.18/1.01      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.18/1.01      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 2.18/1.01      | sP0_iProver_split = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_799]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1563,plain,
% 2.18/1.01      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.18/1.01      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.18/1.01      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.18/1.01      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 2.18/1.01      | sP0_iProver_split = iProver_top ),
% 2.18/1.01      inference(light_normalisation,[status(thm)],[c_1342,c_771,c_772]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_798,plain,
% 2.18/1.01      ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.18/1.01      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.18/1.01      | ~ v1_funct_1(X0_54)
% 2.18/1.01      | ~ sP0_iProver_split ),
% 2.18/1.01      inference(splitting,
% 2.18/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.18/1.01                [c_770]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1343,plain,
% 2.18/1.01      ( v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.18/1.01      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top
% 2.18/1.01      | sP0_iProver_split != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_798]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1426,plain,
% 2.18/1.01      ( v1_funct_2(X0_54,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.18/1.01      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.18/1.01      | v1_funct_1(X0_54) != iProver_top
% 2.18/1.01      | sP0_iProver_split != iProver_top ),
% 2.18/1.01      inference(light_normalisation,[status(thm)],[c_1343,c_771,c_772]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1569,plain,
% 2.18/1.01      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.18/1.01      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.18/1.01      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.18/1.01      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.18/1.01      inference(forward_subsumption_resolution,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_1563,c_1426]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1987,plain,
% 2.18/1.01      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 2.18/1.01      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.18/1.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.18/1.01      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.18/1.01      inference(demodulation,[status(thm)],[c_1949,c_1569]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4116,plain,
% 2.18/1.01      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 2.18/1.01      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.18/1.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.18/1.01      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 2.18/1.01      inference(demodulation,[status(thm)],[c_4113,c_1987]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_5296,plain,
% 2.18/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 2.18/1.01      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.18/1.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.18/1.01      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.18/1.02      inference(demodulation,[status(thm)],[c_5291,c_4116]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_7713,plain,
% 2.18/1.02      ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.18/1.02      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.18/1.02      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.18/1.02      inference(global_propositional_subsumption,
% 2.18/1.02                [status(thm)],
% 2.18/1.02                [c_5296,c_6695]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_8843,plain,
% 2.18/1.02      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.18/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.18/1.02      | v1_funct_1(sK2) != iProver_top ),
% 2.18/1.02      inference(demodulation,[status(thm)],[c_6695,c_7713]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(contradiction,plain,
% 2.18/1.02      ( $false ),
% 2.18/1.02      inference(minisat,
% 2.18/1.02                [status(thm)],
% 2.18/1.02                [c_8843,c_1637,c_880,c_877,c_43,c_41]) ).
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.18/1.02  
% 2.18/1.02  ------                               Statistics
% 2.18/1.02  
% 2.18/1.02  ------ General
% 2.18/1.02  
% 2.18/1.02  abstr_ref_over_cycles:                  0
% 2.18/1.02  abstr_ref_under_cycles:                 0
% 2.18/1.02  gc_basic_clause_elim:                   0
% 2.18/1.02  forced_gc_time:                         0
% 2.18/1.02  parsing_time:                           0.027
% 2.18/1.02  unif_index_cands_time:                  0.
% 2.18/1.02  unif_index_add_time:                    0.
% 2.18/1.02  orderings_time:                         0.
% 2.18/1.02  out_proof_time:                         0.018
% 2.18/1.02  total_time:                             0.383
% 2.18/1.02  num_of_symbols:                         63
% 2.18/1.02  num_of_terms:                           8041
% 2.18/1.02  
% 2.18/1.02  ------ Preprocessing
% 2.18/1.02  
% 2.18/1.02  num_of_splits:                          1
% 2.18/1.02  num_of_split_atoms:                     1
% 2.18/1.02  num_of_reused_defs:                     0
% 2.18/1.02  num_eq_ax_congr_red:                    7
% 2.18/1.02  num_of_sem_filtered_clauses:            2
% 2.18/1.02  num_of_subtypes:                        5
% 2.18/1.02  monotx_restored_types:                  1
% 2.18/1.02  sat_num_of_epr_types:                   0
% 2.18/1.02  sat_num_of_non_cyclic_types:            0
% 2.18/1.02  sat_guarded_non_collapsed_types:        1
% 2.18/1.02  num_pure_diseq_elim:                    0
% 2.18/1.02  simp_replaced_by:                       0
% 2.18/1.02  res_preprocessed:                       167
% 2.18/1.02  prep_upred:                             0
% 2.18/1.02  prep_unflattend:                        12
% 2.18/1.02  smt_new_axioms:                         0
% 2.18/1.02  pred_elim_cands:                        5
% 2.18/1.02  pred_elim:                              6
% 2.18/1.02  pred_elim_cl:                           7
% 2.18/1.02  pred_elim_cycles:                       8
% 2.18/1.02  merged_defs:                            0
% 2.18/1.02  merged_defs_ncl:                        0
% 2.18/1.02  bin_hyper_res:                          0
% 2.18/1.02  prep_cycles:                            4
% 2.18/1.02  pred_elim_time:                         0.008
% 2.18/1.02  splitting_time:                         0.
% 2.18/1.02  sem_filter_time:                        0.
% 2.18/1.02  monotx_time:                            0.001
% 2.18/1.02  subtype_inf_time:                       0.002
% 2.18/1.02  
% 2.18/1.02  ------ Problem properties
% 2.18/1.02  
% 2.18/1.02  clauses:                                31
% 2.18/1.02  conjectures:                            5
% 2.18/1.02  epr:                                    2
% 2.18/1.02  horn:                                   28
% 2.18/1.02  ground:                                 9
% 2.18/1.02  unary:                                  10
% 2.18/1.02  binary:                                 2
% 2.18/1.02  lits:                                   110
% 2.18/1.02  lits_eq:                                26
% 2.18/1.02  fd_pure:                                0
% 2.18/1.02  fd_pseudo:                              0
% 2.18/1.02  fd_cond:                                2
% 2.18/1.02  fd_pseudo_cond:                         2
% 2.18/1.02  ac_symbols:                             0
% 2.18/1.02  
% 2.18/1.02  ------ Propositional Solver
% 2.18/1.02  
% 2.18/1.02  prop_solver_calls:                      31
% 2.18/1.02  prop_fast_solver_calls:                 1834
% 2.18/1.02  smt_solver_calls:                       0
% 2.18/1.02  smt_fast_solver_calls:                  0
% 2.18/1.02  prop_num_of_clauses:                    3363
% 2.18/1.02  prop_preprocess_simplified:             8376
% 2.18/1.02  prop_fo_subsumed:                       150
% 2.18/1.02  prop_solver_time:                       0.
% 2.18/1.02  smt_solver_time:                        0.
% 2.18/1.02  smt_fast_solver_time:                   0.
% 2.18/1.02  prop_fast_solver_time:                  0.
% 2.18/1.02  prop_unsat_core_time:                   0.
% 2.18/1.02  
% 2.18/1.02  ------ QBF
% 2.18/1.02  
% 2.18/1.02  qbf_q_res:                              0
% 2.18/1.02  qbf_num_tautologies:                    0
% 2.18/1.02  qbf_prep_cycles:                        0
% 2.18/1.02  
% 2.18/1.02  ------ BMC1
% 2.18/1.02  
% 2.18/1.02  bmc1_current_bound:                     -1
% 2.18/1.02  bmc1_last_solved_bound:                 -1
% 2.18/1.02  bmc1_unsat_core_size:                   -1
% 2.18/1.02  bmc1_unsat_core_parents_size:           -1
% 2.18/1.02  bmc1_merge_next_fun:                    0
% 2.18/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.18/1.02  
% 2.18/1.02  ------ Instantiation
% 2.18/1.02  
% 2.18/1.02  inst_num_of_clauses:                    1182
% 2.18/1.02  inst_num_in_passive:                    310
% 2.18/1.02  inst_num_in_active:                     519
% 2.18/1.02  inst_num_in_unprocessed:                354
% 2.18/1.02  inst_num_of_loops:                      570
% 2.18/1.02  inst_num_of_learning_restarts:          0
% 2.18/1.02  inst_num_moves_active_passive:          45
% 2.18/1.02  inst_lit_activity:                      0
% 2.18/1.02  inst_lit_activity_moves:                0
% 2.18/1.02  inst_num_tautologies:                   0
% 2.18/1.02  inst_num_prop_implied:                  0
% 2.18/1.02  inst_num_existing_simplified:           0
% 2.18/1.02  inst_num_eq_res_simplified:             0
% 2.18/1.02  inst_num_child_elim:                    0
% 2.18/1.02  inst_num_of_dismatching_blockings:      456
% 2.18/1.02  inst_num_of_non_proper_insts:           1197
% 2.18/1.02  inst_num_of_duplicates:                 0
% 2.18/1.02  inst_inst_num_from_inst_to_res:         0
% 2.18/1.02  inst_dismatching_checking_time:         0.
% 2.18/1.02  
% 2.18/1.02  ------ Resolution
% 2.18/1.02  
% 2.18/1.02  res_num_of_clauses:                     0
% 2.18/1.02  res_num_in_passive:                     0
% 2.18/1.02  res_num_in_active:                      0
% 2.18/1.02  res_num_of_loops:                       171
% 2.18/1.02  res_forward_subset_subsumed:            75
% 2.18/1.02  res_backward_subset_subsumed:           4
% 2.18/1.02  res_forward_subsumed:                   0
% 2.18/1.02  res_backward_subsumed:                  0
% 2.18/1.02  res_forward_subsumption_resolution:     1
% 2.18/1.02  res_backward_subsumption_resolution:    0
% 2.18/1.02  res_clause_to_clause_subsumption:       378
% 2.18/1.02  res_orphan_elimination:                 0
% 2.18/1.02  res_tautology_del:                      105
% 2.18/1.02  res_num_eq_res_simplified:              0
% 2.18/1.02  res_num_sel_changes:                    0
% 2.18/1.02  res_moves_from_active_to_pass:          0
% 2.18/1.02  
% 2.18/1.02  ------ Superposition
% 2.18/1.02  
% 2.18/1.02  sup_time_total:                         0.
% 2.18/1.02  sup_time_generating:                    0.
% 2.18/1.02  sup_time_sim_full:                      0.
% 2.18/1.02  sup_time_sim_immed:                     0.
% 2.18/1.02  
% 2.18/1.02  sup_num_of_clauses:                     90
% 2.18/1.02  sup_num_in_active:                      76
% 2.18/1.02  sup_num_in_passive:                     14
% 2.18/1.02  sup_num_of_loops:                       112
% 2.18/1.02  sup_fw_superposition:                   79
% 2.18/1.02  sup_bw_superposition:                   68
% 2.18/1.02  sup_immediate_simplified:               49
% 2.18/1.02  sup_given_eliminated:                   0
% 2.18/1.02  comparisons_done:                       0
% 2.18/1.02  comparisons_avoided:                    6
% 2.18/1.02  
% 2.18/1.02  ------ Simplifications
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  sim_fw_subset_subsumed:                 18
% 2.18/1.02  sim_bw_subset_subsumed:                 10
% 2.18/1.02  sim_fw_subsumed:                        6
% 2.18/1.02  sim_bw_subsumed:                        0
% 2.18/1.02  sim_fw_subsumption_res:                 8
% 2.18/1.02  sim_bw_subsumption_res:                 0
% 2.18/1.02  sim_tautology_del:                      1
% 2.18/1.02  sim_eq_tautology_del:                   34
% 2.18/1.02  sim_eq_res_simp:                        4
% 2.18/1.02  sim_fw_demodulated:                     6
% 2.18/1.02  sim_bw_demodulated:                     38
% 2.18/1.02  sim_light_normalised:                   57
% 2.18/1.02  sim_joinable_taut:                      0
% 2.18/1.02  sim_joinable_simp:                      0
% 2.18/1.02  sim_ac_normalised:                      0
% 2.18/1.02  sim_smt_subsumption:                    0
% 2.18/1.02  
%------------------------------------------------------------------------------
