%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:37 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  219 (10518 expanded)
%              Number of clauses        :  146 (3856 expanded)
%              Number of leaves         :   19 (2769 expanded)
%              Depth                    :   28
%              Number of atoms          :  815 (62109 expanded)
%              Number of equality atoms :  343 (11122 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f47,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f46,f45,f44])).

fof(f70,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f47])).

fof(f68,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f72,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
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

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f51,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f52,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f60])).

fof(f76,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_26,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_584,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1025,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_584])).

cnf(c_16,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_592,plain,
    ( ~ l1_struct_0(X0_53)
    | u1_struct_0(X0_53) = k2_struct_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1018,plain,
    ( u1_struct_0(X0_53) = k2_struct_0(X0_53)
    | l1_struct_0(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_1373,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1025,c_1018])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_587,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1022,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_1454,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1373,c_1022])).

cnf(c_28,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_583,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1026,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_1374,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1026,c_1018])).

cnf(c_22,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_588,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1456,plain,
    ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1373,c_588])).

cnf(c_1523,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1374,c_1456])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_596,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1014,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_1382,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1022,c_1014])).

cnf(c_1570,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1382,c_1373,c_1374])).

cnf(c_1590,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1523,c_1570])).

cnf(c_1603,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1454,c_1374,c_1590])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_17,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_310,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_311,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_44,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_313,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_311,c_27,c_26,c_44])).

cnf(c_323,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_313])).

cnf(c_324,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_10,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_385,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_324,c_10])).

cnf(c_5,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_401,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_385,c_5])).

cnf(c_582,plain,
    ( ~ v1_funct_2(X0_51,X0_52,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | k1_relat_1(X0_51) = X0_52 ),
    inference(subtyping,[status(esa)],[c_401])).

cnf(c_1027,plain,
    ( k1_relat_1(X0_51) = X0_52
    | v1_funct_2(X0_51,X0_52,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_582])).

cnf(c_1594,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1590,c_1373])).

cnf(c_2403,plain,
    ( k1_relat_1(X0_51) = X0_52
    | v1_funct_2(X0_51,X0_52,k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1027,c_1594])).

cnf(c_2412,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1603,c_2403])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_32,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_601,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | ~ v1_relat_1(X1_51)
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1009,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
    | v1_relat_1(X1_51) != iProver_top
    | v1_relat_1(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_601])).

cnf(c_1336,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1022,c_1009])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_600,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1350,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_1351,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1350])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_586,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1023,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_1455,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1373,c_1023])).

cnf(c_1567,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1455,c_1374])).

cnf(c_1593,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1590,c_1567])).

cnf(c_3021,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2412,c_32,c_1336,c_1351,c_1593])).

cnf(c_1592,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1590,c_1570])).

cnf(c_3028,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3021,c_1592])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_590,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ l1_struct_0(X1_53)
    | ~ l1_struct_0(X0_53)
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51))
    | k2_relset_1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51) != k2_struct_0(X1_53) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1020,plain,
    ( k2_relset_1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51) != k2_struct_0(X1_53)
    | v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | l1_struct_0(X1_53) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_2318,plain,
    ( k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
    | v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1374,c_1020])).

cnf(c_2381,plain,
    ( k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
    | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2318,c_1374])).

cnf(c_29,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2979,plain,
    ( l1_struct_0(X0_53) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2381,c_29])).

cnf(c_2980,plain,
    ( k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
    | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2979])).

cnf(c_2993,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_struct_0(sK1)
    | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),X0_51)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1594,c_2980])).

cnf(c_3001,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
    | v1_funct_2(X0_51,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0_51)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2993,c_1590,c_1594])).

cnf(c_31,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3726,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_2(X0_51,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0_51)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3001,c_31])).

cnf(c_3727,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
    | v1_funct_2(X0_51,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0_51)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3726])).

cnf(c_3732,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
    | v1_funct_2(X0_51,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),X0_51)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3727,c_3021])).

cnf(c_4214,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3028,c_3732])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_591,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1019,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51)
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_591])).

cnf(c_2204,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1592,c_1019])).

cnf(c_21,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_35,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2512,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2204,c_32,c_35,c_1593,c_1603])).

cnf(c_3027,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3021,c_2512])).

cnf(c_4220,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4214,c_3027])).

cnf(c_3029,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3021,c_1593])).

cnf(c_3030,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3021,c_1603])).

cnf(c_4231,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4220,c_32,c_35,c_3029,c_3030])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_595,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1015,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) = iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_595])).

cnf(c_2252,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1592,c_1015])).

cnf(c_3378,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2252,c_32,c_35,c_1593,c_1603])).

cnf(c_3382,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3378,c_3021])).

cnf(c_3385,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3382,c_1014])).

cnf(c_585,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1024,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_585])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_599,plain,
    ( ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1011,plain,
    ( k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51)
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_1717,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1024,c_1011])).

cnf(c_641,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_599])).

cnf(c_1337,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1336])).

cnf(c_1988,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1717,c_25,c_21,c_641,c_1337,c_1350])).

cnf(c_3392,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3385,c_1988])).

cnf(c_3479,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3392,c_1019])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_597,plain,
    ( ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | k2_funct_1(k2_funct_1(X0_51)) = X0_51 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1013,plain,
    ( k2_funct_1(k2_funct_1(X0_51)) = X0_51
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_597])).

cnf(c_1450,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1024,c_1013])).

cnf(c_647,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_597])).

cnf(c_1984,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1450,c_25,c_21,c_647,c_1337,c_1350])).

cnf(c_3499,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3479,c_1984])).

cnf(c_33,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_662,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_592])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_593,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | v1_funct_1(k2_funct_1(X0_51))
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1269,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_593])).

cnf(c_1270,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1269])).

cnf(c_607,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_1291,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_52
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0_52 ),
    inference(instantiation,[status(thm)],[c_607])).

cnf(c_1354,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1291])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_594,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1016,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_594])).

cnf(c_2205,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1592,c_1016])).

cnf(c_3370,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2205,c_32,c_35,c_1593,c_1603])).

cnf(c_3374,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3370,c_3021])).

cnf(c_3617,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3499,c_26,c_32,c_33,c_34,c_35,c_662,c_588,c_1270,c_1354,c_3374,c_3382])).

cnf(c_4236,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_4231,c_3617])).

cnf(c_11,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_20,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_420,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_421,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_581,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_421])).

cnf(c_1028,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_581])).

cnf(c_1453,plain,
    ( k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1373,c_1028])).

cnf(c_2133,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1453,c_1374,c_1590])).

cnf(c_2515,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2512,c_2133])).

cnf(c_3305,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2515,c_3021])).

cnf(c_4239,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4236,c_3305])).

cnf(c_4240,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4239])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4240,c_3030,c_3029,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:17:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.67/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.01  
% 2.67/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.67/1.01  
% 2.67/1.01  ------  iProver source info
% 2.67/1.01  
% 2.67/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.67/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.67/1.01  git: non_committed_changes: false
% 2.67/1.01  git: last_make_outside_of_git: false
% 2.67/1.01  
% 2.67/1.01  ------ 
% 2.67/1.01  
% 2.67/1.01  ------ Input Options
% 2.67/1.01  
% 2.67/1.01  --out_options                           all
% 2.67/1.01  --tptp_safe_out                         true
% 2.67/1.01  --problem_path                          ""
% 2.67/1.01  --include_path                          ""
% 2.67/1.01  --clausifier                            res/vclausify_rel
% 2.67/1.01  --clausifier_options                    --mode clausify
% 2.67/1.01  --stdin                                 false
% 2.67/1.01  --stats_out                             all
% 2.67/1.01  
% 2.67/1.01  ------ General Options
% 2.67/1.01  
% 2.67/1.01  --fof                                   false
% 2.67/1.01  --time_out_real                         305.
% 2.67/1.01  --time_out_virtual                      -1.
% 2.67/1.01  --symbol_type_check                     false
% 2.67/1.01  --clausify_out                          false
% 2.67/1.01  --sig_cnt_out                           false
% 2.67/1.01  --trig_cnt_out                          false
% 2.67/1.01  --trig_cnt_out_tolerance                1.
% 2.67/1.01  --trig_cnt_out_sk_spl                   false
% 2.67/1.01  --abstr_cl_out                          false
% 2.67/1.01  
% 2.67/1.01  ------ Global Options
% 2.67/1.01  
% 2.67/1.01  --schedule                              default
% 2.67/1.01  --add_important_lit                     false
% 2.67/1.01  --prop_solver_per_cl                    1000
% 2.67/1.01  --min_unsat_core                        false
% 2.67/1.01  --soft_assumptions                      false
% 2.67/1.01  --soft_lemma_size                       3
% 2.67/1.01  --prop_impl_unit_size                   0
% 2.67/1.01  --prop_impl_unit                        []
% 2.67/1.01  --share_sel_clauses                     true
% 2.67/1.01  --reset_solvers                         false
% 2.67/1.01  --bc_imp_inh                            [conj_cone]
% 2.67/1.01  --conj_cone_tolerance                   3.
% 2.67/1.01  --extra_neg_conj                        none
% 2.67/1.01  --large_theory_mode                     true
% 2.67/1.01  --prolific_symb_bound                   200
% 2.67/1.01  --lt_threshold                          2000
% 2.67/1.01  --clause_weak_htbl                      true
% 2.67/1.01  --gc_record_bc_elim                     false
% 2.67/1.01  
% 2.67/1.01  ------ Preprocessing Options
% 2.67/1.01  
% 2.67/1.01  --preprocessing_flag                    true
% 2.67/1.01  --time_out_prep_mult                    0.1
% 2.67/1.01  --splitting_mode                        input
% 2.67/1.01  --splitting_grd                         true
% 2.67/1.01  --splitting_cvd                         false
% 2.67/1.01  --splitting_cvd_svl                     false
% 2.67/1.01  --splitting_nvd                         32
% 2.67/1.01  --sub_typing                            true
% 2.67/1.01  --prep_gs_sim                           true
% 2.67/1.01  --prep_unflatten                        true
% 2.67/1.01  --prep_res_sim                          true
% 2.67/1.01  --prep_upred                            true
% 2.67/1.01  --prep_sem_filter                       exhaustive
% 2.67/1.01  --prep_sem_filter_out                   false
% 2.67/1.01  --pred_elim                             true
% 2.67/1.01  --res_sim_input                         true
% 2.67/1.01  --eq_ax_congr_red                       true
% 2.67/1.01  --pure_diseq_elim                       true
% 2.67/1.01  --brand_transform                       false
% 2.67/1.01  --non_eq_to_eq                          false
% 2.67/1.01  --prep_def_merge                        true
% 2.67/1.01  --prep_def_merge_prop_impl              false
% 2.67/1.01  --prep_def_merge_mbd                    true
% 2.67/1.01  --prep_def_merge_tr_red                 false
% 2.67/1.01  --prep_def_merge_tr_cl                  false
% 2.67/1.01  --smt_preprocessing                     true
% 2.67/1.01  --smt_ac_axioms                         fast
% 2.67/1.01  --preprocessed_out                      false
% 2.67/1.01  --preprocessed_stats                    false
% 2.67/1.01  
% 2.67/1.01  ------ Abstraction refinement Options
% 2.67/1.01  
% 2.67/1.01  --abstr_ref                             []
% 2.67/1.01  --abstr_ref_prep                        false
% 2.67/1.01  --abstr_ref_until_sat                   false
% 2.67/1.01  --abstr_ref_sig_restrict                funpre
% 2.67/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/1.01  --abstr_ref_under                       []
% 2.67/1.01  
% 2.67/1.01  ------ SAT Options
% 2.67/1.01  
% 2.67/1.01  --sat_mode                              false
% 2.67/1.01  --sat_fm_restart_options                ""
% 2.67/1.01  --sat_gr_def                            false
% 2.67/1.01  --sat_epr_types                         true
% 2.67/1.01  --sat_non_cyclic_types                  false
% 2.67/1.01  --sat_finite_models                     false
% 2.67/1.01  --sat_fm_lemmas                         false
% 2.67/1.01  --sat_fm_prep                           false
% 2.67/1.01  --sat_fm_uc_incr                        true
% 2.67/1.01  --sat_out_model                         small
% 2.67/1.01  --sat_out_clauses                       false
% 2.67/1.01  
% 2.67/1.01  ------ QBF Options
% 2.67/1.01  
% 2.67/1.01  --qbf_mode                              false
% 2.67/1.01  --qbf_elim_univ                         false
% 2.67/1.01  --qbf_dom_inst                          none
% 2.67/1.01  --qbf_dom_pre_inst                      false
% 2.67/1.01  --qbf_sk_in                             false
% 2.67/1.01  --qbf_pred_elim                         true
% 2.67/1.01  --qbf_split                             512
% 2.67/1.01  
% 2.67/1.01  ------ BMC1 Options
% 2.67/1.01  
% 2.67/1.01  --bmc1_incremental                      false
% 2.67/1.01  --bmc1_axioms                           reachable_all
% 2.67/1.01  --bmc1_min_bound                        0
% 2.67/1.01  --bmc1_max_bound                        -1
% 2.67/1.01  --bmc1_max_bound_default                -1
% 2.67/1.01  --bmc1_symbol_reachability              true
% 2.67/1.01  --bmc1_property_lemmas                  false
% 2.67/1.01  --bmc1_k_induction                      false
% 2.67/1.01  --bmc1_non_equiv_states                 false
% 2.67/1.01  --bmc1_deadlock                         false
% 2.67/1.01  --bmc1_ucm                              false
% 2.67/1.01  --bmc1_add_unsat_core                   none
% 2.67/1.01  --bmc1_unsat_core_children              false
% 2.67/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/1.01  --bmc1_out_stat                         full
% 2.67/1.01  --bmc1_ground_init                      false
% 2.67/1.01  --bmc1_pre_inst_next_state              false
% 2.67/1.01  --bmc1_pre_inst_state                   false
% 2.67/1.01  --bmc1_pre_inst_reach_state             false
% 2.67/1.01  --bmc1_out_unsat_core                   false
% 2.67/1.01  --bmc1_aig_witness_out                  false
% 2.67/1.01  --bmc1_verbose                          false
% 2.67/1.01  --bmc1_dump_clauses_tptp                false
% 2.67/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.67/1.01  --bmc1_dump_file                        -
% 2.67/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.67/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.67/1.01  --bmc1_ucm_extend_mode                  1
% 2.67/1.01  --bmc1_ucm_init_mode                    2
% 2.67/1.01  --bmc1_ucm_cone_mode                    none
% 2.67/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.67/1.01  --bmc1_ucm_relax_model                  4
% 2.67/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.67/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/1.01  --bmc1_ucm_layered_model                none
% 2.67/1.01  --bmc1_ucm_max_lemma_size               10
% 2.67/1.01  
% 2.67/1.01  ------ AIG Options
% 2.67/1.01  
% 2.67/1.01  --aig_mode                              false
% 2.67/1.01  
% 2.67/1.01  ------ Instantiation Options
% 2.67/1.01  
% 2.67/1.01  --instantiation_flag                    true
% 2.67/1.01  --inst_sos_flag                         false
% 2.67/1.01  --inst_sos_phase                        true
% 2.67/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/1.01  --inst_lit_sel_side                     num_symb
% 2.67/1.01  --inst_solver_per_active                1400
% 2.67/1.01  --inst_solver_calls_frac                1.
% 2.67/1.01  --inst_passive_queue_type               priority_queues
% 2.67/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/1.01  --inst_passive_queues_freq              [25;2]
% 2.67/1.01  --inst_dismatching                      true
% 2.67/1.01  --inst_eager_unprocessed_to_passive     true
% 2.67/1.01  --inst_prop_sim_given                   true
% 2.67/1.01  --inst_prop_sim_new                     false
% 2.67/1.01  --inst_subs_new                         false
% 2.67/1.01  --inst_eq_res_simp                      false
% 2.67/1.01  --inst_subs_given                       false
% 2.67/1.01  --inst_orphan_elimination               true
% 2.67/1.01  --inst_learning_loop_flag               true
% 2.67/1.01  --inst_learning_start                   3000
% 2.67/1.01  --inst_learning_factor                  2
% 2.67/1.01  --inst_start_prop_sim_after_learn       3
% 2.67/1.01  --inst_sel_renew                        solver
% 2.67/1.01  --inst_lit_activity_flag                true
% 2.67/1.01  --inst_restr_to_given                   false
% 2.67/1.01  --inst_activity_threshold               500
% 2.67/1.01  --inst_out_proof                        true
% 2.67/1.01  
% 2.67/1.01  ------ Resolution Options
% 2.67/1.01  
% 2.67/1.01  --resolution_flag                       true
% 2.67/1.01  --res_lit_sel                           adaptive
% 2.67/1.01  --res_lit_sel_side                      none
% 2.67/1.01  --res_ordering                          kbo
% 2.67/1.01  --res_to_prop_solver                    active
% 2.67/1.01  --res_prop_simpl_new                    false
% 2.67/1.01  --res_prop_simpl_given                  true
% 2.67/1.01  --res_passive_queue_type                priority_queues
% 2.67/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/1.01  --res_passive_queues_freq               [15;5]
% 2.67/1.01  --res_forward_subs                      full
% 2.67/1.01  --res_backward_subs                     full
% 2.67/1.01  --res_forward_subs_resolution           true
% 2.67/1.01  --res_backward_subs_resolution          true
% 2.67/1.01  --res_orphan_elimination                true
% 2.67/1.01  --res_time_limit                        2.
% 2.67/1.01  --res_out_proof                         true
% 2.67/1.01  
% 2.67/1.01  ------ Superposition Options
% 2.67/1.01  
% 2.67/1.01  --superposition_flag                    true
% 2.67/1.01  --sup_passive_queue_type                priority_queues
% 2.67/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.67/1.01  --demod_completeness_check              fast
% 2.67/1.01  --demod_use_ground                      true
% 2.67/1.01  --sup_to_prop_solver                    passive
% 2.67/1.01  --sup_prop_simpl_new                    true
% 2.67/1.01  --sup_prop_simpl_given                  true
% 2.67/1.01  --sup_fun_splitting                     false
% 2.67/1.01  --sup_smt_interval                      50000
% 2.67/1.01  
% 2.67/1.01  ------ Superposition Simplification Setup
% 2.67/1.01  
% 2.67/1.01  --sup_indices_passive                   []
% 2.67/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.01  --sup_full_bw                           [BwDemod]
% 2.67/1.01  --sup_immed_triv                        [TrivRules]
% 2.67/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.01  --sup_immed_bw_main                     []
% 2.67/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.01  
% 2.67/1.01  ------ Combination Options
% 2.67/1.01  
% 2.67/1.01  --comb_res_mult                         3
% 2.67/1.01  --comb_sup_mult                         2
% 2.67/1.01  --comb_inst_mult                        10
% 2.67/1.01  
% 2.67/1.01  ------ Debug Options
% 2.67/1.01  
% 2.67/1.01  --dbg_backtrace                         false
% 2.67/1.01  --dbg_dump_prop_clauses                 false
% 2.67/1.01  --dbg_dump_prop_clauses_file            -
% 2.67/1.01  --dbg_out_stat                          false
% 2.67/1.01  ------ Parsing...
% 2.67/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.67/1.01  
% 2.67/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.67/1.01  
% 2.67/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.67/1.01  
% 2.67/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.67/1.01  ------ Proving...
% 2.67/1.01  ------ Problem Properties 
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  clauses                                 21
% 2.67/1.01  conjectures                             7
% 2.67/1.01  EPR                                     4
% 2.67/1.01  Horn                                    21
% 2.67/1.01  unary                                   8
% 2.67/1.01  binary                                  2
% 2.67/1.01  lits                                    68
% 2.67/1.01  lits eq                                 14
% 2.67/1.01  fd_pure                                 0
% 2.67/1.01  fd_pseudo                               0
% 2.67/1.01  fd_cond                                 0
% 2.67/1.01  fd_pseudo_cond                          1
% 2.67/1.01  AC symbols                              0
% 2.67/1.01  
% 2.67/1.01  ------ Schedule dynamic 5 is on 
% 2.67/1.01  
% 2.67/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  ------ 
% 2.67/1.01  Current options:
% 2.67/1.01  ------ 
% 2.67/1.01  
% 2.67/1.01  ------ Input Options
% 2.67/1.01  
% 2.67/1.01  --out_options                           all
% 2.67/1.01  --tptp_safe_out                         true
% 2.67/1.01  --problem_path                          ""
% 2.67/1.01  --include_path                          ""
% 2.67/1.01  --clausifier                            res/vclausify_rel
% 2.67/1.01  --clausifier_options                    --mode clausify
% 2.67/1.01  --stdin                                 false
% 2.67/1.01  --stats_out                             all
% 2.67/1.01  
% 2.67/1.01  ------ General Options
% 2.67/1.01  
% 2.67/1.01  --fof                                   false
% 2.67/1.01  --time_out_real                         305.
% 2.67/1.01  --time_out_virtual                      -1.
% 2.67/1.01  --symbol_type_check                     false
% 2.67/1.01  --clausify_out                          false
% 2.67/1.01  --sig_cnt_out                           false
% 2.67/1.01  --trig_cnt_out                          false
% 2.67/1.01  --trig_cnt_out_tolerance                1.
% 2.67/1.01  --trig_cnt_out_sk_spl                   false
% 2.67/1.01  --abstr_cl_out                          false
% 2.67/1.01  
% 2.67/1.01  ------ Global Options
% 2.67/1.01  
% 2.67/1.01  --schedule                              default
% 2.67/1.01  --add_important_lit                     false
% 2.67/1.01  --prop_solver_per_cl                    1000
% 2.67/1.01  --min_unsat_core                        false
% 2.67/1.01  --soft_assumptions                      false
% 2.67/1.01  --soft_lemma_size                       3
% 2.67/1.01  --prop_impl_unit_size                   0
% 2.67/1.01  --prop_impl_unit                        []
% 2.67/1.01  --share_sel_clauses                     true
% 2.67/1.01  --reset_solvers                         false
% 2.67/1.01  --bc_imp_inh                            [conj_cone]
% 2.67/1.01  --conj_cone_tolerance                   3.
% 2.67/1.01  --extra_neg_conj                        none
% 2.67/1.01  --large_theory_mode                     true
% 2.67/1.01  --prolific_symb_bound                   200
% 2.67/1.01  --lt_threshold                          2000
% 2.67/1.01  --clause_weak_htbl                      true
% 2.67/1.01  --gc_record_bc_elim                     false
% 2.67/1.01  
% 2.67/1.01  ------ Preprocessing Options
% 2.67/1.01  
% 2.67/1.01  --preprocessing_flag                    true
% 2.67/1.01  --time_out_prep_mult                    0.1
% 2.67/1.01  --splitting_mode                        input
% 2.67/1.01  --splitting_grd                         true
% 2.67/1.01  --splitting_cvd                         false
% 2.67/1.01  --splitting_cvd_svl                     false
% 2.67/1.01  --splitting_nvd                         32
% 2.67/1.01  --sub_typing                            true
% 2.67/1.01  --prep_gs_sim                           true
% 2.67/1.01  --prep_unflatten                        true
% 2.67/1.01  --prep_res_sim                          true
% 2.67/1.01  --prep_upred                            true
% 2.67/1.01  --prep_sem_filter                       exhaustive
% 2.67/1.01  --prep_sem_filter_out                   false
% 2.67/1.01  --pred_elim                             true
% 2.67/1.01  --res_sim_input                         true
% 2.67/1.01  --eq_ax_congr_red                       true
% 2.67/1.01  --pure_diseq_elim                       true
% 2.67/1.01  --brand_transform                       false
% 2.67/1.01  --non_eq_to_eq                          false
% 2.67/1.01  --prep_def_merge                        true
% 2.67/1.01  --prep_def_merge_prop_impl              false
% 2.67/1.01  --prep_def_merge_mbd                    true
% 2.67/1.01  --prep_def_merge_tr_red                 false
% 2.67/1.01  --prep_def_merge_tr_cl                  false
% 2.67/1.01  --smt_preprocessing                     true
% 2.67/1.01  --smt_ac_axioms                         fast
% 2.67/1.01  --preprocessed_out                      false
% 2.67/1.01  --preprocessed_stats                    false
% 2.67/1.01  
% 2.67/1.01  ------ Abstraction refinement Options
% 2.67/1.01  
% 2.67/1.01  --abstr_ref                             []
% 2.67/1.01  --abstr_ref_prep                        false
% 2.67/1.01  --abstr_ref_until_sat                   false
% 2.67/1.01  --abstr_ref_sig_restrict                funpre
% 2.67/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/1.01  --abstr_ref_under                       []
% 2.67/1.01  
% 2.67/1.01  ------ SAT Options
% 2.67/1.01  
% 2.67/1.01  --sat_mode                              false
% 2.67/1.01  --sat_fm_restart_options                ""
% 2.67/1.01  --sat_gr_def                            false
% 2.67/1.01  --sat_epr_types                         true
% 2.67/1.01  --sat_non_cyclic_types                  false
% 2.67/1.01  --sat_finite_models                     false
% 2.67/1.01  --sat_fm_lemmas                         false
% 2.67/1.01  --sat_fm_prep                           false
% 2.67/1.01  --sat_fm_uc_incr                        true
% 2.67/1.01  --sat_out_model                         small
% 2.67/1.01  --sat_out_clauses                       false
% 2.67/1.01  
% 2.67/1.01  ------ QBF Options
% 2.67/1.01  
% 2.67/1.01  --qbf_mode                              false
% 2.67/1.01  --qbf_elim_univ                         false
% 2.67/1.01  --qbf_dom_inst                          none
% 2.67/1.01  --qbf_dom_pre_inst                      false
% 2.67/1.01  --qbf_sk_in                             false
% 2.67/1.01  --qbf_pred_elim                         true
% 2.67/1.01  --qbf_split                             512
% 2.67/1.01  
% 2.67/1.01  ------ BMC1 Options
% 2.67/1.01  
% 2.67/1.01  --bmc1_incremental                      false
% 2.67/1.01  --bmc1_axioms                           reachable_all
% 2.67/1.01  --bmc1_min_bound                        0
% 2.67/1.01  --bmc1_max_bound                        -1
% 2.67/1.01  --bmc1_max_bound_default                -1
% 2.67/1.01  --bmc1_symbol_reachability              true
% 2.67/1.01  --bmc1_property_lemmas                  false
% 2.67/1.01  --bmc1_k_induction                      false
% 2.67/1.01  --bmc1_non_equiv_states                 false
% 2.67/1.01  --bmc1_deadlock                         false
% 2.67/1.01  --bmc1_ucm                              false
% 2.67/1.01  --bmc1_add_unsat_core                   none
% 2.67/1.01  --bmc1_unsat_core_children              false
% 2.67/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/1.01  --bmc1_out_stat                         full
% 2.67/1.01  --bmc1_ground_init                      false
% 2.67/1.01  --bmc1_pre_inst_next_state              false
% 2.67/1.01  --bmc1_pre_inst_state                   false
% 2.67/1.01  --bmc1_pre_inst_reach_state             false
% 2.67/1.01  --bmc1_out_unsat_core                   false
% 2.67/1.01  --bmc1_aig_witness_out                  false
% 2.67/1.01  --bmc1_verbose                          false
% 2.67/1.01  --bmc1_dump_clauses_tptp                false
% 2.67/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.67/1.01  --bmc1_dump_file                        -
% 2.67/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.67/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.67/1.01  --bmc1_ucm_extend_mode                  1
% 2.67/1.01  --bmc1_ucm_init_mode                    2
% 2.67/1.01  --bmc1_ucm_cone_mode                    none
% 2.67/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.67/1.01  --bmc1_ucm_relax_model                  4
% 2.67/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.67/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/1.01  --bmc1_ucm_layered_model                none
% 2.67/1.01  --bmc1_ucm_max_lemma_size               10
% 2.67/1.01  
% 2.67/1.01  ------ AIG Options
% 2.67/1.01  
% 2.67/1.01  --aig_mode                              false
% 2.67/1.01  
% 2.67/1.01  ------ Instantiation Options
% 2.67/1.01  
% 2.67/1.01  --instantiation_flag                    true
% 2.67/1.01  --inst_sos_flag                         false
% 2.67/1.01  --inst_sos_phase                        true
% 2.67/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/1.01  --inst_lit_sel_side                     none
% 2.67/1.01  --inst_solver_per_active                1400
% 2.67/1.01  --inst_solver_calls_frac                1.
% 2.67/1.01  --inst_passive_queue_type               priority_queues
% 2.67/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/1.01  --inst_passive_queues_freq              [25;2]
% 2.67/1.01  --inst_dismatching                      true
% 2.67/1.01  --inst_eager_unprocessed_to_passive     true
% 2.67/1.01  --inst_prop_sim_given                   true
% 2.67/1.01  --inst_prop_sim_new                     false
% 2.67/1.01  --inst_subs_new                         false
% 2.67/1.01  --inst_eq_res_simp                      false
% 2.67/1.01  --inst_subs_given                       false
% 2.67/1.01  --inst_orphan_elimination               true
% 2.67/1.01  --inst_learning_loop_flag               true
% 2.67/1.01  --inst_learning_start                   3000
% 2.67/1.01  --inst_learning_factor                  2
% 2.67/1.01  --inst_start_prop_sim_after_learn       3
% 2.67/1.01  --inst_sel_renew                        solver
% 2.67/1.01  --inst_lit_activity_flag                true
% 2.67/1.01  --inst_restr_to_given                   false
% 2.67/1.01  --inst_activity_threshold               500
% 2.67/1.01  --inst_out_proof                        true
% 2.67/1.01  
% 2.67/1.01  ------ Resolution Options
% 2.67/1.01  
% 2.67/1.01  --resolution_flag                       false
% 2.67/1.01  --res_lit_sel                           adaptive
% 2.67/1.01  --res_lit_sel_side                      none
% 2.67/1.01  --res_ordering                          kbo
% 2.67/1.01  --res_to_prop_solver                    active
% 2.67/1.01  --res_prop_simpl_new                    false
% 2.67/1.01  --res_prop_simpl_given                  true
% 2.67/1.01  --res_passive_queue_type                priority_queues
% 2.67/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/1.01  --res_passive_queues_freq               [15;5]
% 2.67/1.01  --res_forward_subs                      full
% 2.67/1.01  --res_backward_subs                     full
% 2.67/1.01  --res_forward_subs_resolution           true
% 2.67/1.01  --res_backward_subs_resolution          true
% 2.67/1.01  --res_orphan_elimination                true
% 2.67/1.01  --res_time_limit                        2.
% 2.67/1.01  --res_out_proof                         true
% 2.67/1.01  
% 2.67/1.01  ------ Superposition Options
% 2.67/1.01  
% 2.67/1.01  --superposition_flag                    true
% 2.67/1.01  --sup_passive_queue_type                priority_queues
% 2.67/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.67/1.01  --demod_completeness_check              fast
% 2.67/1.01  --demod_use_ground                      true
% 2.67/1.01  --sup_to_prop_solver                    passive
% 2.67/1.01  --sup_prop_simpl_new                    true
% 2.67/1.01  --sup_prop_simpl_given                  true
% 2.67/1.01  --sup_fun_splitting                     false
% 2.67/1.01  --sup_smt_interval                      50000
% 2.67/1.01  
% 2.67/1.01  ------ Superposition Simplification Setup
% 2.67/1.01  
% 2.67/1.01  --sup_indices_passive                   []
% 2.67/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.01  --sup_full_bw                           [BwDemod]
% 2.67/1.01  --sup_immed_triv                        [TrivRules]
% 2.67/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.01  --sup_immed_bw_main                     []
% 2.67/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.01  
% 2.67/1.01  ------ Combination Options
% 2.67/1.01  
% 2.67/1.01  --comb_res_mult                         3
% 2.67/1.01  --comb_sup_mult                         2
% 2.67/1.01  --comb_inst_mult                        10
% 2.67/1.01  
% 2.67/1.01  ------ Debug Options
% 2.67/1.01  
% 2.67/1.01  --dbg_backtrace                         false
% 2.67/1.01  --dbg_dump_prop_clauses                 false
% 2.67/1.01  --dbg_dump_prop_clauses_file            -
% 2.67/1.01  --dbg_out_stat                          false
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  ------ Proving...
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  % SZS status Theorem for theBenchmark.p
% 2.67/1.01  
% 2.67/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.67/1.01  
% 2.67/1.01  fof(f15,conjecture,(
% 2.67/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.67/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f16,negated_conjecture,(
% 2.67/1.01    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.67/1.01    inference(negated_conjecture,[],[f15])).
% 2.67/1.01  
% 2.67/1.01  fof(f40,plain,(
% 2.67/1.01    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.67/1.01    inference(ennf_transformation,[],[f16])).
% 2.67/1.01  
% 2.67/1.01  fof(f41,plain,(
% 2.67/1.01    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.67/1.01    inference(flattening,[],[f40])).
% 2.67/1.01  
% 2.67/1.01  fof(f46,plain,(
% 2.67/1.01    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.67/1.01    introduced(choice_axiom,[])).
% 2.67/1.01  
% 2.67/1.01  fof(f45,plain,(
% 2.67/1.01    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.67/1.01    introduced(choice_axiom,[])).
% 2.67/1.01  
% 2.67/1.01  fof(f44,plain,(
% 2.67/1.01    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.67/1.01    introduced(choice_axiom,[])).
% 2.67/1.01  
% 2.67/1.01  fof(f47,plain,(
% 2.67/1.01    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.67/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f46,f45,f44])).
% 2.67/1.01  
% 2.67/1.01  fof(f70,plain,(
% 2.67/1.01    l1_struct_0(sK1)),
% 2.67/1.01    inference(cnf_transformation,[],[f47])).
% 2.67/1.01  
% 2.67/1.01  fof(f11,axiom,(
% 2.67/1.01    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.67/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f33,plain,(
% 2.67/1.01    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.67/1.01    inference(ennf_transformation,[],[f11])).
% 2.67/1.01  
% 2.67/1.01  fof(f64,plain,(
% 2.67/1.01    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f33])).
% 2.67/1.01  
% 2.67/1.01  fof(f73,plain,(
% 2.67/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.67/1.01    inference(cnf_transformation,[],[f47])).
% 2.67/1.01  
% 2.67/1.01  fof(f68,plain,(
% 2.67/1.01    l1_struct_0(sK0)),
% 2.67/1.01    inference(cnf_transformation,[],[f47])).
% 2.67/1.01  
% 2.67/1.01  fof(f74,plain,(
% 2.67/1.01    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.67/1.01    inference(cnf_transformation,[],[f47])).
% 2.67/1.01  
% 2.67/1.01  fof(f6,axiom,(
% 2.67/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.67/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f24,plain,(
% 2.67/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.01    inference(ennf_transformation,[],[f6])).
% 2.67/1.01  
% 2.67/1.01  fof(f54,plain,(
% 2.67/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.01    inference(cnf_transformation,[],[f24])).
% 2.67/1.01  
% 2.67/1.01  fof(f7,axiom,(
% 2.67/1.01    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.67/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f25,plain,(
% 2.67/1.01    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.67/1.01    inference(ennf_transformation,[],[f7])).
% 2.67/1.01  
% 2.67/1.01  fof(f26,plain,(
% 2.67/1.01    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.67/1.01    inference(flattening,[],[f25])).
% 2.67/1.01  
% 2.67/1.01  fof(f56,plain,(
% 2.67/1.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f26])).
% 2.67/1.01  
% 2.67/1.01  fof(f12,axiom,(
% 2.67/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.67/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f34,plain,(
% 2.67/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.67/1.01    inference(ennf_transformation,[],[f12])).
% 2.67/1.01  
% 2.67/1.01  fof(f35,plain,(
% 2.67/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.67/1.01    inference(flattening,[],[f34])).
% 2.67/1.01  
% 2.67/1.01  fof(f65,plain,(
% 2.67/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f35])).
% 2.67/1.01  
% 2.67/1.01  fof(f69,plain,(
% 2.67/1.01    ~v2_struct_0(sK1)),
% 2.67/1.01    inference(cnf_transformation,[],[f47])).
% 2.67/1.01  
% 2.67/1.01  fof(f8,axiom,(
% 2.67/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.67/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f27,plain,(
% 2.67/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.67/1.01    inference(ennf_transformation,[],[f8])).
% 2.67/1.01  
% 2.67/1.01  fof(f28,plain,(
% 2.67/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.67/1.01    inference(flattening,[],[f27])).
% 2.67/1.01  
% 2.67/1.01  fof(f42,plain,(
% 2.67/1.01    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.67/1.01    inference(nnf_transformation,[],[f28])).
% 2.67/1.01  
% 2.67/1.01  fof(f57,plain,(
% 2.67/1.01    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f42])).
% 2.67/1.01  
% 2.67/1.01  fof(f5,axiom,(
% 2.67/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.67/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f17,plain,(
% 2.67/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.67/1.01    inference(pure_predicate_removal,[],[f5])).
% 2.67/1.01  
% 2.67/1.01  fof(f23,plain,(
% 2.67/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.01    inference(ennf_transformation,[],[f17])).
% 2.67/1.01  
% 2.67/1.01  fof(f53,plain,(
% 2.67/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.01    inference(cnf_transformation,[],[f23])).
% 2.67/1.01  
% 2.67/1.01  fof(f71,plain,(
% 2.67/1.01    v1_funct_1(sK2)),
% 2.67/1.01    inference(cnf_transformation,[],[f47])).
% 2.67/1.01  
% 2.67/1.01  fof(f1,axiom,(
% 2.67/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.67/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f18,plain,(
% 2.67/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.67/1.01    inference(ennf_transformation,[],[f1])).
% 2.67/1.01  
% 2.67/1.01  fof(f48,plain,(
% 2.67/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f18])).
% 2.67/1.01  
% 2.67/1.01  fof(f2,axiom,(
% 2.67/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.67/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f49,plain,(
% 2.67/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.67/1.01    inference(cnf_transformation,[],[f2])).
% 2.67/1.01  
% 2.67/1.01  fof(f72,plain,(
% 2.67/1.01    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.67/1.01    inference(cnf_transformation,[],[f47])).
% 2.67/1.01  
% 2.67/1.01  fof(f14,axiom,(
% 2.67/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 2.67/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f38,plain,(
% 2.67/1.01    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.67/1.01    inference(ennf_transformation,[],[f14])).
% 2.67/1.01  
% 2.67/1.01  fof(f39,plain,(
% 2.67/1.01    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.67/1.01    inference(flattening,[],[f38])).
% 2.67/1.01  
% 2.67/1.01  fof(f67,plain,(
% 2.67/1.01    ( ! [X2,X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f39])).
% 2.67/1.01  
% 2.67/1.01  fof(f13,axiom,(
% 2.67/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.67/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f36,plain,(
% 2.67/1.01    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.67/1.01    inference(ennf_transformation,[],[f13])).
% 2.67/1.01  
% 2.67/1.01  fof(f37,plain,(
% 2.67/1.01    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.67/1.01    inference(flattening,[],[f36])).
% 2.67/1.01  
% 2.67/1.01  fof(f66,plain,(
% 2.67/1.01    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f37])).
% 2.67/1.01  
% 2.67/1.01  fof(f75,plain,(
% 2.67/1.01    v2_funct_1(sK2)),
% 2.67/1.01    inference(cnf_transformation,[],[f47])).
% 2.67/1.01  
% 2.67/1.01  fof(f10,axiom,(
% 2.67/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.67/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f31,plain,(
% 2.67/1.01    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.67/1.01    inference(ennf_transformation,[],[f10])).
% 2.67/1.01  
% 2.67/1.01  fof(f32,plain,(
% 2.67/1.01    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.67/1.01    inference(flattening,[],[f31])).
% 2.67/1.01  
% 2.67/1.01  fof(f63,plain,(
% 2.67/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f32])).
% 2.67/1.01  
% 2.67/1.01  fof(f3,axiom,(
% 2.67/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.67/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f19,plain,(
% 2.67/1.01    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.67/1.01    inference(ennf_transformation,[],[f3])).
% 2.67/1.01  
% 2.67/1.01  fof(f20,plain,(
% 2.67/1.01    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.67/1.01    inference(flattening,[],[f19])).
% 2.67/1.01  
% 2.67/1.01  fof(f51,plain,(
% 2.67/1.01    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f20])).
% 2.67/1.01  
% 2.67/1.01  fof(f4,axiom,(
% 2.67/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.67/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f21,plain,(
% 2.67/1.01    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.67/1.01    inference(ennf_transformation,[],[f4])).
% 2.67/1.01  
% 2.67/1.01  fof(f22,plain,(
% 2.67/1.01    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.67/1.01    inference(flattening,[],[f21])).
% 2.67/1.01  
% 2.67/1.01  fof(f52,plain,(
% 2.67/1.01    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f22])).
% 2.67/1.01  
% 2.67/1.01  fof(f61,plain,(
% 2.67/1.01    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f32])).
% 2.67/1.01  
% 2.67/1.01  fof(f62,plain,(
% 2.67/1.01    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f32])).
% 2.67/1.01  
% 2.67/1.01  fof(f9,axiom,(
% 2.67/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.67/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f29,plain,(
% 2.67/1.01    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.67/1.01    inference(ennf_transformation,[],[f9])).
% 2.67/1.01  
% 2.67/1.01  fof(f30,plain,(
% 2.67/1.01    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.67/1.01    inference(flattening,[],[f29])).
% 2.67/1.01  
% 2.67/1.01  fof(f43,plain,(
% 2.67/1.01    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.67/1.01    inference(nnf_transformation,[],[f30])).
% 2.67/1.01  
% 2.67/1.01  fof(f60,plain,(
% 2.67/1.01    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f43])).
% 2.67/1.01  
% 2.67/1.01  fof(f78,plain,(
% 2.67/1.01    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.67/1.01    inference(equality_resolution,[],[f60])).
% 2.67/1.01  
% 2.67/1.01  fof(f76,plain,(
% 2.67/1.01    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.67/1.01    inference(cnf_transformation,[],[f47])).
% 2.67/1.01  
% 2.67/1.01  cnf(c_26,negated_conjecture,
% 2.67/1.01      ( l1_struct_0(sK1) ),
% 2.67/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_584,negated_conjecture,
% 2.67/1.01      ( l1_struct_0(sK1) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_26]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1025,plain,
% 2.67/1.01      ( l1_struct_0(sK1) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_584]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_16,plain,
% 2.67/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.67/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_592,plain,
% 2.67/1.01      ( ~ l1_struct_0(X0_53) | u1_struct_0(X0_53) = k2_struct_0(X0_53) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1018,plain,
% 2.67/1.01      ( u1_struct_0(X0_53) = k2_struct_0(X0_53)
% 2.67/1.01      | l1_struct_0(X0_53) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1373,plain,
% 2.67/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_1025,c_1018]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_23,negated_conjecture,
% 2.67/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.67/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_587,negated_conjecture,
% 2.67/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_23]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1022,plain,
% 2.67/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_587]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1454,plain,
% 2.67/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.67/1.01      inference(demodulation,[status(thm)],[c_1373,c_1022]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_28,negated_conjecture,
% 2.67/1.01      ( l1_struct_0(sK0) ),
% 2.67/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_583,negated_conjecture,
% 2.67/1.01      ( l1_struct_0(sK0) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_28]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1026,plain,
% 2.67/1.01      ( l1_struct_0(sK0) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1374,plain,
% 2.67/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_1026,c_1018]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_22,negated_conjecture,
% 2.67/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.67/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_588,negated_conjecture,
% 2.67/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_22]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1456,plain,
% 2.67/1.01      ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.67/1.01      inference(demodulation,[status(thm)],[c_1373,c_588]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1523,plain,
% 2.67/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.67/1.01      inference(demodulation,[status(thm)],[c_1374,c_1456]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_6,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.67/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_596,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.67/1.01      | k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1014,plain,
% 2.67/1.01      ( k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51)
% 2.67/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_596]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1382,plain,
% 2.67/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_1022,c_1014]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1570,plain,
% 2.67/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.67/1.01      inference(light_normalisation,[status(thm)],[c_1382,c_1373,c_1374]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1590,plain,
% 2.67/1.01      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.67/1.01      inference(light_normalisation,[status(thm)],[c_1523,c_1570]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1603,plain,
% 2.67/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.67/1.01      inference(light_normalisation,[status(thm)],[c_1454,c_1374,c_1590]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_7,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/1.01      | v1_partfun1(X0,X1)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | v1_xboole_0(X2)
% 2.67/1.01      | ~ v1_funct_1(X0) ),
% 2.67/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_17,plain,
% 2.67/1.01      ( v2_struct_0(X0)
% 2.67/1.01      | ~ l1_struct_0(X0)
% 2.67/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.67/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_27,negated_conjecture,
% 2.67/1.01      ( ~ v2_struct_0(sK1) ),
% 2.67/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_310,plain,
% 2.67/1.01      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_311,plain,
% 2.67/1.01      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_310]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_44,plain,
% 2.67/1.01      ( v2_struct_0(sK1)
% 2.67/1.01      | ~ l1_struct_0(sK1)
% 2.67/1.01      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.67/1.01      inference(instantiation,[status(thm)],[c_17]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_313,plain,
% 2.67/1.01      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_311,c_27,c_26,c_44]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_323,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/1.01      | v1_partfun1(X0,X1)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | ~ v1_funct_1(X0)
% 2.67/1.01      | u1_struct_0(sK1) != X2 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_313]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_324,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.67/1.01      | v1_partfun1(X0,X1)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.67/1.01      | ~ v1_funct_1(X0) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_323]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_10,plain,
% 2.67/1.01      ( ~ v1_partfun1(X0,X1)
% 2.67/1.01      | ~ v4_relat_1(X0,X1)
% 2.67/1.01      | ~ v1_relat_1(X0)
% 2.67/1.01      | k1_relat_1(X0) = X1 ),
% 2.67/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_385,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.67/1.01      | ~ v4_relat_1(X0,X1)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.67/1.01      | ~ v1_funct_1(X0)
% 2.67/1.01      | ~ v1_relat_1(X0)
% 2.67/1.01      | k1_relat_1(X0) = X1 ),
% 2.67/1.01      inference(resolution,[status(thm)],[c_324,c_10]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_5,plain,
% 2.67/1.01      ( v4_relat_1(X0,X1)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.67/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_401,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.67/1.01      | ~ v1_funct_1(X0)
% 2.67/1.01      | ~ v1_relat_1(X0)
% 2.67/1.01      | k1_relat_1(X0) = X1 ),
% 2.67/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_385,c_5]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_582,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0_51,X0_52,u1_struct_0(sK1))
% 2.67/1.01      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,u1_struct_0(sK1))))
% 2.67/1.01      | ~ v1_funct_1(X0_51)
% 2.67/1.01      | ~ v1_relat_1(X0_51)
% 2.67/1.01      | k1_relat_1(X0_51) = X0_52 ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_401]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1027,plain,
% 2.67/1.01      ( k1_relat_1(X0_51) = X0_52
% 2.67/1.01      | v1_funct_2(X0_51,X0_52,u1_struct_0(sK1)) != iProver_top
% 2.67/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,u1_struct_0(sK1)))) != iProver_top
% 2.67/1.01      | v1_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v1_relat_1(X0_51) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_582]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1594,plain,
% 2.67/1.01      ( u1_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.67/1.01      inference(demodulation,[status(thm)],[c_1590,c_1373]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_2403,plain,
% 2.67/1.01      ( k1_relat_1(X0_51) = X0_52
% 2.67/1.01      | v1_funct_2(X0_51,X0_52,k2_relat_1(sK2)) != iProver_top
% 2.67/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_relat_1(sK2)))) != iProver_top
% 2.67/1.01      | v1_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v1_relat_1(X0_51) != iProver_top ),
% 2.67/1.01      inference(light_normalisation,[status(thm)],[c_1027,c_1594]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_2412,plain,
% 2.67/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.67/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.67/1.01      | v1_funct_1(sK2) != iProver_top
% 2.67/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_1603,c_2403]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_25,negated_conjecture,
% 2.67/1.01      ( v1_funct_1(sK2) ),
% 2.67/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_32,plain,
% 2.67/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_0,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.67/1.01      | ~ v1_relat_1(X1)
% 2.67/1.01      | v1_relat_1(X0) ),
% 2.67/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_601,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 2.67/1.01      | ~ v1_relat_1(X1_51)
% 2.67/1.01      | v1_relat_1(X0_51) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1009,plain,
% 2.67/1.01      ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
% 2.67/1.01      | v1_relat_1(X1_51) != iProver_top
% 2.67/1.01      | v1_relat_1(X0_51) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_601]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1336,plain,
% 2.67/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.67/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_1022,c_1009]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1,plain,
% 2.67/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.67/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_600,plain,
% 2.67/1.01      ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1350,plain,
% 2.67/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.67/1.01      inference(instantiation,[status(thm)],[c_600]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1351,plain,
% 2.67/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_1350]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_24,negated_conjecture,
% 2.67/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.67/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_586,negated_conjecture,
% 2.67/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_24]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1023,plain,
% 2.67/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1455,plain,
% 2.67/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.67/1.01      inference(demodulation,[status(thm)],[c_1373,c_1023]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1567,plain,
% 2.67/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.67/1.01      inference(light_normalisation,[status(thm)],[c_1455,c_1374]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1593,plain,
% 2.67/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.67/1.01      inference(demodulation,[status(thm)],[c_1590,c_1567]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3021,plain,
% 2.67/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_2412,c_32,c_1336,c_1351,c_1593]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1592,plain,
% 2.67/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.67/1.01      inference(demodulation,[status(thm)],[c_1590,c_1570]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3028,plain,
% 2.67/1.01      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.67/1.01      inference(demodulation,[status(thm)],[c_3021,c_1592]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_19,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.67/1.01      | ~ l1_struct_0(X1)
% 2.67/1.01      | ~ l1_struct_0(X2)
% 2.67/1.01      | ~ v1_funct_1(X0)
% 2.67/1.01      | ~ v2_funct_1(X0)
% 2.67/1.01      | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
% 2.67/1.01      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 2.67/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_590,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 2.67/1.01      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 2.67/1.01      | ~ l1_struct_0(X1_53)
% 2.67/1.01      | ~ l1_struct_0(X0_53)
% 2.67/1.01      | ~ v1_funct_1(X0_51)
% 2.67/1.01      | ~ v2_funct_1(X0_51)
% 2.67/1.01      | v2_funct_1(k2_tops_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51))
% 2.67/1.01      | k2_relset_1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51) != k2_struct_0(X1_53) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_19]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1020,plain,
% 2.67/1.01      ( k2_relset_1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51) != k2_struct_0(X1_53)
% 2.67/1.01      | v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 2.67/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 2.67/1.01      | l1_struct_0(X0_53) != iProver_top
% 2.67/1.01      | l1_struct_0(X1_53) != iProver_top
% 2.67/1.01      | v1_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(k2_tops_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51)) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_590]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_2318,plain,
% 2.67/1.01      ( k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
% 2.67/1.01      | v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 2.67/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 2.67/1.01      | l1_struct_0(X0_53) != iProver_top
% 2.67/1.01      | l1_struct_0(sK0) != iProver_top
% 2.67/1.01      | v1_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_1374,c_1020]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_2381,plain,
% 2.67/1.01      ( k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
% 2.67/1.01      | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 2.67/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 2.67/1.01      | l1_struct_0(X0_53) != iProver_top
% 2.67/1.01      | l1_struct_0(sK0) != iProver_top
% 2.67/1.01      | v1_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
% 2.67/1.01      inference(light_normalisation,[status(thm)],[c_2318,c_1374]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_29,plain,
% 2.67/1.01      ( l1_struct_0(sK0) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_2979,plain,
% 2.67/1.01      ( l1_struct_0(X0_53) != iProver_top
% 2.67/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 2.67/1.01      | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 2.67/1.01      | k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
% 2.67/1.01      | v1_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_2381,c_29]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_2980,plain,
% 2.67/1.01      ( k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
% 2.67/1.01      | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 2.67/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 2.67/1.01      | l1_struct_0(X0_53) != iProver_top
% 2.67/1.01      | v1_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
% 2.67/1.01      inference(renaming,[status(thm)],[c_2979]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_2993,plain,
% 2.67/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_struct_0(sK1)
% 2.67/1.01      | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.67/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.67/1.01      | l1_struct_0(sK1) != iProver_top
% 2.67/1.01      | v1_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),X0_51)) = iProver_top ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_1594,c_2980]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3001,plain,
% 2.67/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
% 2.67/1.01      | v1_funct_2(X0_51,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.67/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.67/1.01      | l1_struct_0(sK1) != iProver_top
% 2.67/1.01      | v1_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0_51)) = iProver_top ),
% 2.67/1.01      inference(light_normalisation,[status(thm)],[c_2993,c_1590,c_1594]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_31,plain,
% 2.67/1.01      ( l1_struct_0(sK1) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3726,plain,
% 2.67/1.01      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.67/1.01      | v1_funct_2(X0_51,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.67/1.01      | k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
% 2.67/1.01      | v1_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0_51)) = iProver_top ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_3001,c_31]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3727,plain,
% 2.67/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
% 2.67/1.01      | v1_funct_2(X0_51,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.67/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.67/1.01      | v1_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0_51)) = iProver_top ),
% 2.67/1.01      inference(renaming,[status(thm)],[c_3726]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3732,plain,
% 2.67/1.01      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
% 2.67/1.01      | v1_funct_2(X0_51,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.67/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.67/1.01      | v1_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),X0_51)) = iProver_top ),
% 2.67/1.01      inference(light_normalisation,[status(thm)],[c_3727,c_3021]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_4214,plain,
% 2.67/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.67/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.67/1.01      | v1_funct_1(sK2) != iProver_top
% 2.67/1.01      | v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = iProver_top
% 2.67/1.01      | v2_funct_1(sK2) != iProver_top ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_3028,c_3732]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_18,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | ~ v1_funct_1(X0)
% 2.67/1.01      | ~ v2_funct_1(X0)
% 2.67/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.67/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.67/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_591,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.67/1.01      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.67/1.01      | ~ v1_funct_1(X0_51)
% 2.67/1.01      | ~ v2_funct_1(X0_51)
% 2.67/1.01      | k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 2.67/1.01      | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1019,plain,
% 2.67/1.01      ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 2.67/1.01      | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51)
% 2.67/1.01      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 2.67/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.67/1.01      | v1_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(X0_51) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_591]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_2204,plain,
% 2.67/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.67/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.67/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.67/1.01      | v1_funct_1(sK2) != iProver_top
% 2.67/1.01      | v2_funct_1(sK2) != iProver_top ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_1592,c_1019]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_21,negated_conjecture,
% 2.67/1.01      ( v2_funct_1(sK2) ),
% 2.67/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_35,plain,
% 2.67/1.01      ( v2_funct_1(sK2) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_2512,plain,
% 2.67/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_2204,c_32,c_35,c_1593,c_1603]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3027,plain,
% 2.67/1.01      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.67/1.01      inference(demodulation,[status(thm)],[c_3021,c_2512]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_4220,plain,
% 2.67/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.67/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.67/1.01      | v1_funct_1(sK2) != iProver_top
% 2.67/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.67/1.01      | v2_funct_1(sK2) != iProver_top ),
% 2.67/1.01      inference(light_normalisation,[status(thm)],[c_4214,c_3027]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3029,plain,
% 2.67/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.67/1.01      inference(demodulation,[status(thm)],[c_3021,c_1593]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3030,plain,
% 2.67/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.67/1.01      inference(demodulation,[status(thm)],[c_3021,c_1603]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_4231,plain,
% 2.67/1.01      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_4220,c_32,c_35,c_3029,c_3030]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_13,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.67/1.01      | ~ v1_funct_1(X0)
% 2.67/1.01      | ~ v2_funct_1(X0)
% 2.67/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.67/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_595,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.67/1.01      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.67/1.01      | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52)))
% 2.67/1.01      | ~ v1_funct_1(X0_51)
% 2.67/1.01      | ~ v2_funct_1(X0_51)
% 2.67/1.01      | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_13]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1015,plain,
% 2.67/1.01      ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 2.67/1.01      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 2.67/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.67/1.01      | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) = iProver_top
% 2.67/1.01      | v1_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(X0_51) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_595]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_2252,plain,
% 2.67/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.67/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 2.67/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.67/1.01      | v1_funct_1(sK2) != iProver_top
% 2.67/1.01      | v2_funct_1(sK2) != iProver_top ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_1592,c_1015]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3378,plain,
% 2.67/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_2252,c_32,c_35,c_1593,c_1603]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3382,plain,
% 2.67/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 2.67/1.01      inference(light_normalisation,[status(thm)],[c_3378,c_3021]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3385,plain,
% 2.67/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_3382,c_1014]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_585,negated_conjecture,
% 2.67/1.01      ( v1_funct_1(sK2) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_25]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1024,plain,
% 2.67/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_585]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_2,plain,
% 2.67/1.01      ( ~ v1_funct_1(X0)
% 2.67/1.01      | ~ v2_funct_1(X0)
% 2.67/1.01      | ~ v1_relat_1(X0)
% 2.67/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.67/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_599,plain,
% 2.67/1.01      ( ~ v1_funct_1(X0_51)
% 2.67/1.01      | ~ v2_funct_1(X0_51)
% 2.67/1.01      | ~ v1_relat_1(X0_51)
% 2.67/1.01      | k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1011,plain,
% 2.67/1.01      ( k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51)
% 2.67/1.01      | v1_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v1_relat_1(X0_51) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_599]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1717,plain,
% 2.67/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.67/1.01      | v2_funct_1(sK2) != iProver_top
% 2.67/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_1024,c_1011]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_641,plain,
% 2.67/1.01      ( ~ v1_funct_1(sK2)
% 2.67/1.01      | ~ v2_funct_1(sK2)
% 2.67/1.01      | ~ v1_relat_1(sK2)
% 2.67/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.67/1.01      inference(instantiation,[status(thm)],[c_599]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1337,plain,
% 2.67/1.01      ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.67/1.01      | v1_relat_1(sK2) ),
% 2.67/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1336]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1988,plain,
% 2.67/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_1717,c_25,c_21,c_641,c_1337,c_1350]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3392,plain,
% 2.67/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.67/1.01      inference(light_normalisation,[status(thm)],[c_3385,c_1988]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3479,plain,
% 2.67/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.67/1.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.67/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.67/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.67/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_3392,c_1019]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_4,plain,
% 2.67/1.01      ( ~ v1_funct_1(X0)
% 2.67/1.01      | ~ v2_funct_1(X0)
% 2.67/1.01      | ~ v1_relat_1(X0)
% 2.67/1.01      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.67/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_597,plain,
% 2.67/1.01      ( ~ v1_funct_1(X0_51)
% 2.67/1.01      | ~ v2_funct_1(X0_51)
% 2.67/1.01      | ~ v1_relat_1(X0_51)
% 2.67/1.01      | k2_funct_1(k2_funct_1(X0_51)) = X0_51 ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1013,plain,
% 2.67/1.01      ( k2_funct_1(k2_funct_1(X0_51)) = X0_51
% 2.67/1.01      | v1_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v1_relat_1(X0_51) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_597]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1450,plain,
% 2.67/1.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.67/1.01      | v2_funct_1(sK2) != iProver_top
% 2.67/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_1024,c_1013]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_647,plain,
% 2.67/1.01      ( ~ v1_funct_1(sK2)
% 2.67/1.01      | ~ v2_funct_1(sK2)
% 2.67/1.01      | ~ v1_relat_1(sK2)
% 2.67/1.01      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.67/1.01      inference(instantiation,[status(thm)],[c_597]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1984,plain,
% 2.67/1.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_1450,c_25,c_21,c_647,c_1337,c_1350]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3499,plain,
% 2.67/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 2.67/1.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.67/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.67/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.67/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/1.01      inference(light_normalisation,[status(thm)],[c_3479,c_1984]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_33,plain,
% 2.67/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_34,plain,
% 2.67/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_662,plain,
% 2.67/1.01      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.67/1.01      inference(instantiation,[status(thm)],[c_592]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_15,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | ~ v1_funct_1(X0)
% 2.67/1.01      | v1_funct_1(k2_funct_1(X0))
% 2.67/1.01      | ~ v2_funct_1(X0)
% 2.67/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.67/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_593,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.67/1.01      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.67/1.01      | ~ v1_funct_1(X0_51)
% 2.67/1.01      | v1_funct_1(k2_funct_1(X0_51))
% 2.67/1.01      | ~ v2_funct_1(X0_51)
% 2.67/1.01      | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_15]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1269,plain,
% 2.67/1.01      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.67/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.67/1.01      | v1_funct_1(k2_funct_1(sK2))
% 2.67/1.01      | ~ v1_funct_1(sK2)
% 2.67/1.01      | ~ v2_funct_1(sK2)
% 2.67/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 2.67/1.01      inference(instantiation,[status(thm)],[c_593]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1270,plain,
% 2.67/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 2.67/1.01      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.67/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.67/1.01      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.67/1.01      | v1_funct_1(sK2) != iProver_top
% 2.67/1.01      | v2_funct_1(sK2) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_1269]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_607,plain,
% 2.67/1.01      ( X0_52 != X1_52 | X2_52 != X1_52 | X2_52 = X0_52 ),
% 2.67/1.01      theory(equality) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1291,plain,
% 2.67/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_52
% 2.67/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 2.67/1.01      | u1_struct_0(sK1) != X0_52 ),
% 2.67/1.01      inference(instantiation,[status(thm)],[c_607]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1354,plain,
% 2.67/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 2.67/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 2.67/1.01      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.67/1.01      inference(instantiation,[status(thm)],[c_1291]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_14,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/1.01      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | ~ v1_funct_1(X0)
% 2.67/1.01      | ~ v2_funct_1(X0)
% 2.67/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.67/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_594,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.67/1.01      | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52)
% 2.67/1.01      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.67/1.01      | ~ v1_funct_1(X0_51)
% 2.67/1.01      | ~ v2_funct_1(X0_51)
% 2.67/1.01      | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_14]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1016,plain,
% 2.67/1.01      ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 2.67/1.01      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 2.67/1.01      | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52) = iProver_top
% 2.67/1.01      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.67/1.01      | v1_funct_1(X0_51) != iProver_top
% 2.67/1.01      | v2_funct_1(X0_51) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_594]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_2205,plain,
% 2.67/1.01      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 2.67/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.67/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.67/1.01      | v1_funct_1(sK2) != iProver_top
% 2.67/1.01      | v2_funct_1(sK2) != iProver_top ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_1592,c_1016]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3370,plain,
% 2.67/1.01      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_2205,c_32,c_35,c_1593,c_1603]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3374,plain,
% 2.67/1.01      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
% 2.67/1.01      inference(light_normalisation,[status(thm)],[c_3370,c_3021]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3617,plain,
% 2.67/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 2.67/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_3499,c_26,c_32,c_33,c_34,c_35,c_662,c_588,c_1270,
% 2.67/1.01                 c_1354,c_3374,c_3382]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_4236,plain,
% 2.67/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_4231,c_3617]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_11,plain,
% 2.67/1.01      ( r2_funct_2(X0,X1,X2,X2)
% 2.67/1.01      | ~ v1_funct_2(X2,X0,X1)
% 2.67/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.67/1.01      | ~ v1_funct_1(X2) ),
% 2.67/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_20,negated_conjecture,
% 2.67/1.01      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.67/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_420,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | ~ v1_funct_1(X0)
% 2.67/1.01      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 2.67/1.01      | u1_struct_0(sK1) != X2
% 2.67/1.01      | u1_struct_0(sK0) != X1
% 2.67/1.01      | sK2 != X0 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_421,plain,
% 2.67/1.01      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.67/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.67/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.67/1.01      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_420]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_581,plain,
% 2.67/1.01      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.67/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.67/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.67/1.01      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_421]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1028,plain,
% 2.67/1.01      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.67/1.01      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.67/1.01      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.67/1.01      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_581]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1453,plain,
% 2.67/1.01      ( k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.67/1.01      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.67/1.01      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.67/1.01      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.67/1.01      inference(demodulation,[status(thm)],[c_1373,c_1028]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_2133,plain,
% 2.67/1.01      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 2.67/1.01      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.67/1.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.67/1.01      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.67/1.01      inference(light_normalisation,[status(thm)],[c_1453,c_1374,c_1590]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_2515,plain,
% 2.67/1.01      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 2.67/1.01      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.67/1.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.67/1.01      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 2.67/1.01      inference(demodulation,[status(thm)],[c_2512,c_2133]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3305,plain,
% 2.67/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 2.67/1.01      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.67/1.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.67/1.01      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.67/1.01      inference(light_normalisation,[status(thm)],[c_2515,c_3021]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_4239,plain,
% 2.67/1.01      ( sK2 != sK2
% 2.67/1.01      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.67/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.67/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.67/1.01      inference(demodulation,[status(thm)],[c_4236,c_3305]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_4240,plain,
% 2.67/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.67/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.67/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.67/1.01      inference(equality_resolution_simp,[status(thm)],[c_4239]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(contradiction,plain,
% 2.67/1.01      ( $false ),
% 2.67/1.01      inference(minisat,[status(thm)],[c_4240,c_3030,c_3029,c_32]) ).
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.67/1.01  
% 2.67/1.01  ------                               Statistics
% 2.67/1.01  
% 2.67/1.01  ------ General
% 2.67/1.01  
% 2.67/1.01  abstr_ref_over_cycles:                  0
% 2.67/1.01  abstr_ref_under_cycles:                 0
% 2.67/1.01  gc_basic_clause_elim:                   0
% 2.67/1.01  forced_gc_time:                         0
% 2.67/1.01  parsing_time:                           0.012
% 2.67/1.01  unif_index_cands_time:                  0.
% 2.67/1.01  unif_index_add_time:                    0.
% 2.67/1.01  orderings_time:                         0.
% 2.67/1.01  out_proof_time:                         0.013
% 2.67/1.01  total_time:                             0.217
% 2.67/1.01  num_of_symbols:                         55
% 2.67/1.01  num_of_terms:                           4279
% 2.67/1.01  
% 2.67/1.01  ------ Preprocessing
% 2.67/1.01  
% 2.67/1.01  num_of_splits:                          0
% 2.67/1.01  num_of_split_atoms:                     0
% 2.67/1.01  num_of_reused_defs:                     0
% 2.67/1.01  num_eq_ax_congr_red:                    5
% 2.67/1.01  num_of_sem_filtered_clauses:            1
% 2.67/1.01  num_of_subtypes:                        4
% 2.67/1.01  monotx_restored_types:                  1
% 2.67/1.01  sat_num_of_epr_types:                   0
% 2.67/1.01  sat_num_of_non_cyclic_types:            0
% 2.67/1.01  sat_guarded_non_collapsed_types:        1
% 2.67/1.01  num_pure_diseq_elim:                    0
% 2.67/1.01  simp_replaced_by:                       0
% 2.67/1.01  res_preprocessed:                       126
% 2.67/1.01  prep_upred:                             0
% 2.67/1.01  prep_unflattend:                        13
% 2.67/1.01  smt_new_axioms:                         0
% 2.67/1.01  pred_elim_cands:                        6
% 2.67/1.01  pred_elim:                              5
% 2.67/1.01  pred_elim_cl:                           7
% 2.67/1.01  pred_elim_cycles:                       8
% 2.67/1.01  merged_defs:                            0
% 2.67/1.01  merged_defs_ncl:                        0
% 2.67/1.01  bin_hyper_res:                          0
% 2.67/1.01  prep_cycles:                            4
% 2.67/1.01  pred_elim_time:                         0.007
% 2.67/1.01  splitting_time:                         0.
% 2.67/1.01  sem_filter_time:                        0.
% 2.67/1.01  monotx_time:                            0.001
% 2.67/1.01  subtype_inf_time:                       0.002
% 2.67/1.01  
% 2.67/1.01  ------ Problem properties
% 2.67/1.01  
% 2.67/1.01  clauses:                                21
% 2.67/1.01  conjectures:                            7
% 2.67/1.01  epr:                                    4
% 2.67/1.01  horn:                                   21
% 2.67/1.01  ground:                                 8
% 2.67/1.01  unary:                                  8
% 2.67/1.01  binary:                                 2
% 2.67/1.01  lits:                                   68
% 2.67/1.01  lits_eq:                                14
% 2.67/1.01  fd_pure:                                0
% 2.67/1.01  fd_pseudo:                              0
% 2.67/1.01  fd_cond:                                0
% 2.67/1.01  fd_pseudo_cond:                         1
% 2.67/1.01  ac_symbols:                             0
% 2.67/1.01  
% 2.67/1.01  ------ Propositional Solver
% 2.67/1.01  
% 2.67/1.01  prop_solver_calls:                      28
% 2.67/1.01  prop_fast_solver_calls:                 1154
% 2.67/1.01  smt_solver_calls:                       0
% 2.67/1.01  smt_fast_solver_calls:                  0
% 2.67/1.01  prop_num_of_clauses:                    1496
% 2.67/1.01  prop_preprocess_simplified:             5113
% 2.67/1.01  prop_fo_subsumed:                       49
% 2.67/1.01  prop_solver_time:                       0.
% 2.67/1.01  smt_solver_time:                        0.
% 2.67/1.01  smt_fast_solver_time:                   0.
% 2.67/1.01  prop_fast_solver_time:                  0.
% 2.67/1.01  prop_unsat_core_time:                   0.
% 2.67/1.01  
% 2.67/1.01  ------ QBF
% 2.67/1.01  
% 2.67/1.01  qbf_q_res:                              0
% 2.67/1.01  qbf_num_tautologies:                    0
% 2.67/1.01  qbf_prep_cycles:                        0
% 2.67/1.01  
% 2.67/1.01  ------ BMC1
% 2.67/1.01  
% 2.67/1.01  bmc1_current_bound:                     -1
% 2.67/1.01  bmc1_last_solved_bound:                 -1
% 2.67/1.01  bmc1_unsat_core_size:                   -1
% 2.67/1.01  bmc1_unsat_core_parents_size:           -1
% 2.67/1.01  bmc1_merge_next_fun:                    0
% 2.67/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.67/1.01  
% 2.67/1.01  ------ Instantiation
% 2.67/1.01  
% 2.67/1.01  inst_num_of_clauses:                    515
% 2.67/1.01  inst_num_in_passive:                    43
% 2.67/1.01  inst_num_in_active:                     294
% 2.67/1.01  inst_num_in_unprocessed:                178
% 2.67/1.01  inst_num_of_loops:                      320
% 2.67/1.01  inst_num_of_learning_restarts:          0
% 2.67/1.01  inst_num_moves_active_passive:          22
% 2.67/1.01  inst_lit_activity:                      0
% 2.67/1.01  inst_lit_activity_moves:                0
% 2.67/1.01  inst_num_tautologies:                   0
% 2.67/1.01  inst_num_prop_implied:                  0
% 2.67/1.01  inst_num_existing_simplified:           0
% 2.67/1.01  inst_num_eq_res_simplified:             0
% 2.67/1.01  inst_num_child_elim:                    0
% 2.67/1.01  inst_num_of_dismatching_blockings:      115
% 2.67/1.01  inst_num_of_non_proper_insts:           483
% 2.67/1.01  inst_num_of_duplicates:                 0
% 2.67/1.01  inst_inst_num_from_inst_to_res:         0
% 2.67/1.01  inst_dismatching_checking_time:         0.
% 2.67/1.01  
% 2.67/1.01  ------ Resolution
% 2.67/1.01  
% 2.67/1.01  res_num_of_clauses:                     0
% 2.67/1.01  res_num_in_passive:                     0
% 2.67/1.01  res_num_in_active:                      0
% 2.67/1.01  res_num_of_loops:                       130
% 2.67/1.01  res_forward_subset_subsumed:            47
% 2.67/1.01  res_backward_subset_subsumed:           0
% 2.67/1.01  res_forward_subsumed:                   0
% 2.67/1.01  res_backward_subsumed:                  0
% 2.67/1.01  res_forward_subsumption_resolution:     1
% 2.67/1.01  res_backward_subsumption_resolution:    0
% 2.67/1.01  res_clause_to_clause_subsumption:       80
% 2.67/1.01  res_orphan_elimination:                 0
% 2.67/1.01  res_tautology_del:                      59
% 2.67/1.01  res_num_eq_res_simplified:              0
% 2.67/1.01  res_num_sel_changes:                    0
% 2.67/1.01  res_moves_from_active_to_pass:          0
% 2.67/1.01  
% 2.67/1.01  ------ Superposition
% 2.67/1.01  
% 2.67/1.01  sup_time_total:                         0.
% 2.67/1.01  sup_time_generating:                    0.
% 2.67/1.01  sup_time_sim_full:                      0.
% 2.67/1.01  sup_time_sim_immed:                     0.
% 2.67/1.01  
% 2.67/1.01  sup_num_of_clauses:                     45
% 2.67/1.01  sup_num_in_active:                      43
% 2.67/1.01  sup_num_in_passive:                     2
% 2.67/1.01  sup_num_of_loops:                       63
% 2.67/1.01  sup_fw_superposition:                   26
% 2.67/1.01  sup_bw_superposition:                   25
% 2.67/1.01  sup_immediate_simplified:               34
% 2.67/1.01  sup_given_eliminated:                   0
% 2.67/1.01  comparisons_done:                       0
% 2.67/1.01  comparisons_avoided:                    0
% 2.67/1.01  
% 2.67/1.01  ------ Simplifications
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  sim_fw_subset_subsumed:                 7
% 2.67/1.01  sim_bw_subset_subsumed:                 1
% 2.67/1.01  sim_fw_subsumed:                        8
% 2.67/1.01  sim_bw_subsumed:                        0
% 2.67/1.01  sim_fw_subsumption_res:                 0
% 2.67/1.01  sim_bw_subsumption_res:                 0
% 2.67/1.01  sim_tautology_del:                      0
% 2.67/1.01  sim_eq_tautology_del:                   4
% 2.67/1.01  sim_eq_res_simp:                        1
% 2.67/1.01  sim_fw_demodulated:                     0
% 2.67/1.01  sim_bw_demodulated:                     19
% 2.67/1.01  sim_light_normalised:                   38
% 2.67/1.01  sim_joinable_taut:                      0
% 2.67/1.01  sim_joinable_simp:                      0
% 2.67/1.01  sim_ac_normalised:                      0
% 2.67/1.01  sim_smt_subsumption:                    0
% 2.67/1.01  
%------------------------------------------------------------------------------
