%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:36 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  231 (16993 expanded)
%              Number of clauses        :  149 (5400 expanded)
%              Number of leaves         :   21 (4694 expanded)
%              Depth                    :   30
%              Number of atoms          :  876 (106437 expanded)
%              Number of equality atoms :  344 (16763 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f19])).

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
    inference(flattening,[],[f47])).

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,
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

fof(f53,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f52,f51,f50])).

fof(f85,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f77,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f34])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f87,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f88,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f62,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f5])).

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
    inference(flattening,[],[f24])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f64,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_699,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1228,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_699])).

cnf(c_23,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_34,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_393,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_394,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_695,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_394])).

cnf(c_32,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_388,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_389,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_696,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_389])).

cnf(c_1254,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1228,c_695,c_696])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_24,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_375,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_376,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_47,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_378,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_376,c_33,c_32,c_47])).

cnf(c_400,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_378])).

cnf(c_401,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_18,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_497,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_401,c_18])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_513,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_497,c_13])).

cnf(c_693,plain,
    ( ~ v1_funct_2(X0_53,X0_54,k2_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | k1_relat_1(X0_53) = X0_54 ),
    inference(subtyping,[status(esa)],[c_513])).

cnf(c_1233,plain,
    ( k1_relat_1(X0_53) = X0_54
    | v1_funct_2(X0_53,X0_54,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_1809,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1254,c_1233])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_698,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1229,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_698])).

cnf(c_1248,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1229,c_695,c_696])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_719,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1506,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | v1_relat_1(X0_53)
    | ~ v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_1701,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_1702,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1701])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_718,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1739,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_718])).

cnf(c_1740,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1739])).

cnf(c_1867,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1809,c_38,c_40,c_1248,c_1702,c_1740])).

cnf(c_1871,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1867,c_1254])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_706,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1222,plain,
    ( k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_2066,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1871,c_1222])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_700,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1251,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_700,c_695,c_696])).

cnf(c_1873,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1867,c_1251])).

cnf(c_2226,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2066,c_1873])).

cnf(c_2265,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2226,c_2066])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_702,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | k2_relset_1(X0_54,X1_54,X0_53) != X1_54
    | k2_tops_2(X0_54,X1_54,X0_53) = k2_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1226,plain,
    ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
    | k2_tops_2(X0_54,X1_54,X0_53) = k2_funct_1(X0_53)
    | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_702])).

cnf(c_3363,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2265,c_1226])).

cnf(c_27,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_41,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2266,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2226,c_1871])).

cnf(c_1872,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1867,c_1248])).

cnf(c_2267,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2226,c_1872])).

cnf(c_4592,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3363,c_38,c_41,c_2266,c_2267])).

cnf(c_19,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_26,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_423,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_424,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_694,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_424])).

cnf(c_721,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sP0_iProver_split
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_694])).

cnf(c_1231,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_721])).

cnf(c_1422,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1231,c_695,c_696])).

cnf(c_720,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_694])).

cnf(c_1232,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_720])).

cnf(c_1311,plain,
    ( v1_funct_2(X0_53,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1232,c_695,c_696])).

cnf(c_1428,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1422,c_1311])).

cnf(c_1870,plain,
    ( k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1867,c_1428])).

cnf(c_3812,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1870,c_2226])).

cnf(c_4595,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4592,c_3812])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_717,plain,
    ( ~ v1_funct_1(X0_53)
    | v1_funct_1(k2_funct_1(X0_53))
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_762,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_funct_1(X0_53)) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_764,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_704,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | v1_funct_2(k2_funct_1(X0_53),X1_54,X0_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1224,plain,
    ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
    | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | v1_funct_2(k2_funct_1(X0_53),X1_54,X0_54) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_2728,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2265,c_1224])).

cnf(c_701,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1227,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_710,plain,
    ( ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | k1_relat_1(k2_funct_1(X0_53)) = k2_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1218,plain,
    ( k1_relat_1(k2_funct_1(X0_53)) = k2_relat_1(X0_53)
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_710])).

cnf(c_2122,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1227,c_1218])).

cnf(c_780,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_2203,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2122,c_31,c_29,c_27,c_780,c_1701,c_1739])).

cnf(c_6,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_713,plain,
    ( v2_funct_1(X0_53)
    | ~ v2_funct_1(k5_relat_1(X1_53,X0_53))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | ~ v1_relat_1(X0_53)
    | ~ v1_relat_1(X1_53)
    | k1_relat_1(X0_53) != k2_relat_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1215,plain,
    ( k1_relat_1(X0_53) != k2_relat_1(X1_53)
    | v2_funct_1(X0_53) = iProver_top
    | v2_funct_1(k5_relat_1(X1_53,X0_53)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_2442,plain,
    ( k2_relat_1(X0_53) != k2_relat_1(sK2)
    | v2_funct_1(k5_relat_1(X0_53,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2203,c_1215])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_716,plain,
    ( ~ v1_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | v1_relat_1(k2_funct_1(X0_53)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_765,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(k2_funct_1(X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_767,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(c_2904,plain,
    ( v1_relat_1(X0_53) != iProver_top
    | k2_relat_1(X0_53) != k2_relat_1(sK2)
    | v2_funct_1(k5_relat_1(X0_53,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2442,c_38,c_40,c_764,c_767,c_1702,c_1740])).

cnf(c_2905,plain,
    ( k2_relat_1(X0_53) != k2_relat_1(sK2)
    | v2_funct_1(k5_relat_1(X0_53,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2904])).

cnf(c_2916,plain,
    ( v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2905])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_708,plain,
    ( ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | k5_relat_1(X0_53,k2_funct_1(X0_53)) = k6_relat_1(k1_relat_1(X0_53)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1220,plain,
    ( k5_relat_1(X0_53,k2_funct_1(X0_53)) = k6_relat_1(k1_relat_1(X0_53))
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(c_2481,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1227,c_1220])).

cnf(c_786,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_2731,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2481,c_31,c_29,c_27,c_786,c_1701,c_1739])).

cnf(c_2921,plain,
    ( v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2916,c_2731])).

cnf(c_2997,plain,
    ( v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2921,c_38,c_40,c_1702,c_1740])).

cnf(c_4,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_715,plain,
    ( v2_funct_1(k6_relat_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1213,plain,
    ( v2_funct_1(k6_relat_1(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_715])).

cnf(c_3003,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2997,c_1213])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_705,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54)))
    | ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1223,plain,
    ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
    | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54))) = iProver_top
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_705])).

cnf(c_3372,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2265,c_1223])).

cnf(c_4670,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3372,c_38,c_41,c_2266,c_2267])).

cnf(c_4676,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4670,c_1222])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_711,plain,
    ( ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1217,plain,
    ( k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53)
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_711])).

cnf(c_2072,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1227,c_1217])).

cnf(c_777,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_2199,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2072,c_31,c_29,c_27,c_777,c_1701,c_1739])).

cnf(c_4683,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4676,c_2199])).

cnf(c_4760,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4683,c_1226])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
    | k1_relat_1(X0) != k2_relat_1(X1)
    | k2_funct_1(X0) = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_707,plain,
    ( ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | ~ v1_relat_1(X0_53)
    | ~ v1_relat_1(X1_53)
    | k1_relat_1(X0_53) != k2_relat_1(X1_53)
    | k5_relat_1(X1_53,X0_53) != k6_relat_1(k2_relat_1(X0_53))
    | k2_funct_1(X0_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1221,plain,
    ( k1_relat_1(X0_53) != k2_relat_1(X1_53)
    | k5_relat_1(X1_53,X0_53) != k6_relat_1(k2_relat_1(X0_53))
    | k2_funct_1(X0_53) = X1_53
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_707])).

cnf(c_3252,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k6_relat_1(k1_relat_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2731,c_1221])).

cnf(c_3261,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3252,c_2199,c_2203])).

cnf(c_3262,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3261])).

cnf(c_4402,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3262,c_38,c_40,c_764,c_767,c_1702,c_1740,c_3003])).

cnf(c_4773,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4760,c_4402])).

cnf(c_4852,plain,
    ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4595,c_38,c_40,c_41,c_764,c_1702,c_1740,c_2266,c_2267,c_2728,c_3003,c_3372,c_4773])).

cnf(c_4787,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4773,c_38,c_40,c_41,c_764,c_1702,c_1740,c_2266,c_2267,c_2728,c_3003,c_3372])).

cnf(c_4856,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4852,c_4787])).

cnf(c_697,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1230,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_697])).

cnf(c_4860,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4856,c_1230,c_2266,c_2267])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:12:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.74/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.00  
% 2.74/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.74/1.00  
% 2.74/1.00  ------  iProver source info
% 2.74/1.00  
% 2.74/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.74/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.74/1.00  git: non_committed_changes: false
% 2.74/1.00  git: last_make_outside_of_git: false
% 2.74/1.00  
% 2.74/1.00  ------ 
% 2.74/1.00  
% 2.74/1.00  ------ Input Options
% 2.74/1.00  
% 2.74/1.00  --out_options                           all
% 2.74/1.00  --tptp_safe_out                         true
% 2.74/1.00  --problem_path                          ""
% 2.74/1.00  --include_path                          ""
% 2.74/1.00  --clausifier                            res/vclausify_rel
% 2.74/1.00  --clausifier_options                    --mode clausify
% 2.74/1.00  --stdin                                 false
% 2.74/1.00  --stats_out                             all
% 2.74/1.00  
% 2.74/1.00  ------ General Options
% 2.74/1.00  
% 2.74/1.00  --fof                                   false
% 2.74/1.00  --time_out_real                         305.
% 2.74/1.00  --time_out_virtual                      -1.
% 2.74/1.00  --symbol_type_check                     false
% 2.74/1.00  --clausify_out                          false
% 2.74/1.00  --sig_cnt_out                           false
% 2.74/1.00  --trig_cnt_out                          false
% 2.74/1.00  --trig_cnt_out_tolerance                1.
% 2.74/1.00  --trig_cnt_out_sk_spl                   false
% 2.74/1.00  --abstr_cl_out                          false
% 2.74/1.00  
% 2.74/1.00  ------ Global Options
% 2.74/1.00  
% 2.74/1.00  --schedule                              default
% 2.74/1.00  --add_important_lit                     false
% 2.74/1.00  --prop_solver_per_cl                    1000
% 2.74/1.00  --min_unsat_core                        false
% 2.74/1.00  --soft_assumptions                      false
% 2.74/1.00  --soft_lemma_size                       3
% 2.74/1.00  --prop_impl_unit_size                   0
% 2.74/1.00  --prop_impl_unit                        []
% 2.74/1.00  --share_sel_clauses                     true
% 2.74/1.00  --reset_solvers                         false
% 2.74/1.00  --bc_imp_inh                            [conj_cone]
% 2.74/1.00  --conj_cone_tolerance                   3.
% 2.74/1.00  --extra_neg_conj                        none
% 2.74/1.00  --large_theory_mode                     true
% 2.74/1.00  --prolific_symb_bound                   200
% 2.74/1.00  --lt_threshold                          2000
% 2.74/1.00  --clause_weak_htbl                      true
% 2.74/1.00  --gc_record_bc_elim                     false
% 2.74/1.00  
% 2.74/1.00  ------ Preprocessing Options
% 2.74/1.00  
% 2.74/1.00  --preprocessing_flag                    true
% 2.74/1.00  --time_out_prep_mult                    0.1
% 2.74/1.00  --splitting_mode                        input
% 2.74/1.00  --splitting_grd                         true
% 2.74/1.00  --splitting_cvd                         false
% 2.74/1.00  --splitting_cvd_svl                     false
% 2.74/1.00  --splitting_nvd                         32
% 2.74/1.00  --sub_typing                            true
% 2.74/1.00  --prep_gs_sim                           true
% 2.74/1.00  --prep_unflatten                        true
% 2.74/1.00  --prep_res_sim                          true
% 2.74/1.00  --prep_upred                            true
% 2.74/1.00  --prep_sem_filter                       exhaustive
% 2.74/1.00  --prep_sem_filter_out                   false
% 2.74/1.00  --pred_elim                             true
% 2.74/1.00  --res_sim_input                         true
% 2.74/1.00  --eq_ax_congr_red                       true
% 2.74/1.00  --pure_diseq_elim                       true
% 2.74/1.00  --brand_transform                       false
% 2.74/1.00  --non_eq_to_eq                          false
% 2.74/1.00  --prep_def_merge                        true
% 2.74/1.00  --prep_def_merge_prop_impl              false
% 2.74/1.00  --prep_def_merge_mbd                    true
% 2.74/1.00  --prep_def_merge_tr_red                 false
% 2.74/1.00  --prep_def_merge_tr_cl                  false
% 2.74/1.00  --smt_preprocessing                     true
% 2.74/1.00  --smt_ac_axioms                         fast
% 2.74/1.00  --preprocessed_out                      false
% 2.74/1.00  --preprocessed_stats                    false
% 2.74/1.00  
% 2.74/1.00  ------ Abstraction refinement Options
% 2.74/1.00  
% 2.74/1.00  --abstr_ref                             []
% 2.74/1.00  --abstr_ref_prep                        false
% 2.74/1.00  --abstr_ref_until_sat                   false
% 2.74/1.00  --abstr_ref_sig_restrict                funpre
% 2.74/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/1.00  --abstr_ref_under                       []
% 2.74/1.00  
% 2.74/1.00  ------ SAT Options
% 2.74/1.00  
% 2.74/1.00  --sat_mode                              false
% 2.74/1.00  --sat_fm_restart_options                ""
% 2.74/1.00  --sat_gr_def                            false
% 2.74/1.00  --sat_epr_types                         true
% 2.74/1.00  --sat_non_cyclic_types                  false
% 2.74/1.00  --sat_finite_models                     false
% 2.74/1.00  --sat_fm_lemmas                         false
% 2.74/1.00  --sat_fm_prep                           false
% 2.74/1.00  --sat_fm_uc_incr                        true
% 2.74/1.00  --sat_out_model                         small
% 2.74/1.00  --sat_out_clauses                       false
% 2.74/1.00  
% 2.74/1.00  ------ QBF Options
% 2.74/1.00  
% 2.74/1.00  --qbf_mode                              false
% 2.74/1.00  --qbf_elim_univ                         false
% 2.74/1.00  --qbf_dom_inst                          none
% 2.74/1.00  --qbf_dom_pre_inst                      false
% 2.74/1.00  --qbf_sk_in                             false
% 2.74/1.00  --qbf_pred_elim                         true
% 2.74/1.00  --qbf_split                             512
% 2.74/1.00  
% 2.74/1.00  ------ BMC1 Options
% 2.74/1.00  
% 2.74/1.00  --bmc1_incremental                      false
% 2.74/1.00  --bmc1_axioms                           reachable_all
% 2.74/1.00  --bmc1_min_bound                        0
% 2.74/1.00  --bmc1_max_bound                        -1
% 2.74/1.00  --bmc1_max_bound_default                -1
% 2.74/1.00  --bmc1_symbol_reachability              true
% 2.74/1.00  --bmc1_property_lemmas                  false
% 2.74/1.00  --bmc1_k_induction                      false
% 2.74/1.00  --bmc1_non_equiv_states                 false
% 2.74/1.00  --bmc1_deadlock                         false
% 2.74/1.00  --bmc1_ucm                              false
% 2.74/1.00  --bmc1_add_unsat_core                   none
% 2.74/1.00  --bmc1_unsat_core_children              false
% 2.74/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/1.00  --bmc1_out_stat                         full
% 2.74/1.00  --bmc1_ground_init                      false
% 2.74/1.00  --bmc1_pre_inst_next_state              false
% 2.74/1.00  --bmc1_pre_inst_state                   false
% 2.74/1.00  --bmc1_pre_inst_reach_state             false
% 2.74/1.00  --bmc1_out_unsat_core                   false
% 2.74/1.00  --bmc1_aig_witness_out                  false
% 2.74/1.00  --bmc1_verbose                          false
% 2.74/1.00  --bmc1_dump_clauses_tptp                false
% 2.74/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.74/1.00  --bmc1_dump_file                        -
% 2.74/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.74/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.74/1.00  --bmc1_ucm_extend_mode                  1
% 2.74/1.00  --bmc1_ucm_init_mode                    2
% 2.74/1.00  --bmc1_ucm_cone_mode                    none
% 2.74/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.74/1.00  --bmc1_ucm_relax_model                  4
% 2.74/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.74/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/1.00  --bmc1_ucm_layered_model                none
% 2.74/1.00  --bmc1_ucm_max_lemma_size               10
% 2.74/1.00  
% 2.74/1.00  ------ AIG Options
% 2.74/1.00  
% 2.74/1.00  --aig_mode                              false
% 2.74/1.00  
% 2.74/1.00  ------ Instantiation Options
% 2.74/1.00  
% 2.74/1.00  --instantiation_flag                    true
% 2.74/1.00  --inst_sos_flag                         false
% 2.74/1.00  --inst_sos_phase                        true
% 2.74/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/1.00  --inst_lit_sel_side                     num_symb
% 2.74/1.00  --inst_solver_per_active                1400
% 2.74/1.00  --inst_solver_calls_frac                1.
% 2.74/1.00  --inst_passive_queue_type               priority_queues
% 2.74/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/1.00  --inst_passive_queues_freq              [25;2]
% 2.74/1.00  --inst_dismatching                      true
% 2.74/1.00  --inst_eager_unprocessed_to_passive     true
% 2.74/1.00  --inst_prop_sim_given                   true
% 2.74/1.00  --inst_prop_sim_new                     false
% 2.74/1.00  --inst_subs_new                         false
% 2.74/1.00  --inst_eq_res_simp                      false
% 2.74/1.00  --inst_subs_given                       false
% 2.74/1.00  --inst_orphan_elimination               true
% 2.74/1.00  --inst_learning_loop_flag               true
% 2.74/1.00  --inst_learning_start                   3000
% 2.74/1.00  --inst_learning_factor                  2
% 2.74/1.00  --inst_start_prop_sim_after_learn       3
% 2.74/1.00  --inst_sel_renew                        solver
% 2.74/1.00  --inst_lit_activity_flag                true
% 2.74/1.00  --inst_restr_to_given                   false
% 2.74/1.00  --inst_activity_threshold               500
% 2.74/1.00  --inst_out_proof                        true
% 2.74/1.00  
% 2.74/1.00  ------ Resolution Options
% 2.74/1.00  
% 2.74/1.00  --resolution_flag                       true
% 2.74/1.00  --res_lit_sel                           adaptive
% 2.74/1.00  --res_lit_sel_side                      none
% 2.74/1.00  --res_ordering                          kbo
% 2.74/1.00  --res_to_prop_solver                    active
% 2.74/1.00  --res_prop_simpl_new                    false
% 2.74/1.00  --res_prop_simpl_given                  true
% 2.74/1.00  --res_passive_queue_type                priority_queues
% 2.74/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/1.00  --res_passive_queues_freq               [15;5]
% 2.74/1.00  --res_forward_subs                      full
% 2.74/1.00  --res_backward_subs                     full
% 2.74/1.00  --res_forward_subs_resolution           true
% 2.74/1.00  --res_backward_subs_resolution          true
% 2.74/1.00  --res_orphan_elimination                true
% 2.74/1.00  --res_time_limit                        2.
% 2.74/1.00  --res_out_proof                         true
% 2.74/1.00  
% 2.74/1.00  ------ Superposition Options
% 2.74/1.00  
% 2.74/1.00  --superposition_flag                    true
% 2.74/1.00  --sup_passive_queue_type                priority_queues
% 2.74/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.74/1.00  --demod_completeness_check              fast
% 2.74/1.00  --demod_use_ground                      true
% 2.74/1.00  --sup_to_prop_solver                    passive
% 2.74/1.00  --sup_prop_simpl_new                    true
% 2.74/1.00  --sup_prop_simpl_given                  true
% 2.74/1.00  --sup_fun_splitting                     false
% 2.74/1.00  --sup_smt_interval                      50000
% 2.74/1.00  
% 2.74/1.00  ------ Superposition Simplification Setup
% 2.74/1.00  
% 2.74/1.00  --sup_indices_passive                   []
% 2.74/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.00  --sup_full_bw                           [BwDemod]
% 2.74/1.00  --sup_immed_triv                        [TrivRules]
% 2.74/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.00  --sup_immed_bw_main                     []
% 2.74/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/1.00  
% 2.74/1.00  ------ Combination Options
% 2.74/1.00  
% 2.74/1.00  --comb_res_mult                         3
% 2.74/1.00  --comb_sup_mult                         2
% 2.74/1.00  --comb_inst_mult                        10
% 2.74/1.00  
% 2.74/1.00  ------ Debug Options
% 2.74/1.00  
% 2.74/1.00  --dbg_backtrace                         false
% 2.74/1.00  --dbg_dump_prop_clauses                 false
% 2.74/1.00  --dbg_dump_prop_clauses_file            -
% 2.74/1.00  --dbg_out_stat                          false
% 2.74/1.00  ------ Parsing...
% 2.74/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.74/1.00  
% 2.74/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.74/1.00  
% 2.74/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.74/1.00  
% 2.74/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.74/1.00  ------ Proving...
% 2.74/1.00  ------ Problem Properties 
% 2.74/1.00  
% 2.74/1.00  
% 2.74/1.00  clauses                                 28
% 2.74/1.00  conjectures                             5
% 2.74/1.00  EPR                                     2
% 2.74/1.00  Horn                                    28
% 2.74/1.00  unary                                   10
% 2.74/1.00  binary                                  1
% 2.74/1.00  lits                                    97
% 2.74/1.00  lits eq                                 20
% 2.74/1.00  fd_pure                                 0
% 2.74/1.00  fd_pseudo                               0
% 2.74/1.00  fd_cond                                 0
% 2.74/1.00  fd_pseudo_cond                          2
% 2.74/1.00  AC symbols                              0
% 2.74/1.00  
% 2.74/1.00  ------ Schedule dynamic 5 is on 
% 2.74/1.00  
% 2.74/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.74/1.00  
% 2.74/1.00  
% 2.74/1.00  ------ 
% 2.74/1.00  Current options:
% 2.74/1.00  ------ 
% 2.74/1.00  
% 2.74/1.00  ------ Input Options
% 2.74/1.00  
% 2.74/1.00  --out_options                           all
% 2.74/1.00  --tptp_safe_out                         true
% 2.74/1.00  --problem_path                          ""
% 2.74/1.00  --include_path                          ""
% 2.74/1.00  --clausifier                            res/vclausify_rel
% 2.74/1.00  --clausifier_options                    --mode clausify
% 2.74/1.00  --stdin                                 false
% 2.74/1.00  --stats_out                             all
% 2.74/1.00  
% 2.74/1.00  ------ General Options
% 2.74/1.00  
% 2.74/1.00  --fof                                   false
% 2.74/1.00  --time_out_real                         305.
% 2.74/1.00  --time_out_virtual                      -1.
% 2.74/1.00  --symbol_type_check                     false
% 2.74/1.00  --clausify_out                          false
% 2.74/1.00  --sig_cnt_out                           false
% 2.74/1.00  --trig_cnt_out                          false
% 2.74/1.00  --trig_cnt_out_tolerance                1.
% 2.74/1.00  --trig_cnt_out_sk_spl                   false
% 2.74/1.00  --abstr_cl_out                          false
% 2.74/1.00  
% 2.74/1.00  ------ Global Options
% 2.74/1.00  
% 2.74/1.00  --schedule                              default
% 2.74/1.00  --add_important_lit                     false
% 2.74/1.00  --prop_solver_per_cl                    1000
% 2.74/1.00  --min_unsat_core                        false
% 2.74/1.00  --soft_assumptions                      false
% 2.74/1.00  --soft_lemma_size                       3
% 2.74/1.00  --prop_impl_unit_size                   0
% 2.74/1.00  --prop_impl_unit                        []
% 2.74/1.00  --share_sel_clauses                     true
% 2.74/1.00  --reset_solvers                         false
% 2.74/1.00  --bc_imp_inh                            [conj_cone]
% 2.74/1.00  --conj_cone_tolerance                   3.
% 2.74/1.00  --extra_neg_conj                        none
% 2.74/1.00  --large_theory_mode                     true
% 2.74/1.00  --prolific_symb_bound                   200
% 2.74/1.00  --lt_threshold                          2000
% 2.74/1.00  --clause_weak_htbl                      true
% 2.74/1.00  --gc_record_bc_elim                     false
% 2.74/1.00  
% 2.74/1.00  ------ Preprocessing Options
% 2.74/1.00  
% 2.74/1.00  --preprocessing_flag                    true
% 2.74/1.00  --time_out_prep_mult                    0.1
% 2.74/1.00  --splitting_mode                        input
% 2.74/1.00  --splitting_grd                         true
% 2.74/1.00  --splitting_cvd                         false
% 2.74/1.00  --splitting_cvd_svl                     false
% 2.74/1.00  --splitting_nvd                         32
% 2.74/1.00  --sub_typing                            true
% 2.74/1.00  --prep_gs_sim                           true
% 2.74/1.00  --prep_unflatten                        true
% 2.74/1.00  --prep_res_sim                          true
% 2.74/1.00  --prep_upred                            true
% 2.74/1.00  --prep_sem_filter                       exhaustive
% 2.74/1.00  --prep_sem_filter_out                   false
% 2.74/1.00  --pred_elim                             true
% 2.74/1.00  --res_sim_input                         true
% 2.74/1.00  --eq_ax_congr_red                       true
% 2.74/1.00  --pure_diseq_elim                       true
% 2.74/1.00  --brand_transform                       false
% 2.74/1.00  --non_eq_to_eq                          false
% 2.74/1.00  --prep_def_merge                        true
% 2.74/1.00  --prep_def_merge_prop_impl              false
% 2.74/1.00  --prep_def_merge_mbd                    true
% 2.74/1.00  --prep_def_merge_tr_red                 false
% 2.74/1.00  --prep_def_merge_tr_cl                  false
% 2.74/1.00  --smt_preprocessing                     true
% 2.74/1.00  --smt_ac_axioms                         fast
% 2.74/1.00  --preprocessed_out                      false
% 2.74/1.00  --preprocessed_stats                    false
% 2.74/1.00  
% 2.74/1.00  ------ Abstraction refinement Options
% 2.74/1.00  
% 2.74/1.00  --abstr_ref                             []
% 2.74/1.00  --abstr_ref_prep                        false
% 2.74/1.00  --abstr_ref_until_sat                   false
% 2.74/1.00  --abstr_ref_sig_restrict                funpre
% 2.74/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/1.00  --abstr_ref_under                       []
% 2.74/1.00  
% 2.74/1.00  ------ SAT Options
% 2.74/1.00  
% 2.74/1.00  --sat_mode                              false
% 2.74/1.00  --sat_fm_restart_options                ""
% 2.74/1.00  --sat_gr_def                            false
% 2.74/1.00  --sat_epr_types                         true
% 2.74/1.00  --sat_non_cyclic_types                  false
% 2.74/1.00  --sat_finite_models                     false
% 2.74/1.00  --sat_fm_lemmas                         false
% 2.74/1.00  --sat_fm_prep                           false
% 2.74/1.00  --sat_fm_uc_incr                        true
% 2.74/1.00  --sat_out_model                         small
% 2.74/1.00  --sat_out_clauses                       false
% 2.74/1.00  
% 2.74/1.00  ------ QBF Options
% 2.74/1.00  
% 2.74/1.00  --qbf_mode                              false
% 2.74/1.00  --qbf_elim_univ                         false
% 2.74/1.00  --qbf_dom_inst                          none
% 2.74/1.00  --qbf_dom_pre_inst                      false
% 2.74/1.00  --qbf_sk_in                             false
% 2.74/1.00  --qbf_pred_elim                         true
% 2.74/1.00  --qbf_split                             512
% 2.74/1.00  
% 2.74/1.00  ------ BMC1 Options
% 2.74/1.00  
% 2.74/1.00  --bmc1_incremental                      false
% 2.74/1.00  --bmc1_axioms                           reachable_all
% 2.74/1.00  --bmc1_min_bound                        0
% 2.74/1.00  --bmc1_max_bound                        -1
% 2.74/1.00  --bmc1_max_bound_default                -1
% 2.74/1.00  --bmc1_symbol_reachability              true
% 2.74/1.00  --bmc1_property_lemmas                  false
% 2.74/1.00  --bmc1_k_induction                      false
% 2.74/1.00  --bmc1_non_equiv_states                 false
% 2.74/1.00  --bmc1_deadlock                         false
% 2.74/1.00  --bmc1_ucm                              false
% 2.74/1.00  --bmc1_add_unsat_core                   none
% 2.74/1.00  --bmc1_unsat_core_children              false
% 2.74/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/1.00  --bmc1_out_stat                         full
% 2.74/1.00  --bmc1_ground_init                      false
% 2.74/1.00  --bmc1_pre_inst_next_state              false
% 2.74/1.00  --bmc1_pre_inst_state                   false
% 2.74/1.00  --bmc1_pre_inst_reach_state             false
% 2.74/1.00  --bmc1_out_unsat_core                   false
% 2.74/1.00  --bmc1_aig_witness_out                  false
% 2.74/1.00  --bmc1_verbose                          false
% 2.74/1.00  --bmc1_dump_clauses_tptp                false
% 2.74/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.74/1.00  --bmc1_dump_file                        -
% 2.74/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.74/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.74/1.00  --bmc1_ucm_extend_mode                  1
% 2.74/1.00  --bmc1_ucm_init_mode                    2
% 2.74/1.00  --bmc1_ucm_cone_mode                    none
% 2.74/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.74/1.00  --bmc1_ucm_relax_model                  4
% 2.74/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.74/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/1.00  --bmc1_ucm_layered_model                none
% 2.74/1.00  --bmc1_ucm_max_lemma_size               10
% 2.74/1.00  
% 2.74/1.00  ------ AIG Options
% 2.74/1.00  
% 2.74/1.00  --aig_mode                              false
% 2.74/1.00  
% 2.74/1.00  ------ Instantiation Options
% 2.74/1.00  
% 2.74/1.00  --instantiation_flag                    true
% 2.74/1.00  --inst_sos_flag                         false
% 2.74/1.00  --inst_sos_phase                        true
% 2.74/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/1.00  --inst_lit_sel_side                     none
% 2.74/1.00  --inst_solver_per_active                1400
% 2.74/1.00  --inst_solver_calls_frac                1.
% 2.74/1.00  --inst_passive_queue_type               priority_queues
% 2.74/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/1.00  --inst_passive_queues_freq              [25;2]
% 2.74/1.00  --inst_dismatching                      true
% 2.74/1.00  --inst_eager_unprocessed_to_passive     true
% 2.74/1.00  --inst_prop_sim_given                   true
% 2.74/1.00  --inst_prop_sim_new                     false
% 2.74/1.00  --inst_subs_new                         false
% 2.74/1.00  --inst_eq_res_simp                      false
% 2.74/1.00  --inst_subs_given                       false
% 2.74/1.00  --inst_orphan_elimination               true
% 2.74/1.00  --inst_learning_loop_flag               true
% 2.74/1.00  --inst_learning_start                   3000
% 2.74/1.00  --inst_learning_factor                  2
% 2.74/1.00  --inst_start_prop_sim_after_learn       3
% 2.74/1.00  --inst_sel_renew                        solver
% 2.74/1.00  --inst_lit_activity_flag                true
% 2.74/1.00  --inst_restr_to_given                   false
% 2.74/1.00  --inst_activity_threshold               500
% 2.74/1.00  --inst_out_proof                        true
% 2.74/1.00  
% 2.74/1.00  ------ Resolution Options
% 2.74/1.00  
% 2.74/1.00  --resolution_flag                       false
% 2.74/1.00  --res_lit_sel                           adaptive
% 2.74/1.00  --res_lit_sel_side                      none
% 2.74/1.00  --res_ordering                          kbo
% 2.74/1.00  --res_to_prop_solver                    active
% 2.74/1.00  --res_prop_simpl_new                    false
% 2.74/1.00  --res_prop_simpl_given                  true
% 2.74/1.00  --res_passive_queue_type                priority_queues
% 2.74/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/1.00  --res_passive_queues_freq               [15;5]
% 2.74/1.00  --res_forward_subs                      full
% 2.74/1.00  --res_backward_subs                     full
% 2.74/1.00  --res_forward_subs_resolution           true
% 2.74/1.00  --res_backward_subs_resolution          true
% 2.74/1.00  --res_orphan_elimination                true
% 2.74/1.00  --res_time_limit                        2.
% 2.74/1.00  --res_out_proof                         true
% 2.74/1.00  
% 2.74/1.00  ------ Superposition Options
% 2.74/1.00  
% 2.74/1.00  --superposition_flag                    true
% 2.74/1.00  --sup_passive_queue_type                priority_queues
% 2.74/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.74/1.00  --demod_completeness_check              fast
% 2.74/1.00  --demod_use_ground                      true
% 2.74/1.00  --sup_to_prop_solver                    passive
% 2.74/1.00  --sup_prop_simpl_new                    true
% 2.74/1.00  --sup_prop_simpl_given                  true
% 2.74/1.00  --sup_fun_splitting                     false
% 2.74/1.00  --sup_smt_interval                      50000
% 2.74/1.00  
% 2.74/1.00  ------ Superposition Simplification Setup
% 2.74/1.00  
% 2.74/1.00  --sup_indices_passive                   []
% 2.74/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.00  --sup_full_bw                           [BwDemod]
% 2.74/1.00  --sup_immed_triv                        [TrivRules]
% 2.74/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.00  --sup_immed_bw_main                     []
% 2.74/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/1.00  
% 2.74/1.00  ------ Combination Options
% 2.74/1.00  
% 2.74/1.00  --comb_res_mult                         3
% 2.74/1.00  --comb_sup_mult                         2
% 2.74/1.00  --comb_inst_mult                        10
% 2.74/1.00  
% 2.74/1.00  ------ Debug Options
% 2.74/1.00  
% 2.74/1.00  --dbg_backtrace                         false
% 2.74/1.00  --dbg_dump_prop_clauses                 false
% 2.74/1.00  --dbg_dump_prop_clauses_file            -
% 2.74/1.00  --dbg_out_stat                          false
% 2.74/1.00  
% 2.74/1.00  
% 2.74/1.00  
% 2.74/1.00  
% 2.74/1.00  ------ Proving...
% 2.74/1.00  
% 2.74/1.00  
% 2.74/1.00  % SZS status Theorem for theBenchmark.p
% 2.74/1.00  
% 2.74/1.00   Resolution empty clause
% 2.74/1.00  
% 2.74/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.74/1.00  
% 2.74/1.00  fof(f18,conjecture,(
% 2.74/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f19,negated_conjecture,(
% 2.74/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.74/1.00    inference(negated_conjecture,[],[f18])).
% 2.74/1.00  
% 2.74/1.00  fof(f47,plain,(
% 2.74/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.74/1.00    inference(ennf_transformation,[],[f19])).
% 2.74/1.00  
% 2.74/1.00  fof(f48,plain,(
% 2.74/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.74/1.00    inference(flattening,[],[f47])).
% 2.74/1.00  
% 2.74/1.00  fof(f52,plain,(
% 2.74/1.00    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.74/1.00    introduced(choice_axiom,[])).
% 2.74/1.00  
% 2.74/1.00  fof(f51,plain,(
% 2.74/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.74/1.00    introduced(choice_axiom,[])).
% 2.74/1.00  
% 2.74/1.00  fof(f50,plain,(
% 2.74/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.74/1.00    introduced(choice_axiom,[])).
% 2.74/1.00  
% 2.74/1.00  fof(f53,plain,(
% 2.74/1.00    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.74/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f52,f51,f50])).
% 2.74/1.00  
% 2.74/1.00  fof(f85,plain,(
% 2.74/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.74/1.00    inference(cnf_transformation,[],[f53])).
% 2.74/1.00  
% 2.74/1.00  fof(f15,axiom,(
% 2.74/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f42,plain,(
% 2.74/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.74/1.00    inference(ennf_transformation,[],[f15])).
% 2.74/1.00  
% 2.74/1.00  fof(f77,plain,(
% 2.74/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f42])).
% 2.74/1.00  
% 2.74/1.00  fof(f80,plain,(
% 2.74/1.00    l1_struct_0(sK0)),
% 2.74/1.00    inference(cnf_transformation,[],[f53])).
% 2.74/1.00  
% 2.74/1.00  fof(f82,plain,(
% 2.74/1.00    l1_struct_0(sK1)),
% 2.74/1.00    inference(cnf_transformation,[],[f53])).
% 2.74/1.00  
% 2.74/1.00  fof(f11,axiom,(
% 2.74/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f34,plain,(
% 2.74/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.74/1.00    inference(ennf_transformation,[],[f11])).
% 2.74/1.00  
% 2.74/1.00  fof(f35,plain,(
% 2.74/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.74/1.00    inference(flattening,[],[f34])).
% 2.74/1.00  
% 2.74/1.00  fof(f70,plain,(
% 2.74/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f35])).
% 2.74/1.00  
% 2.74/1.00  fof(f16,axiom,(
% 2.74/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 2.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f43,plain,(
% 2.74/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.74/1.00    inference(ennf_transformation,[],[f16])).
% 2.74/1.00  
% 2.74/1.00  fof(f44,plain,(
% 2.74/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.74/1.00    inference(flattening,[],[f43])).
% 2.74/1.00  
% 2.74/1.00  fof(f78,plain,(
% 2.74/1.00    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f44])).
% 2.74/1.00  
% 2.74/1.00  fof(f81,plain,(
% 2.74/1.00    ~v2_struct_0(sK1)),
% 2.74/1.00    inference(cnf_transformation,[],[f53])).
% 2.74/1.00  
% 2.74/1.00  fof(f12,axiom,(
% 2.74/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f36,plain,(
% 2.74/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.74/1.00    inference(ennf_transformation,[],[f12])).
% 2.74/1.00  
% 2.74/1.00  fof(f37,plain,(
% 2.74/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.74/1.00    inference(flattening,[],[f36])).
% 2.74/1.00  
% 2.74/1.00  fof(f49,plain,(
% 2.74/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.74/1.00    inference(nnf_transformation,[],[f37])).
% 2.74/1.00  
% 2.74/1.00  fof(f71,plain,(
% 2.74/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f49])).
% 2.74/1.00  
% 2.74/1.00  fof(f9,axiom,(
% 2.74/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f20,plain,(
% 2.74/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.74/1.00    inference(pure_predicate_removal,[],[f9])).
% 2.74/1.00  
% 2.74/1.00  fof(f32,plain,(
% 2.74/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/1.00    inference(ennf_transformation,[],[f20])).
% 2.74/1.00  
% 2.74/1.00  fof(f67,plain,(
% 2.74/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/1.00    inference(cnf_transformation,[],[f32])).
% 2.74/1.00  
% 2.74/1.00  fof(f83,plain,(
% 2.74/1.00    v1_funct_1(sK2)),
% 2.74/1.00    inference(cnf_transformation,[],[f53])).
% 2.74/1.00  
% 2.74/1.00  fof(f84,plain,(
% 2.74/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.74/1.00    inference(cnf_transformation,[],[f53])).
% 2.74/1.00  
% 2.74/1.00  fof(f1,axiom,(
% 2.74/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f21,plain,(
% 2.74/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.74/1.00    inference(ennf_transformation,[],[f1])).
% 2.74/1.00  
% 2.74/1.00  fof(f54,plain,(
% 2.74/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f21])).
% 2.74/1.00  
% 2.74/1.00  fof(f2,axiom,(
% 2.74/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f55,plain,(
% 2.74/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.74/1.00    inference(cnf_transformation,[],[f2])).
% 2.74/1.00  
% 2.74/1.00  fof(f10,axiom,(
% 2.74/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f33,plain,(
% 2.74/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/1.00    inference(ennf_transformation,[],[f10])).
% 2.74/1.00  
% 2.74/1.00  fof(f68,plain,(
% 2.74/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/1.00    inference(cnf_transformation,[],[f33])).
% 2.74/1.00  
% 2.74/1.00  fof(f86,plain,(
% 2.74/1.00    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.74/1.00    inference(cnf_transformation,[],[f53])).
% 2.74/1.00  
% 2.74/1.00  fof(f17,axiom,(
% 2.74/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f45,plain,(
% 2.74/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.74/1.00    inference(ennf_transformation,[],[f17])).
% 2.74/1.00  
% 2.74/1.00  fof(f46,plain,(
% 2.74/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.74/1.00    inference(flattening,[],[f45])).
% 2.74/1.00  
% 2.74/1.00  fof(f79,plain,(
% 2.74/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f46])).
% 2.74/1.00  
% 2.74/1.00  fof(f87,plain,(
% 2.74/1.00    v2_funct_1(sK2)),
% 2.74/1.00    inference(cnf_transformation,[],[f53])).
% 2.74/1.00  
% 2.74/1.00  fof(f13,axiom,(
% 2.74/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 2.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f38,plain,(
% 2.74/1.00    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.74/1.00    inference(ennf_transformation,[],[f13])).
% 2.74/1.00  
% 2.74/1.00  fof(f39,plain,(
% 2.74/1.00    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.74/1.00    inference(flattening,[],[f38])).
% 2.74/1.00  
% 2.74/1.00  fof(f73,plain,(
% 2.74/1.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f39])).
% 2.74/1.00  
% 2.74/1.00  fof(f88,plain,(
% 2.74/1.00    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.74/1.00    inference(cnf_transformation,[],[f53])).
% 2.74/1.00  
% 2.74/1.00  fof(f3,axiom,(
% 2.74/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f22,plain,(
% 2.74/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.74/1.00    inference(ennf_transformation,[],[f3])).
% 2.74/1.00  
% 2.74/1.00  fof(f23,plain,(
% 2.74/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.74/1.00    inference(flattening,[],[f22])).
% 2.74/1.00  
% 2.74/1.00  fof(f57,plain,(
% 2.74/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f23])).
% 2.74/1.00  
% 2.74/1.00  fof(f14,axiom,(
% 2.74/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f40,plain,(
% 2.74/1.00    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.74/1.00    inference(ennf_transformation,[],[f14])).
% 2.74/1.00  
% 2.74/1.00  fof(f41,plain,(
% 2.74/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.74/1.00    inference(flattening,[],[f40])).
% 2.74/1.00  
% 2.74/1.00  fof(f75,plain,(
% 2.74/1.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f41])).
% 2.74/1.00  
% 2.74/1.00  fof(f6,axiom,(
% 2.74/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f26,plain,(
% 2.74/1.00    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.74/1.00    inference(ennf_transformation,[],[f6])).
% 2.74/1.00  
% 2.74/1.00  fof(f27,plain,(
% 2.74/1.00    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.74/1.00    inference(flattening,[],[f26])).
% 2.74/1.00  
% 2.74/1.00  fof(f62,plain,(
% 2.74/1.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f27])).
% 2.74/1.00  
% 2.74/1.00  fof(f5,axiom,(
% 2.74/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 2.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f24,plain,(
% 2.74/1.00    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.74/1.00    inference(ennf_transformation,[],[f5])).
% 2.74/1.00  
% 2.74/1.00  fof(f25,plain,(
% 2.74/1.00    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.74/1.00    inference(flattening,[],[f24])).
% 2.74/1.00  
% 2.74/1.00  fof(f61,plain,(
% 2.74/1.00    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f25])).
% 2.74/1.00  
% 2.74/1.00  fof(f56,plain,(
% 2.74/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f23])).
% 2.74/1.00  
% 2.74/1.00  fof(f7,axiom,(
% 2.74/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 2.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f28,plain,(
% 2.74/1.00    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.74/1.00    inference(ennf_transformation,[],[f7])).
% 2.74/1.00  
% 2.74/1.00  fof(f29,plain,(
% 2.74/1.00    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.74/1.00    inference(flattening,[],[f28])).
% 2.74/1.00  
% 2.74/1.00  fof(f64,plain,(
% 2.74/1.00    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f29])).
% 2.74/1.00  
% 2.74/1.00  fof(f4,axiom,(
% 2.74/1.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f59,plain,(
% 2.74/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.74/1.00    inference(cnf_transformation,[],[f4])).
% 2.74/1.00  
% 2.74/1.00  fof(f76,plain,(
% 2.74/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f41])).
% 2.74/1.00  
% 2.74/1.00  fof(f63,plain,(
% 2.74/1.00    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f27])).
% 2.74/1.00  
% 2.74/1.00  fof(f8,axiom,(
% 2.74/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.74/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/1.00  
% 2.74/1.00  fof(f30,plain,(
% 2.74/1.00    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.74/1.00    inference(ennf_transformation,[],[f8])).
% 2.74/1.00  
% 2.74/1.00  fof(f31,plain,(
% 2.74/1.00    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.74/1.00    inference(flattening,[],[f30])).
% 2.74/1.00  
% 2.74/1.00  fof(f66,plain,(
% 2.74/1.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.74/1.00    inference(cnf_transformation,[],[f31])).
% 2.74/1.00  
% 2.74/1.00  cnf(c_29,negated_conjecture,
% 2.74/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.74/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_699,negated_conjecture,
% 2.74/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_29]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1228,plain,
% 2.74/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_699]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_23,plain,
% 2.74/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.74/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_34,negated_conjecture,
% 2.74/1.00      ( l1_struct_0(sK0) ),
% 2.74/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_393,plain,
% 2.74/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.74/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_394,plain,
% 2.74/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.74/1.00      inference(unflattening,[status(thm)],[c_393]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_695,plain,
% 2.74/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_394]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_32,negated_conjecture,
% 2.74/1.00      ( l1_struct_0(sK1) ),
% 2.74/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_388,plain,
% 2.74/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.74/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_389,plain,
% 2.74/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.74/1.00      inference(unflattening,[status(thm)],[c_388]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_696,plain,
% 2.74/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_389]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1254,plain,
% 2.74/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.74/1.00      inference(light_normalisation,[status(thm)],[c_1228,c_695,c_696]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_15,plain,
% 2.74/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/1.00      | v1_partfun1(X0,X1)
% 2.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.00      | v1_xboole_0(X2)
% 2.74/1.00      | ~ v1_funct_1(X0) ),
% 2.74/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_24,plain,
% 2.74/1.00      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 2.74/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_33,negated_conjecture,
% 2.74/1.00      ( ~ v2_struct_0(sK1) ),
% 2.74/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_375,plain,
% 2.74/1.00      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 2.74/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_376,plain,
% 2.74/1.00      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.74/1.00      inference(unflattening,[status(thm)],[c_375]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_47,plain,
% 2.74/1.00      ( v2_struct_0(sK1)
% 2.74/1.00      | ~ l1_struct_0(sK1)
% 2.74/1.00      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_378,plain,
% 2.74/1.00      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.74/1.00      inference(global_propositional_subsumption,
% 2.74/1.00                [status(thm)],
% 2.74/1.00                [c_376,c_33,c_32,c_47]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_400,plain,
% 2.74/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/1.00      | v1_partfun1(X0,X1)
% 2.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.00      | ~ v1_funct_1(X0)
% 2.74/1.00      | k2_struct_0(sK1) != X2 ),
% 2.74/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_378]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_401,plain,
% 2.74/1.00      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 2.74/1.00      | v1_partfun1(X0,X1)
% 2.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.74/1.00      | ~ v1_funct_1(X0) ),
% 2.74/1.00      inference(unflattening,[status(thm)],[c_400]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_18,plain,
% 2.74/1.00      ( ~ v1_partfun1(X0,X1)
% 2.74/1.00      | ~ v4_relat_1(X0,X1)
% 2.74/1.00      | ~ v1_relat_1(X0)
% 2.74/1.00      | k1_relat_1(X0) = X1 ),
% 2.74/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_497,plain,
% 2.74/1.00      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 2.74/1.00      | ~ v4_relat_1(X0,X1)
% 2.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.74/1.00      | ~ v1_funct_1(X0)
% 2.74/1.00      | ~ v1_relat_1(X0)
% 2.74/1.00      | k1_relat_1(X0) = X1 ),
% 2.74/1.00      inference(resolution,[status(thm)],[c_401,c_18]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_13,plain,
% 2.74/1.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.74/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_513,plain,
% 2.74/1.00      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 2.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.74/1.00      | ~ v1_funct_1(X0)
% 2.74/1.00      | ~ v1_relat_1(X0)
% 2.74/1.00      | k1_relat_1(X0) = X1 ),
% 2.74/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_497,c_13]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_693,plain,
% 2.74/1.00      ( ~ v1_funct_2(X0_53,X0_54,k2_struct_0(sK1))
% 2.74/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_struct_0(sK1))))
% 2.74/1.00      | ~ v1_funct_1(X0_53)
% 2.74/1.00      | ~ v1_relat_1(X0_53)
% 2.74/1.00      | k1_relat_1(X0_53) = X0_54 ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_513]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1233,plain,
% 2.74/1.00      ( k1_relat_1(X0_53) = X0_54
% 2.74/1.00      | v1_funct_2(X0_53,X0_54,k2_struct_0(sK1)) != iProver_top
% 2.74/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_struct_0(sK1)))) != iProver_top
% 2.74/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.74/1.00      | v1_relat_1(X0_53) != iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1809,plain,
% 2.74/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.74/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.74/1.00      | v1_funct_1(sK2) != iProver_top
% 2.74/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_1254,c_1233]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_31,negated_conjecture,
% 2.74/1.00      ( v1_funct_1(sK2) ),
% 2.74/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_38,plain,
% 2.74/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_40,plain,
% 2.74/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_30,negated_conjecture,
% 2.74/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.74/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_698,negated_conjecture,
% 2.74/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_30]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1229,plain,
% 2.74/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_698]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1248,plain,
% 2.74/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.74/1.00      inference(light_normalisation,[status(thm)],[c_1229,c_695,c_696]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_0,plain,
% 2.74/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.74/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_719,plain,
% 2.74/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 2.74/1.00      | ~ v1_relat_1(X1_53)
% 2.74/1.00      | v1_relat_1(X0_53) ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1506,plain,
% 2.74/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.74/1.00      | v1_relat_1(X0_53)
% 2.74/1.00      | ~ v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_719]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1701,plain,
% 2.74/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.74/1.00      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.74/1.00      | v1_relat_1(sK2) ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_1506]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1702,plain,
% 2.74/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.74/1.00      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.74/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1701]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1,plain,
% 2.74/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.74/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_718,plain,
% 2.74/1.00      ( v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1739,plain,
% 2.74/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_718]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1740,plain,
% 2.74/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_1739]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1867,plain,
% 2.74/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.74/1.00      inference(global_propositional_subsumption,
% 2.74/1.00                [status(thm)],
% 2.74/1.00                [c_1809,c_38,c_40,c_1248,c_1702,c_1740]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1871,plain,
% 2.74/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
% 2.74/1.00      inference(demodulation,[status(thm)],[c_1867,c_1254]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_14,plain,
% 2.74/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.74/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_706,plain,
% 2.74/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.74/1.00      | k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53) ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1222,plain,
% 2.74/1.00      ( k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53)
% 2.74/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2066,plain,
% 2.74/1.00      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_1871,c_1222]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_28,negated_conjecture,
% 2.74/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.74/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_700,negated_conjecture,
% 2.74/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_28]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1251,plain,
% 2.74/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.74/1.00      inference(light_normalisation,[status(thm)],[c_700,c_695,c_696]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1873,plain,
% 2.74/1.00      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.74/1.00      inference(demodulation,[status(thm)],[c_1867,c_1251]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2226,plain,
% 2.74/1.00      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.74/1.00      inference(demodulation,[status(thm)],[c_2066,c_1873]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2265,plain,
% 2.74/1.00      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.74/1.00      inference(demodulation,[status(thm)],[c_2226,c_2066]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_25,plain,
% 2.74/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.00      | ~ v2_funct_1(X0)
% 2.74/1.00      | ~ v1_funct_1(X0)
% 2.74/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.74/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.74/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_702,plain,
% 2.74/1.00      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 2.74/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.74/1.00      | ~ v2_funct_1(X0_53)
% 2.74/1.00      | ~ v1_funct_1(X0_53)
% 2.74/1.00      | k2_relset_1(X0_54,X1_54,X0_53) != X1_54
% 2.74/1.00      | k2_tops_2(X0_54,X1_54,X0_53) = k2_funct_1(X0_53) ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_25]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1226,plain,
% 2.74/1.00      ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
% 2.74/1.00      | k2_tops_2(X0_54,X1_54,X0_53) = k2_funct_1(X0_53)
% 2.74/1.00      | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 2.74/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.74/1.00      | v2_funct_1(X0_53) != iProver_top
% 2.74/1.00      | v1_funct_1(X0_53) != iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_702]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_3363,plain,
% 2.74/1.00      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.74/1.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.74/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.74/1.00      | v2_funct_1(sK2) != iProver_top
% 2.74/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_2265,c_1226]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_27,negated_conjecture,
% 2.74/1.00      ( v2_funct_1(sK2) ),
% 2.74/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_41,plain,
% 2.74/1.00      ( v2_funct_1(sK2) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2266,plain,
% 2.74/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.74/1.00      inference(demodulation,[status(thm)],[c_2226,c_1871]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1872,plain,
% 2.74/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) = iProver_top ),
% 2.74/1.00      inference(demodulation,[status(thm)],[c_1867,c_1248]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2267,plain,
% 2.74/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.74/1.00      inference(demodulation,[status(thm)],[c_2226,c_1872]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_4592,plain,
% 2.74/1.00      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.74/1.00      inference(global_propositional_subsumption,
% 2.74/1.00                [status(thm)],
% 2.74/1.00                [c_3363,c_38,c_41,c_2266,c_2267]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_19,plain,
% 2.74/1.00      ( r2_funct_2(X0,X1,X2,X2)
% 2.74/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.74/1.00      | ~ v1_funct_2(X3,X0,X1)
% 2.74/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/1.00      | ~ v1_funct_1(X2)
% 2.74/1.00      | ~ v1_funct_1(X3) ),
% 2.74/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_26,negated_conjecture,
% 2.74/1.00      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.74/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_423,plain,
% 2.74/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/1.00      | ~ v1_funct_2(X3,X1,X2)
% 2.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.00      | ~ v1_funct_1(X0)
% 2.74/1.00      | ~ v1_funct_1(X3)
% 2.74/1.00      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 2.74/1.00      | u1_struct_0(sK1) != X2
% 2.74/1.00      | u1_struct_0(sK0) != X1
% 2.74/1.00      | sK2 != X0 ),
% 2.74/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_424,plain,
% 2.74/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.74/1.00      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.74/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.74/1.00      | ~ v1_funct_1(X0)
% 2.74/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.74/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.74/1.00      inference(unflattening,[status(thm)],[c_423]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_694,plain,
% 2.74/1.00      ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.74/1.00      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.74/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.74/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.74/1.00      | ~ v1_funct_1(X0_53)
% 2.74/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.74/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_424]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_721,plain,
% 2.74/1.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.74/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.74/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.74/1.00      | sP0_iProver_split
% 2.74/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.74/1.00      inference(splitting,
% 2.74/1.00                [splitting(split),new_symbols(definition,[])],
% 2.74/1.00                [c_694]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1231,plain,
% 2.74/1.00      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.74/1.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.74/1.00      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.74/1.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 2.74/1.00      | sP0_iProver_split = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_721]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1422,plain,
% 2.74/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.74/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.74/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.74/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 2.74/1.00      | sP0_iProver_split = iProver_top ),
% 2.74/1.00      inference(light_normalisation,[status(thm)],[c_1231,c_695,c_696]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_720,plain,
% 2.74/1.00      ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.74/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.74/1.00      | ~ v1_funct_1(X0_53)
% 2.74/1.00      | ~ sP0_iProver_split ),
% 2.74/1.00      inference(splitting,
% 2.74/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.74/1.00                [c_694]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1232,plain,
% 2.74/1.00      ( v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.74/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.74/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.74/1.00      | sP0_iProver_split != iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_720]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1311,plain,
% 2.74/1.00      ( v1_funct_2(X0_53,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.74/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.74/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.74/1.00      | sP0_iProver_split != iProver_top ),
% 2.74/1.00      inference(light_normalisation,[status(thm)],[c_1232,c_695,c_696]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1428,plain,
% 2.74/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.74/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.74/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.74/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.74/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1422,c_1311]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1870,plain,
% 2.74/1.00      ( k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) != sK2
% 2.74/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
% 2.74/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
% 2.74/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.74/1.00      inference(demodulation,[status(thm)],[c_1867,c_1428]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_3812,plain,
% 2.74/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
% 2.74/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.74/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.74/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.74/1.00      inference(light_normalisation,[status(thm)],[c_1870,c_2226]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_4595,plain,
% 2.74/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 2.74/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.74/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.74/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.74/1.00      inference(demodulation,[status(thm)],[c_4592,c_3812]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2,plain,
% 2.74/1.00      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 2.74/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_717,plain,
% 2.74/1.00      ( ~ v1_funct_1(X0_53)
% 2.74/1.00      | v1_funct_1(k2_funct_1(X0_53))
% 2.74/1.00      | ~ v1_relat_1(X0_53) ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_762,plain,
% 2.74/1.00      ( v1_funct_1(X0_53) != iProver_top
% 2.74/1.00      | v1_funct_1(k2_funct_1(X0_53)) = iProver_top
% 2.74/1.00      | v1_relat_1(X0_53) != iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_764,plain,
% 2.74/1.00      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.74/1.00      | v1_funct_1(sK2) != iProver_top
% 2.74/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_762]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_21,plain,
% 2.74/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/1.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.00      | ~ v2_funct_1(X0)
% 2.74/1.00      | ~ v1_funct_1(X0)
% 2.74/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.74/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_704,plain,
% 2.74/1.00      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 2.74/1.00      | v1_funct_2(k2_funct_1(X0_53),X1_54,X0_54)
% 2.74/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.74/1.00      | ~ v2_funct_1(X0_53)
% 2.74/1.00      | ~ v1_funct_1(X0_53)
% 2.74/1.00      | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1224,plain,
% 2.74/1.00      ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
% 2.74/1.00      | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 2.74/1.00      | v1_funct_2(k2_funct_1(X0_53),X1_54,X0_54) = iProver_top
% 2.74/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.74/1.00      | v2_funct_1(X0_53) != iProver_top
% 2.74/1.00      | v1_funct_1(X0_53) != iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2728,plain,
% 2.74/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 2.74/1.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.74/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.74/1.00      | v2_funct_1(sK2) != iProver_top
% 2.74/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_2265,c_1224]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_701,negated_conjecture,
% 2.74/1.00      ( v2_funct_1(sK2) ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_27]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1227,plain,
% 2.74/1.00      ( v2_funct_1(sK2) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_9,plain,
% 2.74/1.00      ( ~ v2_funct_1(X0)
% 2.74/1.00      | ~ v1_funct_1(X0)
% 2.74/1.00      | ~ v1_relat_1(X0)
% 2.74/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.74/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_710,plain,
% 2.74/1.00      ( ~ v2_funct_1(X0_53)
% 2.74/1.00      | ~ v1_funct_1(X0_53)
% 2.74/1.00      | ~ v1_relat_1(X0_53)
% 2.74/1.00      | k1_relat_1(k2_funct_1(X0_53)) = k2_relat_1(X0_53) ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1218,plain,
% 2.74/1.00      ( k1_relat_1(k2_funct_1(X0_53)) = k2_relat_1(X0_53)
% 2.74/1.00      | v2_funct_1(X0_53) != iProver_top
% 2.74/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.74/1.00      | v1_relat_1(X0_53) != iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_710]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2122,plain,
% 2.74/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.74/1.00      | v1_funct_1(sK2) != iProver_top
% 2.74/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_1227,c_1218]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_780,plain,
% 2.74/1.00      ( ~ v2_funct_1(sK2)
% 2.74/1.00      | ~ v1_funct_1(sK2)
% 2.74/1.00      | ~ v1_relat_1(sK2)
% 2.74/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_710]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2203,plain,
% 2.74/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.74/1.00      inference(global_propositional_subsumption,
% 2.74/1.00                [status(thm)],
% 2.74/1.00                [c_2122,c_31,c_29,c_27,c_780,c_1701,c_1739]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_6,plain,
% 2.74/1.00      ( v2_funct_1(X0)
% 2.74/1.00      | ~ v2_funct_1(k5_relat_1(X1,X0))
% 2.74/1.00      | ~ v1_funct_1(X0)
% 2.74/1.00      | ~ v1_funct_1(X1)
% 2.74/1.00      | ~ v1_relat_1(X0)
% 2.74/1.00      | ~ v1_relat_1(X1)
% 2.74/1.00      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 2.74/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_713,plain,
% 2.74/1.00      ( v2_funct_1(X0_53)
% 2.74/1.00      | ~ v2_funct_1(k5_relat_1(X1_53,X0_53))
% 2.74/1.00      | ~ v1_funct_1(X0_53)
% 2.74/1.00      | ~ v1_funct_1(X1_53)
% 2.74/1.00      | ~ v1_relat_1(X0_53)
% 2.74/1.00      | ~ v1_relat_1(X1_53)
% 2.74/1.00      | k1_relat_1(X0_53) != k2_relat_1(X1_53) ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1215,plain,
% 2.74/1.00      ( k1_relat_1(X0_53) != k2_relat_1(X1_53)
% 2.74/1.00      | v2_funct_1(X0_53) = iProver_top
% 2.74/1.00      | v2_funct_1(k5_relat_1(X1_53,X0_53)) != iProver_top
% 2.74/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.74/1.00      | v1_funct_1(X1_53) != iProver_top
% 2.74/1.00      | v1_relat_1(X0_53) != iProver_top
% 2.74/1.00      | v1_relat_1(X1_53) != iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_713]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2442,plain,
% 2.74/1.00      ( k2_relat_1(X0_53) != k2_relat_1(sK2)
% 2.74/1.00      | v2_funct_1(k5_relat_1(X0_53,k2_funct_1(sK2))) != iProver_top
% 2.74/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.74/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.74/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.74/1.00      | v1_relat_1(X0_53) != iProver_top
% 2.74/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_2203,c_1215]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_3,plain,
% 2.74/1.00      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 2.74/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_716,plain,
% 2.74/1.00      ( ~ v1_funct_1(X0_53)
% 2.74/1.00      | ~ v1_relat_1(X0_53)
% 2.74/1.00      | v1_relat_1(k2_funct_1(X0_53)) ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_765,plain,
% 2.74/1.00      ( v1_funct_1(X0_53) != iProver_top
% 2.74/1.00      | v1_relat_1(X0_53) != iProver_top
% 2.74/1.00      | v1_relat_1(k2_funct_1(X0_53)) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_767,plain,
% 2.74/1.00      ( v1_funct_1(sK2) != iProver_top
% 2.74/1.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 2.74/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_765]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2904,plain,
% 2.74/1.00      ( v1_relat_1(X0_53) != iProver_top
% 2.74/1.00      | k2_relat_1(X0_53) != k2_relat_1(sK2)
% 2.74/1.00      | v2_funct_1(k5_relat_1(X0_53,k2_funct_1(sK2))) != iProver_top
% 2.74/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.74/1.00      | v1_funct_1(X0_53) != iProver_top ),
% 2.74/1.00      inference(global_propositional_subsumption,
% 2.74/1.00                [status(thm)],
% 2.74/1.00                [c_2442,c_38,c_40,c_764,c_767,c_1702,c_1740]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2905,plain,
% 2.74/1.00      ( k2_relat_1(X0_53) != k2_relat_1(sK2)
% 2.74/1.00      | v2_funct_1(k5_relat_1(X0_53,k2_funct_1(sK2))) != iProver_top
% 2.74/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.74/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.74/1.00      | v1_relat_1(X0_53) != iProver_top ),
% 2.74/1.00      inference(renaming,[status(thm)],[c_2904]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2916,plain,
% 2.74/1.00      ( v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top
% 2.74/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.74/1.00      | v1_funct_1(sK2) != iProver_top
% 2.74/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.74/1.00      inference(equality_resolution,[status(thm)],[c_2905]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_11,plain,
% 2.74/1.00      ( ~ v2_funct_1(X0)
% 2.74/1.00      | ~ v1_funct_1(X0)
% 2.74/1.00      | ~ v1_relat_1(X0)
% 2.74/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
% 2.74/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_708,plain,
% 2.74/1.00      ( ~ v2_funct_1(X0_53)
% 2.74/1.00      | ~ v1_funct_1(X0_53)
% 2.74/1.00      | ~ v1_relat_1(X0_53)
% 2.74/1.00      | k5_relat_1(X0_53,k2_funct_1(X0_53)) = k6_relat_1(k1_relat_1(X0_53)) ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1220,plain,
% 2.74/1.00      ( k5_relat_1(X0_53,k2_funct_1(X0_53)) = k6_relat_1(k1_relat_1(X0_53))
% 2.74/1.00      | v2_funct_1(X0_53) != iProver_top
% 2.74/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.74/1.00      | v1_relat_1(X0_53) != iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_708]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2481,plain,
% 2.74/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
% 2.74/1.00      | v1_funct_1(sK2) != iProver_top
% 2.74/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_1227,c_1220]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_786,plain,
% 2.74/1.00      ( ~ v2_funct_1(sK2)
% 2.74/1.00      | ~ v1_funct_1(sK2)
% 2.74/1.00      | ~ v1_relat_1(sK2)
% 2.74/1.00      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_708]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2731,plain,
% 2.74/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
% 2.74/1.00      inference(global_propositional_subsumption,
% 2.74/1.00                [status(thm)],
% 2.74/1.00                [c_2481,c_31,c_29,c_27,c_786,c_1701,c_1739]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2921,plain,
% 2.74/1.00      ( v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
% 2.74/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.74/1.00      | v1_funct_1(sK2) != iProver_top
% 2.74/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.74/1.00      inference(light_normalisation,[status(thm)],[c_2916,c_2731]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2997,plain,
% 2.74/1.00      ( v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
% 2.74/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.74/1.00      inference(global_propositional_subsumption,
% 2.74/1.00                [status(thm)],
% 2.74/1.00                [c_2921,c_38,c_40,c_1702,c_1740]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_4,plain,
% 2.74/1.00      ( v2_funct_1(k6_relat_1(X0)) ),
% 2.74/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_715,plain,
% 2.74/1.00      ( v2_funct_1(k6_relat_1(X0_54)) ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1213,plain,
% 2.74/1.00      ( v2_funct_1(k6_relat_1(X0_54)) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_715]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_3003,plain,
% 2.74/1.00      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.74/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2997,c_1213]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_20,plain,
% 2.74/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/1.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.74/1.00      | ~ v2_funct_1(X0)
% 2.74/1.00      | ~ v1_funct_1(X0)
% 2.74/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.74/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_705,plain,
% 2.74/1.00      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 2.74/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.74/1.00      | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54)))
% 2.74/1.00      | ~ v2_funct_1(X0_53)
% 2.74/1.00      | ~ v1_funct_1(X0_53)
% 2.74/1.00      | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1223,plain,
% 2.74/1.00      ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
% 2.74/1.00      | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 2.74/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.74/1.00      | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54))) = iProver_top
% 2.74/1.00      | v2_funct_1(X0_53) != iProver_top
% 2.74/1.00      | v1_funct_1(X0_53) != iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_705]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_3372,plain,
% 2.74/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.74/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.74/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.74/1.00      | v2_funct_1(sK2) != iProver_top
% 2.74/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_2265,c_1223]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_4670,plain,
% 2.74/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 2.74/1.00      inference(global_propositional_subsumption,
% 2.74/1.00                [status(thm)],
% 2.74/1.00                [c_3372,c_38,c_41,c_2266,c_2267]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_4676,plain,
% 2.74/1.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_4670,c_1222]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_8,plain,
% 2.74/1.00      ( ~ v2_funct_1(X0)
% 2.74/1.00      | ~ v1_funct_1(X0)
% 2.74/1.00      | ~ v1_relat_1(X0)
% 2.74/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.74/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_711,plain,
% 2.74/1.00      ( ~ v2_funct_1(X0_53)
% 2.74/1.00      | ~ v1_funct_1(X0_53)
% 2.74/1.00      | ~ v1_relat_1(X0_53)
% 2.74/1.00      | k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53) ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1217,plain,
% 2.74/1.00      ( k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53)
% 2.74/1.00      | v2_funct_1(X0_53) != iProver_top
% 2.74/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.74/1.00      | v1_relat_1(X0_53) != iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_711]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2072,plain,
% 2.74/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.74/1.00      | v1_funct_1(sK2) != iProver_top
% 2.74/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_1227,c_1217]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_777,plain,
% 2.74/1.00      ( ~ v2_funct_1(sK2)
% 2.74/1.00      | ~ v1_funct_1(sK2)
% 2.74/1.00      | ~ v1_relat_1(sK2)
% 2.74/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.74/1.00      inference(instantiation,[status(thm)],[c_711]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_2199,plain,
% 2.74/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.74/1.00      inference(global_propositional_subsumption,
% 2.74/1.00                [status(thm)],
% 2.74/1.00                [c_2072,c_31,c_29,c_27,c_777,c_1701,c_1739]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_4683,plain,
% 2.74/1.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.74/1.00      inference(light_normalisation,[status(thm)],[c_4676,c_2199]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_4760,plain,
% 2.74/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.74/1.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.74/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.74/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.74/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_4683,c_1226]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_12,plain,
% 2.74/1.00      ( ~ v2_funct_1(X0)
% 2.74/1.00      | ~ v1_funct_1(X0)
% 2.74/1.00      | ~ v1_funct_1(X1)
% 2.74/1.00      | ~ v1_relat_1(X0)
% 2.74/1.00      | ~ v1_relat_1(X1)
% 2.74/1.00      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
% 2.74/1.00      | k1_relat_1(X0) != k2_relat_1(X1)
% 2.74/1.00      | k2_funct_1(X0) = X1 ),
% 2.74/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_707,plain,
% 2.74/1.00      ( ~ v2_funct_1(X0_53)
% 2.74/1.00      | ~ v1_funct_1(X0_53)
% 2.74/1.00      | ~ v1_funct_1(X1_53)
% 2.74/1.00      | ~ v1_relat_1(X0_53)
% 2.74/1.00      | ~ v1_relat_1(X1_53)
% 2.74/1.00      | k1_relat_1(X0_53) != k2_relat_1(X1_53)
% 2.74/1.00      | k5_relat_1(X1_53,X0_53) != k6_relat_1(k2_relat_1(X0_53))
% 2.74/1.00      | k2_funct_1(X0_53) = X1_53 ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1221,plain,
% 2.74/1.00      ( k1_relat_1(X0_53) != k2_relat_1(X1_53)
% 2.74/1.00      | k5_relat_1(X1_53,X0_53) != k6_relat_1(k2_relat_1(X0_53))
% 2.74/1.00      | k2_funct_1(X0_53) = X1_53
% 2.74/1.00      | v2_funct_1(X0_53) != iProver_top
% 2.74/1.00      | v1_funct_1(X0_53) != iProver_top
% 2.74/1.00      | v1_funct_1(X1_53) != iProver_top
% 2.74/1.00      | v1_relat_1(X0_53) != iProver_top
% 2.74/1.00      | v1_relat_1(X1_53) != iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_707]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_3252,plain,
% 2.74/1.00      ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 2.74/1.00      | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k6_relat_1(k1_relat_1(sK2))
% 2.74/1.00      | k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.74/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.74/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.74/1.00      | v1_funct_1(sK2) != iProver_top
% 2.74/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.74/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.74/1.00      inference(superposition,[status(thm)],[c_2731,c_1221]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_3261,plain,
% 2.74/1.00      ( k2_relat_1(sK2) != k2_relat_1(sK2)
% 2.74/1.00      | k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
% 2.74/1.00      | k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.74/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.74/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.74/1.00      | v1_funct_1(sK2) != iProver_top
% 2.74/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.74/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.74/1.00      inference(light_normalisation,[status(thm)],[c_3252,c_2199,c_2203]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_3262,plain,
% 2.74/1.00      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.74/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.74/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.74/1.00      | v1_funct_1(sK2) != iProver_top
% 2.74/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.74/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.74/1.00      inference(equality_resolution_simp,[status(thm)],[c_3261]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_4402,plain,
% 2.74/1.00      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.74/1.00      inference(global_propositional_subsumption,
% 2.74/1.00                [status(thm)],
% 2.74/1.00                [c_3262,c_38,c_40,c_764,c_767,c_1702,c_1740,c_3003]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_4773,plain,
% 2.74/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 2.74/1.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.74/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.74/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.74/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.74/1.00      inference(light_normalisation,[status(thm)],[c_4760,c_4402]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_4852,plain,
% 2.74/1.00      ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.74/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.74/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.74/1.00      inference(global_propositional_subsumption,
% 2.74/1.00                [status(thm)],
% 2.74/1.00                [c_4595,c_38,c_40,c_41,c_764,c_1702,c_1740,c_2266,c_2267,
% 2.74/1.00                 c_2728,c_3003,c_3372,c_4773]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_4787,plain,
% 2.74/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.74/1.00      inference(global_propositional_subsumption,
% 2.74/1.00                [status(thm)],
% 2.74/1.00                [c_4773,c_38,c_40,c_41,c_764,c_1702,c_1740,c_2266,c_2267,
% 2.74/1.00                 c_2728,c_3003,c_3372]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_4856,plain,
% 2.74/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.74/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.74/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.74/1.00      inference(light_normalisation,[status(thm)],[c_4852,c_4787]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_697,negated_conjecture,
% 2.74/1.00      ( v1_funct_1(sK2) ),
% 2.74/1.00      inference(subtyping,[status(esa)],[c_31]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_1230,plain,
% 2.74/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.74/1.00      inference(predicate_to_equality,[status(thm)],[c_697]) ).
% 2.74/1.00  
% 2.74/1.00  cnf(c_4860,plain,
% 2.74/1.00      ( $false ),
% 2.74/1.00      inference(forward_subsumption_resolution,
% 2.74/1.00                [status(thm)],
% 2.74/1.00                [c_4856,c_1230,c_2266,c_2267]) ).
% 2.74/1.00  
% 2.74/1.00  
% 2.74/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.74/1.00  
% 2.74/1.00  ------                               Statistics
% 2.74/1.00  
% 2.74/1.00  ------ General
% 2.74/1.00  
% 2.74/1.00  abstr_ref_over_cycles:                  0
% 2.74/1.00  abstr_ref_under_cycles:                 0
% 2.74/1.00  gc_basic_clause_elim:                   0
% 2.74/1.00  forced_gc_time:                         0
% 2.74/1.00  parsing_time:                           0.01
% 2.74/1.00  unif_index_cands_time:                  0.
% 2.74/1.00  unif_index_add_time:                    0.
% 2.74/1.00  orderings_time:                         0.
% 2.74/1.00  out_proof_time:                         0.013
% 2.74/1.00  total_time:                             0.254
% 2.74/1.00  num_of_symbols:                         61
% 2.74/1.00  num_of_terms:                           4414
% 2.74/1.00  
% 2.74/1.00  ------ Preprocessing
% 2.74/1.00  
% 2.74/1.00  num_of_splits:                          1
% 2.74/1.00  num_of_split_atoms:                     1
% 2.74/1.00  num_of_reused_defs:                     0
% 2.74/1.00  num_eq_ax_congr_red:                    7
% 2.74/1.00  num_of_sem_filtered_clauses:            2
% 2.74/1.00  num_of_subtypes:                        4
% 2.74/1.00  monotx_restored_types:                  1
% 2.74/1.00  sat_num_of_epr_types:                   0
% 2.74/1.00  sat_num_of_non_cyclic_types:            0
% 2.74/1.00  sat_guarded_non_collapsed_types:        1
% 2.74/1.00  num_pure_diseq_elim:                    0
% 2.74/1.00  simp_replaced_by:                       0
% 2.74/1.00  res_preprocessed:                       153
% 2.74/1.00  prep_upred:                             0
% 2.74/1.00  prep_unflattend:                        11
% 2.74/1.00  smt_new_axioms:                         0
% 2.74/1.00  pred_elim_cands:                        5
% 2.74/1.00  pred_elim:                              6
% 2.74/1.00  pred_elim_cl:                           7
% 2.74/1.00  pred_elim_cycles:                       9
% 2.74/1.00  merged_defs:                            0
% 2.74/1.00  merged_defs_ncl:                        0
% 2.74/1.00  bin_hyper_res:                          0
% 2.74/1.00  prep_cycles:                            4
% 2.74/1.00  pred_elim_time:                         0.008
% 2.74/1.00  splitting_time:                         0.
% 2.74/1.00  sem_filter_time:                        0.
% 2.74/1.00  monotx_time:                            0.001
% 2.74/1.00  subtype_inf_time:                       0.002
% 2.74/1.00  
% 2.74/1.00  ------ Problem properties
% 2.74/1.00  
% 2.74/1.00  clauses:                                28
% 2.74/1.00  conjectures:                            5
% 2.74/1.00  epr:                                    2
% 2.74/1.00  horn:                                   28
% 2.74/1.00  ground:                                 8
% 2.74/1.00  unary:                                  10
% 2.74/1.00  binary:                                 1
% 2.74/1.00  lits:                                   97
% 2.74/1.00  lits_eq:                                20
% 2.74/1.00  fd_pure:                                0
% 2.74/1.00  fd_pseudo:                              0
% 2.74/1.00  fd_cond:                                0
% 2.74/1.00  fd_pseudo_cond:                         2
% 2.74/1.00  ac_symbols:                             0
% 2.74/1.00  
% 2.74/1.00  ------ Propositional Solver
% 2.74/1.00  
% 2.74/1.00  prop_solver_calls:                      29
% 2.74/1.00  prop_fast_solver_calls:                 1453
% 2.74/1.00  smt_solver_calls:                       0
% 2.74/1.00  smt_fast_solver_calls:                  0
% 2.74/1.00  prop_num_of_clauses:                    1647
% 2.74/1.00  prop_preprocess_simplified:             5680
% 2.74/1.00  prop_fo_subsumed:                       109
% 2.74/1.00  prop_solver_time:                       0.
% 2.74/1.00  smt_solver_time:                        0.
% 2.74/1.00  smt_fast_solver_time:                   0.
% 2.74/1.00  prop_fast_solver_time:                  0.
% 2.74/1.00  prop_unsat_core_time:                   0.
% 2.74/1.00  
% 2.74/1.00  ------ QBF
% 2.74/1.00  
% 2.74/1.00  qbf_q_res:                              0
% 2.74/1.00  qbf_num_tautologies:                    0
% 2.74/1.00  qbf_prep_cycles:                        0
% 2.74/1.00  
% 2.74/1.00  ------ BMC1
% 2.74/1.00  
% 2.74/1.00  bmc1_current_bound:                     -1
% 2.74/1.00  bmc1_last_solved_bound:                 -1
% 2.74/1.00  bmc1_unsat_core_size:                   -1
% 2.74/1.00  bmc1_unsat_core_parents_size:           -1
% 2.74/1.00  bmc1_merge_next_fun:                    0
% 2.74/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.74/1.00  
% 2.74/1.00  ------ Instantiation
% 2.74/1.00  
% 2.74/1.00  inst_num_of_clauses:                    548
% 2.74/1.00  inst_num_in_passive:                    29
% 2.74/1.00  inst_num_in_active:                     355
% 2.74/1.00  inst_num_in_unprocessed:                164
% 2.74/1.00  inst_num_of_loops:                      390
% 2.74/1.00  inst_num_of_learning_restarts:          0
% 2.74/1.00  inst_num_moves_active_passive:          31
% 2.74/1.00  inst_lit_activity:                      0
% 2.74/1.00  inst_lit_activity_moves:                0
% 2.74/1.00  inst_num_tautologies:                   0
% 2.74/1.00  inst_num_prop_implied:                  0
% 2.74/1.00  inst_num_existing_simplified:           0
% 2.74/1.00  inst_num_eq_res_simplified:             0
% 2.74/1.00  inst_num_child_elim:                    0
% 2.74/1.00  inst_num_of_dismatching_blockings:      203
% 2.74/1.00  inst_num_of_non_proper_insts:           654
% 2.74/1.00  inst_num_of_duplicates:                 0
% 2.74/1.00  inst_inst_num_from_inst_to_res:         0
% 2.74/1.00  inst_dismatching_checking_time:         0.
% 2.74/1.00  
% 2.74/1.00  ------ Resolution
% 2.74/1.00  
% 2.74/1.00  res_num_of_clauses:                     0
% 2.74/1.00  res_num_in_passive:                     0
% 2.74/1.00  res_num_in_active:                      0
% 2.74/1.00  res_num_of_loops:                       157
% 2.74/1.00  res_forward_subset_subsumed:            95
% 2.74/1.00  res_backward_subset_subsumed:           0
% 2.74/1.00  res_forward_subsumed:                   0
% 2.74/1.00  res_backward_subsumed:                  0
% 2.74/1.00  res_forward_subsumption_resolution:     1
% 2.74/1.00  res_backward_subsumption_resolution:    0
% 2.74/1.00  res_clause_to_clause_subsumption:       127
% 2.74/1.00  res_orphan_elimination:                 0
% 2.74/1.00  res_tautology_del:                      98
% 2.74/1.00  res_num_eq_res_simplified:              0
% 2.74/1.00  res_num_sel_changes:                    0
% 2.74/1.00  res_moves_from_active_to_pass:          0
% 2.74/1.00  
% 2.74/1.00  ------ Superposition
% 2.74/1.00  
% 2.74/1.00  sup_time_total:                         0.
% 2.74/1.00  sup_time_generating:                    0.
% 2.74/1.00  sup_time_sim_full:                      0.
% 2.74/1.00  sup_time_sim_immed:                     0.
% 2.74/1.00  
% 2.74/1.00  sup_num_of_clauses:                     60
% 2.74/1.00  sup_num_in_active:                      53
% 2.74/1.00  sup_num_in_passive:                     7
% 2.74/1.00  sup_num_of_loops:                       77
% 2.74/1.00  sup_fw_superposition:                   31
% 2.74/1.00  sup_bw_superposition:                   37
% 2.74/1.00  sup_immediate_simplified:               29
% 2.74/1.01  sup_given_eliminated:                   0
% 2.74/1.01  comparisons_done:                       0
% 2.74/1.01  comparisons_avoided:                    0
% 2.74/1.01  
% 2.74/1.01  ------ Simplifications
% 2.74/1.01  
% 2.74/1.01  
% 2.74/1.01  sim_fw_subset_subsumed:                 12
% 2.74/1.01  sim_bw_subset_subsumed:                 4
% 2.74/1.01  sim_fw_subsumed:                        3
% 2.74/1.01  sim_bw_subsumed:                        0
% 2.74/1.01  sim_fw_subsumption_res:                 8
% 2.74/1.01  sim_bw_subsumption_res:                 0
% 2.74/1.01  sim_tautology_del:                      0
% 2.74/1.01  sim_eq_tautology_del:                   9
% 2.74/1.01  sim_eq_res_simp:                        2
% 2.74/1.01  sim_fw_demodulated:                     0
% 2.74/1.01  sim_bw_demodulated:                     21
% 2.74/1.01  sim_light_normalised:                   36
% 2.74/1.01  sim_joinable_taut:                      0
% 2.74/1.01  sim_joinable_simp:                      0
% 2.74/1.01  sim_ac_normalised:                      0
% 2.74/1.01  sim_smt_subsumption:                    0
% 2.74/1.01  
%------------------------------------------------------------------------------
