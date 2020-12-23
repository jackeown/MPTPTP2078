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
% DateTime   : Thu Dec  3 12:17:37 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :  232 (8508 expanded)
%              Number of clauses        :  148 (2655 expanded)
%              Number of leaves         :   22 (2361 expanded)
%              Depth                    :   31
%              Number of atoms          :  783 (53240 expanded)
%              Number of equality atoms :  294 (8624 expanded)
%              Maximal formula depth    :   13 (   4 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,
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

fof(f54,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f53,f52,f51])).

fof(f84,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f76,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f81,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f68,plain,(
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
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f69,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f86,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f64,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f38])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f39])).

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
    inference(cnf_transformation,[],[f50])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f72])).

fof(f87,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_687,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1150,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_687])).

cnf(c_21,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_32,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_375,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_376,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_683,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_376])).

cnf(c_30,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_370,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_371,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_684,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_371])).

cnf(c_1172,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1150,c_683,c_684])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_22,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_357,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_358,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_45,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_360,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_358,c_31,c_30,c_45])).

cnf(c_382,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_360])).

cnf(c_383,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_15,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_461,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_383,c_15])).

cnf(c_10,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_477,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_461,c_10])).

cnf(c_681,plain,
    ( ~ v1_funct_2(X0_54,X0_55,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | k1_relat_1(X0_54) = X0_55 ),
    inference(subtyping,[status(esa)],[c_477])).

cnf(c_1154,plain,
    ( k1_relat_1(X0_54) = X0_55
    | v1_funct_2(X0_54,X0_55,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_681])).

cnf(c_1239,plain,
    ( k1_relat_1(X0_54) = X0_55
    | v1_funct_2(X0_54,X0_55,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1154,c_684])).

cnf(c_1452,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_1239])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_686,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1151,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_686])).

cnf(c_1166,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1151,c_683,c_684])).

cnf(c_1316,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1166])).

cnf(c_1453,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1452])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_703,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ v1_relat_1(X1_54)
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1385,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | v1_relat_1(X0_54)
    | ~ v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(c_1506,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1385])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_702,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1530,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_702])).

cnf(c_2223,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1452,c_29,c_27,c_1316,c_1453,c_1506,c_1530])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_694,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1144,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_694])).

cnf(c_1573,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1172,c_1144])).

cnf(c_26,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_688,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1169,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_688,c_683,c_684])).

cnf(c_1627,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1573,c_1169])).

cnf(c_1629,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1627,c_1573])).

cnf(c_2227,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2223,c_1629])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_693,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55)))
    | ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1145,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_2730,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2227,c_1145])).

cnf(c_36,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_39,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1632,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1627,c_1172])).

cnf(c_2226,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2223,c_1632])).

cnf(c_1633,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1627,c_1166])).

cnf(c_2228,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2223,c_1633])).

cnf(c_3811,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2730,c_36,c_39,c_2226,c_2228])).

cnf(c_3818,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3811,c_1144])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_10,c_4])).

cnf(c_682,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_relat_1(X0_54)
    | k7_relat_1(X0_54,X0_55) = X0_54 ),
    inference(subtyping,[status(esa)],[c_494])).

cnf(c_1153,plain,
    ( k7_relat_1(X0_54,X0_55) = X0_54
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_682])).

cnf(c_741,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_702])).

cnf(c_784,plain,
    ( k7_relat_1(X0_54,X0_55) = X0_54
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_682])).

cnf(c_1386,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_relat_1(X0_54) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1385])).

cnf(c_3174,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | k7_relat_1(X0_54,X0_55) = X0_54 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1153,c_741,c_784,c_1386])).

cnf(c_3175,plain,
    ( k7_relat_1(X0_54,X0_55) = X0_54
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3174])).

cnf(c_3816,plain,
    ( k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_3811,c_3175])).

cnf(c_685,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1152,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_685])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_697,plain,
    ( ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | v1_relat_1(k2_funct_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1141,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(k2_funct_1(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_697])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_701,plain,
    ( ~ v1_relat_1(X0_54)
    | k2_relat_1(k7_relat_1(X0_54,X0_55)) = k9_relat_1(X0_54,X0_55) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1137,plain,
    ( k2_relat_1(k7_relat_1(X0_54,X0_55)) = k9_relat_1(X0_54,X0_55)
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_1869,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(X0_54),X0_55)) = k9_relat_1(k2_funct_1(X0_54),X0_55)
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_1141,c_1137])).

cnf(c_3308,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0_55)) = k9_relat_1(k2_funct_1(sK2),X0_55)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1152,c_1869])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_696,plain,
    ( ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | k9_relat_1(k2_funct_1(X0_54),X0_55) = k10_relat_1(X0_54,X0_55) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1142,plain,
    ( k9_relat_1(k2_funct_1(X0_54),X0_55) = k10_relat_1(X0_54,X0_55)
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_696])).

cnf(c_2000,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0_55) = k10_relat_1(sK2,X0_55)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1152,c_1142])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1507,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1506])).

cnf(c_1531,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1530])).

cnf(c_2120,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0_55) = k10_relat_1(sK2,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2000,c_38,c_39,c_1507,c_1531])).

cnf(c_3330,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0_55)) = k10_relat_1(sK2,X0_55)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3308,c_2120])).

cnf(c_3535,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0_55)) = k10_relat_1(sK2,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3330,c_38,c_39,c_1507,c_1531])).

cnf(c_3880,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3816,c_3535])).

cnf(c_1135,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
    | v1_relat_1(X1_54) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_703])).

cnf(c_1488,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_1135])).

cnf(c_1756,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1488,c_38,c_1507,c_1531])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_700,plain,
    ( ~ v1_relat_1(X0_54)
    | k10_relat_1(X0_54,k2_relat_1(X0_54)) = k1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1138,plain,
    ( k10_relat_1(X0_54,k2_relat_1(X0_54)) = k1_relat_1(X0_54)
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_700])).

cnf(c_1762,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1756,c_1138])).

cnf(c_3881,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3880,c_1762])).

cnf(c_4081,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3818,c_3881])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_690,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1148,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54)
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_690])).

cnf(c_4083,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4081,c_1148])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_695,plain,
    ( ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | k2_funct_1(k2_funct_1(X0_54)) = X0_54 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1143,plain,
    ( k2_funct_1(k2_funct_1(X0_54)) = X0_54
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_695])).

cnf(c_1971,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1152,c_1143])).

cnf(c_763,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_695])).

cnf(c_2113,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1971,c_29,c_27,c_25,c_763,c_1506,c_1530])).

cnf(c_4103,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4083,c_2113])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_699,plain,
    ( ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | v2_funct_1(k2_funct_1(X0_54))
    | ~ v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_750,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v2_funct_1(k2_funct_1(X0_54)) = iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_699])).

cnf(c_752,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_698,plain,
    ( ~ v1_funct_1(X0_54)
    | v1_funct_1(k2_funct_1(X0_54))
    | ~ v2_funct_1(X0_54)
    | ~ v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_753,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_funct_1(X0_54)) = iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_698])).

cnf(c_755,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_753])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_692,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1146,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_692])).

cnf(c_2729,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2227,c_1146])).

cnf(c_4414,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4103,c_36,c_38,c_39,c_752,c_755,c_1507,c_1531,c_2226,c_2228,c_2729,c_2730])).

cnf(c_2728,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2227,c_1148])).

cnf(c_2947,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2728,c_36,c_39,c_2226,c_2228])).

cnf(c_16,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_24,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_512,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_513,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_680,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_513])).

cnf(c_1155,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_680])).

cnf(c_1298,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1155,c_683,c_684])).

cnf(c_1630,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1627,c_1298])).

cnf(c_2289,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1630,c_2223])).

cnf(c_2950,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2947,c_2289])).

cnf(c_4417,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4414,c_2950])).

cnf(c_705,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_737,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4417,c_2228,c_2226,c_737,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:53:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.61/1.07  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.07  
% 2.61/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.61/1.07  
% 2.61/1.07  ------  iProver source info
% 2.61/1.07  
% 2.61/1.07  git: date: 2020-06-30 10:37:57 +0100
% 2.61/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.61/1.07  git: non_committed_changes: false
% 2.61/1.07  git: last_make_outside_of_git: false
% 2.61/1.07  
% 2.61/1.07  ------ 
% 2.61/1.07  
% 2.61/1.07  ------ Input Options
% 2.61/1.07  
% 2.61/1.07  --out_options                           all
% 2.61/1.07  --tptp_safe_out                         true
% 2.61/1.07  --problem_path                          ""
% 2.61/1.07  --include_path                          ""
% 2.61/1.07  --clausifier                            res/vclausify_rel
% 2.61/1.07  --clausifier_options                    --mode clausify
% 2.61/1.07  --stdin                                 false
% 2.61/1.07  --stats_out                             all
% 2.61/1.07  
% 2.61/1.07  ------ General Options
% 2.61/1.07  
% 2.61/1.07  --fof                                   false
% 2.61/1.07  --time_out_real                         305.
% 2.61/1.07  --time_out_virtual                      -1.
% 2.61/1.07  --symbol_type_check                     false
% 2.61/1.07  --clausify_out                          false
% 2.61/1.07  --sig_cnt_out                           false
% 2.61/1.07  --trig_cnt_out                          false
% 2.61/1.07  --trig_cnt_out_tolerance                1.
% 2.61/1.07  --trig_cnt_out_sk_spl                   false
% 2.61/1.07  --abstr_cl_out                          false
% 2.61/1.07  
% 2.61/1.07  ------ Global Options
% 2.61/1.07  
% 2.61/1.07  --schedule                              default
% 2.61/1.07  --add_important_lit                     false
% 2.61/1.07  --prop_solver_per_cl                    1000
% 2.61/1.07  --min_unsat_core                        false
% 2.61/1.07  --soft_assumptions                      false
% 2.61/1.07  --soft_lemma_size                       3
% 2.61/1.07  --prop_impl_unit_size                   0
% 2.61/1.07  --prop_impl_unit                        []
% 2.61/1.07  --share_sel_clauses                     true
% 2.61/1.07  --reset_solvers                         false
% 2.61/1.07  --bc_imp_inh                            [conj_cone]
% 2.61/1.07  --conj_cone_tolerance                   3.
% 2.61/1.07  --extra_neg_conj                        none
% 2.61/1.07  --large_theory_mode                     true
% 2.61/1.07  --prolific_symb_bound                   200
% 2.61/1.07  --lt_threshold                          2000
% 2.61/1.07  --clause_weak_htbl                      true
% 2.61/1.07  --gc_record_bc_elim                     false
% 2.61/1.07  
% 2.61/1.07  ------ Preprocessing Options
% 2.61/1.07  
% 2.61/1.07  --preprocessing_flag                    true
% 2.61/1.07  --time_out_prep_mult                    0.1
% 2.61/1.07  --splitting_mode                        input
% 2.61/1.07  --splitting_grd                         true
% 2.61/1.07  --splitting_cvd                         false
% 2.61/1.07  --splitting_cvd_svl                     false
% 2.61/1.07  --splitting_nvd                         32
% 2.61/1.07  --sub_typing                            true
% 2.61/1.07  --prep_gs_sim                           true
% 2.61/1.07  --prep_unflatten                        true
% 2.61/1.07  --prep_res_sim                          true
% 2.61/1.07  --prep_upred                            true
% 2.61/1.07  --prep_sem_filter                       exhaustive
% 2.61/1.07  --prep_sem_filter_out                   false
% 2.61/1.07  --pred_elim                             true
% 2.61/1.07  --res_sim_input                         true
% 2.61/1.07  --eq_ax_congr_red                       true
% 2.61/1.07  --pure_diseq_elim                       true
% 2.61/1.07  --brand_transform                       false
% 2.61/1.07  --non_eq_to_eq                          false
% 2.61/1.07  --prep_def_merge                        true
% 2.61/1.07  --prep_def_merge_prop_impl              false
% 2.61/1.07  --prep_def_merge_mbd                    true
% 2.61/1.07  --prep_def_merge_tr_red                 false
% 2.61/1.07  --prep_def_merge_tr_cl                  false
% 2.61/1.07  --smt_preprocessing                     true
% 2.61/1.07  --smt_ac_axioms                         fast
% 2.61/1.07  --preprocessed_out                      false
% 2.61/1.07  --preprocessed_stats                    false
% 2.61/1.07  
% 2.61/1.07  ------ Abstraction refinement Options
% 2.61/1.07  
% 2.61/1.07  --abstr_ref                             []
% 2.61/1.07  --abstr_ref_prep                        false
% 2.61/1.07  --abstr_ref_until_sat                   false
% 2.61/1.07  --abstr_ref_sig_restrict                funpre
% 2.61/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 2.61/1.07  --abstr_ref_under                       []
% 2.61/1.07  
% 2.61/1.07  ------ SAT Options
% 2.61/1.07  
% 2.61/1.07  --sat_mode                              false
% 2.61/1.07  --sat_fm_restart_options                ""
% 2.61/1.07  --sat_gr_def                            false
% 2.61/1.07  --sat_epr_types                         true
% 2.61/1.07  --sat_non_cyclic_types                  false
% 2.61/1.07  --sat_finite_models                     false
% 2.61/1.07  --sat_fm_lemmas                         false
% 2.61/1.07  --sat_fm_prep                           false
% 2.61/1.07  --sat_fm_uc_incr                        true
% 2.61/1.07  --sat_out_model                         small
% 2.61/1.07  --sat_out_clauses                       false
% 2.61/1.07  
% 2.61/1.07  ------ QBF Options
% 2.61/1.07  
% 2.61/1.07  --qbf_mode                              false
% 2.61/1.07  --qbf_elim_univ                         false
% 2.61/1.07  --qbf_dom_inst                          none
% 2.61/1.07  --qbf_dom_pre_inst                      false
% 2.61/1.07  --qbf_sk_in                             false
% 2.61/1.07  --qbf_pred_elim                         true
% 2.61/1.07  --qbf_split                             512
% 2.61/1.07  
% 2.61/1.07  ------ BMC1 Options
% 2.61/1.07  
% 2.61/1.07  --bmc1_incremental                      false
% 2.61/1.07  --bmc1_axioms                           reachable_all
% 2.61/1.07  --bmc1_min_bound                        0
% 2.61/1.07  --bmc1_max_bound                        -1
% 2.61/1.07  --bmc1_max_bound_default                -1
% 2.61/1.07  --bmc1_symbol_reachability              true
% 2.61/1.07  --bmc1_property_lemmas                  false
% 2.61/1.07  --bmc1_k_induction                      false
% 2.61/1.07  --bmc1_non_equiv_states                 false
% 2.61/1.07  --bmc1_deadlock                         false
% 2.61/1.07  --bmc1_ucm                              false
% 2.61/1.07  --bmc1_add_unsat_core                   none
% 2.61/1.07  --bmc1_unsat_core_children              false
% 2.61/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 2.61/1.07  --bmc1_out_stat                         full
% 2.61/1.07  --bmc1_ground_init                      false
% 2.61/1.07  --bmc1_pre_inst_next_state              false
% 2.61/1.07  --bmc1_pre_inst_state                   false
% 2.61/1.07  --bmc1_pre_inst_reach_state             false
% 2.61/1.07  --bmc1_out_unsat_core                   false
% 2.61/1.07  --bmc1_aig_witness_out                  false
% 2.61/1.07  --bmc1_verbose                          false
% 2.61/1.07  --bmc1_dump_clauses_tptp                false
% 2.61/1.07  --bmc1_dump_unsat_core_tptp             false
% 2.61/1.07  --bmc1_dump_file                        -
% 2.61/1.07  --bmc1_ucm_expand_uc_limit              128
% 2.61/1.07  --bmc1_ucm_n_expand_iterations          6
% 2.61/1.07  --bmc1_ucm_extend_mode                  1
% 2.61/1.07  --bmc1_ucm_init_mode                    2
% 2.61/1.07  --bmc1_ucm_cone_mode                    none
% 2.61/1.07  --bmc1_ucm_reduced_relation_type        0
% 2.61/1.07  --bmc1_ucm_relax_model                  4
% 2.61/1.07  --bmc1_ucm_full_tr_after_sat            true
% 2.61/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 2.61/1.07  --bmc1_ucm_layered_model                none
% 2.61/1.07  --bmc1_ucm_max_lemma_size               10
% 2.61/1.07  
% 2.61/1.07  ------ AIG Options
% 2.61/1.07  
% 2.61/1.07  --aig_mode                              false
% 2.61/1.07  
% 2.61/1.07  ------ Instantiation Options
% 2.61/1.07  
% 2.61/1.07  --instantiation_flag                    true
% 2.61/1.07  --inst_sos_flag                         false
% 2.61/1.07  --inst_sos_phase                        true
% 2.61/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.61/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.61/1.07  --inst_lit_sel_side                     num_symb
% 2.61/1.07  --inst_solver_per_active                1400
% 2.61/1.07  --inst_solver_calls_frac                1.
% 2.61/1.07  --inst_passive_queue_type               priority_queues
% 2.61/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.61/1.07  --inst_passive_queues_freq              [25;2]
% 2.61/1.07  --inst_dismatching                      true
% 2.61/1.07  --inst_eager_unprocessed_to_passive     true
% 2.61/1.07  --inst_prop_sim_given                   true
% 2.61/1.07  --inst_prop_sim_new                     false
% 2.61/1.07  --inst_subs_new                         false
% 2.61/1.07  --inst_eq_res_simp                      false
% 2.61/1.07  --inst_subs_given                       false
% 2.61/1.07  --inst_orphan_elimination               true
% 2.61/1.07  --inst_learning_loop_flag               true
% 2.61/1.07  --inst_learning_start                   3000
% 2.61/1.07  --inst_learning_factor                  2
% 2.61/1.07  --inst_start_prop_sim_after_learn       3
% 2.61/1.07  --inst_sel_renew                        solver
% 2.61/1.07  --inst_lit_activity_flag                true
% 2.61/1.07  --inst_restr_to_given                   false
% 2.61/1.07  --inst_activity_threshold               500
% 2.61/1.07  --inst_out_proof                        true
% 2.61/1.07  
% 2.61/1.07  ------ Resolution Options
% 2.61/1.07  
% 2.61/1.07  --resolution_flag                       true
% 2.61/1.07  --res_lit_sel                           adaptive
% 2.61/1.07  --res_lit_sel_side                      none
% 2.61/1.07  --res_ordering                          kbo
% 2.61/1.07  --res_to_prop_solver                    active
% 2.61/1.07  --res_prop_simpl_new                    false
% 2.61/1.07  --res_prop_simpl_given                  true
% 2.61/1.07  --res_passive_queue_type                priority_queues
% 2.61/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.61/1.07  --res_passive_queues_freq               [15;5]
% 2.61/1.07  --res_forward_subs                      full
% 2.61/1.07  --res_backward_subs                     full
% 2.61/1.07  --res_forward_subs_resolution           true
% 2.61/1.07  --res_backward_subs_resolution          true
% 2.61/1.07  --res_orphan_elimination                true
% 2.61/1.07  --res_time_limit                        2.
% 2.61/1.07  --res_out_proof                         true
% 2.61/1.07  
% 2.61/1.07  ------ Superposition Options
% 2.61/1.07  
% 2.61/1.07  --superposition_flag                    true
% 2.61/1.07  --sup_passive_queue_type                priority_queues
% 2.61/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.61/1.07  --sup_passive_queues_freq               [8;1;4]
% 2.61/1.07  --demod_completeness_check              fast
% 2.61/1.07  --demod_use_ground                      true
% 2.61/1.07  --sup_to_prop_solver                    passive
% 2.61/1.07  --sup_prop_simpl_new                    true
% 2.61/1.07  --sup_prop_simpl_given                  true
% 2.61/1.07  --sup_fun_splitting                     false
% 2.61/1.07  --sup_smt_interval                      50000
% 2.61/1.07  
% 2.61/1.07  ------ Superposition Simplification Setup
% 2.61/1.07  
% 2.61/1.07  --sup_indices_passive                   []
% 2.61/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 2.61/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.07  --sup_full_bw                           [BwDemod]
% 2.61/1.07  --sup_immed_triv                        [TrivRules]
% 2.61/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.61/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.07  --sup_immed_bw_main                     []
% 2.61/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 2.61/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/1.07  
% 2.61/1.07  ------ Combination Options
% 2.61/1.07  
% 2.61/1.07  --comb_res_mult                         3
% 2.61/1.07  --comb_sup_mult                         2
% 2.61/1.07  --comb_inst_mult                        10
% 2.61/1.07  
% 2.61/1.07  ------ Debug Options
% 2.61/1.07  
% 2.61/1.07  --dbg_backtrace                         false
% 2.61/1.07  --dbg_dump_prop_clauses                 false
% 2.61/1.07  --dbg_dump_prop_clauses_file            -
% 2.61/1.07  --dbg_out_stat                          false
% 2.61/1.07  ------ Parsing...
% 2.61/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.61/1.07  
% 2.61/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.61/1.07  
% 2.61/1.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.61/1.07  
% 2.61/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.61/1.07  ------ Proving...
% 2.61/1.07  ------ Problem Properties 
% 2.61/1.07  
% 2.61/1.07  
% 2.61/1.07  clauses                                 24
% 2.61/1.07  conjectures                             5
% 2.61/1.07  EPR                                     2
% 2.61/1.07  Horn                                    24
% 2.61/1.07  unary                                   8
% 2.61/1.07  binary                                  3
% 2.61/1.07  lits                                    73
% 2.61/1.07  lits eq                                 16
% 2.61/1.07  fd_pure                                 0
% 2.61/1.07  fd_pseudo                               0
% 2.61/1.07  fd_cond                                 0
% 2.61/1.07  fd_pseudo_cond                          1
% 2.61/1.07  AC symbols                              0
% 2.61/1.07  
% 2.61/1.07  ------ Schedule dynamic 5 is on 
% 2.61/1.07  
% 2.61/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.61/1.07  
% 2.61/1.07  
% 2.61/1.07  ------ 
% 2.61/1.07  Current options:
% 2.61/1.07  ------ 
% 2.61/1.07  
% 2.61/1.07  ------ Input Options
% 2.61/1.07  
% 2.61/1.07  --out_options                           all
% 2.61/1.07  --tptp_safe_out                         true
% 2.61/1.07  --problem_path                          ""
% 2.61/1.07  --include_path                          ""
% 2.61/1.07  --clausifier                            res/vclausify_rel
% 2.61/1.07  --clausifier_options                    --mode clausify
% 2.61/1.07  --stdin                                 false
% 2.61/1.07  --stats_out                             all
% 2.61/1.07  
% 2.61/1.07  ------ General Options
% 2.61/1.07  
% 2.61/1.07  --fof                                   false
% 2.61/1.07  --time_out_real                         305.
% 2.61/1.07  --time_out_virtual                      -1.
% 2.61/1.07  --symbol_type_check                     false
% 2.61/1.07  --clausify_out                          false
% 2.61/1.07  --sig_cnt_out                           false
% 2.61/1.07  --trig_cnt_out                          false
% 2.61/1.07  --trig_cnt_out_tolerance                1.
% 2.61/1.07  --trig_cnt_out_sk_spl                   false
% 2.61/1.07  --abstr_cl_out                          false
% 2.61/1.07  
% 2.61/1.07  ------ Global Options
% 2.61/1.07  
% 2.61/1.07  --schedule                              default
% 2.61/1.07  --add_important_lit                     false
% 2.61/1.07  --prop_solver_per_cl                    1000
% 2.61/1.07  --min_unsat_core                        false
% 2.61/1.07  --soft_assumptions                      false
% 2.61/1.07  --soft_lemma_size                       3
% 2.61/1.07  --prop_impl_unit_size                   0
% 2.61/1.07  --prop_impl_unit                        []
% 2.61/1.07  --share_sel_clauses                     true
% 2.61/1.07  --reset_solvers                         false
% 2.61/1.07  --bc_imp_inh                            [conj_cone]
% 2.61/1.07  --conj_cone_tolerance                   3.
% 2.61/1.07  --extra_neg_conj                        none
% 2.61/1.07  --large_theory_mode                     true
% 2.61/1.07  --prolific_symb_bound                   200
% 2.61/1.07  --lt_threshold                          2000
% 2.61/1.07  --clause_weak_htbl                      true
% 2.61/1.07  --gc_record_bc_elim                     false
% 2.61/1.07  
% 2.61/1.07  ------ Preprocessing Options
% 2.61/1.07  
% 2.61/1.07  --preprocessing_flag                    true
% 2.61/1.07  --time_out_prep_mult                    0.1
% 2.61/1.07  --splitting_mode                        input
% 2.61/1.07  --splitting_grd                         true
% 2.61/1.07  --splitting_cvd                         false
% 2.61/1.07  --splitting_cvd_svl                     false
% 2.61/1.07  --splitting_nvd                         32
% 2.61/1.07  --sub_typing                            true
% 2.61/1.07  --prep_gs_sim                           true
% 2.61/1.07  --prep_unflatten                        true
% 2.61/1.07  --prep_res_sim                          true
% 2.61/1.07  --prep_upred                            true
% 2.61/1.07  --prep_sem_filter                       exhaustive
% 2.61/1.07  --prep_sem_filter_out                   false
% 2.61/1.07  --pred_elim                             true
% 2.61/1.07  --res_sim_input                         true
% 2.61/1.07  --eq_ax_congr_red                       true
% 2.61/1.07  --pure_diseq_elim                       true
% 2.61/1.07  --brand_transform                       false
% 2.61/1.07  --non_eq_to_eq                          false
% 2.61/1.07  --prep_def_merge                        true
% 2.61/1.07  --prep_def_merge_prop_impl              false
% 2.61/1.07  --prep_def_merge_mbd                    true
% 2.61/1.07  --prep_def_merge_tr_red                 false
% 2.61/1.07  --prep_def_merge_tr_cl                  false
% 2.61/1.07  --smt_preprocessing                     true
% 2.61/1.07  --smt_ac_axioms                         fast
% 2.61/1.07  --preprocessed_out                      false
% 2.61/1.07  --preprocessed_stats                    false
% 2.61/1.07  
% 2.61/1.07  ------ Abstraction refinement Options
% 2.61/1.07  
% 2.61/1.07  --abstr_ref                             []
% 2.61/1.07  --abstr_ref_prep                        false
% 2.61/1.07  --abstr_ref_until_sat                   false
% 2.61/1.07  --abstr_ref_sig_restrict                funpre
% 2.61/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 2.61/1.07  --abstr_ref_under                       []
% 2.61/1.07  
% 2.61/1.07  ------ SAT Options
% 2.61/1.07  
% 2.61/1.07  --sat_mode                              false
% 2.61/1.07  --sat_fm_restart_options                ""
% 2.61/1.07  --sat_gr_def                            false
% 2.61/1.07  --sat_epr_types                         true
% 2.61/1.07  --sat_non_cyclic_types                  false
% 2.61/1.07  --sat_finite_models                     false
% 2.61/1.07  --sat_fm_lemmas                         false
% 2.61/1.07  --sat_fm_prep                           false
% 2.61/1.07  --sat_fm_uc_incr                        true
% 2.61/1.07  --sat_out_model                         small
% 2.61/1.07  --sat_out_clauses                       false
% 2.61/1.07  
% 2.61/1.07  ------ QBF Options
% 2.61/1.07  
% 2.61/1.07  --qbf_mode                              false
% 2.61/1.07  --qbf_elim_univ                         false
% 2.61/1.07  --qbf_dom_inst                          none
% 2.61/1.07  --qbf_dom_pre_inst                      false
% 2.61/1.07  --qbf_sk_in                             false
% 2.61/1.07  --qbf_pred_elim                         true
% 2.61/1.07  --qbf_split                             512
% 2.61/1.07  
% 2.61/1.07  ------ BMC1 Options
% 2.61/1.07  
% 2.61/1.07  --bmc1_incremental                      false
% 2.61/1.07  --bmc1_axioms                           reachable_all
% 2.61/1.07  --bmc1_min_bound                        0
% 2.61/1.07  --bmc1_max_bound                        -1
% 2.61/1.07  --bmc1_max_bound_default                -1
% 2.61/1.07  --bmc1_symbol_reachability              true
% 2.61/1.07  --bmc1_property_lemmas                  false
% 2.61/1.07  --bmc1_k_induction                      false
% 2.61/1.07  --bmc1_non_equiv_states                 false
% 2.61/1.07  --bmc1_deadlock                         false
% 2.61/1.07  --bmc1_ucm                              false
% 2.61/1.07  --bmc1_add_unsat_core                   none
% 2.61/1.07  --bmc1_unsat_core_children              false
% 2.61/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 2.61/1.07  --bmc1_out_stat                         full
% 2.61/1.07  --bmc1_ground_init                      false
% 2.61/1.07  --bmc1_pre_inst_next_state              false
% 2.61/1.07  --bmc1_pre_inst_state                   false
% 2.61/1.07  --bmc1_pre_inst_reach_state             false
% 2.61/1.07  --bmc1_out_unsat_core                   false
% 2.61/1.07  --bmc1_aig_witness_out                  false
% 2.61/1.07  --bmc1_verbose                          false
% 2.61/1.07  --bmc1_dump_clauses_tptp                false
% 2.61/1.07  --bmc1_dump_unsat_core_tptp             false
% 2.61/1.07  --bmc1_dump_file                        -
% 2.61/1.07  --bmc1_ucm_expand_uc_limit              128
% 2.61/1.07  --bmc1_ucm_n_expand_iterations          6
% 2.61/1.07  --bmc1_ucm_extend_mode                  1
% 2.61/1.07  --bmc1_ucm_init_mode                    2
% 2.61/1.07  --bmc1_ucm_cone_mode                    none
% 2.61/1.07  --bmc1_ucm_reduced_relation_type        0
% 2.61/1.07  --bmc1_ucm_relax_model                  4
% 2.61/1.07  --bmc1_ucm_full_tr_after_sat            true
% 2.61/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 2.61/1.07  --bmc1_ucm_layered_model                none
% 2.61/1.07  --bmc1_ucm_max_lemma_size               10
% 2.61/1.07  
% 2.61/1.07  ------ AIG Options
% 2.61/1.07  
% 2.61/1.07  --aig_mode                              false
% 2.61/1.07  
% 2.61/1.07  ------ Instantiation Options
% 2.61/1.07  
% 2.61/1.07  --instantiation_flag                    true
% 2.61/1.07  --inst_sos_flag                         false
% 2.61/1.07  --inst_sos_phase                        true
% 2.61/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.61/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.61/1.07  --inst_lit_sel_side                     none
% 2.61/1.07  --inst_solver_per_active                1400
% 2.61/1.07  --inst_solver_calls_frac                1.
% 2.61/1.07  --inst_passive_queue_type               priority_queues
% 2.61/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.61/1.07  --inst_passive_queues_freq              [25;2]
% 2.61/1.07  --inst_dismatching                      true
% 2.61/1.07  --inst_eager_unprocessed_to_passive     true
% 2.61/1.07  --inst_prop_sim_given                   true
% 2.61/1.07  --inst_prop_sim_new                     false
% 2.61/1.07  --inst_subs_new                         false
% 2.61/1.07  --inst_eq_res_simp                      false
% 2.61/1.07  --inst_subs_given                       false
% 2.61/1.07  --inst_orphan_elimination               true
% 2.61/1.07  --inst_learning_loop_flag               true
% 2.61/1.07  --inst_learning_start                   3000
% 2.61/1.07  --inst_learning_factor                  2
% 2.61/1.07  --inst_start_prop_sim_after_learn       3
% 2.61/1.07  --inst_sel_renew                        solver
% 2.61/1.07  --inst_lit_activity_flag                true
% 2.61/1.07  --inst_restr_to_given                   false
% 2.61/1.07  --inst_activity_threshold               500
% 2.61/1.07  --inst_out_proof                        true
% 2.61/1.07  
% 2.61/1.07  ------ Resolution Options
% 2.61/1.07  
% 2.61/1.07  --resolution_flag                       false
% 2.61/1.07  --res_lit_sel                           adaptive
% 2.61/1.07  --res_lit_sel_side                      none
% 2.61/1.07  --res_ordering                          kbo
% 2.61/1.07  --res_to_prop_solver                    active
% 2.61/1.07  --res_prop_simpl_new                    false
% 2.61/1.07  --res_prop_simpl_given                  true
% 2.61/1.07  --res_passive_queue_type                priority_queues
% 2.61/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.61/1.07  --res_passive_queues_freq               [15;5]
% 2.61/1.07  --res_forward_subs                      full
% 2.61/1.07  --res_backward_subs                     full
% 2.61/1.07  --res_forward_subs_resolution           true
% 2.61/1.07  --res_backward_subs_resolution          true
% 2.61/1.07  --res_orphan_elimination                true
% 2.61/1.07  --res_time_limit                        2.
% 2.61/1.07  --res_out_proof                         true
% 2.61/1.07  
% 2.61/1.07  ------ Superposition Options
% 2.61/1.07  
% 2.61/1.07  --superposition_flag                    true
% 2.61/1.07  --sup_passive_queue_type                priority_queues
% 2.61/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.61/1.07  --sup_passive_queues_freq               [8;1;4]
% 2.61/1.07  --demod_completeness_check              fast
% 2.61/1.07  --demod_use_ground                      true
% 2.61/1.07  --sup_to_prop_solver                    passive
% 2.61/1.07  --sup_prop_simpl_new                    true
% 2.61/1.07  --sup_prop_simpl_given                  true
% 2.61/1.07  --sup_fun_splitting                     false
% 2.61/1.07  --sup_smt_interval                      50000
% 2.61/1.07  
% 2.61/1.07  ------ Superposition Simplification Setup
% 2.61/1.07  
% 2.61/1.07  --sup_indices_passive                   []
% 2.61/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 2.61/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.07  --sup_full_bw                           [BwDemod]
% 2.61/1.07  --sup_immed_triv                        [TrivRules]
% 2.61/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.61/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.07  --sup_immed_bw_main                     []
% 2.61/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 2.61/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/1.07  
% 2.61/1.07  ------ Combination Options
% 2.61/1.07  
% 2.61/1.07  --comb_res_mult                         3
% 2.61/1.07  --comb_sup_mult                         2
% 2.61/1.07  --comb_inst_mult                        10
% 2.61/1.07  
% 2.61/1.07  ------ Debug Options
% 2.61/1.07  
% 2.61/1.07  --dbg_backtrace                         false
% 2.61/1.07  --dbg_dump_prop_clauses                 false
% 2.61/1.07  --dbg_dump_prop_clauses_file            -
% 2.61/1.07  --dbg_out_stat                          false
% 2.61/1.07  
% 2.61/1.07  
% 2.61/1.07  
% 2.61/1.07  
% 2.61/1.07  ------ Proving...
% 2.61/1.07  
% 2.61/1.07  
% 2.61/1.07  % SZS status Theorem for theBenchmark.p
% 2.61/1.07  
% 2.61/1.07  % SZS output start CNFRefutation for theBenchmark.p
% 2.61/1.07  
% 2.61/1.07  fof(f18,conjecture,(
% 2.61/1.07    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.61/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.07  
% 2.61/1.07  fof(f19,negated_conjecture,(
% 2.61/1.07    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.61/1.07    inference(negated_conjecture,[],[f18])).
% 2.61/1.07  
% 2.61/1.07  fof(f47,plain,(
% 2.61/1.07    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.61/1.07    inference(ennf_transformation,[],[f19])).
% 2.61/1.07  
% 2.61/1.07  fof(f48,plain,(
% 2.61/1.07    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.61/1.07    inference(flattening,[],[f47])).
% 2.61/1.07  
% 2.61/1.07  fof(f53,plain,(
% 2.61/1.07    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.61/1.07    introduced(choice_axiom,[])).
% 2.61/1.07  
% 2.61/1.07  fof(f52,plain,(
% 2.61/1.07    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.61/1.07    introduced(choice_axiom,[])).
% 2.61/1.07  
% 2.61/1.07  fof(f51,plain,(
% 2.61/1.07    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.61/1.07    introduced(choice_axiom,[])).
% 2.61/1.07  
% 2.61/1.07  fof(f54,plain,(
% 2.61/1.07    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.61/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f53,f52,f51])).
% 2.61/1.07  
% 2.61/1.07  fof(f84,plain,(
% 2.61/1.07    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.61/1.07    inference(cnf_transformation,[],[f54])).
% 2.61/1.07  
% 2.61/1.07  fof(f15,axiom,(
% 2.61/1.07    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.61/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.07  
% 2.61/1.07  fof(f42,plain,(
% 2.61/1.07    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.61/1.07    inference(ennf_transformation,[],[f15])).
% 2.61/1.07  
% 2.61/1.07  fof(f76,plain,(
% 2.61/1.07    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.61/1.07    inference(cnf_transformation,[],[f42])).
% 2.61/1.07  
% 2.61/1.07  fof(f79,plain,(
% 2.61/1.07    l1_struct_0(sK0)),
% 2.61/1.07    inference(cnf_transformation,[],[f54])).
% 2.61/1.07  
% 2.61/1.07  fof(f81,plain,(
% 2.61/1.07    l1_struct_0(sK1)),
% 2.61/1.07    inference(cnf_transformation,[],[f54])).
% 2.61/1.07  
% 2.61/1.07  fof(f11,axiom,(
% 2.61/1.07    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.61/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.07  
% 2.61/1.07  fof(f34,plain,(
% 2.61/1.07    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.61/1.07    inference(ennf_transformation,[],[f11])).
% 2.61/1.07  
% 2.61/1.07  fof(f35,plain,(
% 2.61/1.07    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.61/1.07    inference(flattening,[],[f34])).
% 2.61/1.07  
% 2.61/1.07  fof(f68,plain,(
% 2.61/1.07    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.61/1.07    inference(cnf_transformation,[],[f35])).
% 2.61/1.07  
% 2.61/1.07  fof(f16,axiom,(
% 2.61/1.07    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.61/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.07  
% 2.61/1.07  fof(f43,plain,(
% 2.61/1.07    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.61/1.07    inference(ennf_transformation,[],[f16])).
% 2.61/1.07  
% 2.61/1.07  fof(f44,plain,(
% 2.61/1.07    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.61/1.07    inference(flattening,[],[f43])).
% 2.61/1.07  
% 2.61/1.07  fof(f77,plain,(
% 2.61/1.07    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.61/1.07    inference(cnf_transformation,[],[f44])).
% 2.61/1.07  
% 2.61/1.07  fof(f80,plain,(
% 2.61/1.07    ~v2_struct_0(sK1)),
% 2.61/1.07    inference(cnf_transformation,[],[f54])).
% 2.61/1.07  
% 2.61/1.07  fof(f12,axiom,(
% 2.61/1.07    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.61/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.07  
% 2.61/1.07  fof(f36,plain,(
% 2.61/1.07    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.61/1.07    inference(ennf_transformation,[],[f12])).
% 2.61/1.07  
% 2.61/1.07  fof(f37,plain,(
% 2.61/1.07    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.61/1.07    inference(flattening,[],[f36])).
% 2.61/1.07  
% 2.61/1.07  fof(f49,plain,(
% 2.61/1.07    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.61/1.07    inference(nnf_transformation,[],[f37])).
% 2.61/1.07  
% 2.61/1.07  fof(f69,plain,(
% 2.61/1.07    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.61/1.07    inference(cnf_transformation,[],[f49])).
% 2.61/1.07  
% 2.61/1.07  fof(f9,axiom,(
% 2.61/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.61/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.07  
% 2.61/1.07  fof(f20,plain,(
% 2.61/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.61/1.07    inference(pure_predicate_removal,[],[f9])).
% 2.61/1.07  
% 2.61/1.07  fof(f32,plain,(
% 2.61/1.07    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.61/1.07    inference(ennf_transformation,[],[f20])).
% 2.61/1.07  
% 2.61/1.07  fof(f65,plain,(
% 2.61/1.07    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.61/1.07    inference(cnf_transformation,[],[f32])).
% 2.61/1.07  
% 2.61/1.07  fof(f82,plain,(
% 2.61/1.07    v1_funct_1(sK2)),
% 2.61/1.07    inference(cnf_transformation,[],[f54])).
% 2.61/1.07  
% 2.61/1.07  fof(f83,plain,(
% 2.61/1.07    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.61/1.07    inference(cnf_transformation,[],[f54])).
% 2.61/1.07  
% 2.61/1.07  fof(f1,axiom,(
% 2.61/1.07    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.61/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.07  
% 2.61/1.07  fof(f21,plain,(
% 2.61/1.07    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.61/1.07    inference(ennf_transformation,[],[f1])).
% 2.61/1.07  
% 2.61/1.07  fof(f55,plain,(
% 2.61/1.07    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.61/1.07    inference(cnf_transformation,[],[f21])).
% 2.61/1.07  
% 2.61/1.07  fof(f2,axiom,(
% 2.61/1.07    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.61/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.07  
% 2.61/1.07  fof(f56,plain,(
% 2.61/1.07    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.61/1.07    inference(cnf_transformation,[],[f2])).
% 2.61/1.07  
% 2.61/1.07  fof(f10,axiom,(
% 2.61/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.61/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.07  
% 2.61/1.07  fof(f33,plain,(
% 2.61/1.07    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.61/1.07    inference(ennf_transformation,[],[f10])).
% 2.61/1.07  
% 2.61/1.07  fof(f66,plain,(
% 2.61/1.07    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.61/1.07    inference(cnf_transformation,[],[f33])).
% 2.61/1.07  
% 2.61/1.07  fof(f85,plain,(
% 2.61/1.07    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.61/1.07    inference(cnf_transformation,[],[f54])).
% 2.61/1.07  
% 2.61/1.07  fof(f14,axiom,(
% 2.61/1.07    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.61/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.07  
% 2.61/1.07  fof(f40,plain,(
% 2.61/1.07    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.61/1.07    inference(ennf_transformation,[],[f14])).
% 2.61/1.07  
% 2.61/1.07  fof(f41,plain,(
% 2.61/1.07    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.61/1.07    inference(flattening,[],[f40])).
% 2.61/1.07  
% 2.61/1.07  fof(f75,plain,(
% 2.61/1.07    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.61/1.07    inference(cnf_transformation,[],[f41])).
% 2.61/1.07  
% 2.61/1.07  fof(f86,plain,(
% 2.61/1.07    v2_funct_1(sK2)),
% 2.61/1.07    inference(cnf_transformation,[],[f54])).
% 2.61/1.07  
% 2.61/1.07  fof(f5,axiom,(
% 2.61/1.07    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.61/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.07  
% 2.61/1.07  fof(f24,plain,(
% 2.61/1.07    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.61/1.07    inference(ennf_transformation,[],[f5])).
% 2.61/1.07  
% 2.61/1.07  fof(f25,plain,(
% 2.61/1.07    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.61/1.07    inference(flattening,[],[f24])).
% 2.61/1.07  
% 2.61/1.07  fof(f59,plain,(
% 2.61/1.07    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.61/1.07    inference(cnf_transformation,[],[f25])).
% 2.61/1.07  
% 2.61/1.07  fof(f6,axiom,(
% 2.61/1.07    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.61/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.07  
% 2.61/1.07  fof(f26,plain,(
% 2.61/1.07    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.61/1.07    inference(ennf_transformation,[],[f6])).
% 2.61/1.07  
% 2.61/1.07  fof(f27,plain,(
% 2.61/1.07    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.61/1.07    inference(flattening,[],[f26])).
% 2.61/1.07  
% 2.61/1.07  fof(f60,plain,(
% 2.61/1.07    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.61/1.07    inference(cnf_transformation,[],[f27])).
% 2.61/1.07  
% 2.61/1.07  fof(f3,axiom,(
% 2.61/1.07    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.61/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.07  
% 2.61/1.07  fof(f22,plain,(
% 2.61/1.07    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.61/1.07    inference(ennf_transformation,[],[f3])).
% 2.61/1.07  
% 2.61/1.07  fof(f57,plain,(
% 2.61/1.07    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.61/1.07    inference(cnf_transformation,[],[f22])).
% 2.61/1.07  
% 2.61/1.07  fof(f7,axiom,(
% 2.61/1.07    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 2.61/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.07  
% 2.61/1.07  fof(f28,plain,(
% 2.61/1.07    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.61/1.07    inference(ennf_transformation,[],[f7])).
% 2.61/1.07  
% 2.61/1.07  fof(f29,plain,(
% 2.61/1.07    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.61/1.07    inference(flattening,[],[f28])).
% 2.61/1.07  
% 2.61/1.07  fof(f63,plain,(
% 2.61/1.07    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.61/1.07    inference(cnf_transformation,[],[f29])).
% 2.61/1.07  
% 2.61/1.07  fof(f4,axiom,(
% 2.61/1.07    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.61/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.07  
% 2.61/1.07  fof(f23,plain,(
% 2.61/1.07    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.61/1.07    inference(ennf_transformation,[],[f4])).
% 2.61/1.07  
% 2.61/1.07  fof(f58,plain,(
% 2.61/1.07    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.61/1.07    inference(cnf_transformation,[],[f23])).
% 2.61/1.07  
% 2.61/1.07  fof(f17,axiom,(
% 2.61/1.07    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.61/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.07  
% 2.61/1.07  fof(f45,plain,(
% 2.61/1.07    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.61/1.07    inference(ennf_transformation,[],[f17])).
% 2.61/1.07  
% 2.61/1.07  fof(f46,plain,(
% 2.61/1.07    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.61/1.07    inference(flattening,[],[f45])).
% 2.61/1.07  
% 2.61/1.07  fof(f78,plain,(
% 2.61/1.07    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.61/1.07    inference(cnf_transformation,[],[f46])).
% 2.61/1.07  
% 2.61/1.07  fof(f8,axiom,(
% 2.61/1.07    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.61/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.07  
% 2.61/1.07  fof(f30,plain,(
% 2.61/1.07    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.61/1.07    inference(ennf_transformation,[],[f8])).
% 2.61/1.07  
% 2.61/1.07  fof(f31,plain,(
% 2.61/1.07    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.61/1.07    inference(flattening,[],[f30])).
% 2.61/1.07  
% 2.61/1.07  fof(f64,plain,(
% 2.61/1.07    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.61/1.07    inference(cnf_transformation,[],[f31])).
% 2.61/1.07  
% 2.61/1.07  fof(f62,plain,(
% 2.61/1.07    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.61/1.07    inference(cnf_transformation,[],[f27])).
% 2.61/1.07  
% 2.61/1.07  fof(f61,plain,(
% 2.61/1.07    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.61/1.07    inference(cnf_transformation,[],[f27])).
% 2.61/1.07  
% 2.61/1.07  fof(f74,plain,(
% 2.61/1.07    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.61/1.07    inference(cnf_transformation,[],[f41])).
% 2.61/1.07  
% 2.61/1.07  fof(f13,axiom,(
% 2.61/1.07    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.61/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.07  
% 2.61/1.07  fof(f38,plain,(
% 2.61/1.07    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.61/1.07    inference(ennf_transformation,[],[f13])).
% 2.61/1.07  
% 2.61/1.07  fof(f39,plain,(
% 2.61/1.07    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.61/1.07    inference(flattening,[],[f38])).
% 2.61/1.07  
% 2.61/1.07  fof(f50,plain,(
% 2.61/1.07    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.61/1.07    inference(nnf_transformation,[],[f39])).
% 2.61/1.07  
% 2.61/1.07  fof(f72,plain,(
% 2.61/1.07    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.61/1.07    inference(cnf_transformation,[],[f50])).
% 2.61/1.07  
% 2.61/1.07  fof(f89,plain,(
% 2.61/1.07    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.61/1.07    inference(equality_resolution,[],[f72])).
% 2.61/1.07  
% 2.61/1.07  fof(f87,plain,(
% 2.61/1.07    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.61/1.07    inference(cnf_transformation,[],[f54])).
% 2.61/1.07  
% 2.61/1.07  cnf(c_27,negated_conjecture,
% 2.61/1.07      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.61/1.07      inference(cnf_transformation,[],[f84]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_687,negated_conjecture,
% 2.61/1.07      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_27]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1150,plain,
% 2.61/1.07      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_687]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_21,plain,
% 2.61/1.07      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.61/1.07      inference(cnf_transformation,[],[f76]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_32,negated_conjecture,
% 2.61/1.07      ( l1_struct_0(sK0) ),
% 2.61/1.07      inference(cnf_transformation,[],[f79]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_375,plain,
% 2.61/1.07      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.61/1.07      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_376,plain,
% 2.61/1.07      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.61/1.07      inference(unflattening,[status(thm)],[c_375]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_683,plain,
% 2.61/1.07      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_376]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_30,negated_conjecture,
% 2.61/1.07      ( l1_struct_0(sK1) ),
% 2.61/1.07      inference(cnf_transformation,[],[f81]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_370,plain,
% 2.61/1.07      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.61/1.07      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_371,plain,
% 2.61/1.07      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.61/1.07      inference(unflattening,[status(thm)],[c_370]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_684,plain,
% 2.61/1.07      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_371]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1172,plain,
% 2.61/1.07      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.61/1.07      inference(light_normalisation,[status(thm)],[c_1150,c_683,c_684]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_12,plain,
% 2.61/1.07      ( ~ v1_funct_2(X0,X1,X2)
% 2.61/1.07      | v1_partfun1(X0,X1)
% 2.61/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.07      | v1_xboole_0(X2)
% 2.61/1.07      | ~ v1_funct_1(X0) ),
% 2.61/1.07      inference(cnf_transformation,[],[f68]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_22,plain,
% 2.61/1.07      ( v2_struct_0(X0)
% 2.61/1.07      | ~ l1_struct_0(X0)
% 2.61/1.07      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.61/1.07      inference(cnf_transformation,[],[f77]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_31,negated_conjecture,
% 2.61/1.07      ( ~ v2_struct_0(sK1) ),
% 2.61/1.07      inference(cnf_transformation,[],[f80]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_357,plain,
% 2.61/1.07      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 2.61/1.07      inference(resolution_lifted,[status(thm)],[c_22,c_31]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_358,plain,
% 2.61/1.07      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.61/1.07      inference(unflattening,[status(thm)],[c_357]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_45,plain,
% 2.61/1.07      ( v2_struct_0(sK1)
% 2.61/1.07      | ~ l1_struct_0(sK1)
% 2.61/1.07      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.61/1.07      inference(instantiation,[status(thm)],[c_22]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_360,plain,
% 2.61/1.07      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.61/1.07      inference(global_propositional_subsumption,
% 2.61/1.07                [status(thm)],
% 2.61/1.07                [c_358,c_31,c_30,c_45]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_382,plain,
% 2.61/1.07      ( ~ v1_funct_2(X0,X1,X2)
% 2.61/1.07      | v1_partfun1(X0,X1)
% 2.61/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.07      | ~ v1_funct_1(X0)
% 2.61/1.07      | u1_struct_0(sK1) != X2 ),
% 2.61/1.07      inference(resolution_lifted,[status(thm)],[c_12,c_360]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_383,plain,
% 2.61/1.07      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.61/1.07      | v1_partfun1(X0,X1)
% 2.61/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.61/1.07      | ~ v1_funct_1(X0) ),
% 2.61/1.07      inference(unflattening,[status(thm)],[c_382]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_15,plain,
% 2.61/1.07      ( ~ v1_partfun1(X0,X1)
% 2.61/1.07      | ~ v4_relat_1(X0,X1)
% 2.61/1.07      | ~ v1_relat_1(X0)
% 2.61/1.07      | k1_relat_1(X0) = X1 ),
% 2.61/1.07      inference(cnf_transformation,[],[f69]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_461,plain,
% 2.61/1.07      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.61/1.07      | ~ v4_relat_1(X0,X1)
% 2.61/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.61/1.07      | ~ v1_funct_1(X0)
% 2.61/1.07      | ~ v1_relat_1(X0)
% 2.61/1.07      | k1_relat_1(X0) = X1 ),
% 2.61/1.07      inference(resolution,[status(thm)],[c_383,c_15]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_10,plain,
% 2.61/1.07      ( v4_relat_1(X0,X1)
% 2.61/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.61/1.07      inference(cnf_transformation,[],[f65]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_477,plain,
% 2.61/1.07      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.61/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.61/1.07      | ~ v1_funct_1(X0)
% 2.61/1.07      | ~ v1_relat_1(X0)
% 2.61/1.07      | k1_relat_1(X0) = X1 ),
% 2.61/1.07      inference(forward_subsumption_resolution,
% 2.61/1.07                [status(thm)],
% 2.61/1.07                [c_461,c_10]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_681,plain,
% 2.61/1.07      ( ~ v1_funct_2(X0_54,X0_55,u1_struct_0(sK1))
% 2.61/1.07      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,u1_struct_0(sK1))))
% 2.61/1.07      | ~ v1_funct_1(X0_54)
% 2.61/1.07      | ~ v1_relat_1(X0_54)
% 2.61/1.07      | k1_relat_1(X0_54) = X0_55 ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_477]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1154,plain,
% 2.61/1.07      ( k1_relat_1(X0_54) = X0_55
% 2.61/1.07      | v1_funct_2(X0_54,X0_55,u1_struct_0(sK1)) != iProver_top
% 2.61/1.07      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,u1_struct_0(sK1)))) != iProver_top
% 2.61/1.07      | v1_funct_1(X0_54) != iProver_top
% 2.61/1.07      | v1_relat_1(X0_54) != iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_681]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1239,plain,
% 2.61/1.07      ( k1_relat_1(X0_54) = X0_55
% 2.61/1.07      | v1_funct_2(X0_54,X0_55,k2_struct_0(sK1)) != iProver_top
% 2.61/1.07      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_struct_0(sK1)))) != iProver_top
% 2.61/1.07      | v1_funct_1(X0_54) != iProver_top
% 2.61/1.07      | v1_relat_1(X0_54) != iProver_top ),
% 2.61/1.07      inference(light_normalisation,[status(thm)],[c_1154,c_684]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1452,plain,
% 2.61/1.07      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.61/1.07      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.61/1.07      | v1_funct_1(sK2) != iProver_top
% 2.61/1.07      | v1_relat_1(sK2) != iProver_top ),
% 2.61/1.07      inference(superposition,[status(thm)],[c_1172,c_1239]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_29,negated_conjecture,
% 2.61/1.07      ( v1_funct_1(sK2) ),
% 2.61/1.07      inference(cnf_transformation,[],[f82]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_28,negated_conjecture,
% 2.61/1.07      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.61/1.07      inference(cnf_transformation,[],[f83]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_686,negated_conjecture,
% 2.61/1.07      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_28]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1151,plain,
% 2.61/1.07      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_686]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1166,plain,
% 2.61/1.07      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.61/1.07      inference(light_normalisation,[status(thm)],[c_1151,c_683,c_684]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1316,plain,
% 2.61/1.07      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
% 2.61/1.07      inference(predicate_to_equality_rev,[status(thm)],[c_1166]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1453,plain,
% 2.61/1.07      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
% 2.61/1.07      | ~ v1_funct_1(sK2)
% 2.61/1.07      | ~ v1_relat_1(sK2)
% 2.61/1.07      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.61/1.07      inference(predicate_to_equality_rev,[status(thm)],[c_1452]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_0,plain,
% 2.61/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.61/1.07      | ~ v1_relat_1(X1)
% 2.61/1.07      | v1_relat_1(X0) ),
% 2.61/1.07      inference(cnf_transformation,[],[f55]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_703,plain,
% 2.61/1.07      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 2.61/1.07      | ~ v1_relat_1(X1_54)
% 2.61/1.07      | v1_relat_1(X0_54) ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_0]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1385,plain,
% 2.61/1.07      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.61/1.07      | v1_relat_1(X0_54)
% 2.61/1.07      | ~ v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
% 2.61/1.07      inference(instantiation,[status(thm)],[c_703]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1506,plain,
% 2.61/1.07      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.61/1.07      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.61/1.07      | v1_relat_1(sK2) ),
% 2.61/1.07      inference(instantiation,[status(thm)],[c_1385]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1,plain,
% 2.61/1.07      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.61/1.07      inference(cnf_transformation,[],[f56]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_702,plain,
% 2.61/1.07      ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_1]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1530,plain,
% 2.61/1.07      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.61/1.07      inference(instantiation,[status(thm)],[c_702]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_2223,plain,
% 2.61/1.07      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.61/1.07      inference(global_propositional_subsumption,
% 2.61/1.07                [status(thm)],
% 2.61/1.07                [c_1452,c_29,c_27,c_1316,c_1453,c_1506,c_1530]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_11,plain,
% 2.61/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.07      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.61/1.07      inference(cnf_transformation,[],[f66]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_694,plain,
% 2.61/1.07      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.61/1.07      | k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54) ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_11]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1144,plain,
% 2.61/1.07      ( k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54)
% 2.61/1.07      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_694]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1573,plain,
% 2.61/1.07      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.61/1.07      inference(superposition,[status(thm)],[c_1172,c_1144]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_26,negated_conjecture,
% 2.61/1.07      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.61/1.07      inference(cnf_transformation,[],[f85]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_688,negated_conjecture,
% 2.61/1.07      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_26]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1169,plain,
% 2.61/1.07      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.61/1.07      inference(light_normalisation,[status(thm)],[c_688,c_683,c_684]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1627,plain,
% 2.61/1.07      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.61/1.07      inference(demodulation,[status(thm)],[c_1573,c_1169]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1629,plain,
% 2.61/1.07      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.61/1.07      inference(demodulation,[status(thm)],[c_1627,c_1573]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_2227,plain,
% 2.61/1.07      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.61/1.07      inference(demodulation,[status(thm)],[c_2223,c_1629]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_18,plain,
% 2.61/1.07      ( ~ v1_funct_2(X0,X1,X2)
% 2.61/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.07      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.61/1.07      | ~ v1_funct_1(X0)
% 2.61/1.07      | ~ v2_funct_1(X0)
% 2.61/1.07      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.61/1.07      inference(cnf_transformation,[],[f75]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_693,plain,
% 2.61/1.07      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 2.61/1.07      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.61/1.07      | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55)))
% 2.61/1.07      | ~ v1_funct_1(X0_54)
% 2.61/1.07      | ~ v2_funct_1(X0_54)
% 2.61/1.07      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_18]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1145,plain,
% 2.61/1.07      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.61/1.07      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.61/1.07      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.61/1.07      | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top
% 2.61/1.07      | v1_funct_1(X0_54) != iProver_top
% 2.61/1.07      | v2_funct_1(X0_54) != iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_2730,plain,
% 2.61/1.07      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.61/1.07      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.61/1.07      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.61/1.07      | v1_funct_1(sK2) != iProver_top
% 2.61/1.07      | v2_funct_1(sK2) != iProver_top ),
% 2.61/1.07      inference(superposition,[status(thm)],[c_2227,c_1145]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_36,plain,
% 2.61/1.07      ( v1_funct_1(sK2) = iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_25,negated_conjecture,
% 2.61/1.07      ( v2_funct_1(sK2) ),
% 2.61/1.07      inference(cnf_transformation,[],[f86]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_39,plain,
% 2.61/1.07      ( v2_funct_1(sK2) = iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1632,plain,
% 2.61/1.07      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.61/1.07      inference(demodulation,[status(thm)],[c_1627,c_1172]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_2226,plain,
% 2.61/1.07      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.61/1.07      inference(demodulation,[status(thm)],[c_2223,c_1632]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1633,plain,
% 2.61/1.07      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.61/1.07      inference(demodulation,[status(thm)],[c_1627,c_1166]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_2228,plain,
% 2.61/1.07      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.61/1.07      inference(demodulation,[status(thm)],[c_2223,c_1633]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_3811,plain,
% 2.61/1.07      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 2.61/1.07      inference(global_propositional_subsumption,
% 2.61/1.07                [status(thm)],
% 2.61/1.07                [c_2730,c_36,c_39,c_2226,c_2228]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_3818,plain,
% 2.61/1.07      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.61/1.07      inference(superposition,[status(thm)],[c_3811,c_1144]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_4,plain,
% 2.61/1.07      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.61/1.07      inference(cnf_transformation,[],[f59]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_494,plain,
% 2.61/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.07      | ~ v1_relat_1(X0)
% 2.61/1.07      | k7_relat_1(X0,X1) = X0 ),
% 2.61/1.07      inference(resolution,[status(thm)],[c_10,c_4]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_682,plain,
% 2.61/1.07      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.61/1.07      | ~ v1_relat_1(X0_54)
% 2.61/1.07      | k7_relat_1(X0_54,X0_55) = X0_54 ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_494]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1153,plain,
% 2.61/1.07      ( k7_relat_1(X0_54,X0_55) = X0_54
% 2.61/1.07      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.61/1.07      | v1_relat_1(X0_54) != iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_682]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_741,plain,
% 2.61/1.07      ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) = iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_702]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_784,plain,
% 2.61/1.07      ( k7_relat_1(X0_54,X0_55) = X0_54
% 2.61/1.07      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.61/1.07      | v1_relat_1(X0_54) != iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_682]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1386,plain,
% 2.61/1.07      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.61/1.07      | v1_relat_1(X0_54) = iProver_top
% 2.61/1.07      | v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) != iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_1385]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_3174,plain,
% 2.61/1.07      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.61/1.07      | k7_relat_1(X0_54,X0_55) = X0_54 ),
% 2.61/1.07      inference(global_propositional_subsumption,
% 2.61/1.07                [status(thm)],
% 2.61/1.07                [c_1153,c_741,c_784,c_1386]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_3175,plain,
% 2.61/1.07      ( k7_relat_1(X0_54,X0_55) = X0_54
% 2.61/1.07      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 2.61/1.07      inference(renaming,[status(thm)],[c_3174]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_3816,plain,
% 2.61/1.07      ( k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_funct_1(sK2) ),
% 2.61/1.07      inference(superposition,[status(thm)],[c_3811,c_3175]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_685,negated_conjecture,
% 2.61/1.07      ( v1_funct_1(sK2) ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_29]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1152,plain,
% 2.61/1.07      ( v1_funct_1(sK2) = iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_685]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_7,plain,
% 2.61/1.07      ( ~ v1_funct_1(X0)
% 2.61/1.07      | ~ v2_funct_1(X0)
% 2.61/1.07      | ~ v1_relat_1(X0)
% 2.61/1.07      | v1_relat_1(k2_funct_1(X0)) ),
% 2.61/1.07      inference(cnf_transformation,[],[f60]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_697,plain,
% 2.61/1.07      ( ~ v1_funct_1(X0_54)
% 2.61/1.07      | ~ v2_funct_1(X0_54)
% 2.61/1.07      | ~ v1_relat_1(X0_54)
% 2.61/1.07      | v1_relat_1(k2_funct_1(X0_54)) ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_7]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1141,plain,
% 2.61/1.07      ( v1_funct_1(X0_54) != iProver_top
% 2.61/1.07      | v2_funct_1(X0_54) != iProver_top
% 2.61/1.07      | v1_relat_1(X0_54) != iProver_top
% 2.61/1.07      | v1_relat_1(k2_funct_1(X0_54)) = iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_697]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_2,plain,
% 2.61/1.07      ( ~ v1_relat_1(X0)
% 2.61/1.07      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.61/1.07      inference(cnf_transformation,[],[f57]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_701,plain,
% 2.61/1.07      ( ~ v1_relat_1(X0_54)
% 2.61/1.07      | k2_relat_1(k7_relat_1(X0_54,X0_55)) = k9_relat_1(X0_54,X0_55) ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_2]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1137,plain,
% 2.61/1.07      ( k2_relat_1(k7_relat_1(X0_54,X0_55)) = k9_relat_1(X0_54,X0_55)
% 2.61/1.07      | v1_relat_1(X0_54) != iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1869,plain,
% 2.61/1.07      ( k2_relat_1(k7_relat_1(k2_funct_1(X0_54),X0_55)) = k9_relat_1(k2_funct_1(X0_54),X0_55)
% 2.61/1.07      | v1_funct_1(X0_54) != iProver_top
% 2.61/1.07      | v2_funct_1(X0_54) != iProver_top
% 2.61/1.07      | v1_relat_1(X0_54) != iProver_top ),
% 2.61/1.07      inference(superposition,[status(thm)],[c_1141,c_1137]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_3308,plain,
% 2.61/1.07      ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0_55)) = k9_relat_1(k2_funct_1(sK2),X0_55)
% 2.61/1.07      | v2_funct_1(sK2) != iProver_top
% 2.61/1.07      | v1_relat_1(sK2) != iProver_top ),
% 2.61/1.07      inference(superposition,[status(thm)],[c_1152,c_1869]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_8,plain,
% 2.61/1.07      ( ~ v1_funct_1(X0)
% 2.61/1.07      | ~ v2_funct_1(X0)
% 2.61/1.07      | ~ v1_relat_1(X0)
% 2.61/1.07      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 2.61/1.07      inference(cnf_transformation,[],[f63]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_696,plain,
% 2.61/1.07      ( ~ v1_funct_1(X0_54)
% 2.61/1.07      | ~ v2_funct_1(X0_54)
% 2.61/1.07      | ~ v1_relat_1(X0_54)
% 2.61/1.07      | k9_relat_1(k2_funct_1(X0_54),X0_55) = k10_relat_1(X0_54,X0_55) ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_8]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1142,plain,
% 2.61/1.07      ( k9_relat_1(k2_funct_1(X0_54),X0_55) = k10_relat_1(X0_54,X0_55)
% 2.61/1.07      | v1_funct_1(X0_54) != iProver_top
% 2.61/1.07      | v2_funct_1(X0_54) != iProver_top
% 2.61/1.07      | v1_relat_1(X0_54) != iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_696]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_2000,plain,
% 2.61/1.07      ( k9_relat_1(k2_funct_1(sK2),X0_55) = k10_relat_1(sK2,X0_55)
% 2.61/1.07      | v2_funct_1(sK2) != iProver_top
% 2.61/1.07      | v1_relat_1(sK2) != iProver_top ),
% 2.61/1.07      inference(superposition,[status(thm)],[c_1152,c_1142]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_38,plain,
% 2.61/1.07      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1507,plain,
% 2.61/1.07      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.61/1.07      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.61/1.07      | v1_relat_1(sK2) = iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_1506]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1531,plain,
% 2.61/1.07      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_1530]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_2120,plain,
% 2.61/1.07      ( k9_relat_1(k2_funct_1(sK2),X0_55) = k10_relat_1(sK2,X0_55) ),
% 2.61/1.07      inference(global_propositional_subsumption,
% 2.61/1.07                [status(thm)],
% 2.61/1.07                [c_2000,c_38,c_39,c_1507,c_1531]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_3330,plain,
% 2.61/1.07      ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0_55)) = k10_relat_1(sK2,X0_55)
% 2.61/1.07      | v2_funct_1(sK2) != iProver_top
% 2.61/1.07      | v1_relat_1(sK2) != iProver_top ),
% 2.61/1.07      inference(light_normalisation,[status(thm)],[c_3308,c_2120]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_3535,plain,
% 2.61/1.07      ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0_55)) = k10_relat_1(sK2,X0_55) ),
% 2.61/1.07      inference(global_propositional_subsumption,
% 2.61/1.07                [status(thm)],
% 2.61/1.07                [c_3330,c_38,c_39,c_1507,c_1531]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_3880,plain,
% 2.61/1.07      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.61/1.07      inference(superposition,[status(thm)],[c_3816,c_3535]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1135,plain,
% 2.61/1.07      ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
% 2.61/1.07      | v1_relat_1(X1_54) != iProver_top
% 2.61/1.07      | v1_relat_1(X0_54) = iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_703]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1488,plain,
% 2.61/1.07      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
% 2.61/1.07      | v1_relat_1(sK2) = iProver_top ),
% 2.61/1.07      inference(superposition,[status(thm)],[c_1172,c_1135]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1756,plain,
% 2.61/1.07      ( v1_relat_1(sK2) = iProver_top ),
% 2.61/1.07      inference(global_propositional_subsumption,
% 2.61/1.07                [status(thm)],
% 2.61/1.07                [c_1488,c_38,c_1507,c_1531]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_3,plain,
% 2.61/1.07      ( ~ v1_relat_1(X0)
% 2.61/1.07      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 2.61/1.07      inference(cnf_transformation,[],[f58]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_700,plain,
% 2.61/1.07      ( ~ v1_relat_1(X0_54)
% 2.61/1.07      | k10_relat_1(X0_54,k2_relat_1(X0_54)) = k1_relat_1(X0_54) ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_3]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1138,plain,
% 2.61/1.07      ( k10_relat_1(X0_54,k2_relat_1(X0_54)) = k1_relat_1(X0_54)
% 2.61/1.07      | v1_relat_1(X0_54) != iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_700]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1762,plain,
% 2.61/1.07      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.61/1.07      inference(superposition,[status(thm)],[c_1756,c_1138]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_3881,plain,
% 2.61/1.07      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.61/1.07      inference(light_normalisation,[status(thm)],[c_3880,c_1762]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_4081,plain,
% 2.61/1.07      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.61/1.07      inference(light_normalisation,[status(thm)],[c_3818,c_3881]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_23,plain,
% 2.61/1.07      ( ~ v1_funct_2(X0,X1,X2)
% 2.61/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.07      | ~ v1_funct_1(X0)
% 2.61/1.07      | ~ v2_funct_1(X0)
% 2.61/1.07      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.61/1.07      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.61/1.07      inference(cnf_transformation,[],[f78]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_690,plain,
% 2.61/1.07      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 2.61/1.07      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.61/1.07      | ~ v1_funct_1(X0_54)
% 2.61/1.07      | ~ v2_funct_1(X0_54)
% 2.61/1.07      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.61/1.07      | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54) ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_23]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1148,plain,
% 2.61/1.07      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.61/1.07      | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54)
% 2.61/1.07      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.61/1.07      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.61/1.07      | v1_funct_1(X0_54) != iProver_top
% 2.61/1.07      | v2_funct_1(X0_54) != iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_690]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_4083,plain,
% 2.61/1.07      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.61/1.07      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.61/1.07      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.61/1.07      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.61/1.07      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.61/1.07      inference(superposition,[status(thm)],[c_4081,c_1148]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_9,plain,
% 2.61/1.07      ( ~ v1_funct_1(X0)
% 2.61/1.07      | ~ v2_funct_1(X0)
% 2.61/1.07      | ~ v1_relat_1(X0)
% 2.61/1.07      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.61/1.07      inference(cnf_transformation,[],[f64]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_695,plain,
% 2.61/1.07      ( ~ v1_funct_1(X0_54)
% 2.61/1.07      | ~ v2_funct_1(X0_54)
% 2.61/1.07      | ~ v1_relat_1(X0_54)
% 2.61/1.07      | k2_funct_1(k2_funct_1(X0_54)) = X0_54 ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_9]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1143,plain,
% 2.61/1.07      ( k2_funct_1(k2_funct_1(X0_54)) = X0_54
% 2.61/1.07      | v1_funct_1(X0_54) != iProver_top
% 2.61/1.07      | v2_funct_1(X0_54) != iProver_top
% 2.61/1.07      | v1_relat_1(X0_54) != iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_695]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1971,plain,
% 2.61/1.07      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.61/1.07      | v2_funct_1(sK2) != iProver_top
% 2.61/1.07      | v1_relat_1(sK2) != iProver_top ),
% 2.61/1.07      inference(superposition,[status(thm)],[c_1152,c_1143]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_763,plain,
% 2.61/1.07      ( ~ v1_funct_1(sK2)
% 2.61/1.07      | ~ v2_funct_1(sK2)
% 2.61/1.07      | ~ v1_relat_1(sK2)
% 2.61/1.07      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.61/1.07      inference(instantiation,[status(thm)],[c_695]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_2113,plain,
% 2.61/1.07      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.61/1.07      inference(global_propositional_subsumption,
% 2.61/1.07                [status(thm)],
% 2.61/1.07                [c_1971,c_29,c_27,c_25,c_763,c_1506,c_1530]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_4103,plain,
% 2.61/1.07      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 2.61/1.07      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.61/1.07      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.61/1.07      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.61/1.07      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.61/1.07      inference(light_normalisation,[status(thm)],[c_4083,c_2113]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_5,plain,
% 2.61/1.07      ( ~ v1_funct_1(X0)
% 2.61/1.07      | ~ v2_funct_1(X0)
% 2.61/1.07      | v2_funct_1(k2_funct_1(X0))
% 2.61/1.07      | ~ v1_relat_1(X0) ),
% 2.61/1.07      inference(cnf_transformation,[],[f62]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_699,plain,
% 2.61/1.07      ( ~ v1_funct_1(X0_54)
% 2.61/1.07      | ~ v2_funct_1(X0_54)
% 2.61/1.07      | v2_funct_1(k2_funct_1(X0_54))
% 2.61/1.07      | ~ v1_relat_1(X0_54) ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_5]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_750,plain,
% 2.61/1.07      ( v1_funct_1(X0_54) != iProver_top
% 2.61/1.07      | v2_funct_1(X0_54) != iProver_top
% 2.61/1.07      | v2_funct_1(k2_funct_1(X0_54)) = iProver_top
% 2.61/1.07      | v1_relat_1(X0_54) != iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_699]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_752,plain,
% 2.61/1.07      ( v1_funct_1(sK2) != iProver_top
% 2.61/1.07      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.61/1.07      | v2_funct_1(sK2) != iProver_top
% 2.61/1.07      | v1_relat_1(sK2) != iProver_top ),
% 2.61/1.07      inference(instantiation,[status(thm)],[c_750]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_6,plain,
% 2.61/1.07      ( ~ v1_funct_1(X0)
% 2.61/1.07      | v1_funct_1(k2_funct_1(X0))
% 2.61/1.07      | ~ v2_funct_1(X0)
% 2.61/1.07      | ~ v1_relat_1(X0) ),
% 2.61/1.07      inference(cnf_transformation,[],[f61]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_698,plain,
% 2.61/1.07      ( ~ v1_funct_1(X0_54)
% 2.61/1.07      | v1_funct_1(k2_funct_1(X0_54))
% 2.61/1.07      | ~ v2_funct_1(X0_54)
% 2.61/1.07      | ~ v1_relat_1(X0_54) ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_6]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_753,plain,
% 2.61/1.07      ( v1_funct_1(X0_54) != iProver_top
% 2.61/1.07      | v1_funct_1(k2_funct_1(X0_54)) = iProver_top
% 2.61/1.07      | v2_funct_1(X0_54) != iProver_top
% 2.61/1.07      | v1_relat_1(X0_54) != iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_698]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_755,plain,
% 2.61/1.07      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.61/1.07      | v1_funct_1(sK2) != iProver_top
% 2.61/1.07      | v2_funct_1(sK2) != iProver_top
% 2.61/1.07      | v1_relat_1(sK2) != iProver_top ),
% 2.61/1.07      inference(instantiation,[status(thm)],[c_753]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_19,plain,
% 2.61/1.07      ( ~ v1_funct_2(X0,X1,X2)
% 2.61/1.07      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.61/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.07      | ~ v1_funct_1(X0)
% 2.61/1.07      | ~ v2_funct_1(X0)
% 2.61/1.07      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.61/1.07      inference(cnf_transformation,[],[f74]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_692,plain,
% 2.61/1.07      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 2.61/1.07      | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55)
% 2.61/1.07      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.61/1.07      | ~ v1_funct_1(X0_54)
% 2.61/1.07      | ~ v2_funct_1(X0_54)
% 2.61/1.07      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_19]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_1146,plain,
% 2.61/1.07      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.61/1.07      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.61/1.07      | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55) = iProver_top
% 2.61/1.07      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.61/1.07      | v1_funct_1(X0_54) != iProver_top
% 2.61/1.07      | v2_funct_1(X0_54) != iProver_top ),
% 2.61/1.07      inference(predicate_to_equality,[status(thm)],[c_692]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_2729,plain,
% 2.61/1.07      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 2.61/1.07      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.61/1.07      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.61/1.07      | v1_funct_1(sK2) != iProver_top
% 2.61/1.07      | v2_funct_1(sK2) != iProver_top ),
% 2.61/1.07      inference(superposition,[status(thm)],[c_2227,c_1146]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_4414,plain,
% 2.61/1.07      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.61/1.07      inference(global_propositional_subsumption,
% 2.61/1.07                [status(thm)],
% 2.61/1.07                [c_4103,c_36,c_38,c_39,c_752,c_755,c_1507,c_1531,c_2226,
% 2.61/1.07                 c_2228,c_2729,c_2730]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_2728,plain,
% 2.61/1.07      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.61/1.07      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.61/1.07      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.61/1.07      | v1_funct_1(sK2) != iProver_top
% 2.61/1.07      | v2_funct_1(sK2) != iProver_top ),
% 2.61/1.07      inference(superposition,[status(thm)],[c_2227,c_1148]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_2947,plain,
% 2.61/1.07      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.61/1.07      inference(global_propositional_subsumption,
% 2.61/1.07                [status(thm)],
% 2.61/1.07                [c_2728,c_36,c_39,c_2226,c_2228]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_16,plain,
% 2.61/1.07      ( r2_funct_2(X0,X1,X2,X2)
% 2.61/1.07      | ~ v1_funct_2(X2,X0,X1)
% 2.61/1.07      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.61/1.07      | ~ v1_funct_1(X2) ),
% 2.61/1.07      inference(cnf_transformation,[],[f89]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_24,negated_conjecture,
% 2.61/1.07      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.61/1.07      inference(cnf_transformation,[],[f87]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_512,plain,
% 2.61/1.07      ( ~ v1_funct_2(X0,X1,X2)
% 2.61/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.07      | ~ v1_funct_1(X0)
% 2.61/1.07      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 2.61/1.07      | u1_struct_0(sK1) != X2
% 2.61/1.07      | u1_struct_0(sK0) != X1
% 2.61/1.07      | sK2 != X0 ),
% 2.61/1.07      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_513,plain,
% 2.61/1.07      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.61/1.07      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.61/1.07      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.61/1.07      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.61/1.07      inference(unflattening,[status(thm)],[c_512]) ).
% 2.61/1.07  
% 2.61/1.07  cnf(c_680,plain,
% 2.61/1.07      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.61/1.07      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.61/1.07      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.61/1.07      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.61/1.07      inference(subtyping,[status(esa)],[c_513]) ).
% 2.61/1.08  
% 2.61/1.08  cnf(c_1155,plain,
% 2.61/1.08      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.61/1.08      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.61/1.08      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.61/1.08      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 2.61/1.08      inference(predicate_to_equality,[status(thm)],[c_680]) ).
% 2.61/1.08  
% 2.61/1.08  cnf(c_1298,plain,
% 2.61/1.08      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.61/1.08      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.61/1.08      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.61/1.08      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.61/1.08      inference(light_normalisation,[status(thm)],[c_1155,c_683,c_684]) ).
% 2.61/1.08  
% 2.61/1.08  cnf(c_1630,plain,
% 2.61/1.08      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 2.61/1.08      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.61/1.08      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.61/1.08      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.61/1.08      inference(demodulation,[status(thm)],[c_1627,c_1298]) ).
% 2.61/1.08  
% 2.61/1.08  cnf(c_2289,plain,
% 2.61/1.08      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
% 2.61/1.08      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.61/1.08      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.61/1.08      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.61/1.08      inference(light_normalisation,[status(thm)],[c_1630,c_2223]) ).
% 2.61/1.08  
% 2.61/1.08  cnf(c_2950,plain,
% 2.61/1.08      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 2.61/1.08      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.61/1.08      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.61/1.08      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.61/1.08      inference(demodulation,[status(thm)],[c_2947,c_2289]) ).
% 2.61/1.08  
% 2.61/1.08  cnf(c_4417,plain,
% 2.61/1.08      ( sK2 != sK2
% 2.61/1.08      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.61/1.08      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.61/1.08      | v1_funct_1(sK2) != iProver_top ),
% 2.61/1.08      inference(demodulation,[status(thm)],[c_4414,c_2950]) ).
% 2.61/1.08  
% 2.61/1.08  cnf(c_705,plain,( X0_54 = X0_54 ),theory(equality) ).
% 2.61/1.08  
% 2.61/1.08  cnf(c_737,plain,
% 2.61/1.08      ( sK2 = sK2 ),
% 2.61/1.08      inference(instantiation,[status(thm)],[c_705]) ).
% 2.61/1.08  
% 2.61/1.08  cnf(contradiction,plain,
% 2.61/1.08      ( $false ),
% 2.61/1.08      inference(minisat,[status(thm)],[c_4417,c_2228,c_2226,c_737,c_36]) ).
% 2.61/1.08  
% 2.61/1.08  
% 2.61/1.08  % SZS output end CNFRefutation for theBenchmark.p
% 2.61/1.08  
% 2.61/1.08  ------                               Statistics
% 2.61/1.08  
% 2.61/1.08  ------ General
% 2.61/1.08  
% 2.61/1.08  abstr_ref_over_cycles:                  0
% 2.61/1.08  abstr_ref_under_cycles:                 0
% 2.61/1.08  gc_basic_clause_elim:                   0
% 2.61/1.08  forced_gc_time:                         0
% 2.61/1.08  parsing_time:                           0.008
% 2.61/1.08  unif_index_cands_time:                  0.
% 2.61/1.08  unif_index_add_time:                    0.
% 2.61/1.08  orderings_time:                         0.
% 2.61/1.08  out_proof_time:                         0.014
% 2.61/1.08  total_time:                             0.18
% 2.61/1.08  num_of_symbols:                         58
% 2.61/1.08  num_of_terms:                           4099
% 2.61/1.08  
% 2.61/1.08  ------ Preprocessing
% 2.61/1.08  
% 2.61/1.08  num_of_splits:                          0
% 2.61/1.08  num_of_split_atoms:                     0
% 2.61/1.08  num_of_reused_defs:                     0
% 2.61/1.08  num_eq_ax_congr_red:                    19
% 2.61/1.08  num_of_sem_filtered_clauses:            1
% 2.61/1.08  num_of_subtypes:                        4
% 2.61/1.08  monotx_restored_types:                  1
% 2.61/1.08  sat_num_of_epr_types:                   0
% 2.61/1.08  sat_num_of_non_cyclic_types:            0
% 2.61/1.08  sat_guarded_non_collapsed_types:        1
% 2.61/1.08  num_pure_diseq_elim:                    0
% 2.61/1.08  simp_replaced_by:                       0
% 2.61/1.08  res_preprocessed:                       141
% 2.61/1.08  prep_upred:                             0
% 2.61/1.08  prep_unflattend:                        15
% 2.61/1.08  smt_new_axioms:                         0
% 2.61/1.08  pred_elim_cands:                        5
% 2.61/1.08  pred_elim:                              6
% 2.61/1.08  pred_elim_cl:                           8
% 2.61/1.08  pred_elim_cycles:                       9
% 2.61/1.08  merged_defs:                            0
% 2.61/1.08  merged_defs_ncl:                        0
% 2.61/1.08  bin_hyper_res:                          0
% 2.61/1.08  prep_cycles:                            4
% 2.61/1.08  pred_elim_time:                         0.006
% 2.61/1.08  splitting_time:                         0.
% 2.61/1.08  sem_filter_time:                        0.
% 2.61/1.08  monotx_time:                            0.001
% 2.61/1.08  subtype_inf_time:                       0.002
% 2.61/1.08  
% 2.61/1.08  ------ Problem properties
% 2.61/1.08  
% 2.61/1.08  clauses:                                24
% 2.61/1.08  conjectures:                            5
% 2.61/1.08  epr:                                    2
% 2.61/1.08  horn:                                   24
% 2.61/1.08  ground:                                 8
% 2.61/1.08  unary:                                  8
% 2.61/1.08  binary:                                 3
% 2.61/1.08  lits:                                   73
% 2.61/1.08  lits_eq:                                16
% 2.61/1.08  fd_pure:                                0
% 2.61/1.08  fd_pseudo:                              0
% 2.61/1.08  fd_cond:                                0
% 2.61/1.08  fd_pseudo_cond:                         1
% 2.61/1.08  ac_symbols:                             0
% 2.61/1.08  
% 2.61/1.08  ------ Propositional Solver
% 2.61/1.08  
% 2.61/1.08  prop_solver_calls:                      29
% 2.61/1.08  prop_fast_solver_calls:                 1084
% 2.61/1.08  smt_solver_calls:                       0
% 2.61/1.08  smt_fast_solver_calls:                  0
% 2.61/1.08  prop_num_of_clauses:                    1683
% 2.61/1.08  prop_preprocess_simplified:             5573
% 2.61/1.08  prop_fo_subsumed:                       46
% 2.61/1.08  prop_solver_time:                       0.
% 2.61/1.08  smt_solver_time:                        0.
% 2.61/1.08  smt_fast_solver_time:                   0.
% 2.61/1.08  prop_fast_solver_time:                  0.
% 2.61/1.08  prop_unsat_core_time:                   0.
% 2.61/1.08  
% 2.61/1.08  ------ QBF
% 2.61/1.08  
% 2.61/1.08  qbf_q_res:                              0
% 2.61/1.08  qbf_num_tautologies:                    0
% 2.61/1.08  qbf_prep_cycles:                        0
% 2.61/1.08  
% 2.61/1.08  ------ BMC1
% 2.61/1.08  
% 2.61/1.08  bmc1_current_bound:                     -1
% 2.61/1.08  bmc1_last_solved_bound:                 -1
% 2.61/1.08  bmc1_unsat_core_size:                   -1
% 2.61/1.08  bmc1_unsat_core_parents_size:           -1
% 2.61/1.08  bmc1_merge_next_fun:                    0
% 2.61/1.08  bmc1_unsat_core_clauses_time:           0.
% 2.61/1.08  
% 2.61/1.08  ------ Instantiation
% 2.61/1.08  
% 2.61/1.08  inst_num_of_clauses:                    611
% 2.61/1.08  inst_num_in_passive:                    56
% 2.61/1.08  inst_num_in_active:                     295
% 2.61/1.08  inst_num_in_unprocessed:                260
% 2.61/1.08  inst_num_of_loops:                      330
% 2.61/1.08  inst_num_of_learning_restarts:          0
% 2.61/1.08  inst_num_moves_active_passive:          31
% 2.61/1.08  inst_lit_activity:                      0
% 2.61/1.08  inst_lit_activity_moves:                0
% 2.61/1.08  inst_num_tautologies:                   0
% 2.61/1.08  inst_num_prop_implied:                  0
% 2.61/1.08  inst_num_existing_simplified:           0
% 2.61/1.08  inst_num_eq_res_simplified:             0
% 2.61/1.08  inst_num_child_elim:                    0
% 2.61/1.08  inst_num_of_dismatching_blockings:      132
% 2.61/1.08  inst_num_of_non_proper_insts:           534
% 2.61/1.08  inst_num_of_duplicates:                 0
% 2.61/1.08  inst_inst_num_from_inst_to_res:         0
% 2.61/1.08  inst_dismatching_checking_time:         0.
% 2.61/1.08  
% 2.61/1.08  ------ Resolution
% 2.61/1.08  
% 2.61/1.08  res_num_of_clauses:                     0
% 2.61/1.08  res_num_in_passive:                     0
% 2.61/1.08  res_num_in_active:                      0
% 2.61/1.08  res_num_of_loops:                       145
% 2.61/1.08  res_forward_subset_subsumed:            54
% 2.61/1.08  res_backward_subset_subsumed:           0
% 2.61/1.08  res_forward_subsumed:                   0
% 2.61/1.08  res_backward_subsumed:                  0
% 2.61/1.08  res_forward_subsumption_resolution:     1
% 2.61/1.08  res_backward_subsumption_resolution:    0
% 2.61/1.08  res_clause_to_clause_subsumption:       140
% 2.61/1.08  res_orphan_elimination:                 0
% 2.61/1.08  res_tautology_del:                      57
% 2.61/1.08  res_num_eq_res_simplified:              0
% 2.61/1.08  res_num_sel_changes:                    0
% 2.61/1.08  res_moves_from_active_to_pass:          0
% 2.61/1.08  
% 2.61/1.08  ------ Superposition
% 2.61/1.08  
% 2.61/1.08  sup_time_total:                         0.
% 2.61/1.08  sup_time_generating:                    0.
% 2.61/1.08  sup_time_sim_full:                      0.
% 2.61/1.08  sup_time_sim_immed:                     0.
% 2.61/1.08  
% 2.61/1.08  sup_num_of_clauses:                     58
% 2.61/1.08  sup_num_in_active:                      50
% 2.61/1.08  sup_num_in_passive:                     8
% 2.61/1.08  sup_num_of_loops:                       64
% 2.61/1.08  sup_fw_superposition:                   28
% 2.61/1.08  sup_bw_superposition:                   29
% 2.61/1.08  sup_immediate_simplified:               26
% 2.61/1.08  sup_given_eliminated:                   0
% 2.61/1.08  comparisons_done:                       0
% 2.61/1.08  comparisons_avoided:                    0
% 2.61/1.08  
% 2.61/1.08  ------ Simplifications
% 2.61/1.08  
% 2.61/1.08  
% 2.61/1.08  sim_fw_subset_subsumed:                 4
% 2.61/1.08  sim_bw_subset_subsumed:                 0
% 2.61/1.08  sim_fw_subsumed:                        3
% 2.61/1.08  sim_bw_subsumed:                        0
% 2.61/1.08  sim_fw_subsumption_res:                 0
% 2.61/1.08  sim_bw_subsumption_res:                 0
% 2.61/1.08  sim_tautology_del:                      0
% 2.61/1.08  sim_eq_tautology_del:                   13
% 2.61/1.08  sim_eq_res_simp:                        0
% 2.61/1.08  sim_fw_demodulated:                     1
% 2.61/1.08  sim_bw_demodulated:                     14
% 2.61/1.08  sim_light_normalised:                   28
% 2.61/1.08  sim_joinable_taut:                      0
% 2.61/1.08  sim_joinable_simp:                      0
% 2.61/1.08  sim_ac_normalised:                      0
% 2.61/1.08  sim_smt_subsumption:                    0
% 2.61/1.08  
%------------------------------------------------------------------------------
