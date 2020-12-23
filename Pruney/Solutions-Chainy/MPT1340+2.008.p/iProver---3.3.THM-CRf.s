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
% DateTime   : Thu Dec  3 12:17:22 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :  220 (18463 expanded)
%              Number of clauses        :  141 (5620 expanded)
%              Number of leaves         :   20 (5106 expanded)
%              Depth                    :   31
%              Number of atoms          :  801 (114735 expanded)
%              Number of equality atoms :  302 (18645 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f18])).

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
    inference(flattening,[],[f46])).

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,
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

fof(f52,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f47,f51,f50,f49])).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f75,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f78,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f80,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

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

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f85,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f54,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f60,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f62,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f63,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_695,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1212,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_695])).

cnf(c_22,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_33,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_392,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_393,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_690,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_393])).

cnf(c_31,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_387,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_388,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_691,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_388])).

cnf(c_1237,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1212,c_690,c_691])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_23,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_374,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_375,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_46,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_377,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_375,c_32,c_31,c_46])).

cnf(c_399,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_377])).

cnf(c_400,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_17,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_457,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_12,c_17])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_461,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_457,c_17,c_12,c_11])).

cnf(c_462,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_461])).

cnf(c_501,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_400,c_462])).

cnf(c_688,plain,
    ( ~ v1_funct_2(X0_53,X0_54,k2_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | k1_relat_1(X0_53) = X0_54 ),
    inference(subtyping,[status(esa)],[c_501])).

cnf(c_1218,plain,
    ( k1_relat_1(X0_53) = X0_54
    | v1_funct_2(X0_53,X0_54,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_688])).

cnf(c_1647,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_54))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_1218])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_37,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_694,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1213,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_694])).

cnf(c_1231,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1213,c_690,c_691])).

cnf(c_1726,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_54))) != iProver_top
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1647,c_37,c_1231])).

cnf(c_1727,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_54))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1726])).

cnf(c_1734,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1237,c_1727])).

cnf(c_1737,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1734,c_1237])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_701,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1207,plain,
    ( k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_2250,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1737,c_1207])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_696,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1234,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_696,c_690,c_691])).

cnf(c_1739,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1734,c_1234])).

cnf(c_2422,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2250,c_1739])).

cnf(c_2812,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2422,c_2250])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_698,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | k2_relset_1(X0_54,X1_54,X0_53) != X1_54
    | k2_tops_2(X0_54,X1_54,X0_53) = k2_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1210,plain,
    ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
    | k2_tops_2(X0_54,X1_54,X0_53) = k2_funct_1(X0_53)
    | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_698])).

cnf(c_3610,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2812,c_1210])).

cnf(c_26,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_40,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2813,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2422,c_1737])).

cnf(c_1738,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1734,c_1231])).

cnf(c_2814,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2422,c_1738])).

cnf(c_3845,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3610,c_37,c_40,c_2813,c_2814])).

cnf(c_18,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_25,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_422,plain,
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
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_423,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_689,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_423])).

cnf(c_715,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sP0_iProver_split
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_689])).

cnf(c_1216,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_715])).

cnf(c_1389,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1216,c_690,c_691])).

cnf(c_714,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_689])).

cnf(c_1217,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_714])).

cnf(c_1306,plain,
    ( v1_funct_2(X0_53,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1217,c_690,c_691])).

cnf(c_1395,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1389,c_1306])).

cnf(c_1736,plain,
    ( k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1734,c_1395])).

cnf(c_3722,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1736,c_2422])).

cnf(c_3848,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3845,c_3722])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_713,plain,
    ( ~ v1_relat_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k2_funct_1(X0_53)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_756,plain,
    ( v1_relat_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_funct_1(X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_758,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_756])).

cnf(c_702,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1456,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_702])).

cnf(c_1457,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1456])).

cnf(c_697,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1211,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_697])).

cnf(c_6,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_707,plain,
    ( ~ v2_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1201,plain,
    ( k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53)
    | v2_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_707])).

cnf(c_2014,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1211,c_1201])).

cnf(c_771,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(c_2142,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2014,c_30,c_28,c_26,c_771,c_1456])).

cnf(c_5,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_708,plain,
    ( v2_funct_1(X0_53)
    | ~ v2_funct_1(k5_relat_1(X0_53,X1_53))
    | ~ v1_relat_1(X0_53)
    | ~ v1_relat_1(X1_53)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | k1_relat_1(X1_53) != k2_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1200,plain,
    ( k1_relat_1(X0_53) != k2_relat_1(X1_53)
    | v2_funct_1(X1_53) = iProver_top
    | v2_funct_1(k5_relat_1(X1_53,X0_53)) != iProver_top
    | v1_relat_1(X1_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(c_2518,plain,
    ( k1_relat_1(X0_53) != k1_relat_1(sK2)
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_53)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2142,c_1200])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_712,plain,
    ( ~ v1_relat_1(X0_53)
    | v1_relat_1(k2_funct_1(X0_53))
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_759,plain,
    ( v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(k2_funct_1(X0_53)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_712])).

cnf(c_761,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_759])).

cnf(c_3074,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | k1_relat_1(X0_53) != k1_relat_1(sK2)
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_53)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2518,c_37,c_39,c_758,c_761,c_1457])).

cnf(c_3075,plain,
    ( k1_relat_1(X0_53) != k1_relat_1(sK2)
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_53)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_3074])).

cnf(c_3086,plain,
    ( v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3075])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_705,plain,
    ( ~ v2_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | k5_relat_1(k2_funct_1(X0_53),X0_53) = k6_relat_1(k2_relat_1(X0_53)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1203,plain,
    ( k5_relat_1(k2_funct_1(X0_53),X0_53) = k6_relat_1(k2_relat_1(X0_53))
    | v2_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_705])).

cnf(c_2556,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1211,c_1203])).

cnf(c_777,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_2728,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2556,c_30,c_28,c_26,c_777,c_1456])).

cnf(c_3091,plain,
    ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3086,c_2728])).

cnf(c_3098,plain,
    ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3091,c_37,c_39,c_1457])).

cnf(c_2,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_711,plain,
    ( v2_funct_1(k6_relat_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1197,plain,
    ( v2_funct_1(k6_relat_1(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_711])).

cnf(c_3104,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3098,c_1197])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_700,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54)))
    | ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1208,plain,
    ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
    | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54))) = iProver_top
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_700])).

cnf(c_3609,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2812,c_1208])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_699,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | v1_funct_2(k2_funct_1(X0_53),X1_54,X0_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1209,plain,
    ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
    | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | v1_funct_2(k2_funct_1(X0_53),X1_54,X0_54) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_699])).

cnf(c_3611,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2812,c_1209])).

cnf(c_4087,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3609,c_37,c_40,c_2813,c_2814])).

cnf(c_4093,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4087,c_1207])).

cnf(c_4098,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4093,c_2142])).

cnf(c_4175,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4098,c_1210])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_703,plain,
    ( ~ v2_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | k2_funct_1(k2_funct_1(X0_53)) = X0_53 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1205,plain,
    ( k2_funct_1(k2_funct_1(X0_53)) = X0_53
    | v2_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_703])).

cnf(c_1908,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1211,c_1205])).

cnf(c_783,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(c_2136,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1908,c_30,c_28,c_26,c_783,c_1456])).

cnf(c_4188,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4175,c_2136])).

cnf(c_4304,plain,
    ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3848,c_37,c_39,c_40,c_758,c_1457,c_2813,c_2814,c_3104,c_3609,c_3611,c_4188])).

cnf(c_4202,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4188,c_37,c_39,c_40,c_758,c_1457,c_2813,c_2814,c_3104,c_3609,c_3611])).

cnf(c_4308,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4304,c_4202])).

cnf(c_693,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1214,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_4312,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4308,c_1214,c_2813,c_2814])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.06  % Command    : iproveropt_run.sh %d %s
% 0.06/0.25  % Computer   : n001.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 17:50:15 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.25  % Running in FOF mode
% 2.07/0.88  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/0.88  
% 2.07/0.88  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.07/0.88  
% 2.07/0.88  ------  iProver source info
% 2.07/0.88  
% 2.07/0.88  git: date: 2020-06-30 10:37:57 +0100
% 2.07/0.88  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.07/0.88  git: non_committed_changes: false
% 2.07/0.88  git: last_make_outside_of_git: false
% 2.07/0.88  
% 2.07/0.88  ------ 
% 2.07/0.88  
% 2.07/0.88  ------ Input Options
% 2.07/0.88  
% 2.07/0.88  --out_options                           all
% 2.07/0.88  --tptp_safe_out                         true
% 2.07/0.88  --problem_path                          ""
% 2.07/0.88  --include_path                          ""
% 2.07/0.88  --clausifier                            res/vclausify_rel
% 2.07/0.88  --clausifier_options                    --mode clausify
% 2.07/0.88  --stdin                                 false
% 2.07/0.88  --stats_out                             all
% 2.07/0.88  
% 2.07/0.88  ------ General Options
% 2.07/0.88  
% 2.07/0.88  --fof                                   false
% 2.07/0.88  --time_out_real                         305.
% 2.07/0.88  --time_out_virtual                      -1.
% 2.07/0.88  --symbol_type_check                     false
% 2.07/0.88  --clausify_out                          false
% 2.07/0.88  --sig_cnt_out                           false
% 2.07/0.88  --trig_cnt_out                          false
% 2.07/0.88  --trig_cnt_out_tolerance                1.
% 2.07/0.88  --trig_cnt_out_sk_spl                   false
% 2.07/0.88  --abstr_cl_out                          false
% 2.07/0.88  
% 2.07/0.88  ------ Global Options
% 2.07/0.88  
% 2.07/0.88  --schedule                              default
% 2.07/0.88  --add_important_lit                     false
% 2.07/0.88  --prop_solver_per_cl                    1000
% 2.07/0.88  --min_unsat_core                        false
% 2.07/0.88  --soft_assumptions                      false
% 2.07/0.88  --soft_lemma_size                       3
% 2.07/0.88  --prop_impl_unit_size                   0
% 2.07/0.88  --prop_impl_unit                        []
% 2.07/0.88  --share_sel_clauses                     true
% 2.07/0.88  --reset_solvers                         false
% 2.07/0.88  --bc_imp_inh                            [conj_cone]
% 2.07/0.88  --conj_cone_tolerance                   3.
% 2.07/0.88  --extra_neg_conj                        none
% 2.07/0.88  --large_theory_mode                     true
% 2.07/0.88  --prolific_symb_bound                   200
% 2.07/0.88  --lt_threshold                          2000
% 2.07/0.88  --clause_weak_htbl                      true
% 2.07/0.88  --gc_record_bc_elim                     false
% 2.07/0.88  
% 2.07/0.88  ------ Preprocessing Options
% 2.07/0.88  
% 2.07/0.88  --preprocessing_flag                    true
% 2.07/0.88  --time_out_prep_mult                    0.1
% 2.07/0.88  --splitting_mode                        input
% 2.07/0.88  --splitting_grd                         true
% 2.07/0.88  --splitting_cvd                         false
% 2.07/0.88  --splitting_cvd_svl                     false
% 2.07/0.88  --splitting_nvd                         32
% 2.07/0.88  --sub_typing                            true
% 2.07/0.88  --prep_gs_sim                           true
% 2.07/0.88  --prep_unflatten                        true
% 2.07/0.88  --prep_res_sim                          true
% 2.07/0.88  --prep_upred                            true
% 2.07/0.88  --prep_sem_filter                       exhaustive
% 2.07/0.88  --prep_sem_filter_out                   false
% 2.07/0.88  --pred_elim                             true
% 2.07/0.88  --res_sim_input                         true
% 2.07/0.88  --eq_ax_congr_red                       true
% 2.07/0.88  --pure_diseq_elim                       true
% 2.07/0.88  --brand_transform                       false
% 2.07/0.88  --non_eq_to_eq                          false
% 2.07/0.88  --prep_def_merge                        true
% 2.07/0.88  --prep_def_merge_prop_impl              false
% 2.07/0.88  --prep_def_merge_mbd                    true
% 2.07/0.88  --prep_def_merge_tr_red                 false
% 2.07/0.88  --prep_def_merge_tr_cl                  false
% 2.07/0.88  --smt_preprocessing                     true
% 2.07/0.88  --smt_ac_axioms                         fast
% 2.07/0.88  --preprocessed_out                      false
% 2.07/0.88  --preprocessed_stats                    false
% 2.07/0.88  
% 2.07/0.88  ------ Abstraction refinement Options
% 2.07/0.88  
% 2.07/0.88  --abstr_ref                             []
% 2.07/0.88  --abstr_ref_prep                        false
% 2.07/0.88  --abstr_ref_until_sat                   false
% 2.07/0.88  --abstr_ref_sig_restrict                funpre
% 2.07/0.88  --abstr_ref_af_restrict_to_split_sk     false
% 2.07/0.88  --abstr_ref_under                       []
% 2.07/0.88  
% 2.07/0.88  ------ SAT Options
% 2.07/0.88  
% 2.07/0.88  --sat_mode                              false
% 2.07/0.88  --sat_fm_restart_options                ""
% 2.07/0.88  --sat_gr_def                            false
% 2.07/0.88  --sat_epr_types                         true
% 2.07/0.88  --sat_non_cyclic_types                  false
% 2.07/0.88  --sat_finite_models                     false
% 2.07/0.88  --sat_fm_lemmas                         false
% 2.07/0.88  --sat_fm_prep                           false
% 2.07/0.88  --sat_fm_uc_incr                        true
% 2.07/0.88  --sat_out_model                         small
% 2.07/0.88  --sat_out_clauses                       false
% 2.07/0.88  
% 2.07/0.88  ------ QBF Options
% 2.07/0.88  
% 2.07/0.88  --qbf_mode                              false
% 2.07/0.88  --qbf_elim_univ                         false
% 2.07/0.88  --qbf_dom_inst                          none
% 2.07/0.88  --qbf_dom_pre_inst                      false
% 2.07/0.88  --qbf_sk_in                             false
% 2.07/0.88  --qbf_pred_elim                         true
% 2.07/0.88  --qbf_split                             512
% 2.07/0.88  
% 2.07/0.88  ------ BMC1 Options
% 2.07/0.88  
% 2.07/0.88  --bmc1_incremental                      false
% 2.07/0.88  --bmc1_axioms                           reachable_all
% 2.07/0.88  --bmc1_min_bound                        0
% 2.07/0.88  --bmc1_max_bound                        -1
% 2.07/0.88  --bmc1_max_bound_default                -1
% 2.07/0.88  --bmc1_symbol_reachability              true
% 2.07/0.88  --bmc1_property_lemmas                  false
% 2.07/0.88  --bmc1_k_induction                      false
% 2.07/0.88  --bmc1_non_equiv_states                 false
% 2.07/0.88  --bmc1_deadlock                         false
% 2.07/0.88  --bmc1_ucm                              false
% 2.07/0.88  --bmc1_add_unsat_core                   none
% 2.07/0.88  --bmc1_unsat_core_children              false
% 2.07/0.88  --bmc1_unsat_core_extrapolate_axioms    false
% 2.07/0.88  --bmc1_out_stat                         full
% 2.07/0.88  --bmc1_ground_init                      false
% 2.07/0.88  --bmc1_pre_inst_next_state              false
% 2.07/0.88  --bmc1_pre_inst_state                   false
% 2.07/0.88  --bmc1_pre_inst_reach_state             false
% 2.07/0.88  --bmc1_out_unsat_core                   false
% 2.07/0.88  --bmc1_aig_witness_out                  false
% 2.07/0.88  --bmc1_verbose                          false
% 2.07/0.88  --bmc1_dump_clauses_tptp                false
% 2.07/0.88  --bmc1_dump_unsat_core_tptp             false
% 2.07/0.88  --bmc1_dump_file                        -
% 2.07/0.88  --bmc1_ucm_expand_uc_limit              128
% 2.07/0.88  --bmc1_ucm_n_expand_iterations          6
% 2.07/0.88  --bmc1_ucm_extend_mode                  1
% 2.07/0.88  --bmc1_ucm_init_mode                    2
% 2.07/0.88  --bmc1_ucm_cone_mode                    none
% 2.07/0.88  --bmc1_ucm_reduced_relation_type        0
% 2.07/0.88  --bmc1_ucm_relax_model                  4
% 2.07/0.88  --bmc1_ucm_full_tr_after_sat            true
% 2.07/0.88  --bmc1_ucm_expand_neg_assumptions       false
% 2.07/0.88  --bmc1_ucm_layered_model                none
% 2.07/0.88  --bmc1_ucm_max_lemma_size               10
% 2.07/0.88  
% 2.07/0.88  ------ AIG Options
% 2.07/0.88  
% 2.07/0.88  --aig_mode                              false
% 2.07/0.88  
% 2.07/0.88  ------ Instantiation Options
% 2.07/0.88  
% 2.07/0.88  --instantiation_flag                    true
% 2.07/0.88  --inst_sos_flag                         false
% 2.07/0.88  --inst_sos_phase                        true
% 2.07/0.88  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.07/0.88  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.07/0.88  --inst_lit_sel_side                     num_symb
% 2.07/0.88  --inst_solver_per_active                1400
% 2.07/0.88  --inst_solver_calls_frac                1.
% 2.07/0.88  --inst_passive_queue_type               priority_queues
% 2.07/0.88  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.07/0.88  --inst_passive_queues_freq              [25;2]
% 2.07/0.88  --inst_dismatching                      true
% 2.07/0.88  --inst_eager_unprocessed_to_passive     true
% 2.07/0.88  --inst_prop_sim_given                   true
% 2.07/0.88  --inst_prop_sim_new                     false
% 2.07/0.88  --inst_subs_new                         false
% 2.07/0.88  --inst_eq_res_simp                      false
% 2.07/0.88  --inst_subs_given                       false
% 2.07/0.88  --inst_orphan_elimination               true
% 2.07/0.88  --inst_learning_loop_flag               true
% 2.07/0.88  --inst_learning_start                   3000
% 2.07/0.88  --inst_learning_factor                  2
% 2.07/0.88  --inst_start_prop_sim_after_learn       3
% 2.07/0.88  --inst_sel_renew                        solver
% 2.07/0.88  --inst_lit_activity_flag                true
% 2.07/0.88  --inst_restr_to_given                   false
% 2.07/0.88  --inst_activity_threshold               500
% 2.07/0.88  --inst_out_proof                        true
% 2.07/0.88  
% 2.07/0.88  ------ Resolution Options
% 2.07/0.88  
% 2.07/0.88  --resolution_flag                       true
% 2.07/0.88  --res_lit_sel                           adaptive
% 2.07/0.88  --res_lit_sel_side                      none
% 2.07/0.88  --res_ordering                          kbo
% 2.07/0.88  --res_to_prop_solver                    active
% 2.07/0.88  --res_prop_simpl_new                    false
% 2.07/0.88  --res_prop_simpl_given                  true
% 2.07/0.88  --res_passive_queue_type                priority_queues
% 2.07/0.88  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.07/0.88  --res_passive_queues_freq               [15;5]
% 2.07/0.88  --res_forward_subs                      full
% 2.07/0.88  --res_backward_subs                     full
% 2.07/0.88  --res_forward_subs_resolution           true
% 2.07/0.88  --res_backward_subs_resolution          true
% 2.07/0.88  --res_orphan_elimination                true
% 2.07/0.88  --res_time_limit                        2.
% 2.07/0.88  --res_out_proof                         true
% 2.07/0.88  
% 2.07/0.88  ------ Superposition Options
% 2.07/0.88  
% 2.07/0.88  --superposition_flag                    true
% 2.07/0.88  --sup_passive_queue_type                priority_queues
% 2.07/0.88  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.07/0.88  --sup_passive_queues_freq               [8;1;4]
% 2.07/0.88  --demod_completeness_check              fast
% 2.07/0.88  --demod_use_ground                      true
% 2.07/0.88  --sup_to_prop_solver                    passive
% 2.07/0.88  --sup_prop_simpl_new                    true
% 2.07/0.88  --sup_prop_simpl_given                  true
% 2.07/0.88  --sup_fun_splitting                     false
% 2.07/0.88  --sup_smt_interval                      50000
% 2.07/0.88  
% 2.07/0.88  ------ Superposition Simplification Setup
% 2.07/0.88  
% 2.07/0.88  --sup_indices_passive                   []
% 2.07/0.88  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.88  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.88  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.88  --sup_full_triv                         [TrivRules;PropSubs]
% 2.07/0.88  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.88  --sup_full_bw                           [BwDemod]
% 2.07/0.88  --sup_immed_triv                        [TrivRules]
% 2.07/0.88  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.07/0.88  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.88  --sup_immed_bw_main                     []
% 2.07/0.88  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/0.88  --sup_input_triv                        [Unflattening;TrivRules]
% 2.07/0.88  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.88  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/0.88  
% 2.07/0.88  ------ Combination Options
% 2.07/0.88  
% 2.07/0.88  --comb_res_mult                         3
% 2.07/0.88  --comb_sup_mult                         2
% 2.07/0.88  --comb_inst_mult                        10
% 2.07/0.88  
% 2.07/0.88  ------ Debug Options
% 2.07/0.88  
% 2.07/0.88  --dbg_backtrace                         false
% 2.07/0.88  --dbg_dump_prop_clauses                 false
% 2.07/0.88  --dbg_dump_prop_clauses_file            -
% 2.07/0.88  --dbg_out_stat                          false
% 2.07/0.88  ------ Parsing...
% 2.07/0.88  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.07/0.88  
% 2.07/0.88  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.07/0.88  
% 2.07/0.88  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.07/0.88  
% 2.07/0.88  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.07/0.88  ------ Proving...
% 2.07/0.88  ------ Problem Properties 
% 2.07/0.88  
% 2.07/0.88  
% 2.07/0.88  clauses                                 27
% 2.07/0.88  conjectures                             5
% 2.07/0.88  EPR                                     2
% 2.07/0.88  Horn                                    27
% 2.07/0.88  unary                                   9
% 2.07/0.88  binary                                  2
% 2.07/0.88  lits                                    88
% 2.07/0.88  lits eq                                 17
% 2.07/0.88  fd_pure                                 0
% 2.07/0.88  fd_pseudo                               0
% 2.07/0.88  fd_cond                                 0
% 2.07/0.88  fd_pseudo_cond                          1
% 2.07/0.88  AC symbols                              0
% 2.07/0.88  
% 2.07/0.88  ------ Schedule dynamic 5 is on 
% 2.07/0.88  
% 2.07/0.88  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.07/0.88  
% 2.07/0.88  
% 2.07/0.88  ------ 
% 2.07/0.88  Current options:
% 2.07/0.88  ------ 
% 2.07/0.88  
% 2.07/0.88  ------ Input Options
% 2.07/0.88  
% 2.07/0.88  --out_options                           all
% 2.07/0.88  --tptp_safe_out                         true
% 2.07/0.88  --problem_path                          ""
% 2.07/0.88  --include_path                          ""
% 2.07/0.88  --clausifier                            res/vclausify_rel
% 2.07/0.88  --clausifier_options                    --mode clausify
% 2.07/0.88  --stdin                                 false
% 2.07/0.88  --stats_out                             all
% 2.07/0.88  
% 2.07/0.88  ------ General Options
% 2.07/0.88  
% 2.07/0.88  --fof                                   false
% 2.07/0.88  --time_out_real                         305.
% 2.07/0.88  --time_out_virtual                      -1.
% 2.07/0.88  --symbol_type_check                     false
% 2.07/0.88  --clausify_out                          false
% 2.07/0.88  --sig_cnt_out                           false
% 2.07/0.88  --trig_cnt_out                          false
% 2.07/0.88  --trig_cnt_out_tolerance                1.
% 2.07/0.88  --trig_cnt_out_sk_spl                   false
% 2.07/0.88  --abstr_cl_out                          false
% 2.07/0.88  
% 2.07/0.88  ------ Global Options
% 2.07/0.88  
% 2.07/0.88  --schedule                              default
% 2.07/0.88  --add_important_lit                     false
% 2.07/0.88  --prop_solver_per_cl                    1000
% 2.07/0.88  --min_unsat_core                        false
% 2.07/0.88  --soft_assumptions                      false
% 2.07/0.88  --soft_lemma_size                       3
% 2.07/0.88  --prop_impl_unit_size                   0
% 2.07/0.88  --prop_impl_unit                        []
% 2.07/0.88  --share_sel_clauses                     true
% 2.07/0.88  --reset_solvers                         false
% 2.07/0.88  --bc_imp_inh                            [conj_cone]
% 2.07/0.88  --conj_cone_tolerance                   3.
% 2.07/0.88  --extra_neg_conj                        none
% 2.07/0.88  --large_theory_mode                     true
% 2.07/0.88  --prolific_symb_bound                   200
% 2.07/0.88  --lt_threshold                          2000
% 2.07/0.88  --clause_weak_htbl                      true
% 2.07/0.88  --gc_record_bc_elim                     false
% 2.07/0.88  
% 2.07/0.88  ------ Preprocessing Options
% 2.07/0.88  
% 2.07/0.88  --preprocessing_flag                    true
% 2.07/0.88  --time_out_prep_mult                    0.1
% 2.07/0.88  --splitting_mode                        input
% 2.07/0.88  --splitting_grd                         true
% 2.07/0.88  --splitting_cvd                         false
% 2.07/0.88  --splitting_cvd_svl                     false
% 2.07/0.88  --splitting_nvd                         32
% 2.07/0.88  --sub_typing                            true
% 2.07/0.88  --prep_gs_sim                           true
% 2.07/0.88  --prep_unflatten                        true
% 2.07/0.88  --prep_res_sim                          true
% 2.07/0.88  --prep_upred                            true
% 2.07/0.88  --prep_sem_filter                       exhaustive
% 2.07/0.88  --prep_sem_filter_out                   false
% 2.07/0.88  --pred_elim                             true
% 2.07/0.88  --res_sim_input                         true
% 2.07/0.88  --eq_ax_congr_red                       true
% 2.07/0.88  --pure_diseq_elim                       true
% 2.07/0.88  --brand_transform                       false
% 2.07/0.88  --non_eq_to_eq                          false
% 2.07/0.88  --prep_def_merge                        true
% 2.07/0.88  --prep_def_merge_prop_impl              false
% 2.07/0.88  --prep_def_merge_mbd                    true
% 2.07/0.88  --prep_def_merge_tr_red                 false
% 2.07/0.88  --prep_def_merge_tr_cl                  false
% 2.07/0.88  --smt_preprocessing                     true
% 2.07/0.88  --smt_ac_axioms                         fast
% 2.07/0.88  --preprocessed_out                      false
% 2.07/0.88  --preprocessed_stats                    false
% 2.07/0.88  
% 2.07/0.88  ------ Abstraction refinement Options
% 2.07/0.88  
% 2.07/0.88  --abstr_ref                             []
% 2.07/0.88  --abstr_ref_prep                        false
% 2.07/0.88  --abstr_ref_until_sat                   false
% 2.07/0.88  --abstr_ref_sig_restrict                funpre
% 2.07/0.88  --abstr_ref_af_restrict_to_split_sk     false
% 2.07/0.88  --abstr_ref_under                       []
% 2.07/0.88  
% 2.07/0.88  ------ SAT Options
% 2.07/0.88  
% 2.07/0.88  --sat_mode                              false
% 2.07/0.88  --sat_fm_restart_options                ""
% 2.07/0.88  --sat_gr_def                            false
% 2.07/0.88  --sat_epr_types                         true
% 2.07/0.88  --sat_non_cyclic_types                  false
% 2.07/0.88  --sat_finite_models                     false
% 2.07/0.88  --sat_fm_lemmas                         false
% 2.07/0.88  --sat_fm_prep                           false
% 2.07/0.88  --sat_fm_uc_incr                        true
% 2.07/0.88  --sat_out_model                         small
% 2.07/0.88  --sat_out_clauses                       false
% 2.07/0.88  
% 2.07/0.88  ------ QBF Options
% 2.07/0.88  
% 2.07/0.88  --qbf_mode                              false
% 2.07/0.88  --qbf_elim_univ                         false
% 2.07/0.88  --qbf_dom_inst                          none
% 2.07/0.88  --qbf_dom_pre_inst                      false
% 2.07/0.88  --qbf_sk_in                             false
% 2.07/0.88  --qbf_pred_elim                         true
% 2.07/0.88  --qbf_split                             512
% 2.07/0.88  
% 2.07/0.88  ------ BMC1 Options
% 2.07/0.88  
% 2.07/0.88  --bmc1_incremental                      false
% 2.07/0.88  --bmc1_axioms                           reachable_all
% 2.07/0.88  --bmc1_min_bound                        0
% 2.07/0.88  --bmc1_max_bound                        -1
% 2.07/0.88  --bmc1_max_bound_default                -1
% 2.07/0.88  --bmc1_symbol_reachability              true
% 2.07/0.88  --bmc1_property_lemmas                  false
% 2.07/0.88  --bmc1_k_induction                      false
% 2.07/0.88  --bmc1_non_equiv_states                 false
% 2.07/0.88  --bmc1_deadlock                         false
% 2.07/0.88  --bmc1_ucm                              false
% 2.07/0.88  --bmc1_add_unsat_core                   none
% 2.07/0.88  --bmc1_unsat_core_children              false
% 2.07/0.88  --bmc1_unsat_core_extrapolate_axioms    false
% 2.07/0.88  --bmc1_out_stat                         full
% 2.07/0.88  --bmc1_ground_init                      false
% 2.07/0.88  --bmc1_pre_inst_next_state              false
% 2.07/0.88  --bmc1_pre_inst_state                   false
% 2.07/0.88  --bmc1_pre_inst_reach_state             false
% 2.07/0.88  --bmc1_out_unsat_core                   false
% 2.07/0.88  --bmc1_aig_witness_out                  false
% 2.07/0.88  --bmc1_verbose                          false
% 2.07/0.88  --bmc1_dump_clauses_tptp                false
% 2.07/0.88  --bmc1_dump_unsat_core_tptp             false
% 2.07/0.88  --bmc1_dump_file                        -
% 2.07/0.88  --bmc1_ucm_expand_uc_limit              128
% 2.07/0.88  --bmc1_ucm_n_expand_iterations          6
% 2.07/0.88  --bmc1_ucm_extend_mode                  1
% 2.07/0.88  --bmc1_ucm_init_mode                    2
% 2.07/0.88  --bmc1_ucm_cone_mode                    none
% 2.07/0.88  --bmc1_ucm_reduced_relation_type        0
% 2.07/0.88  --bmc1_ucm_relax_model                  4
% 2.07/0.88  --bmc1_ucm_full_tr_after_sat            true
% 2.07/0.88  --bmc1_ucm_expand_neg_assumptions       false
% 2.07/0.88  --bmc1_ucm_layered_model                none
% 2.07/0.88  --bmc1_ucm_max_lemma_size               10
% 2.07/0.88  
% 2.07/0.88  ------ AIG Options
% 2.07/0.88  
% 2.07/0.88  --aig_mode                              false
% 2.07/0.88  
% 2.07/0.88  ------ Instantiation Options
% 2.07/0.88  
% 2.07/0.88  --instantiation_flag                    true
% 2.07/0.88  --inst_sos_flag                         false
% 2.07/0.88  --inst_sos_phase                        true
% 2.07/0.88  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.07/0.88  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.07/0.88  --inst_lit_sel_side                     none
% 2.07/0.88  --inst_solver_per_active                1400
% 2.07/0.88  --inst_solver_calls_frac                1.
% 2.07/0.88  --inst_passive_queue_type               priority_queues
% 2.07/0.88  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.07/0.88  --inst_passive_queues_freq              [25;2]
% 2.07/0.88  --inst_dismatching                      true
% 2.07/0.88  --inst_eager_unprocessed_to_passive     true
% 2.07/0.88  --inst_prop_sim_given                   true
% 2.07/0.88  --inst_prop_sim_new                     false
% 2.07/0.88  --inst_subs_new                         false
% 2.07/0.88  --inst_eq_res_simp                      false
% 2.07/0.88  --inst_subs_given                       false
% 2.07/0.88  --inst_orphan_elimination               true
% 2.07/0.88  --inst_learning_loop_flag               true
% 2.07/0.88  --inst_learning_start                   3000
% 2.07/0.88  --inst_learning_factor                  2
% 2.07/0.88  --inst_start_prop_sim_after_learn       3
% 2.07/0.88  --inst_sel_renew                        solver
% 2.07/0.88  --inst_lit_activity_flag                true
% 2.07/0.88  --inst_restr_to_given                   false
% 2.07/0.88  --inst_activity_threshold               500
% 2.07/0.88  --inst_out_proof                        true
% 2.07/0.88  
% 2.07/0.88  ------ Resolution Options
% 2.07/0.88  
% 2.07/0.88  --resolution_flag                       false
% 2.07/0.88  --res_lit_sel                           adaptive
% 2.07/0.88  --res_lit_sel_side                      none
% 2.07/0.88  --res_ordering                          kbo
% 2.07/0.88  --res_to_prop_solver                    active
% 2.07/0.88  --res_prop_simpl_new                    false
% 2.07/0.88  --res_prop_simpl_given                  true
% 2.07/0.88  --res_passive_queue_type                priority_queues
% 2.07/0.88  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.07/0.88  --res_passive_queues_freq               [15;5]
% 2.07/0.88  --res_forward_subs                      full
% 2.07/0.88  --res_backward_subs                     full
% 2.07/0.88  --res_forward_subs_resolution           true
% 2.07/0.88  --res_backward_subs_resolution          true
% 2.07/0.88  --res_orphan_elimination                true
% 2.07/0.88  --res_time_limit                        2.
% 2.07/0.88  --res_out_proof                         true
% 2.07/0.88  
% 2.07/0.88  ------ Superposition Options
% 2.07/0.88  
% 2.07/0.88  --superposition_flag                    true
% 2.07/0.88  --sup_passive_queue_type                priority_queues
% 2.07/0.88  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.07/0.88  --sup_passive_queues_freq               [8;1;4]
% 2.07/0.88  --demod_completeness_check              fast
% 2.07/0.88  --demod_use_ground                      true
% 2.07/0.88  --sup_to_prop_solver                    passive
% 2.07/0.88  --sup_prop_simpl_new                    true
% 2.07/0.88  --sup_prop_simpl_given                  true
% 2.07/0.88  --sup_fun_splitting                     false
% 2.07/0.88  --sup_smt_interval                      50000
% 2.07/0.88  
% 2.07/0.88  ------ Superposition Simplification Setup
% 2.07/0.88  
% 2.07/0.88  --sup_indices_passive                   []
% 2.07/0.88  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.88  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.88  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.88  --sup_full_triv                         [TrivRules;PropSubs]
% 2.07/0.88  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.88  --sup_full_bw                           [BwDemod]
% 2.07/0.88  --sup_immed_triv                        [TrivRules]
% 2.07/0.88  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.07/0.88  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.88  --sup_immed_bw_main                     []
% 2.07/0.88  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/0.88  --sup_input_triv                        [Unflattening;TrivRules]
% 2.07/0.88  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.88  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/0.88  
% 2.07/0.88  ------ Combination Options
% 2.07/0.88  
% 2.07/0.88  --comb_res_mult                         3
% 2.07/0.88  --comb_sup_mult                         2
% 2.07/0.88  --comb_inst_mult                        10
% 2.07/0.88  
% 2.07/0.88  ------ Debug Options
% 2.07/0.88  
% 2.07/0.88  --dbg_backtrace                         false
% 2.07/0.88  --dbg_dump_prop_clauses                 false
% 2.07/0.88  --dbg_dump_prop_clauses_file            -
% 2.07/0.88  --dbg_out_stat                          false
% 2.07/0.88  
% 2.07/0.88  
% 2.07/0.88  
% 2.07/0.88  
% 2.07/0.88  ------ Proving...
% 2.07/0.88  
% 2.07/0.88  
% 2.07/0.88  % SZS status Theorem for theBenchmark.p
% 2.07/0.88  
% 2.07/0.88   Resolution empty clause
% 2.07/0.88  
% 2.07/0.88  % SZS output start CNFRefutation for theBenchmark.p
% 2.07/0.88  
% 2.07/0.88  fof(f17,conjecture,(
% 2.07/0.88    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.07/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.88  
% 2.07/0.88  fof(f18,negated_conjecture,(
% 2.07/0.88    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.07/0.88    inference(negated_conjecture,[],[f17])).
% 2.07/0.88  
% 2.07/0.88  fof(f46,plain,(
% 2.07/0.88    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.07/0.88    inference(ennf_transformation,[],[f18])).
% 2.07/0.88  
% 2.07/0.88  fof(f47,plain,(
% 2.07/0.88    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.07/0.88    inference(flattening,[],[f46])).
% 2.07/0.88  
% 2.07/0.88  fof(f51,plain,(
% 2.07/0.88    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.07/0.88    introduced(choice_axiom,[])).
% 2.07/0.88  
% 2.07/0.88  fof(f50,plain,(
% 2.07/0.88    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.07/0.88    introduced(choice_axiom,[])).
% 2.07/0.88  
% 2.07/0.88  fof(f49,plain,(
% 2.07/0.88    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.07/0.88    introduced(choice_axiom,[])).
% 2.07/0.88  
% 2.07/0.88  fof(f52,plain,(
% 2.07/0.88    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.07/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f47,f51,f50,f49])).
% 2.07/0.88  
% 2.07/0.88  fof(f83,plain,(
% 2.07/0.88    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.07/0.88    inference(cnf_transformation,[],[f52])).
% 2.07/0.88  
% 2.07/0.88  fof(f14,axiom,(
% 2.07/0.88    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.07/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.88  
% 2.07/0.88  fof(f41,plain,(
% 2.07/0.88    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.07/0.88    inference(ennf_transformation,[],[f14])).
% 2.07/0.88  
% 2.07/0.88  fof(f75,plain,(
% 2.07/0.88    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.07/0.88    inference(cnf_transformation,[],[f41])).
% 2.07/0.88  
% 2.07/0.88  fof(f78,plain,(
% 2.07/0.88    l1_struct_0(sK0)),
% 2.07/0.88    inference(cnf_transformation,[],[f52])).
% 2.07/0.88  
% 2.07/0.88  fof(f80,plain,(
% 2.07/0.88    l1_struct_0(sK1)),
% 2.07/0.88    inference(cnf_transformation,[],[f52])).
% 2.07/0.88  
% 2.07/0.88  fof(f10,axiom,(
% 2.07/0.88    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.07/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.88  
% 2.07/0.88  fof(f33,plain,(
% 2.07/0.88    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.07/0.88    inference(ennf_transformation,[],[f10])).
% 2.07/0.88  
% 2.07/0.88  fof(f34,plain,(
% 2.07/0.88    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.07/0.88    inference(flattening,[],[f33])).
% 2.07/0.88  
% 2.07/0.88  fof(f68,plain,(
% 2.07/0.88    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.07/0.88    inference(cnf_transformation,[],[f34])).
% 2.07/0.88  
% 2.07/0.88  fof(f15,axiom,(
% 2.07/0.88    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 2.07/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.88  
% 2.07/0.88  fof(f42,plain,(
% 2.07/0.88    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.07/0.88    inference(ennf_transformation,[],[f15])).
% 2.07/0.88  
% 2.07/0.88  fof(f43,plain,(
% 2.07/0.88    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.07/0.88    inference(flattening,[],[f42])).
% 2.07/0.88  
% 2.07/0.88  fof(f76,plain,(
% 2.07/0.88    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.07/0.88    inference(cnf_transformation,[],[f43])).
% 2.07/0.88  
% 2.07/0.88  fof(f79,plain,(
% 2.07/0.88    ~v2_struct_0(sK1)),
% 2.07/0.88    inference(cnf_transformation,[],[f52])).
% 2.07/0.88  
% 2.07/0.88  fof(f8,axiom,(
% 2.07/0.88    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.07/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.88  
% 2.07/0.88  fof(f19,plain,(
% 2.07/0.88    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.07/0.88    inference(pure_predicate_removal,[],[f8])).
% 2.07/0.88  
% 2.07/0.88  fof(f31,plain,(
% 2.07/0.88    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/0.88    inference(ennf_transformation,[],[f19])).
% 2.07/0.88  
% 2.07/0.88  fof(f65,plain,(
% 2.07/0.88    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.07/0.88    inference(cnf_transformation,[],[f31])).
% 2.07/0.88  
% 2.07/0.88  fof(f11,axiom,(
% 2.07/0.88    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.07/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.88  
% 2.07/0.88  fof(f35,plain,(
% 2.07/0.88    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.07/0.88    inference(ennf_transformation,[],[f11])).
% 2.07/0.88  
% 2.07/0.88  fof(f36,plain,(
% 2.07/0.88    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.07/0.88    inference(flattening,[],[f35])).
% 2.07/0.88  
% 2.07/0.88  fof(f48,plain,(
% 2.07/0.88    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.07/0.88    inference(nnf_transformation,[],[f36])).
% 2.07/0.88  
% 2.07/0.88  fof(f69,plain,(
% 2.07/0.88    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.07/0.88    inference(cnf_transformation,[],[f48])).
% 2.07/0.88  
% 2.07/0.88  fof(f7,axiom,(
% 2.07/0.88    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.07/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.88  
% 2.07/0.88  fof(f30,plain,(
% 2.07/0.88    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/0.88    inference(ennf_transformation,[],[f7])).
% 2.07/0.88  
% 2.07/0.88  fof(f64,plain,(
% 2.07/0.88    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.07/0.88    inference(cnf_transformation,[],[f30])).
% 2.07/0.88  
% 2.07/0.88  fof(f81,plain,(
% 2.07/0.88    v1_funct_1(sK2)),
% 2.07/0.88    inference(cnf_transformation,[],[f52])).
% 2.07/0.88  
% 2.07/0.88  fof(f82,plain,(
% 2.07/0.88    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.07/0.88    inference(cnf_transformation,[],[f52])).
% 2.07/0.88  
% 2.07/0.88  fof(f9,axiom,(
% 2.07/0.88    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.07/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.88  
% 2.07/0.88  fof(f32,plain,(
% 2.07/0.88    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/0.88    inference(ennf_transformation,[],[f9])).
% 2.07/0.88  
% 2.07/0.88  fof(f66,plain,(
% 2.07/0.88    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.07/0.88    inference(cnf_transformation,[],[f32])).
% 2.07/0.88  
% 2.07/0.88  fof(f84,plain,(
% 2.07/0.88    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.07/0.88    inference(cnf_transformation,[],[f52])).
% 2.07/0.88  
% 2.07/0.88  fof(f16,axiom,(
% 2.07/0.88    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.07/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.88  
% 2.07/0.88  fof(f44,plain,(
% 2.07/0.88    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.07/0.88    inference(ennf_transformation,[],[f16])).
% 2.07/0.88  
% 2.07/0.88  fof(f45,plain,(
% 2.07/0.88    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.07/0.88    inference(flattening,[],[f44])).
% 2.07/0.88  
% 2.07/0.88  fof(f77,plain,(
% 2.07/0.88    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.07/0.88    inference(cnf_transformation,[],[f45])).
% 2.07/0.88  
% 2.07/0.88  fof(f85,plain,(
% 2.07/0.88    v2_funct_1(sK2)),
% 2.07/0.88    inference(cnf_transformation,[],[f52])).
% 2.07/0.88  
% 2.07/0.88  fof(f12,axiom,(
% 2.07/0.88    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 2.07/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.88  
% 2.07/0.88  fof(f37,plain,(
% 2.07/0.88    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.07/0.88    inference(ennf_transformation,[],[f12])).
% 2.07/0.88  
% 2.07/0.88  fof(f38,plain,(
% 2.07/0.88    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.07/0.88    inference(flattening,[],[f37])).
% 2.07/0.88  
% 2.07/0.88  fof(f71,plain,(
% 2.07/0.88    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.07/0.88    inference(cnf_transformation,[],[f38])).
% 2.07/0.88  
% 2.07/0.88  fof(f86,plain,(
% 2.07/0.88    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.07/0.88    inference(cnf_transformation,[],[f52])).
% 2.07/0.88  
% 2.07/0.88  fof(f1,axiom,(
% 2.07/0.88    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.07/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.88  
% 2.07/0.88  fof(f20,plain,(
% 2.07/0.88    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.07/0.88    inference(ennf_transformation,[],[f1])).
% 2.07/0.88  
% 2.07/0.88  fof(f21,plain,(
% 2.07/0.88    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.07/0.88    inference(flattening,[],[f20])).
% 2.07/0.88  
% 2.07/0.88  fof(f54,plain,(
% 2.07/0.88    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.07/0.88    inference(cnf_transformation,[],[f21])).
% 2.07/0.88  
% 2.07/0.88  fof(f4,axiom,(
% 2.07/0.88    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.07/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.88  
% 2.07/0.88  fof(f24,plain,(
% 2.07/0.88    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.07/0.88    inference(ennf_transformation,[],[f4])).
% 2.07/0.88  
% 2.07/0.88  fof(f25,plain,(
% 2.07/0.88    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.07/0.88    inference(flattening,[],[f24])).
% 2.07/0.88  
% 2.07/0.88  fof(f60,plain,(
% 2.07/0.88    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.07/0.88    inference(cnf_transformation,[],[f25])).
% 2.07/0.88  
% 2.07/0.88  fof(f3,axiom,(
% 2.07/0.88    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 2.07/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.88  
% 2.07/0.88  fof(f22,plain,(
% 2.07/0.88    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.07/0.88    inference(ennf_transformation,[],[f3])).
% 2.07/0.88  
% 2.07/0.88  fof(f23,plain,(
% 2.07/0.88    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.07/0.88    inference(flattening,[],[f22])).
% 2.07/0.88  
% 2.07/0.88  fof(f57,plain,(
% 2.07/0.88    ( ! [X0,X1] : (v2_funct_1(X1) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.07/0.88    inference(cnf_transformation,[],[f23])).
% 2.07/0.88  
% 2.07/0.88  fof(f53,plain,(
% 2.07/0.88    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.07/0.88    inference(cnf_transformation,[],[f21])).
% 2.07/0.88  
% 2.07/0.88  fof(f5,axiom,(
% 2.07/0.88    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 2.07/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.88  
% 2.07/0.88  fof(f26,plain,(
% 2.07/0.88    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.07/0.88    inference(ennf_transformation,[],[f5])).
% 2.07/0.88  
% 2.07/0.88  fof(f27,plain,(
% 2.07/0.88    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.07/0.88    inference(flattening,[],[f26])).
% 2.07/0.88  
% 2.07/0.88  fof(f62,plain,(
% 2.07/0.88    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.07/0.88    inference(cnf_transformation,[],[f27])).
% 2.07/0.88  
% 2.07/0.88  fof(f2,axiom,(
% 2.07/0.88    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.07/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.88  
% 2.07/0.88  fof(f56,plain,(
% 2.07/0.88    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.07/0.88    inference(cnf_transformation,[],[f2])).
% 2.07/0.88  
% 2.07/0.88  fof(f13,axiom,(
% 2.07/0.88    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.07/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.88  
% 2.07/0.88  fof(f39,plain,(
% 2.07/0.88    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.07/0.88    inference(ennf_transformation,[],[f13])).
% 2.07/0.88  
% 2.07/0.88  fof(f40,plain,(
% 2.07/0.88    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.07/0.88    inference(flattening,[],[f39])).
% 2.07/0.88  
% 2.07/0.88  fof(f74,plain,(
% 2.07/0.88    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.07/0.88    inference(cnf_transformation,[],[f40])).
% 2.07/0.88  
% 2.07/0.88  fof(f73,plain,(
% 2.07/0.88    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.07/0.88    inference(cnf_transformation,[],[f40])).
% 2.07/0.88  
% 2.07/0.88  fof(f6,axiom,(
% 2.07/0.88    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.07/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.88  
% 2.07/0.88  fof(f28,plain,(
% 2.07/0.88    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.07/0.88    inference(ennf_transformation,[],[f6])).
% 2.07/0.88  
% 2.07/0.88  fof(f29,plain,(
% 2.07/0.88    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.07/0.88    inference(flattening,[],[f28])).
% 2.07/0.88  
% 2.07/0.88  fof(f63,plain,(
% 2.07/0.88    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.07/0.88    inference(cnf_transformation,[],[f29])).
% 2.07/0.88  
% 2.07/0.88  cnf(c_28,negated_conjecture,
% 2.07/0.88      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.07/0.88      inference(cnf_transformation,[],[f83]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_695,negated_conjecture,
% 2.07/0.88      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.07/0.88      inference(subtyping,[status(esa)],[c_28]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1212,plain,
% 2.07/0.88      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_695]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_22,plain,
% 2.07/0.88      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.07/0.88      inference(cnf_transformation,[],[f75]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_33,negated_conjecture,
% 2.07/0.88      ( l1_struct_0(sK0) ),
% 2.07/0.88      inference(cnf_transformation,[],[f78]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_392,plain,
% 2.07/0.88      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.07/0.88      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_393,plain,
% 2.07/0.88      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.07/0.88      inference(unflattening,[status(thm)],[c_392]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_690,plain,
% 2.07/0.88      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.07/0.88      inference(subtyping,[status(esa)],[c_393]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_31,negated_conjecture,
% 2.07/0.88      ( l1_struct_0(sK1) ),
% 2.07/0.88      inference(cnf_transformation,[],[f80]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_387,plain,
% 2.07/0.88      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.07/0.88      inference(resolution_lifted,[status(thm)],[c_22,c_31]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_388,plain,
% 2.07/0.88      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.07/0.88      inference(unflattening,[status(thm)],[c_387]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_691,plain,
% 2.07/0.88      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.07/0.88      inference(subtyping,[status(esa)],[c_388]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1237,plain,
% 2.07/0.88      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.07/0.88      inference(light_normalisation,[status(thm)],[c_1212,c_690,c_691]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_14,plain,
% 2.07/0.88      ( ~ v1_funct_2(X0,X1,X2)
% 2.07/0.88      | v1_partfun1(X0,X1)
% 2.07/0.88      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/0.88      | v1_xboole_0(X2)
% 2.07/0.88      | ~ v1_funct_1(X0) ),
% 2.07/0.88      inference(cnf_transformation,[],[f68]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_23,plain,
% 2.07/0.88      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 2.07/0.88      inference(cnf_transformation,[],[f76]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_32,negated_conjecture,
% 2.07/0.88      ( ~ v2_struct_0(sK1) ),
% 2.07/0.88      inference(cnf_transformation,[],[f79]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_374,plain,
% 2.07/0.88      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 2.07/0.88      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_375,plain,
% 2.07/0.88      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.07/0.88      inference(unflattening,[status(thm)],[c_374]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_46,plain,
% 2.07/0.88      ( v2_struct_0(sK1)
% 2.07/0.88      | ~ l1_struct_0(sK1)
% 2.07/0.88      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.07/0.88      inference(instantiation,[status(thm)],[c_23]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_377,plain,
% 2.07/0.88      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.07/0.88      inference(global_propositional_subsumption,
% 2.07/0.88                [status(thm)],
% 2.07/0.88                [c_375,c_32,c_31,c_46]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_399,plain,
% 2.07/0.88      ( ~ v1_funct_2(X0,X1,X2)
% 2.07/0.88      | v1_partfun1(X0,X1)
% 2.07/0.88      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/0.88      | ~ v1_funct_1(X0)
% 2.07/0.88      | k2_struct_0(sK1) != X2 ),
% 2.07/0.88      inference(resolution_lifted,[status(thm)],[c_14,c_377]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_400,plain,
% 2.07/0.88      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 2.07/0.88      | v1_partfun1(X0,X1)
% 2.07/0.88      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.07/0.88      | ~ v1_funct_1(X0) ),
% 2.07/0.88      inference(unflattening,[status(thm)],[c_399]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_12,plain,
% 2.07/0.88      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.07/0.88      inference(cnf_transformation,[],[f65]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_17,plain,
% 2.07/0.88      ( ~ v1_partfun1(X0,X1)
% 2.07/0.88      | ~ v4_relat_1(X0,X1)
% 2.07/0.88      | ~ v1_relat_1(X0)
% 2.07/0.88      | k1_relat_1(X0) = X1 ),
% 2.07/0.88      inference(cnf_transformation,[],[f69]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_457,plain,
% 2.07/0.88      ( ~ v1_partfun1(X0,X1)
% 2.07/0.88      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/0.88      | ~ v1_relat_1(X0)
% 2.07/0.88      | k1_relat_1(X0) = X1 ),
% 2.07/0.88      inference(resolution,[status(thm)],[c_12,c_17]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_11,plain,
% 2.07/0.88      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.07/0.88      inference(cnf_transformation,[],[f64]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_461,plain,
% 2.07/0.88      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/0.88      | ~ v1_partfun1(X0,X1)
% 2.07/0.88      | k1_relat_1(X0) = X1 ),
% 2.07/0.88      inference(global_propositional_subsumption,
% 2.07/0.88                [status(thm)],
% 2.07/0.88                [c_457,c_17,c_12,c_11]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_462,plain,
% 2.07/0.88      ( ~ v1_partfun1(X0,X1)
% 2.07/0.88      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/0.88      | k1_relat_1(X0) = X1 ),
% 2.07/0.88      inference(renaming,[status(thm)],[c_461]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_501,plain,
% 2.07/0.88      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 2.07/0.88      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/0.88      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.07/0.88      | ~ v1_funct_1(X0)
% 2.07/0.88      | k1_relat_1(X0) = X1 ),
% 2.07/0.88      inference(resolution,[status(thm)],[c_400,c_462]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_688,plain,
% 2.07/0.88      ( ~ v1_funct_2(X0_53,X0_54,k2_struct_0(sK1))
% 2.07/0.88      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.07/0.88      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_struct_0(sK1))))
% 2.07/0.88      | ~ v1_funct_1(X0_53)
% 2.07/0.88      | k1_relat_1(X0_53) = X0_54 ),
% 2.07/0.88      inference(subtyping,[status(esa)],[c_501]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1218,plain,
% 2.07/0.88      ( k1_relat_1(X0_53) = X0_54
% 2.07/0.88      | v1_funct_2(X0_53,X0_54,k2_struct_0(sK1)) != iProver_top
% 2.07/0.88      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.07/0.88      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_struct_0(sK1)))) != iProver_top
% 2.07/0.88      | v1_funct_1(X0_53) != iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_688]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1647,plain,
% 2.07/0.88      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.07/0.88      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.07/0.88      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_54))) != iProver_top
% 2.07/0.88      | v1_funct_1(sK2) != iProver_top ),
% 2.07/0.88      inference(superposition,[status(thm)],[c_1237,c_1218]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_30,negated_conjecture,
% 2.07/0.88      ( v1_funct_1(sK2) ),
% 2.07/0.88      inference(cnf_transformation,[],[f81]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_37,plain,
% 2.07/0.88      ( v1_funct_1(sK2) = iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_29,negated_conjecture,
% 2.07/0.88      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.07/0.88      inference(cnf_transformation,[],[f82]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_694,negated_conjecture,
% 2.07/0.88      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.07/0.88      inference(subtyping,[status(esa)],[c_29]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1213,plain,
% 2.07/0.88      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_694]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1231,plain,
% 2.07/0.88      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.07/0.88      inference(light_normalisation,[status(thm)],[c_1213,c_690,c_691]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1726,plain,
% 2.07/0.88      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_54))) != iProver_top
% 2.07/0.88      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.07/0.88      inference(global_propositional_subsumption,
% 2.07/0.88                [status(thm)],
% 2.07/0.88                [c_1647,c_37,c_1231]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1727,plain,
% 2.07/0.88      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.07/0.88      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_54))) != iProver_top ),
% 2.07/0.88      inference(renaming,[status(thm)],[c_1726]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1734,plain,
% 2.07/0.88      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.07/0.88      inference(superposition,[status(thm)],[c_1237,c_1727]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1737,plain,
% 2.07/0.88      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
% 2.07/0.88      inference(demodulation,[status(thm)],[c_1734,c_1237]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_13,plain,
% 2.07/0.88      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/0.88      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.07/0.88      inference(cnf_transformation,[],[f66]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_701,plain,
% 2.07/0.88      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.07/0.88      | k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53) ),
% 2.07/0.88      inference(subtyping,[status(esa)],[c_13]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1207,plain,
% 2.07/0.88      ( k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53)
% 2.07/0.88      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_2250,plain,
% 2.07/0.88      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.07/0.88      inference(superposition,[status(thm)],[c_1737,c_1207]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_27,negated_conjecture,
% 2.07/0.88      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.07/0.88      inference(cnf_transformation,[],[f84]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_696,negated_conjecture,
% 2.07/0.88      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.07/0.88      inference(subtyping,[status(esa)],[c_27]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1234,plain,
% 2.07/0.88      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.07/0.88      inference(light_normalisation,[status(thm)],[c_696,c_690,c_691]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1739,plain,
% 2.07/0.88      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.07/0.88      inference(demodulation,[status(thm)],[c_1734,c_1234]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_2422,plain,
% 2.07/0.88      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.07/0.88      inference(demodulation,[status(thm)],[c_2250,c_1739]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_2812,plain,
% 2.07/0.88      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.07/0.88      inference(demodulation,[status(thm)],[c_2422,c_2250]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_24,plain,
% 2.07/0.88      ( ~ v1_funct_2(X0,X1,X2)
% 2.07/0.88      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/0.88      | ~ v2_funct_1(X0)
% 2.07/0.88      | ~ v1_funct_1(X0)
% 2.07/0.88      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.07/0.88      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.07/0.88      inference(cnf_transformation,[],[f77]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_698,plain,
% 2.07/0.88      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 2.07/0.88      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.07/0.88      | ~ v2_funct_1(X0_53)
% 2.07/0.88      | ~ v1_funct_1(X0_53)
% 2.07/0.88      | k2_relset_1(X0_54,X1_54,X0_53) != X1_54
% 2.07/0.88      | k2_tops_2(X0_54,X1_54,X0_53) = k2_funct_1(X0_53) ),
% 2.07/0.88      inference(subtyping,[status(esa)],[c_24]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1210,plain,
% 2.07/0.88      ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
% 2.07/0.88      | k2_tops_2(X0_54,X1_54,X0_53) = k2_funct_1(X0_53)
% 2.07/0.88      | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 2.07/0.88      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.07/0.88      | v2_funct_1(X0_53) != iProver_top
% 2.07/0.88      | v1_funct_1(X0_53) != iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_698]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_3610,plain,
% 2.07/0.88      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.07/0.88      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.07/0.88      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.07/0.88      | v2_funct_1(sK2) != iProver_top
% 2.07/0.88      | v1_funct_1(sK2) != iProver_top ),
% 2.07/0.88      inference(superposition,[status(thm)],[c_2812,c_1210]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_26,negated_conjecture,
% 2.07/0.88      ( v2_funct_1(sK2) ),
% 2.07/0.88      inference(cnf_transformation,[],[f85]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_40,plain,
% 2.07/0.88      ( v2_funct_1(sK2) = iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_2813,plain,
% 2.07/0.88      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.07/0.88      inference(demodulation,[status(thm)],[c_2422,c_1737]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1738,plain,
% 2.07/0.88      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) = iProver_top ),
% 2.07/0.88      inference(demodulation,[status(thm)],[c_1734,c_1231]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_2814,plain,
% 2.07/0.88      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.07/0.88      inference(demodulation,[status(thm)],[c_2422,c_1738]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_3845,plain,
% 2.07/0.88      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.07/0.88      inference(global_propositional_subsumption,
% 2.07/0.88                [status(thm)],
% 2.07/0.88                [c_3610,c_37,c_40,c_2813,c_2814]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_18,plain,
% 2.07/0.88      ( r2_funct_2(X0,X1,X2,X2)
% 2.07/0.88      | ~ v1_funct_2(X2,X0,X1)
% 2.07/0.88      | ~ v1_funct_2(X3,X0,X1)
% 2.07/0.88      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.07/0.88      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.07/0.88      | ~ v1_funct_1(X2)
% 2.07/0.88      | ~ v1_funct_1(X3) ),
% 2.07/0.88      inference(cnf_transformation,[],[f71]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_25,negated_conjecture,
% 2.07/0.88      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.07/0.88      inference(cnf_transformation,[],[f86]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_422,plain,
% 2.07/0.88      ( ~ v1_funct_2(X0,X1,X2)
% 2.07/0.88      | ~ v1_funct_2(X3,X1,X2)
% 2.07/0.88      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/0.88      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/0.88      | ~ v1_funct_1(X0)
% 2.07/0.88      | ~ v1_funct_1(X3)
% 2.07/0.88      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 2.07/0.88      | u1_struct_0(sK1) != X2
% 2.07/0.88      | u1_struct_0(sK0) != X1
% 2.07/0.88      | sK2 != X0 ),
% 2.07/0.88      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_423,plain,
% 2.07/0.88      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.07/0.88      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.07/0.88      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.07/0.88      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.07/0.88      | ~ v1_funct_1(X0)
% 2.07/0.88      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.07/0.88      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.07/0.88      inference(unflattening,[status(thm)],[c_422]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_689,plain,
% 2.07/0.88      ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.07/0.88      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.07/0.88      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.07/0.88      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.07/0.88      | ~ v1_funct_1(X0_53)
% 2.07/0.88      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.07/0.88      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.07/0.88      inference(subtyping,[status(esa)],[c_423]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_715,plain,
% 2.07/0.88      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.07/0.88      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.07/0.88      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.07/0.88      | sP0_iProver_split
% 2.07/0.88      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.07/0.88      inference(splitting,
% 2.07/0.88                [splitting(split),new_symbols(definition,[])],
% 2.07/0.88                [c_689]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1216,plain,
% 2.07/0.88      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.07/0.88      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.07/0.88      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.07/0.88      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 2.07/0.88      | sP0_iProver_split = iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_715]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1389,plain,
% 2.07/0.88      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.07/0.88      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.07/0.88      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.07/0.88      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 2.07/0.88      | sP0_iProver_split = iProver_top ),
% 2.07/0.88      inference(light_normalisation,[status(thm)],[c_1216,c_690,c_691]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_714,plain,
% 2.07/0.88      ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.07/0.88      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.07/0.88      | ~ v1_funct_1(X0_53)
% 2.07/0.88      | ~ sP0_iProver_split ),
% 2.07/0.88      inference(splitting,
% 2.07/0.88                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.07/0.88                [c_689]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1217,plain,
% 2.07/0.88      ( v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.07/0.88      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.07/0.88      | v1_funct_1(X0_53) != iProver_top
% 2.07/0.88      | sP0_iProver_split != iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_714]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1306,plain,
% 2.07/0.88      ( v1_funct_2(X0_53,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.07/0.88      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.07/0.88      | v1_funct_1(X0_53) != iProver_top
% 2.07/0.88      | sP0_iProver_split != iProver_top ),
% 2.07/0.88      inference(light_normalisation,[status(thm)],[c_1217,c_690,c_691]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1395,plain,
% 2.07/0.88      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.07/0.88      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.07/0.88      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.07/0.88      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.07/0.88      inference(forward_subsumption_resolution,[status(thm)],[c_1389,c_1306]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1736,plain,
% 2.07/0.88      ( k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) != sK2
% 2.07/0.88      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
% 2.07/0.88      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
% 2.07/0.88      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.07/0.88      inference(demodulation,[status(thm)],[c_1734,c_1395]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_3722,plain,
% 2.07/0.88      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
% 2.07/0.88      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.07/0.88      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.07/0.88      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.07/0.88      inference(light_normalisation,[status(thm)],[c_1736,c_2422]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_3848,plain,
% 2.07/0.88      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 2.07/0.88      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.07/0.88      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.07/0.88      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.07/0.88      inference(demodulation,[status(thm)],[c_3845,c_3722]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_39,plain,
% 2.07/0.88      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_0,plain,
% 2.07/0.88      ( ~ v1_relat_1(X0) | ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) ),
% 2.07/0.88      inference(cnf_transformation,[],[f54]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_713,plain,
% 2.07/0.88      ( ~ v1_relat_1(X0_53)
% 2.07/0.88      | ~ v1_funct_1(X0_53)
% 2.07/0.88      | v1_funct_1(k2_funct_1(X0_53)) ),
% 2.07/0.88      inference(subtyping,[status(esa)],[c_0]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_756,plain,
% 2.07/0.88      ( v1_relat_1(X0_53) != iProver_top
% 2.07/0.88      | v1_funct_1(X0_53) != iProver_top
% 2.07/0.88      | v1_funct_1(k2_funct_1(X0_53)) = iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_713]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_758,plain,
% 2.07/0.88      ( v1_relat_1(sK2) != iProver_top
% 2.07/0.88      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.07/0.88      | v1_funct_1(sK2) != iProver_top ),
% 2.07/0.88      inference(instantiation,[status(thm)],[c_756]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_702,plain,
% 2.07/0.88      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.07/0.88      | v1_relat_1(X0_53) ),
% 2.07/0.88      inference(subtyping,[status(esa)],[c_11]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1456,plain,
% 2.07/0.88      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.07/0.88      | v1_relat_1(sK2) ),
% 2.07/0.88      inference(instantiation,[status(thm)],[c_702]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1457,plain,
% 2.07/0.88      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.07/0.88      | v1_relat_1(sK2) = iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_1456]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_697,negated_conjecture,
% 2.07/0.88      ( v2_funct_1(sK2) ),
% 2.07/0.88      inference(subtyping,[status(esa)],[c_26]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1211,plain,
% 2.07/0.88      ( v2_funct_1(sK2) = iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_697]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_6,plain,
% 2.07/0.88      ( ~ v2_funct_1(X0)
% 2.07/0.88      | ~ v1_relat_1(X0)
% 2.07/0.88      | ~ v1_funct_1(X0)
% 2.07/0.88      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.07/0.88      inference(cnf_transformation,[],[f60]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_707,plain,
% 2.07/0.88      ( ~ v2_funct_1(X0_53)
% 2.07/0.88      | ~ v1_relat_1(X0_53)
% 2.07/0.88      | ~ v1_funct_1(X0_53)
% 2.07/0.88      | k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53) ),
% 2.07/0.88      inference(subtyping,[status(esa)],[c_6]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1201,plain,
% 2.07/0.88      ( k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53)
% 2.07/0.88      | v2_funct_1(X0_53) != iProver_top
% 2.07/0.88      | v1_relat_1(X0_53) != iProver_top
% 2.07/0.88      | v1_funct_1(X0_53) != iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_707]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_2014,plain,
% 2.07/0.88      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.07/0.88      | v1_relat_1(sK2) != iProver_top
% 2.07/0.88      | v1_funct_1(sK2) != iProver_top ),
% 2.07/0.88      inference(superposition,[status(thm)],[c_1211,c_1201]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_771,plain,
% 2.07/0.88      ( ~ v2_funct_1(sK2)
% 2.07/0.88      | ~ v1_relat_1(sK2)
% 2.07/0.88      | ~ v1_funct_1(sK2)
% 2.07/0.88      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.07/0.88      inference(instantiation,[status(thm)],[c_707]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_2142,plain,
% 2.07/0.88      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.07/0.88      inference(global_propositional_subsumption,
% 2.07/0.88                [status(thm)],
% 2.07/0.88                [c_2014,c_30,c_28,c_26,c_771,c_1456]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_5,plain,
% 2.07/0.88      ( v2_funct_1(X0)
% 2.07/0.88      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 2.07/0.88      | ~ v1_relat_1(X1)
% 2.07/0.88      | ~ v1_relat_1(X0)
% 2.07/0.88      | ~ v1_funct_1(X1)
% 2.07/0.88      | ~ v1_funct_1(X0)
% 2.07/0.88      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 2.07/0.88      inference(cnf_transformation,[],[f57]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_708,plain,
% 2.07/0.88      ( v2_funct_1(X0_53)
% 2.07/0.88      | ~ v2_funct_1(k5_relat_1(X0_53,X1_53))
% 2.07/0.88      | ~ v1_relat_1(X0_53)
% 2.07/0.88      | ~ v1_relat_1(X1_53)
% 2.07/0.88      | ~ v1_funct_1(X0_53)
% 2.07/0.88      | ~ v1_funct_1(X1_53)
% 2.07/0.88      | k1_relat_1(X1_53) != k2_relat_1(X0_53) ),
% 2.07/0.88      inference(subtyping,[status(esa)],[c_5]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1200,plain,
% 2.07/0.88      ( k1_relat_1(X0_53) != k2_relat_1(X1_53)
% 2.07/0.88      | v2_funct_1(X1_53) = iProver_top
% 2.07/0.88      | v2_funct_1(k5_relat_1(X1_53,X0_53)) != iProver_top
% 2.07/0.88      | v1_relat_1(X1_53) != iProver_top
% 2.07/0.88      | v1_relat_1(X0_53) != iProver_top
% 2.07/0.88      | v1_funct_1(X1_53) != iProver_top
% 2.07/0.88      | v1_funct_1(X0_53) != iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_708]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_2518,plain,
% 2.07/0.88      ( k1_relat_1(X0_53) != k1_relat_1(sK2)
% 2.07/0.88      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_53)) != iProver_top
% 2.07/0.88      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.07/0.88      | v1_relat_1(X0_53) != iProver_top
% 2.07/0.88      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.07/0.88      | v1_funct_1(X0_53) != iProver_top
% 2.07/0.88      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.07/0.88      inference(superposition,[status(thm)],[c_2142,c_1200]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1,plain,
% 2.07/0.88      ( ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~ v1_funct_1(X0) ),
% 2.07/0.88      inference(cnf_transformation,[],[f53]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_712,plain,
% 2.07/0.88      ( ~ v1_relat_1(X0_53)
% 2.07/0.88      | v1_relat_1(k2_funct_1(X0_53))
% 2.07/0.88      | ~ v1_funct_1(X0_53) ),
% 2.07/0.88      inference(subtyping,[status(esa)],[c_1]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_759,plain,
% 2.07/0.88      ( v1_relat_1(X0_53) != iProver_top
% 2.07/0.88      | v1_relat_1(k2_funct_1(X0_53)) = iProver_top
% 2.07/0.88      | v1_funct_1(X0_53) != iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_712]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_761,plain,
% 2.07/0.88      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 2.07/0.88      | v1_relat_1(sK2) != iProver_top
% 2.07/0.88      | v1_funct_1(sK2) != iProver_top ),
% 2.07/0.88      inference(instantiation,[status(thm)],[c_759]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_3074,plain,
% 2.07/0.88      ( v1_funct_1(X0_53) != iProver_top
% 2.07/0.88      | k1_relat_1(X0_53) != k1_relat_1(sK2)
% 2.07/0.88      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_53)) != iProver_top
% 2.07/0.88      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.07/0.88      | v1_relat_1(X0_53) != iProver_top ),
% 2.07/0.88      inference(global_propositional_subsumption,
% 2.07/0.88                [status(thm)],
% 2.07/0.88                [c_2518,c_37,c_39,c_758,c_761,c_1457]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_3075,plain,
% 2.07/0.88      ( k1_relat_1(X0_53) != k1_relat_1(sK2)
% 2.07/0.88      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_53)) != iProver_top
% 2.07/0.88      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.07/0.88      | v1_relat_1(X0_53) != iProver_top
% 2.07/0.88      | v1_funct_1(X0_53) != iProver_top ),
% 2.07/0.88      inference(renaming,[status(thm)],[c_3074]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_3086,plain,
% 2.07/0.88      ( v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
% 2.07/0.88      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.07/0.88      | v1_relat_1(sK2) != iProver_top
% 2.07/0.88      | v1_funct_1(sK2) != iProver_top ),
% 2.07/0.88      inference(equality_resolution,[status(thm)],[c_3075]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_8,plain,
% 2.07/0.88      ( ~ v2_funct_1(X0)
% 2.07/0.88      | ~ v1_relat_1(X0)
% 2.07/0.88      | ~ v1_funct_1(X0)
% 2.07/0.88      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
% 2.07/0.88      inference(cnf_transformation,[],[f62]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_705,plain,
% 2.07/0.88      ( ~ v2_funct_1(X0_53)
% 2.07/0.88      | ~ v1_relat_1(X0_53)
% 2.07/0.88      | ~ v1_funct_1(X0_53)
% 2.07/0.88      | k5_relat_1(k2_funct_1(X0_53),X0_53) = k6_relat_1(k2_relat_1(X0_53)) ),
% 2.07/0.88      inference(subtyping,[status(esa)],[c_8]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1203,plain,
% 2.07/0.88      ( k5_relat_1(k2_funct_1(X0_53),X0_53) = k6_relat_1(k2_relat_1(X0_53))
% 2.07/0.88      | v2_funct_1(X0_53) != iProver_top
% 2.07/0.88      | v1_relat_1(X0_53) != iProver_top
% 2.07/0.88      | v1_funct_1(X0_53) != iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_705]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_2556,plain,
% 2.07/0.88      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
% 2.07/0.88      | v1_relat_1(sK2) != iProver_top
% 2.07/0.88      | v1_funct_1(sK2) != iProver_top ),
% 2.07/0.88      inference(superposition,[status(thm)],[c_1211,c_1203]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_777,plain,
% 2.07/0.88      ( ~ v2_funct_1(sK2)
% 2.07/0.88      | ~ v1_relat_1(sK2)
% 2.07/0.88      | ~ v1_funct_1(sK2)
% 2.07/0.88      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
% 2.07/0.88      inference(instantiation,[status(thm)],[c_705]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_2728,plain,
% 2.07/0.88      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
% 2.07/0.88      inference(global_propositional_subsumption,
% 2.07/0.88                [status(thm)],
% 2.07/0.88                [c_2556,c_30,c_28,c_26,c_777,c_1456]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_3091,plain,
% 2.07/0.88      ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top
% 2.07/0.88      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.07/0.88      | v1_relat_1(sK2) != iProver_top
% 2.07/0.88      | v1_funct_1(sK2) != iProver_top ),
% 2.07/0.88      inference(light_normalisation,[status(thm)],[c_3086,c_2728]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_3098,plain,
% 2.07/0.88      ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top
% 2.07/0.88      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.07/0.88      inference(global_propositional_subsumption,
% 2.07/0.88                [status(thm)],
% 2.07/0.88                [c_3091,c_37,c_39,c_1457]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_2,plain,
% 2.07/0.88      ( v2_funct_1(k6_relat_1(X0)) ),
% 2.07/0.88      inference(cnf_transformation,[],[f56]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_711,plain,
% 2.07/0.88      ( v2_funct_1(k6_relat_1(X0_54)) ),
% 2.07/0.88      inference(subtyping,[status(esa)],[c_2]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1197,plain,
% 2.07/0.88      ( v2_funct_1(k6_relat_1(X0_54)) = iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_711]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_3104,plain,
% 2.07/0.88      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.07/0.88      inference(forward_subsumption_resolution,[status(thm)],[c_3098,c_1197]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_19,plain,
% 2.07/0.88      ( ~ v1_funct_2(X0,X1,X2)
% 2.07/0.88      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/0.88      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.07/0.88      | ~ v2_funct_1(X0)
% 2.07/0.88      | ~ v1_funct_1(X0)
% 2.07/0.88      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.07/0.88      inference(cnf_transformation,[],[f74]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_700,plain,
% 2.07/0.88      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 2.07/0.88      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.07/0.88      | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54)))
% 2.07/0.88      | ~ v2_funct_1(X0_53)
% 2.07/0.88      | ~ v1_funct_1(X0_53)
% 2.07/0.88      | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
% 2.07/0.88      inference(subtyping,[status(esa)],[c_19]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1208,plain,
% 2.07/0.88      ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
% 2.07/0.88      | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 2.07/0.88      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.07/0.88      | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54))) = iProver_top
% 2.07/0.88      | v2_funct_1(X0_53) != iProver_top
% 2.07/0.88      | v1_funct_1(X0_53) != iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_700]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_3609,plain,
% 2.07/0.88      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.07/0.88      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.07/0.88      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.07/0.88      | v2_funct_1(sK2) != iProver_top
% 2.07/0.88      | v1_funct_1(sK2) != iProver_top ),
% 2.07/0.88      inference(superposition,[status(thm)],[c_2812,c_1208]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_20,plain,
% 2.07/0.88      ( ~ v1_funct_2(X0,X1,X2)
% 2.07/0.88      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.07/0.88      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/0.88      | ~ v2_funct_1(X0)
% 2.07/0.88      | ~ v1_funct_1(X0)
% 2.07/0.88      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.07/0.88      inference(cnf_transformation,[],[f73]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_699,plain,
% 2.07/0.88      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 2.07/0.88      | v1_funct_2(k2_funct_1(X0_53),X1_54,X0_54)
% 2.07/0.88      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.07/0.88      | ~ v2_funct_1(X0_53)
% 2.07/0.88      | ~ v1_funct_1(X0_53)
% 2.07/0.88      | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
% 2.07/0.88      inference(subtyping,[status(esa)],[c_20]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1209,plain,
% 2.07/0.88      ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
% 2.07/0.88      | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 2.07/0.88      | v1_funct_2(k2_funct_1(X0_53),X1_54,X0_54) = iProver_top
% 2.07/0.88      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.07/0.88      | v2_funct_1(X0_53) != iProver_top
% 2.07/0.88      | v1_funct_1(X0_53) != iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_699]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_3611,plain,
% 2.07/0.88      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 2.07/0.88      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.07/0.88      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.07/0.88      | v2_funct_1(sK2) != iProver_top
% 2.07/0.88      | v1_funct_1(sK2) != iProver_top ),
% 2.07/0.88      inference(superposition,[status(thm)],[c_2812,c_1209]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_4087,plain,
% 2.07/0.88      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 2.07/0.88      inference(global_propositional_subsumption,
% 2.07/0.88                [status(thm)],
% 2.07/0.88                [c_3609,c_37,c_40,c_2813,c_2814]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_4093,plain,
% 2.07/0.88      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.07/0.88      inference(superposition,[status(thm)],[c_4087,c_1207]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_4098,plain,
% 2.07/0.88      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.07/0.88      inference(light_normalisation,[status(thm)],[c_4093,c_2142]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_4175,plain,
% 2.07/0.88      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.07/0.88      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.07/0.88      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.07/0.88      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.07/0.88      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.07/0.88      inference(superposition,[status(thm)],[c_4098,c_1210]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_10,plain,
% 2.07/0.88      ( ~ v2_funct_1(X0)
% 2.07/0.88      | ~ v1_relat_1(X0)
% 2.07/0.88      | ~ v1_funct_1(X0)
% 2.07/0.88      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.07/0.88      inference(cnf_transformation,[],[f63]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_703,plain,
% 2.07/0.88      ( ~ v2_funct_1(X0_53)
% 2.07/0.88      | ~ v1_relat_1(X0_53)
% 2.07/0.88      | ~ v1_funct_1(X0_53)
% 2.07/0.88      | k2_funct_1(k2_funct_1(X0_53)) = X0_53 ),
% 2.07/0.88      inference(subtyping,[status(esa)],[c_10]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1205,plain,
% 2.07/0.88      ( k2_funct_1(k2_funct_1(X0_53)) = X0_53
% 2.07/0.88      | v2_funct_1(X0_53) != iProver_top
% 2.07/0.88      | v1_relat_1(X0_53) != iProver_top
% 2.07/0.88      | v1_funct_1(X0_53) != iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_703]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1908,plain,
% 2.07/0.88      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.07/0.88      | v1_relat_1(sK2) != iProver_top
% 2.07/0.88      | v1_funct_1(sK2) != iProver_top ),
% 2.07/0.88      inference(superposition,[status(thm)],[c_1211,c_1205]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_783,plain,
% 2.07/0.88      ( ~ v2_funct_1(sK2)
% 2.07/0.88      | ~ v1_relat_1(sK2)
% 2.07/0.88      | ~ v1_funct_1(sK2)
% 2.07/0.88      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.07/0.88      inference(instantiation,[status(thm)],[c_703]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_2136,plain,
% 2.07/0.88      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.07/0.88      inference(global_propositional_subsumption,
% 2.07/0.88                [status(thm)],
% 2.07/0.88                [c_1908,c_30,c_28,c_26,c_783,c_1456]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_4188,plain,
% 2.07/0.88      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 2.07/0.88      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.07/0.88      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.07/0.88      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.07/0.88      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.07/0.88      inference(light_normalisation,[status(thm)],[c_4175,c_2136]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_4304,plain,
% 2.07/0.88      ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.07/0.88      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.07/0.88      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.07/0.88      inference(global_propositional_subsumption,
% 2.07/0.88                [status(thm)],
% 2.07/0.88                [c_3848,c_37,c_39,c_40,c_758,c_1457,c_2813,c_2814,c_3104,
% 2.07/0.88                 c_3609,c_3611,c_4188]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_4202,plain,
% 2.07/0.88      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.07/0.88      inference(global_propositional_subsumption,
% 2.07/0.88                [status(thm)],
% 2.07/0.88                [c_4188,c_37,c_39,c_40,c_758,c_1457,c_2813,c_2814,c_3104,
% 2.07/0.88                 c_3609,c_3611]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_4308,plain,
% 2.07/0.88      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.07/0.88      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.07/0.88      | v1_funct_1(sK2) != iProver_top ),
% 2.07/0.88      inference(light_normalisation,[status(thm)],[c_4304,c_4202]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_693,negated_conjecture,
% 2.07/0.88      ( v1_funct_1(sK2) ),
% 2.07/0.88      inference(subtyping,[status(esa)],[c_30]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_1214,plain,
% 2.07/0.88      ( v1_funct_1(sK2) = iProver_top ),
% 2.07/0.88      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 2.07/0.88  
% 2.07/0.88  cnf(c_4312,plain,
% 2.07/0.88      ( $false ),
% 2.07/0.88      inference(forward_subsumption_resolution,
% 2.07/0.88                [status(thm)],
% 2.07/0.88                [c_4308,c_1214,c_2813,c_2814]) ).
% 2.07/0.88  
% 2.07/0.88  
% 2.07/0.88  % SZS output end CNFRefutation for theBenchmark.p
% 2.07/0.88  
% 2.07/0.88  ------                               Statistics
% 2.07/0.88  
% 2.07/0.88  ------ General
% 2.07/0.88  
% 2.07/0.88  abstr_ref_over_cycles:                  0
% 2.07/0.88  abstr_ref_under_cycles:                 0
% 2.07/0.88  gc_basic_clause_elim:                   0
% 2.07/0.88  forced_gc_time:                         0
% 2.07/0.88  parsing_time:                           0.009
% 2.07/0.88  unif_index_cands_time:                  0.
% 2.07/0.88  unif_index_add_time:                    0.
% 2.07/0.88  orderings_time:                         0.
% 2.07/0.88  out_proof_time:                         0.012
% 2.07/0.88  total_time:                             0.153
% 2.07/0.88  num_of_symbols:                         62
% 2.07/0.88  num_of_terms:                           3889
% 2.07/0.88  
% 2.07/0.88  ------ Preprocessing
% 2.07/0.88  
% 2.07/0.88  num_of_splits:                          1
% 2.07/0.88  num_of_split_atoms:                     1
% 2.07/0.88  num_of_reused_defs:                     0
% 2.07/0.88  num_eq_ax_congr_red:                    4
% 2.07/0.88  num_of_sem_filtered_clauses:            2
% 2.07/0.88  num_of_subtypes:                        5
% 2.07/0.88  monotx_restored_types:                  1
% 2.07/0.88  sat_num_of_epr_types:                   0
% 2.07/0.88  sat_num_of_non_cyclic_types:            0
% 2.07/0.88  sat_guarded_non_collapsed_types:        1
% 2.07/0.88  num_pure_diseq_elim:                    0
% 2.07/0.88  simp_replaced_by:                       0
% 2.07/0.88  res_preprocessed:                       153
% 2.07/0.88  prep_upred:                             0
% 2.07/0.88  prep_unflattend:                        11
% 2.07/0.88  smt_new_axioms:                         0
% 2.07/0.88  pred_elim_cands:                        5
% 2.07/0.88  pred_elim:                              6
% 2.07/0.88  pred_elim_cl:                           7
% 2.07/0.88  pred_elim_cycles:                       8
% 2.07/0.88  merged_defs:                            0
% 2.07/0.88  merged_defs_ncl:                        0
% 2.07/0.88  bin_hyper_res:                          0
% 2.07/0.88  prep_cycles:                            4
% 2.07/0.88  pred_elim_time:                         0.005
% 2.07/0.88  splitting_time:                         0.
% 2.07/0.88  sem_filter_time:                        0.
% 2.07/0.88  monotx_time:                            0.
% 2.07/0.88  subtype_inf_time:                       0.001
% 2.07/0.88  
% 2.07/0.88  ------ Problem properties
% 2.07/0.88  
% 2.07/0.88  clauses:                                27
% 2.07/0.88  conjectures:                            5
% 2.07/0.88  epr:                                    2
% 2.07/0.88  horn:                                   27
% 2.07/0.88  ground:                                 8
% 2.07/0.88  unary:                                  9
% 2.07/0.88  binary:                                 2
% 2.07/0.88  lits:                                   88
% 2.07/0.88  lits_eq:                                17
% 2.07/0.88  fd_pure:                                0
% 2.07/0.88  fd_pseudo:                              0
% 2.07/0.88  fd_cond:                                0
% 2.07/0.88  fd_pseudo_cond:                         1
% 2.07/0.88  ac_symbols:                             0
% 2.07/0.88  
% 2.07/0.88  ------ Propositional Solver
% 2.07/0.88  
% 2.07/0.88  prop_solver_calls:                      29
% 2.07/0.88  prop_fast_solver_calls:                 1248
% 2.07/0.88  smt_solver_calls:                       0
% 2.07/0.88  smt_fast_solver_calls:                  0
% 2.07/0.88  prop_num_of_clauses:                    1576
% 2.07/0.88  prop_preprocess_simplified:             5717
% 2.07/0.88  prop_fo_subsumed:                       72
% 2.07/0.88  prop_solver_time:                       0.
% 2.07/0.88  smt_solver_time:                        0.
% 2.07/0.88  smt_fast_solver_time:                   0.
% 2.07/0.88  prop_fast_solver_time:                  0.
% 2.07/0.88  prop_unsat_core_time:                   0.
% 2.07/0.88  
% 2.07/0.88  ------ QBF
% 2.07/0.88  
% 2.07/0.88  qbf_q_res:                              0
% 2.07/0.88  qbf_num_tautologies:                    0
% 2.07/0.88  qbf_prep_cycles:                        0
% 2.07/0.88  
% 2.07/0.88  ------ BMC1
% 2.07/0.88  
% 2.07/0.88  bmc1_current_bound:                     -1
% 2.07/0.88  bmc1_last_solved_bound:                 -1
% 2.07/0.88  bmc1_unsat_core_size:                   -1
% 2.07/0.88  bmc1_unsat_core_parents_size:           -1
% 2.07/0.88  bmc1_merge_next_fun:                    0
% 2.07/0.88  bmc1_unsat_core_clauses_time:           0.
% 2.07/0.88  
% 2.07/0.88  ------ Instantiation
% 2.07/0.88  
% 2.07/0.88  inst_num_of_clauses:                    552
% 2.07/0.88  inst_num_in_passive:                    76
% 2.07/0.88  inst_num_in_active:                     307
% 2.07/0.88  inst_num_in_unprocessed:                169
% 2.07/0.88  inst_num_of_loops:                      330
% 2.07/0.88  inst_num_of_learning_restarts:          0
% 2.07/0.88  inst_num_moves_active_passive:          19
% 2.07/0.88  inst_lit_activity:                      0
% 2.07/0.88  inst_lit_activity_moves:                0
% 2.07/0.88  inst_num_tautologies:                   0
% 2.07/0.88  inst_num_prop_implied:                  0
% 2.07/0.88  inst_num_existing_simplified:           0
% 2.07/0.88  inst_num_eq_res_simplified:             0
% 2.07/0.88  inst_num_child_elim:                    0
% 2.07/0.88  inst_num_of_dismatching_blockings:      101
% 2.07/0.88  inst_num_of_non_proper_insts:           533
% 2.07/0.88  inst_num_of_duplicates:                 0
% 2.07/0.88  inst_inst_num_from_inst_to_res:         0
% 2.07/0.88  inst_dismatching_checking_time:         0.
% 2.07/0.88  
% 2.07/0.88  ------ Resolution
% 2.07/0.88  
% 2.07/0.88  res_num_of_clauses:                     0
% 2.07/0.88  res_num_in_passive:                     0
% 2.07/0.88  res_num_in_active:                      0
% 2.07/0.88  res_num_of_loops:                       157
% 2.07/0.88  res_forward_subset_subsumed:            64
% 2.07/0.88  res_backward_subset_subsumed:           0
% 2.07/0.88  res_forward_subsumed:                   0
% 2.07/0.88  res_backward_subsumed:                  0
% 2.07/0.88  res_forward_subsumption_resolution:     1
% 2.07/0.88  res_backward_subsumption_resolution:    0
% 2.07/0.88  res_clause_to_clause_subsumption:       85
% 2.07/0.88  res_orphan_elimination:                 0
% 2.07/0.88  res_tautology_del:                      67
% 2.07/0.88  res_num_eq_res_simplified:              0
% 2.07/0.88  res_num_sel_changes:                    0
% 2.07/0.88  res_moves_from_active_to_pass:          0
% 2.07/0.88  
% 2.07/0.88  ------ Superposition
% 2.07/0.88  
% 2.07/0.88  sup_time_total:                         0.
% 2.07/0.88  sup_time_generating:                    0.
% 2.07/0.88  sup_time_sim_full:                      0.
% 2.07/0.88  sup_time_sim_immed:                     0.
% 2.07/0.88  
% 2.07/0.88  sup_num_of_clauses:                     53
% 2.07/0.88  sup_num_in_active:                      52
% 2.07/0.88  sup_num_in_passive:                     1
% 2.07/0.88  sup_num_of_loops:                       65
% 2.07/0.88  sup_fw_superposition:                   23
% 2.07/0.88  sup_bw_superposition:                   23
% 2.07/0.88  sup_immediate_simplified:               16
% 2.07/0.88  sup_given_eliminated:                   0
% 2.07/0.88  comparisons_done:                       0
% 2.07/0.88  comparisons_avoided:                    0
% 2.07/0.88  
% 2.07/0.88  ------ Simplifications
% 2.07/0.88  
% 2.07/0.88  
% 2.07/0.88  sim_fw_subset_subsumed:                 4
% 2.07/0.88  sim_bw_subset_subsumed:                 2
% 2.07/0.88  sim_fw_subsumed:                        3
% 2.07/0.88  sim_bw_subsumed:                        0
% 2.07/0.88  sim_fw_subsumption_res:                 5
% 2.07/0.88  sim_bw_subsumption_res:                 0
% 2.07/0.88  sim_tautology_del:                      0
% 2.07/0.88  sim_eq_tautology_del:                   8
% 2.07/0.88  sim_eq_res_simp:                        0
% 2.07/0.88  sim_fw_demodulated:                     0
% 2.07/0.88  sim_bw_demodulated:                     12
% 2.07/0.88  sim_light_normalised:                   20
% 2.07/0.88  sim_joinable_taut:                      0
% 2.07/0.88  sim_joinable_simp:                      0
% 2.07/0.88  sim_ac_normalised:                      0
% 2.07/0.88  sim_smt_subsumption:                    0
% 2.07/0.88  
%------------------------------------------------------------------------------
