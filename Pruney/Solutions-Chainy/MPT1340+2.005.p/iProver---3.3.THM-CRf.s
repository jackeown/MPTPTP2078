%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:21 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  250 (18149 expanded)
%              Number of clauses        :  167 (6605 expanded)
%              Number of leaves         :   26 (4769 expanded)
%              Depth                    :   29
%              Number of atoms          :  848 (106513 expanded)
%              Number of equality atoms :  343 (19088 expanded)
%              Maximal formula depth    :   13 (   5 average)
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

fof(f78,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f32])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
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

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f36])).

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
    inference(nnf_transformation,[],[f37])).

fof(f70,plain,(
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

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f70])).

fof(f86,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k4_relat_1(X2) = k3_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f55,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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
    inference(flattening,[],[f38])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f56,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f17,axiom,(
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

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f45])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_31,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_724,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1220,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_724])).

cnf(c_19,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_733,plain,
    ( ~ l1_struct_0(X0_56)
    | u1_struct_0(X0_56) = k2_struct_0(X0_56) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1212,plain,
    ( u1_struct_0(X0_56) = k2_struct_0(X0_56)
    | l1_struct_0(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_1524,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1220,c_1212])).

cnf(c_29,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_725,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1219,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_725])).

cnf(c_1523,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1219,c_1212])).

cnf(c_25,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_729,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1705,plain,
    ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1523,c_729])).

cnf(c_1775,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1524,c_1705])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_728,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1216,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_740,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1205,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_740])).

cnf(c_1638,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1216,c_1205])).

cnf(c_1871,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1638,c_1523,c_1524])).

cnf(c_1907,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1775,c_1871])).

cnf(c_1909,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1907,c_1871])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_732,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1213,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54)
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_2531,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1909,c_1213])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_24,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_38,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_727,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1217,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_1704,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1523,c_1217])).

cnf(c_1777,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1704,c_1524])).

cnf(c_1911,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1907,c_1777])).

cnf(c_1703,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1523,c_1216])).

cnf(c_2147,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1703,c_1524,c_1907])).

cnf(c_6120,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2531,c_35,c_38,c_1911,c_2147])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_20,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_349,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_350,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_47,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_352,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_30,c_29,c_47])).

cnf(c_362,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_352])).

cnf(c_363,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_3,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_13,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_385,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_3,c_13])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_389,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_385,c_13,c_3,c_2])).

cnf(c_390,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_389])).

cnf(c_471,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_363,c_390])).

cnf(c_723,plain,
    ( ~ v1_funct_2(X0_54,X0_55,k2_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | k1_relat_1(X0_54) = X0_55 ),
    inference(subtyping,[status(esa)],[c_471])).

cnf(c_1221,plain,
    ( k1_relat_1(X0_54) = X0_55
    | v1_funct_2(X0_54,X0_55,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_723])).

cnf(c_2939,plain,
    ( k1_relat_1(X0_54) = X0_55
    | v1_funct_2(X0_54,X0_55,k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1221,c_1907])).

cnf(c_2949,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_55))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2147,c_2939])).

cnf(c_3005,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_55))) != iProver_top
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2949,c_35,c_1911])).

cnf(c_3006,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_55))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3005])).

cnf(c_3013,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2147,c_3006])).

cnf(c_6122,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_6120,c_3013])).

cnf(c_14,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_23,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_501,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_502,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_722,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_502])).

cnf(c_1222,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_722])).

cnf(c_1702,plain,
    ( k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1523,c_1222])).

cnf(c_2256,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1702,c_1524,c_1907])).

cnf(c_3022,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3013,c_2256])).

cnf(c_6124,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6122,c_3022])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_739,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k3_relset_1(X0_55,X1_55,X0_54) = k4_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1206,plain,
    ( k3_relset_1(X0_55,X1_55,X0_54) = k4_relat_1(X0_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_739])).

cnf(c_2150,plain,
    ( k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2147,c_1206])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X2,X1,k3_relset_1(X1,X2,X0)) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_738,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k2_relset_1(X1_55,X0_55,k3_relset_1(X0_55,X1_55,X0_54)) = k1_relset_1(X0_55,X1_55,X0_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1207,plain,
    ( k2_relset_1(X0_55,X1_55,k3_relset_1(X1_55,X0_55,X0_54)) = k1_relset_1(X1_55,X0_55,X0_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_738])).

cnf(c_2155,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(superposition,[status(thm)],[c_2147,c_1207])).

cnf(c_2162,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(demodulation,[status(thm)],[c_2150,c_2155])).

cnf(c_743,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1202,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_1562,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_1202])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k4_relat_1(X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_745,plain,
    ( ~ v1_relat_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | k4_relat_1(X0_54) = k2_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1200,plain,
    ( k4_relat_1(X0_54) = k2_funct_1(X0_54)
    | v1_relat_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_745])).

cnf(c_1641,plain,
    ( k4_relat_1(sK2) = k2_funct_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1562,c_1200])).

cnf(c_779,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_745])).

cnf(c_1420,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_2214,plain,
    ( k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1641,c_28,c_26,c_24,c_779,c_1420])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_741,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k1_relset_1(X0_55,X1_55,X0_54) = k1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1204,plain,
    ( k1_relset_1(X0_55,X1_55,X0_54) = k1_relat_1(X0_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_1567,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1216,c_1204])).

cnf(c_1869,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1567,c_1523,c_1524])).

cnf(c_1910,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1907,c_1869])).

cnf(c_3019,plain,
    ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3013,c_1910])).

cnf(c_2934,plain,
    ( k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2150,c_2214])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_742,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | m1_subset_1(k3_relset_1(X0_55,X1_55,X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1203,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(k3_relset_1(X0_55,X1_55,X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_742])).

cnf(c_2936,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2934,c_1203])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_736,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55)))
    | ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1209,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_2400,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1909,c_1209])).

cnf(c_4178,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2936,c_35,c_38,c_1911,c_2147,c_2400])).

cnf(c_4182,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4178,c_3013])).

cnf(c_4188,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4182,c_1205])).

cnf(c_5556,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2162,c_2214,c_3013,c_3019,c_4188])).

cnf(c_5559,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_5556,c_4188])).

cnf(c_5571,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5559,c_1213])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_744,plain,
    ( ~ v1_relat_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | k2_funct_1(k2_funct_1(X0_54)) = X0_54 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1201,plain,
    ( k2_funct_1(k2_funct_1(X0_54)) = X0_54
    | v1_relat_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_1927,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1562,c_1201])).

cnf(c_782,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_744])).

cnf(c_2218,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1927,c_28,c_26,c_24,c_782,c_1420])).

cnf(c_5609,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5571,c_2218])).

cnf(c_32,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_34,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_36,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_753,plain,
    ( X0_54 != X1_54
    | k2_funct_1(X0_54) = k2_funct_1(X1_54) ),
    theory(equality)).

cnf(c_763,plain,
    ( k2_funct_1(sK2) = k2_funct_1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_753])).

cnf(c_747,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_774,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_747])).

cnf(c_815,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_1473,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_732])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_731,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ l1_struct_0(X1_56)
    | ~ l1_struct_0(X0_56)
    | ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_54))
    | k2_relset_1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_54) != k2_struct_0(X1_56) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1476,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_1477,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1476])).

cnf(c_752,plain,
    ( X0_55 != X1_55
    | X2_55 != X1_55
    | X2_55 = X0_55 ),
    theory(equality)).

cnf(c_1512,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_55
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0_55 ),
    inference(instantiation,[status(thm)],[c_752])).

cnf(c_1604,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1512])).

cnf(c_3021,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3013,c_1911])).

cnf(c_3023,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3013,c_2147])).

cnf(c_751,plain,
    ( X0_54 != X1_54
    | X2_54 != X1_54
    | X2_54 = X0_54 ),
    theory(equality)).

cnf(c_2470,plain,
    ( X0_54 != X1_54
    | k2_funct_1(sK2) != X1_54
    | k2_funct_1(sK2) = X0_54 ),
    inference(instantiation,[status(thm)],[c_751])).

cnf(c_3919,plain,
    ( X0_54 != k2_funct_1(sK2)
    | k2_funct_1(sK2) = X0_54
    | k2_funct_1(sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2470])).

cnf(c_5138,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_funct_1(sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3919])).

cnf(c_4835,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4188,c_1213])).

cnf(c_4879,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4835,c_2218])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_734,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k2_funct_1(X0_54))
    | ~ v2_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1464,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_1465,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1464])).

cnf(c_5169,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4879,c_29,c_35,c_36,c_37,c_38,c_815,c_729,c_1465,c_1604,c_4182])).

cnf(c_3020,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3013,c_1909])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_735,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1210,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_735])).

cnf(c_5179,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3020,c_1210])).

cnf(c_754,plain,
    ( ~ v2_funct_1(X0_54)
    | v2_funct_1(X1_54)
    | X1_54 != X0_54 ),
    theory(equality)).

cnf(c_2047,plain,
    ( ~ v2_funct_1(X0_54)
    | v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != X0_54 ),
    inference(instantiation,[status(thm)],[c_754])).

cnf(c_5511,plain,
    ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_2047])).

cnf(c_5512,plain,
    ( k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5511])).

cnf(c_5629,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5609,c_32,c_29,c_34,c_28,c_35,c_27,c_36,c_26,c_37,c_24,c_38,c_763,c_774,c_815,c_729,c_1473,c_1477,c_1604,c_3021,c_3023,c_5138,c_5169,c_5179,c_5512,c_5556])).

cnf(c_6125,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6124,c_5629])).

cnf(c_6126,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6125])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6126,c_3023,c_3021,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:47:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.01/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/0.97  
% 3.01/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.01/0.97  
% 3.01/0.97  ------  iProver source info
% 3.01/0.97  
% 3.01/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.01/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.01/0.97  git: non_committed_changes: false
% 3.01/0.97  git: last_make_outside_of_git: false
% 3.01/0.97  
% 3.01/0.97  ------ 
% 3.01/0.97  
% 3.01/0.97  ------ Input Options
% 3.01/0.97  
% 3.01/0.97  --out_options                           all
% 3.01/0.97  --tptp_safe_out                         true
% 3.01/0.97  --problem_path                          ""
% 3.01/0.97  --include_path                          ""
% 3.01/0.97  --clausifier                            res/vclausify_rel
% 3.01/0.97  --clausifier_options                    --mode clausify
% 3.01/0.97  --stdin                                 false
% 3.01/0.97  --stats_out                             all
% 3.01/0.97  
% 3.01/0.97  ------ General Options
% 3.01/0.97  
% 3.01/0.97  --fof                                   false
% 3.01/0.97  --time_out_real                         305.
% 3.01/0.97  --time_out_virtual                      -1.
% 3.01/0.97  --symbol_type_check                     false
% 3.01/0.97  --clausify_out                          false
% 3.01/0.97  --sig_cnt_out                           false
% 3.01/0.97  --trig_cnt_out                          false
% 3.01/0.97  --trig_cnt_out_tolerance                1.
% 3.01/0.97  --trig_cnt_out_sk_spl                   false
% 3.01/0.97  --abstr_cl_out                          false
% 3.01/0.97  
% 3.01/0.97  ------ Global Options
% 3.01/0.97  
% 3.01/0.97  --schedule                              default
% 3.01/0.97  --add_important_lit                     false
% 3.01/0.97  --prop_solver_per_cl                    1000
% 3.01/0.97  --min_unsat_core                        false
% 3.01/0.97  --soft_assumptions                      false
% 3.01/0.97  --soft_lemma_size                       3
% 3.01/0.97  --prop_impl_unit_size                   0
% 3.01/0.97  --prop_impl_unit                        []
% 3.01/0.97  --share_sel_clauses                     true
% 3.01/0.97  --reset_solvers                         false
% 3.01/0.97  --bc_imp_inh                            [conj_cone]
% 3.01/0.97  --conj_cone_tolerance                   3.
% 3.01/0.97  --extra_neg_conj                        none
% 3.01/0.97  --large_theory_mode                     true
% 3.01/0.97  --prolific_symb_bound                   200
% 3.01/0.97  --lt_threshold                          2000
% 3.01/0.97  --clause_weak_htbl                      true
% 3.01/0.97  --gc_record_bc_elim                     false
% 3.01/0.97  
% 3.01/0.97  ------ Preprocessing Options
% 3.01/0.97  
% 3.01/0.97  --preprocessing_flag                    true
% 3.01/0.97  --time_out_prep_mult                    0.1
% 3.01/0.97  --splitting_mode                        input
% 3.01/0.97  --splitting_grd                         true
% 3.01/0.97  --splitting_cvd                         false
% 3.01/0.97  --splitting_cvd_svl                     false
% 3.01/0.97  --splitting_nvd                         32
% 3.01/0.97  --sub_typing                            true
% 3.01/0.97  --prep_gs_sim                           true
% 3.01/0.97  --prep_unflatten                        true
% 3.01/0.97  --prep_res_sim                          true
% 3.01/0.97  --prep_upred                            true
% 3.01/0.97  --prep_sem_filter                       exhaustive
% 3.01/0.97  --prep_sem_filter_out                   false
% 3.01/0.97  --pred_elim                             true
% 3.01/0.97  --res_sim_input                         true
% 3.01/0.97  --eq_ax_congr_red                       true
% 3.01/0.97  --pure_diseq_elim                       true
% 3.01/0.97  --brand_transform                       false
% 3.01/0.97  --non_eq_to_eq                          false
% 3.01/0.97  --prep_def_merge                        true
% 3.01/0.97  --prep_def_merge_prop_impl              false
% 3.01/0.97  --prep_def_merge_mbd                    true
% 3.01/0.97  --prep_def_merge_tr_red                 false
% 3.01/0.97  --prep_def_merge_tr_cl                  false
% 3.01/0.97  --smt_preprocessing                     true
% 3.01/0.97  --smt_ac_axioms                         fast
% 3.01/0.97  --preprocessed_out                      false
% 3.01/0.97  --preprocessed_stats                    false
% 3.01/0.97  
% 3.01/0.97  ------ Abstraction refinement Options
% 3.01/0.97  
% 3.01/0.97  --abstr_ref                             []
% 3.01/0.97  --abstr_ref_prep                        false
% 3.01/0.97  --abstr_ref_until_sat                   false
% 3.01/0.97  --abstr_ref_sig_restrict                funpre
% 3.01/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/0.97  --abstr_ref_under                       []
% 3.01/0.97  
% 3.01/0.97  ------ SAT Options
% 3.01/0.97  
% 3.01/0.97  --sat_mode                              false
% 3.01/0.97  --sat_fm_restart_options                ""
% 3.01/0.97  --sat_gr_def                            false
% 3.01/0.97  --sat_epr_types                         true
% 3.01/0.97  --sat_non_cyclic_types                  false
% 3.01/0.97  --sat_finite_models                     false
% 3.01/0.97  --sat_fm_lemmas                         false
% 3.01/0.97  --sat_fm_prep                           false
% 3.01/0.97  --sat_fm_uc_incr                        true
% 3.01/0.97  --sat_out_model                         small
% 3.01/0.97  --sat_out_clauses                       false
% 3.01/0.97  
% 3.01/0.97  ------ QBF Options
% 3.01/0.97  
% 3.01/0.97  --qbf_mode                              false
% 3.01/0.97  --qbf_elim_univ                         false
% 3.01/0.97  --qbf_dom_inst                          none
% 3.01/0.97  --qbf_dom_pre_inst                      false
% 3.01/0.97  --qbf_sk_in                             false
% 3.01/0.97  --qbf_pred_elim                         true
% 3.01/0.97  --qbf_split                             512
% 3.01/0.97  
% 3.01/0.97  ------ BMC1 Options
% 3.01/0.97  
% 3.01/0.97  --bmc1_incremental                      false
% 3.01/0.97  --bmc1_axioms                           reachable_all
% 3.01/0.97  --bmc1_min_bound                        0
% 3.01/0.97  --bmc1_max_bound                        -1
% 3.01/0.97  --bmc1_max_bound_default                -1
% 3.01/0.97  --bmc1_symbol_reachability              true
% 3.01/0.97  --bmc1_property_lemmas                  false
% 3.01/0.97  --bmc1_k_induction                      false
% 3.01/0.97  --bmc1_non_equiv_states                 false
% 3.01/0.97  --bmc1_deadlock                         false
% 3.01/0.97  --bmc1_ucm                              false
% 3.01/0.97  --bmc1_add_unsat_core                   none
% 3.01/0.97  --bmc1_unsat_core_children              false
% 3.01/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/0.97  --bmc1_out_stat                         full
% 3.01/0.97  --bmc1_ground_init                      false
% 3.01/0.97  --bmc1_pre_inst_next_state              false
% 3.01/0.97  --bmc1_pre_inst_state                   false
% 3.01/0.97  --bmc1_pre_inst_reach_state             false
% 3.01/0.97  --bmc1_out_unsat_core                   false
% 3.01/0.97  --bmc1_aig_witness_out                  false
% 3.01/0.97  --bmc1_verbose                          false
% 3.01/0.97  --bmc1_dump_clauses_tptp                false
% 3.01/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.01/0.97  --bmc1_dump_file                        -
% 3.01/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.01/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.01/0.97  --bmc1_ucm_extend_mode                  1
% 3.01/0.97  --bmc1_ucm_init_mode                    2
% 3.01/0.97  --bmc1_ucm_cone_mode                    none
% 3.01/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.01/0.97  --bmc1_ucm_relax_model                  4
% 3.01/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.01/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/0.97  --bmc1_ucm_layered_model                none
% 3.01/0.97  --bmc1_ucm_max_lemma_size               10
% 3.01/0.97  
% 3.01/0.97  ------ AIG Options
% 3.01/0.97  
% 3.01/0.97  --aig_mode                              false
% 3.01/0.97  
% 3.01/0.97  ------ Instantiation Options
% 3.01/0.97  
% 3.01/0.97  --instantiation_flag                    true
% 3.01/0.97  --inst_sos_flag                         false
% 3.01/0.97  --inst_sos_phase                        true
% 3.01/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/0.97  --inst_lit_sel_side                     num_symb
% 3.01/0.97  --inst_solver_per_active                1400
% 3.01/0.97  --inst_solver_calls_frac                1.
% 3.01/0.97  --inst_passive_queue_type               priority_queues
% 3.01/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/0.97  --inst_passive_queues_freq              [25;2]
% 3.01/0.97  --inst_dismatching                      true
% 3.01/0.97  --inst_eager_unprocessed_to_passive     true
% 3.01/0.97  --inst_prop_sim_given                   true
% 3.01/0.97  --inst_prop_sim_new                     false
% 3.01/0.97  --inst_subs_new                         false
% 3.01/0.97  --inst_eq_res_simp                      false
% 3.01/0.97  --inst_subs_given                       false
% 3.01/0.97  --inst_orphan_elimination               true
% 3.01/0.97  --inst_learning_loop_flag               true
% 3.01/0.97  --inst_learning_start                   3000
% 3.01/0.97  --inst_learning_factor                  2
% 3.01/0.97  --inst_start_prop_sim_after_learn       3
% 3.01/0.97  --inst_sel_renew                        solver
% 3.01/0.97  --inst_lit_activity_flag                true
% 3.01/0.97  --inst_restr_to_given                   false
% 3.01/0.97  --inst_activity_threshold               500
% 3.01/0.97  --inst_out_proof                        true
% 3.01/0.97  
% 3.01/0.97  ------ Resolution Options
% 3.01/0.97  
% 3.01/0.97  --resolution_flag                       true
% 3.01/0.97  --res_lit_sel                           adaptive
% 3.01/0.97  --res_lit_sel_side                      none
% 3.01/0.97  --res_ordering                          kbo
% 3.01/0.97  --res_to_prop_solver                    active
% 3.01/0.97  --res_prop_simpl_new                    false
% 3.01/0.97  --res_prop_simpl_given                  true
% 3.01/0.97  --res_passive_queue_type                priority_queues
% 3.01/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/0.97  --res_passive_queues_freq               [15;5]
% 3.01/0.97  --res_forward_subs                      full
% 3.01/0.97  --res_backward_subs                     full
% 3.01/0.97  --res_forward_subs_resolution           true
% 3.01/0.97  --res_backward_subs_resolution          true
% 3.01/0.97  --res_orphan_elimination                true
% 3.01/0.97  --res_time_limit                        2.
% 3.01/0.97  --res_out_proof                         true
% 3.01/0.97  
% 3.01/0.97  ------ Superposition Options
% 3.01/0.97  
% 3.01/0.97  --superposition_flag                    true
% 3.01/0.97  --sup_passive_queue_type                priority_queues
% 3.01/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.01/0.97  --demod_completeness_check              fast
% 3.01/0.97  --demod_use_ground                      true
% 3.01/0.97  --sup_to_prop_solver                    passive
% 3.01/0.97  --sup_prop_simpl_new                    true
% 3.01/0.97  --sup_prop_simpl_given                  true
% 3.01/0.97  --sup_fun_splitting                     false
% 3.01/0.97  --sup_smt_interval                      50000
% 3.01/0.97  
% 3.01/0.97  ------ Superposition Simplification Setup
% 3.01/0.97  
% 3.01/0.97  --sup_indices_passive                   []
% 3.01/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.97  --sup_full_bw                           [BwDemod]
% 3.01/0.97  --sup_immed_triv                        [TrivRules]
% 3.01/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.97  --sup_immed_bw_main                     []
% 3.01/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.97  
% 3.01/0.97  ------ Combination Options
% 3.01/0.97  
% 3.01/0.97  --comb_res_mult                         3
% 3.01/0.97  --comb_sup_mult                         2
% 3.01/0.97  --comb_inst_mult                        10
% 3.01/0.97  
% 3.01/0.97  ------ Debug Options
% 3.01/0.97  
% 3.01/0.97  --dbg_backtrace                         false
% 3.01/0.97  --dbg_dump_prop_clauses                 false
% 3.01/0.97  --dbg_dump_prop_clauses_file            -
% 3.01/0.97  --dbg_out_stat                          false
% 3.01/0.97  ------ Parsing...
% 3.01/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.01/0.97  
% 3.01/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.01/0.97  
% 3.01/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.01/0.97  
% 3.01/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/0.97  ------ Proving...
% 3.01/0.97  ------ Problem Properties 
% 3.01/0.97  
% 3.01/0.97  
% 3.01/0.97  clauses                                 24
% 3.01/0.97  conjectures                             7
% 3.01/0.97  EPR                                     4
% 3.01/0.97  Horn                                    24
% 3.01/0.97  unary                                   7
% 3.01/0.97  binary                                  8
% 3.01/0.97  lits                                    72
% 3.01/0.97  lits eq                                 17
% 3.01/0.97  fd_pure                                 0
% 3.01/0.97  fd_pseudo                               0
% 3.01/0.97  fd_cond                                 0
% 3.01/0.97  fd_pseudo_cond                          1
% 3.01/0.97  AC symbols                              0
% 3.01/0.97  
% 3.01/0.97  ------ Schedule dynamic 5 is on 
% 3.01/0.97  
% 3.01/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.01/0.97  
% 3.01/0.97  
% 3.01/0.97  ------ 
% 3.01/0.97  Current options:
% 3.01/0.97  ------ 
% 3.01/0.97  
% 3.01/0.97  ------ Input Options
% 3.01/0.97  
% 3.01/0.97  --out_options                           all
% 3.01/0.97  --tptp_safe_out                         true
% 3.01/0.97  --problem_path                          ""
% 3.01/0.97  --include_path                          ""
% 3.01/0.97  --clausifier                            res/vclausify_rel
% 3.01/0.97  --clausifier_options                    --mode clausify
% 3.01/0.97  --stdin                                 false
% 3.01/0.97  --stats_out                             all
% 3.01/0.97  
% 3.01/0.97  ------ General Options
% 3.01/0.97  
% 3.01/0.97  --fof                                   false
% 3.01/0.97  --time_out_real                         305.
% 3.01/0.97  --time_out_virtual                      -1.
% 3.01/0.97  --symbol_type_check                     false
% 3.01/0.97  --clausify_out                          false
% 3.01/0.97  --sig_cnt_out                           false
% 3.01/0.97  --trig_cnt_out                          false
% 3.01/0.97  --trig_cnt_out_tolerance                1.
% 3.01/0.97  --trig_cnt_out_sk_spl                   false
% 3.01/0.97  --abstr_cl_out                          false
% 3.01/0.97  
% 3.01/0.97  ------ Global Options
% 3.01/0.97  
% 3.01/0.97  --schedule                              default
% 3.01/0.97  --add_important_lit                     false
% 3.01/0.97  --prop_solver_per_cl                    1000
% 3.01/0.97  --min_unsat_core                        false
% 3.01/0.97  --soft_assumptions                      false
% 3.01/0.97  --soft_lemma_size                       3
% 3.01/0.97  --prop_impl_unit_size                   0
% 3.01/0.97  --prop_impl_unit                        []
% 3.01/0.97  --share_sel_clauses                     true
% 3.01/0.97  --reset_solvers                         false
% 3.01/0.97  --bc_imp_inh                            [conj_cone]
% 3.01/0.97  --conj_cone_tolerance                   3.
% 3.01/0.97  --extra_neg_conj                        none
% 3.01/0.97  --large_theory_mode                     true
% 3.01/0.97  --prolific_symb_bound                   200
% 3.01/0.97  --lt_threshold                          2000
% 3.01/0.97  --clause_weak_htbl                      true
% 3.01/0.97  --gc_record_bc_elim                     false
% 3.01/0.97  
% 3.01/0.97  ------ Preprocessing Options
% 3.01/0.97  
% 3.01/0.97  --preprocessing_flag                    true
% 3.01/0.97  --time_out_prep_mult                    0.1
% 3.01/0.97  --splitting_mode                        input
% 3.01/0.97  --splitting_grd                         true
% 3.01/0.97  --splitting_cvd                         false
% 3.01/0.97  --splitting_cvd_svl                     false
% 3.01/0.97  --splitting_nvd                         32
% 3.01/0.97  --sub_typing                            true
% 3.01/0.97  --prep_gs_sim                           true
% 3.01/0.97  --prep_unflatten                        true
% 3.01/0.97  --prep_res_sim                          true
% 3.01/0.97  --prep_upred                            true
% 3.01/0.97  --prep_sem_filter                       exhaustive
% 3.01/0.97  --prep_sem_filter_out                   false
% 3.01/0.97  --pred_elim                             true
% 3.01/0.97  --res_sim_input                         true
% 3.01/0.97  --eq_ax_congr_red                       true
% 3.01/0.97  --pure_diseq_elim                       true
% 3.01/0.97  --brand_transform                       false
% 3.01/0.97  --non_eq_to_eq                          false
% 3.01/0.97  --prep_def_merge                        true
% 3.01/0.97  --prep_def_merge_prop_impl              false
% 3.01/0.97  --prep_def_merge_mbd                    true
% 3.01/0.97  --prep_def_merge_tr_red                 false
% 3.01/0.97  --prep_def_merge_tr_cl                  false
% 3.01/0.97  --smt_preprocessing                     true
% 3.01/0.97  --smt_ac_axioms                         fast
% 3.01/0.97  --preprocessed_out                      false
% 3.01/0.97  --preprocessed_stats                    false
% 3.01/0.97  
% 3.01/0.97  ------ Abstraction refinement Options
% 3.01/0.97  
% 3.01/0.97  --abstr_ref                             []
% 3.01/0.97  --abstr_ref_prep                        false
% 3.01/0.97  --abstr_ref_until_sat                   false
% 3.01/0.97  --abstr_ref_sig_restrict                funpre
% 3.01/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/0.97  --abstr_ref_under                       []
% 3.01/0.97  
% 3.01/0.97  ------ SAT Options
% 3.01/0.97  
% 3.01/0.97  --sat_mode                              false
% 3.01/0.97  --sat_fm_restart_options                ""
% 3.01/0.97  --sat_gr_def                            false
% 3.01/0.97  --sat_epr_types                         true
% 3.01/0.97  --sat_non_cyclic_types                  false
% 3.01/0.97  --sat_finite_models                     false
% 3.01/0.97  --sat_fm_lemmas                         false
% 3.01/0.97  --sat_fm_prep                           false
% 3.01/0.97  --sat_fm_uc_incr                        true
% 3.01/0.97  --sat_out_model                         small
% 3.01/0.97  --sat_out_clauses                       false
% 3.01/0.97  
% 3.01/0.97  ------ QBF Options
% 3.01/0.97  
% 3.01/0.97  --qbf_mode                              false
% 3.01/0.97  --qbf_elim_univ                         false
% 3.01/0.97  --qbf_dom_inst                          none
% 3.01/0.97  --qbf_dom_pre_inst                      false
% 3.01/0.97  --qbf_sk_in                             false
% 3.01/0.97  --qbf_pred_elim                         true
% 3.01/0.97  --qbf_split                             512
% 3.01/0.97  
% 3.01/0.97  ------ BMC1 Options
% 3.01/0.97  
% 3.01/0.97  --bmc1_incremental                      false
% 3.01/0.97  --bmc1_axioms                           reachable_all
% 3.01/0.97  --bmc1_min_bound                        0
% 3.01/0.97  --bmc1_max_bound                        -1
% 3.01/0.97  --bmc1_max_bound_default                -1
% 3.01/0.97  --bmc1_symbol_reachability              true
% 3.01/0.97  --bmc1_property_lemmas                  false
% 3.01/0.97  --bmc1_k_induction                      false
% 3.01/0.97  --bmc1_non_equiv_states                 false
% 3.01/0.97  --bmc1_deadlock                         false
% 3.01/0.97  --bmc1_ucm                              false
% 3.01/0.97  --bmc1_add_unsat_core                   none
% 3.01/0.97  --bmc1_unsat_core_children              false
% 3.01/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/0.97  --bmc1_out_stat                         full
% 3.01/0.97  --bmc1_ground_init                      false
% 3.01/0.97  --bmc1_pre_inst_next_state              false
% 3.01/0.97  --bmc1_pre_inst_state                   false
% 3.01/0.97  --bmc1_pre_inst_reach_state             false
% 3.01/0.97  --bmc1_out_unsat_core                   false
% 3.01/0.97  --bmc1_aig_witness_out                  false
% 3.01/0.97  --bmc1_verbose                          false
% 3.01/0.97  --bmc1_dump_clauses_tptp                false
% 3.01/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.01/0.97  --bmc1_dump_file                        -
% 3.01/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.01/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.01/0.97  --bmc1_ucm_extend_mode                  1
% 3.01/0.97  --bmc1_ucm_init_mode                    2
% 3.01/0.97  --bmc1_ucm_cone_mode                    none
% 3.01/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.01/0.97  --bmc1_ucm_relax_model                  4
% 3.01/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.01/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/0.97  --bmc1_ucm_layered_model                none
% 3.01/0.97  --bmc1_ucm_max_lemma_size               10
% 3.01/0.97  
% 3.01/0.97  ------ AIG Options
% 3.01/0.97  
% 3.01/0.97  --aig_mode                              false
% 3.01/0.97  
% 3.01/0.97  ------ Instantiation Options
% 3.01/0.97  
% 3.01/0.97  --instantiation_flag                    true
% 3.01/0.97  --inst_sos_flag                         false
% 3.01/0.97  --inst_sos_phase                        true
% 3.01/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/0.97  --inst_lit_sel_side                     none
% 3.01/0.97  --inst_solver_per_active                1400
% 3.01/0.97  --inst_solver_calls_frac                1.
% 3.01/0.97  --inst_passive_queue_type               priority_queues
% 3.01/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/0.97  --inst_passive_queues_freq              [25;2]
% 3.01/0.97  --inst_dismatching                      true
% 3.01/0.97  --inst_eager_unprocessed_to_passive     true
% 3.01/0.97  --inst_prop_sim_given                   true
% 3.01/0.97  --inst_prop_sim_new                     false
% 3.01/0.97  --inst_subs_new                         false
% 3.01/0.97  --inst_eq_res_simp                      false
% 3.01/0.97  --inst_subs_given                       false
% 3.01/0.97  --inst_orphan_elimination               true
% 3.01/0.97  --inst_learning_loop_flag               true
% 3.01/0.97  --inst_learning_start                   3000
% 3.01/0.97  --inst_learning_factor                  2
% 3.01/0.97  --inst_start_prop_sim_after_learn       3
% 3.01/0.97  --inst_sel_renew                        solver
% 3.01/0.97  --inst_lit_activity_flag                true
% 3.01/0.97  --inst_restr_to_given                   false
% 3.01/0.97  --inst_activity_threshold               500
% 3.01/0.97  --inst_out_proof                        true
% 3.01/0.97  
% 3.01/0.97  ------ Resolution Options
% 3.01/0.97  
% 3.01/0.97  --resolution_flag                       false
% 3.01/0.97  --res_lit_sel                           adaptive
% 3.01/0.97  --res_lit_sel_side                      none
% 3.01/0.97  --res_ordering                          kbo
% 3.01/0.97  --res_to_prop_solver                    active
% 3.01/0.97  --res_prop_simpl_new                    false
% 3.01/0.97  --res_prop_simpl_given                  true
% 3.01/0.97  --res_passive_queue_type                priority_queues
% 3.01/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/0.97  --res_passive_queues_freq               [15;5]
% 3.01/0.97  --res_forward_subs                      full
% 3.01/0.97  --res_backward_subs                     full
% 3.01/0.97  --res_forward_subs_resolution           true
% 3.01/0.97  --res_backward_subs_resolution          true
% 3.01/0.97  --res_orphan_elimination                true
% 3.01/0.97  --res_time_limit                        2.
% 3.01/0.97  --res_out_proof                         true
% 3.01/0.97  
% 3.01/0.97  ------ Superposition Options
% 3.01/0.97  
% 3.01/0.97  --superposition_flag                    true
% 3.01/0.97  --sup_passive_queue_type                priority_queues
% 3.01/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.01/0.97  --demod_completeness_check              fast
% 3.01/0.97  --demod_use_ground                      true
% 3.01/0.97  --sup_to_prop_solver                    passive
% 3.01/0.97  --sup_prop_simpl_new                    true
% 3.01/0.97  --sup_prop_simpl_given                  true
% 3.01/0.97  --sup_fun_splitting                     false
% 3.01/0.97  --sup_smt_interval                      50000
% 3.01/0.97  
% 3.01/0.97  ------ Superposition Simplification Setup
% 3.01/0.97  
% 3.01/0.97  --sup_indices_passive                   []
% 3.01/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.97  --sup_full_bw                           [BwDemod]
% 3.01/0.97  --sup_immed_triv                        [TrivRules]
% 3.01/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.97  --sup_immed_bw_main                     []
% 3.01/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.97  
% 3.01/0.97  ------ Combination Options
% 3.01/0.97  
% 3.01/0.97  --comb_res_mult                         3
% 3.01/0.97  --comb_sup_mult                         2
% 3.01/0.97  --comb_inst_mult                        10
% 3.01/0.97  
% 3.01/0.97  ------ Debug Options
% 3.01/0.97  
% 3.01/0.97  --dbg_backtrace                         false
% 3.01/0.97  --dbg_dump_prop_clauses                 false
% 3.01/0.97  --dbg_dump_prop_clauses_file            -
% 3.01/0.97  --dbg_out_stat                          false
% 3.01/0.97  
% 3.01/0.97  
% 3.01/0.97  
% 3.01/0.97  
% 3.01/0.97  ------ Proving...
% 3.01/0.97  
% 3.01/0.97  
% 3.01/0.97  % SZS status Theorem for theBenchmark.p
% 3.01/0.97  
% 3.01/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.01/0.97  
% 3.01/0.97  fof(f18,conjecture,(
% 3.01/0.97    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.97  
% 3.01/0.97  fof(f19,negated_conjecture,(
% 3.01/0.97    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.01/0.97    inference(negated_conjecture,[],[f18])).
% 3.01/0.97  
% 3.01/0.97  fof(f47,plain,(
% 3.01/0.97    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.01/0.97    inference(ennf_transformation,[],[f19])).
% 3.01/0.97  
% 3.01/0.97  fof(f48,plain,(
% 3.01/0.97    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.01/0.97    inference(flattening,[],[f47])).
% 3.01/0.97  
% 3.01/0.97  fof(f53,plain,(
% 3.01/0.97    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.01/0.97    introduced(choice_axiom,[])).
% 3.01/0.97  
% 3.01/0.97  fof(f52,plain,(
% 3.01/0.97    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 3.01/0.97    introduced(choice_axiom,[])).
% 3.01/0.97  
% 3.01/0.97  fof(f51,plain,(
% 3.01/0.97    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 3.01/0.97    introduced(choice_axiom,[])).
% 3.01/0.97  
% 3.01/0.97  fof(f54,plain,(
% 3.01/0.97    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 3.01/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f53,f52,f51])).
% 3.01/0.97  
% 3.01/0.97  fof(f78,plain,(
% 3.01/0.97    l1_struct_0(sK0)),
% 3.01/0.97    inference(cnf_transformation,[],[f54])).
% 3.01/0.97  
% 3.01/0.97  fof(f14,axiom,(
% 3.01/0.97    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.97  
% 3.01/0.97  fof(f40,plain,(
% 3.01/0.97    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.01/0.97    inference(ennf_transformation,[],[f14])).
% 3.01/0.97  
% 3.01/0.97  fof(f74,plain,(
% 3.01/0.97    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.01/0.97    inference(cnf_transformation,[],[f40])).
% 3.01/0.97  
% 3.01/0.97  fof(f80,plain,(
% 3.01/0.97    l1_struct_0(sK1)),
% 3.01/0.97    inference(cnf_transformation,[],[f54])).
% 3.01/0.97  
% 3.01/0.97  fof(f84,plain,(
% 3.01/0.97    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 3.01/0.97    inference(cnf_transformation,[],[f54])).
% 3.01/0.97  
% 3.01/0.97  fof(f83,plain,(
% 3.01/0.97    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.01/0.97    inference(cnf_transformation,[],[f54])).
% 3.01/0.97  
% 3.01/0.97  fof(f7,axiom,(
% 3.01/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.97  
% 3.01/0.97  fof(f29,plain,(
% 3.01/0.97    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/0.97    inference(ennf_transformation,[],[f7])).
% 3.01/0.97  
% 3.01/0.97  fof(f61,plain,(
% 3.01/0.97    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/0.97    inference(cnf_transformation,[],[f29])).
% 3.01/0.97  
% 3.01/0.97  fof(f16,axiom,(
% 3.01/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.97  
% 3.01/0.97  fof(f43,plain,(
% 3.01/0.97    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.01/0.97    inference(ennf_transformation,[],[f16])).
% 3.01/0.97  
% 3.01/0.97  fof(f44,plain,(
% 3.01/0.97    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.01/0.97    inference(flattening,[],[f43])).
% 3.01/0.97  
% 3.01/0.97  fof(f76,plain,(
% 3.01/0.97    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.01/0.97    inference(cnf_transformation,[],[f44])).
% 3.01/0.97  
% 3.01/0.97  fof(f81,plain,(
% 3.01/0.97    v1_funct_1(sK2)),
% 3.01/0.97    inference(cnf_transformation,[],[f54])).
% 3.01/0.97  
% 3.01/0.97  fof(f85,plain,(
% 3.01/0.97    v2_funct_1(sK2)),
% 3.01/0.97    inference(cnf_transformation,[],[f54])).
% 3.01/0.97  
% 3.01/0.97  fof(f82,plain,(
% 3.01/0.97    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.01/0.97    inference(cnf_transformation,[],[f54])).
% 3.01/0.97  
% 3.01/0.97  fof(f10,axiom,(
% 3.01/0.97    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.97  
% 3.01/0.97  fof(f32,plain,(
% 3.01/0.97    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.01/0.97    inference(ennf_transformation,[],[f10])).
% 3.01/0.97  
% 3.01/0.97  fof(f33,plain,(
% 3.01/0.97    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.01/0.97    inference(flattening,[],[f32])).
% 3.01/0.97  
% 3.01/0.97  fof(f66,plain,(
% 3.01/0.97    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.01/0.97    inference(cnf_transformation,[],[f33])).
% 3.01/0.97  
% 3.01/0.97  fof(f15,axiom,(
% 3.01/0.97    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 3.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.97  
% 3.01/0.97  fof(f41,plain,(
% 3.01/0.97    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.01/0.97    inference(ennf_transformation,[],[f15])).
% 3.01/0.97  
% 3.01/0.97  fof(f42,plain,(
% 3.01/0.97    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.01/0.97    inference(flattening,[],[f41])).
% 3.01/0.97  
% 3.01/0.97  fof(f75,plain,(
% 3.01/0.97    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.01/0.97    inference(cnf_transformation,[],[f42])).
% 3.01/0.97  
% 3.01/0.97  fof(f79,plain,(
% 3.01/0.97    ~v2_struct_0(sK1)),
% 3.01/0.97    inference(cnf_transformation,[],[f54])).
% 3.01/0.97  
% 3.01/0.97  fof(f4,axiom,(
% 3.01/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.97  
% 3.01/0.97  fof(f20,plain,(
% 3.01/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.01/0.97    inference(pure_predicate_removal,[],[f4])).
% 3.01/0.97  
% 3.01/0.97  fof(f26,plain,(
% 3.01/0.97    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/0.97    inference(ennf_transformation,[],[f20])).
% 3.01/0.97  
% 3.01/0.97  fof(f58,plain,(
% 3.01/0.97    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/0.97    inference(cnf_transformation,[],[f26])).
% 3.01/0.97  
% 3.01/0.97  fof(f11,axiom,(
% 3.01/0.97    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.97  
% 3.01/0.97  fof(f34,plain,(
% 3.01/0.97    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.01/0.97    inference(ennf_transformation,[],[f11])).
% 3.01/0.97  
% 3.01/0.97  fof(f35,plain,(
% 3.01/0.97    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.01/0.97    inference(flattening,[],[f34])).
% 3.01/0.97  
% 3.01/0.97  fof(f49,plain,(
% 3.01/0.97    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.01/0.97    inference(nnf_transformation,[],[f35])).
% 3.01/0.97  
% 3.01/0.97  fof(f67,plain,(
% 3.01/0.97    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.01/0.97    inference(cnf_transformation,[],[f49])).
% 3.01/0.97  
% 3.01/0.97  fof(f3,axiom,(
% 3.01/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.97  
% 3.01/0.97  fof(f25,plain,(
% 3.01/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/0.97    inference(ennf_transformation,[],[f3])).
% 3.01/0.97  
% 3.01/0.97  fof(f57,plain,(
% 3.01/0.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/0.97    inference(cnf_transformation,[],[f25])).
% 3.01/0.97  
% 3.01/0.97  fof(f12,axiom,(
% 3.01/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 3.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.97  
% 3.01/0.97  fof(f36,plain,(
% 3.01/0.97    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.01/0.97    inference(ennf_transformation,[],[f12])).
% 3.01/0.97  
% 3.01/0.97  fof(f37,plain,(
% 3.01/0.97    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.01/0.97    inference(flattening,[],[f36])).
% 3.01/0.97  
% 3.01/0.97  fof(f50,plain,(
% 3.01/0.97    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.01/0.97    inference(nnf_transformation,[],[f37])).
% 3.01/0.97  
% 3.01/0.97  fof(f70,plain,(
% 3.01/0.97    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.01/0.97    inference(cnf_transformation,[],[f50])).
% 3.01/0.97  
% 3.01/0.97  fof(f88,plain,(
% 3.01/0.97    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.01/0.97    inference(equality_resolution,[],[f70])).
% 3.01/0.97  
% 3.01/0.97  fof(f86,plain,(
% 3.01/0.97    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 3.01/0.97    inference(cnf_transformation,[],[f54])).
% 3.01/0.97  
% 3.01/0.97  fof(f8,axiom,(
% 3.01/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k4_relat_1(X2) = k3_relset_1(X0,X1,X2))),
% 3.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.97  
% 3.01/0.97  fof(f30,plain,(
% 3.01/0.97    ! [X0,X1,X2] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/0.97    inference(ennf_transformation,[],[f8])).
% 3.01/0.97  
% 3.01/0.97  fof(f62,plain,(
% 3.01/0.97    ( ! [X2,X0,X1] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/0.97    inference(cnf_transformation,[],[f30])).
% 3.01/0.97  
% 3.01/0.97  fof(f9,axiom,(
% 3.01/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)))),
% 3.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.97  
% 3.01/0.97  fof(f31,plain,(
% 3.01/0.97    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/0.97    inference(ennf_transformation,[],[f9])).
% 3.01/0.97  
% 3.01/0.97  fof(f64,plain,(
% 3.01/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/0.97    inference(cnf_transformation,[],[f31])).
% 3.01/0.97  
% 3.01/0.97  fof(f1,axiom,(
% 3.01/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(X0) = k4_relat_1(X0)))),
% 3.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.97  
% 3.01/0.97  fof(f21,plain,(
% 3.01/0.97    ! [X0] : ((k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.01/0.97    inference(ennf_transformation,[],[f1])).
% 3.01/0.97  
% 3.01/0.97  fof(f22,plain,(
% 3.01/0.97    ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.01/0.97    inference(flattening,[],[f21])).
% 3.01/0.97  
% 3.01/0.97  fof(f55,plain,(
% 3.01/0.97    ( ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/0.97    inference(cnf_transformation,[],[f22])).
% 3.01/0.97  
% 3.01/0.97  fof(f6,axiom,(
% 3.01/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.97  
% 3.01/0.97  fof(f28,plain,(
% 3.01/0.97    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/0.97    inference(ennf_transformation,[],[f6])).
% 3.01/0.97  
% 3.01/0.97  fof(f60,plain,(
% 3.01/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/0.97    inference(cnf_transformation,[],[f28])).
% 3.01/0.97  
% 3.01/0.97  fof(f5,axiom,(
% 3.01/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.97  
% 3.01/0.97  fof(f27,plain,(
% 3.01/0.97    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/0.97    inference(ennf_transformation,[],[f5])).
% 3.01/0.97  
% 3.01/0.97  fof(f59,plain,(
% 3.01/0.97    ( ! [X2,X0,X1] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/0.97    inference(cnf_transformation,[],[f27])).
% 3.01/0.97  
% 3.01/0.97  fof(f13,axiom,(
% 3.01/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.97  
% 3.01/0.97  fof(f38,plain,(
% 3.01/0.97    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.01/0.97    inference(ennf_transformation,[],[f13])).
% 3.01/0.97  
% 3.01/0.97  fof(f39,plain,(
% 3.01/0.97    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.01/0.97    inference(flattening,[],[f38])).
% 3.01/0.97  
% 3.01/0.97  fof(f73,plain,(
% 3.01/0.97    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.01/0.97    inference(cnf_transformation,[],[f39])).
% 3.01/0.97  
% 3.01/0.97  fof(f2,axiom,(
% 3.01/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.97  
% 3.01/0.97  fof(f23,plain,(
% 3.01/0.97    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.01/0.97    inference(ennf_transformation,[],[f2])).
% 3.01/0.97  
% 3.01/0.97  fof(f24,plain,(
% 3.01/0.97    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.01/0.97    inference(flattening,[],[f23])).
% 3.01/0.97  
% 3.01/0.97  fof(f56,plain,(
% 3.01/0.97    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/0.97    inference(cnf_transformation,[],[f24])).
% 3.01/0.97  
% 3.01/0.97  fof(f17,axiom,(
% 3.01/0.97    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 3.01/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.97  
% 3.01/0.97  fof(f45,plain,(
% 3.01/0.97    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.01/0.97    inference(ennf_transformation,[],[f17])).
% 3.01/0.97  
% 3.01/0.97  fof(f46,plain,(
% 3.01/0.97    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.01/0.97    inference(flattening,[],[f45])).
% 3.01/0.97  
% 3.01/0.97  fof(f77,plain,(
% 3.01/0.97    ( ! [X2,X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.01/0.97    inference(cnf_transformation,[],[f46])).
% 3.01/0.97  
% 3.01/0.97  fof(f71,plain,(
% 3.01/0.97    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.01/0.97    inference(cnf_transformation,[],[f39])).
% 3.01/0.97  
% 3.01/0.97  fof(f72,plain,(
% 3.01/0.97    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.01/0.97    inference(cnf_transformation,[],[f39])).
% 3.01/0.97  
% 3.01/0.97  cnf(c_31,negated_conjecture,
% 3.01/0.97      ( l1_struct_0(sK0) ),
% 3.01/0.97      inference(cnf_transformation,[],[f78]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_724,negated_conjecture,
% 3.01/0.97      ( l1_struct_0(sK0) ),
% 3.01/0.97      inference(subtyping,[status(esa)],[c_31]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1220,plain,
% 3.01/0.97      ( l1_struct_0(sK0) = iProver_top ),
% 3.01/0.97      inference(predicate_to_equality,[status(thm)],[c_724]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_19,plain,
% 3.01/0.97      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.01/0.97      inference(cnf_transformation,[],[f74]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_733,plain,
% 3.01/0.97      ( ~ l1_struct_0(X0_56) | u1_struct_0(X0_56) = k2_struct_0(X0_56) ),
% 3.01/0.97      inference(subtyping,[status(esa)],[c_19]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1212,plain,
% 3.01/0.97      ( u1_struct_0(X0_56) = k2_struct_0(X0_56)
% 3.01/0.97      | l1_struct_0(X0_56) != iProver_top ),
% 3.01/0.97      inference(predicate_to_equality,[status(thm)],[c_733]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1524,plain,
% 3.01/0.97      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.01/0.97      inference(superposition,[status(thm)],[c_1220,c_1212]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_29,negated_conjecture,
% 3.01/0.97      ( l1_struct_0(sK1) ),
% 3.01/0.97      inference(cnf_transformation,[],[f80]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_725,negated_conjecture,
% 3.01/0.97      ( l1_struct_0(sK1) ),
% 3.01/0.97      inference(subtyping,[status(esa)],[c_29]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1219,plain,
% 3.01/0.97      ( l1_struct_0(sK1) = iProver_top ),
% 3.01/0.97      inference(predicate_to_equality,[status(thm)],[c_725]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1523,plain,
% 3.01/0.97      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.01/0.97      inference(superposition,[status(thm)],[c_1219,c_1212]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_25,negated_conjecture,
% 3.01/0.97      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.01/0.97      inference(cnf_transformation,[],[f84]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_729,negated_conjecture,
% 3.01/0.97      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.01/0.97      inference(subtyping,[status(esa)],[c_25]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1705,plain,
% 3.01/0.97      ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.01/0.97      inference(demodulation,[status(thm)],[c_1523,c_729]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1775,plain,
% 3.01/0.97      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.01/0.97      inference(demodulation,[status(thm)],[c_1524,c_1705]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_26,negated_conjecture,
% 3.01/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.01/0.97      inference(cnf_transformation,[],[f83]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_728,negated_conjecture,
% 3.01/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.01/0.97      inference(subtyping,[status(esa)],[c_26]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1216,plain,
% 3.01/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.01/0.97      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_6,plain,
% 3.01/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.97      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.01/0.97      inference(cnf_transformation,[],[f61]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_740,plain,
% 3.01/0.97      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.01/0.97      | k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54) ),
% 3.01/0.97      inference(subtyping,[status(esa)],[c_6]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1205,plain,
% 3.01/0.97      ( k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54)
% 3.01/0.97      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 3.01/0.97      inference(predicate_to_equality,[status(thm)],[c_740]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1638,plain,
% 3.01/0.97      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 3.01/0.97      inference(superposition,[status(thm)],[c_1216,c_1205]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1871,plain,
% 3.01/0.97      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 3.01/0.97      inference(light_normalisation,[status(thm)],[c_1638,c_1523,c_1524]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1907,plain,
% 3.01/0.97      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 3.01/0.97      inference(light_normalisation,[status(thm)],[c_1775,c_1871]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1909,plain,
% 3.01/0.97      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 3.01/0.97      inference(demodulation,[status(thm)],[c_1907,c_1871]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_21,plain,
% 3.01/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.97      | ~ v1_funct_1(X0)
% 3.01/0.97      | ~ v2_funct_1(X0)
% 3.01/0.97      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.01/0.97      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.01/0.97      inference(cnf_transformation,[],[f76]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_732,plain,
% 3.01/0.97      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 3.01/0.97      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.01/0.97      | ~ v1_funct_1(X0_54)
% 3.01/0.97      | ~ v2_funct_1(X0_54)
% 3.01/0.97      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 3.01/0.97      | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54) ),
% 3.01/0.97      inference(subtyping,[status(esa)],[c_21]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1213,plain,
% 3.01/0.97      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 3.01/0.97      | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54)
% 3.01/0.97      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 3.01/0.97      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.01/0.97      | v1_funct_1(X0_54) != iProver_top
% 3.01/0.97      | v2_funct_1(X0_54) != iProver_top ),
% 3.01/0.97      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_2531,plain,
% 3.01/0.97      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 3.01/0.97      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.01/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.01/0.97      | v1_funct_1(sK2) != iProver_top
% 3.01/0.97      | v2_funct_1(sK2) != iProver_top ),
% 3.01/0.97      inference(superposition,[status(thm)],[c_1909,c_1213]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_28,negated_conjecture,
% 3.01/0.97      ( v1_funct_1(sK2) ),
% 3.01/0.97      inference(cnf_transformation,[],[f81]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_35,plain,
% 3.01/0.97      ( v1_funct_1(sK2) = iProver_top ),
% 3.01/0.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_24,negated_conjecture,
% 3.01/0.97      ( v2_funct_1(sK2) ),
% 3.01/0.97      inference(cnf_transformation,[],[f85]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_38,plain,
% 3.01/0.97      ( v2_funct_1(sK2) = iProver_top ),
% 3.01/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_27,negated_conjecture,
% 3.01/0.97      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.01/0.97      inference(cnf_transformation,[],[f82]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_727,negated_conjecture,
% 3.01/0.97      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.01/0.97      inference(subtyping,[status(esa)],[c_27]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1217,plain,
% 3.01/0.97      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.01/0.97      inference(predicate_to_equality,[status(thm)],[c_727]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1704,plain,
% 3.01/0.97      ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.01/0.97      inference(demodulation,[status(thm)],[c_1523,c_1217]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1777,plain,
% 3.01/0.97      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.01/0.97      inference(light_normalisation,[status(thm)],[c_1704,c_1524]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1911,plain,
% 3.01/0.97      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 3.01/0.97      inference(demodulation,[status(thm)],[c_1907,c_1777]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1703,plain,
% 3.01/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 3.01/0.97      inference(demodulation,[status(thm)],[c_1523,c_1216]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_2147,plain,
% 3.01/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 3.01/0.97      inference(light_normalisation,[status(thm)],[c_1703,c_1524,c_1907]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_6120,plain,
% 3.01/0.97      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 3.01/0.97      inference(global_propositional_subsumption,
% 3.01/0.97                [status(thm)],
% 3.01/0.97                [c_2531,c_35,c_38,c_1911,c_2147]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_10,plain,
% 3.01/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/0.97      | v1_partfun1(X0,X1)
% 3.01/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.97      | v1_xboole_0(X2)
% 3.01/0.97      | ~ v1_funct_1(X0) ),
% 3.01/0.97      inference(cnf_transformation,[],[f66]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_20,plain,
% 3.01/0.97      ( v2_struct_0(X0)
% 3.01/0.97      | ~ l1_struct_0(X0)
% 3.01/0.97      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 3.01/0.97      inference(cnf_transformation,[],[f75]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_30,negated_conjecture,
% 3.01/0.97      ( ~ v2_struct_0(sK1) ),
% 3.01/0.97      inference(cnf_transformation,[],[f79]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_349,plain,
% 3.01/0.97      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 3.01/0.97      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_350,plain,
% 3.01/0.97      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 3.01/0.97      inference(unflattening,[status(thm)],[c_349]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_47,plain,
% 3.01/0.97      ( v2_struct_0(sK1)
% 3.01/0.97      | ~ l1_struct_0(sK1)
% 3.01/0.97      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 3.01/0.97      inference(instantiation,[status(thm)],[c_20]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_352,plain,
% 3.01/0.97      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 3.01/0.97      inference(global_propositional_subsumption,
% 3.01/0.97                [status(thm)],
% 3.01/0.97                [c_350,c_30,c_29,c_47]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_362,plain,
% 3.01/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/0.97      | v1_partfun1(X0,X1)
% 3.01/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.97      | ~ v1_funct_1(X0)
% 3.01/0.97      | k2_struct_0(sK1) != X2 ),
% 3.01/0.97      inference(resolution_lifted,[status(thm)],[c_10,c_352]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_363,plain,
% 3.01/0.97      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 3.01/0.97      | v1_partfun1(X0,X1)
% 3.01/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 3.01/0.97      | ~ v1_funct_1(X0) ),
% 3.01/0.97      inference(unflattening,[status(thm)],[c_362]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_3,plain,
% 3.01/0.97      ( v4_relat_1(X0,X1)
% 3.01/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.01/0.97      inference(cnf_transformation,[],[f58]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_13,plain,
% 3.01/0.97      ( ~ v1_partfun1(X0,X1)
% 3.01/0.97      | ~ v4_relat_1(X0,X1)
% 3.01/0.97      | ~ v1_relat_1(X0)
% 3.01/0.97      | k1_relat_1(X0) = X1 ),
% 3.01/0.97      inference(cnf_transformation,[],[f67]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_385,plain,
% 3.01/0.97      ( ~ v1_partfun1(X0,X1)
% 3.01/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.97      | ~ v1_relat_1(X0)
% 3.01/0.97      | k1_relat_1(X0) = X1 ),
% 3.01/0.97      inference(resolution,[status(thm)],[c_3,c_13]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_2,plain,
% 3.01/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.97      | v1_relat_1(X0) ),
% 3.01/0.97      inference(cnf_transformation,[],[f57]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_389,plain,
% 3.01/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.97      | ~ v1_partfun1(X0,X1)
% 3.01/0.97      | k1_relat_1(X0) = X1 ),
% 3.01/0.97      inference(global_propositional_subsumption,
% 3.01/0.97                [status(thm)],
% 3.01/0.97                [c_385,c_13,c_3,c_2]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_390,plain,
% 3.01/0.97      ( ~ v1_partfun1(X0,X1)
% 3.01/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.97      | k1_relat_1(X0) = X1 ),
% 3.01/0.97      inference(renaming,[status(thm)],[c_389]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_471,plain,
% 3.01/0.97      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 3.01/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 3.01/0.97      | ~ v1_funct_1(X0)
% 3.01/0.97      | k1_relat_1(X0) = X1 ),
% 3.01/0.97      inference(resolution,[status(thm)],[c_363,c_390]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_723,plain,
% 3.01/0.97      ( ~ v1_funct_2(X0_54,X0_55,k2_struct_0(sK1))
% 3.01/0.97      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.01/0.97      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_struct_0(sK1))))
% 3.01/0.97      | ~ v1_funct_1(X0_54)
% 3.01/0.97      | k1_relat_1(X0_54) = X0_55 ),
% 3.01/0.97      inference(subtyping,[status(esa)],[c_471]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1221,plain,
% 3.01/0.97      ( k1_relat_1(X0_54) = X0_55
% 3.01/0.97      | v1_funct_2(X0_54,X0_55,k2_struct_0(sK1)) != iProver_top
% 3.01/0.97      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.01/0.97      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_struct_0(sK1)))) != iProver_top
% 3.01/0.97      | v1_funct_1(X0_54) != iProver_top ),
% 3.01/0.97      inference(predicate_to_equality,[status(thm)],[c_723]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_2939,plain,
% 3.01/0.97      ( k1_relat_1(X0_54) = X0_55
% 3.01/0.97      | v1_funct_2(X0_54,X0_55,k2_relat_1(sK2)) != iProver_top
% 3.01/0.97      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.01/0.97      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_relat_1(sK2)))) != iProver_top
% 3.01/0.97      | v1_funct_1(X0_54) != iProver_top ),
% 3.01/0.97      inference(light_normalisation,[status(thm)],[c_1221,c_1907]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_2949,plain,
% 3.01/0.97      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.01/0.97      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.01/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_55))) != iProver_top
% 3.01/0.97      | v1_funct_1(sK2) != iProver_top ),
% 3.01/0.97      inference(superposition,[status(thm)],[c_2147,c_2939]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_3005,plain,
% 3.01/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_55))) != iProver_top
% 3.01/0.97      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.01/0.97      inference(global_propositional_subsumption,
% 3.01/0.97                [status(thm)],
% 3.01/0.97                [c_2949,c_35,c_1911]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_3006,plain,
% 3.01/0.97      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.01/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_55))) != iProver_top ),
% 3.01/0.97      inference(renaming,[status(thm)],[c_3005]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_3013,plain,
% 3.01/0.97      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.01/0.97      inference(superposition,[status(thm)],[c_2147,c_3006]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_6122,plain,
% 3.01/0.97      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 3.01/0.97      inference(light_normalisation,[status(thm)],[c_6120,c_3013]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_14,plain,
% 3.01/0.97      ( r2_funct_2(X0,X1,X2,X2)
% 3.01/0.97      | ~ v1_funct_2(X2,X0,X1)
% 3.01/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.01/0.97      | ~ v1_funct_1(X2) ),
% 3.01/0.97      inference(cnf_transformation,[],[f88]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_23,negated_conjecture,
% 3.01/0.97      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 3.01/0.97      inference(cnf_transformation,[],[f86]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_501,plain,
% 3.01/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.97      | ~ v1_funct_1(X0)
% 3.01/0.97      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 3.01/0.97      | u1_struct_0(sK1) != X2
% 3.01/0.97      | u1_struct_0(sK0) != X1
% 3.01/0.97      | sK2 != X0 ),
% 3.01/0.97      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_502,plain,
% 3.01/0.97      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.01/0.97      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.01/0.97      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.01/0.97      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.01/0.97      inference(unflattening,[status(thm)],[c_501]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_722,plain,
% 3.01/0.97      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.01/0.97      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.01/0.97      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.01/0.97      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.01/0.97      inference(subtyping,[status(esa)],[c_502]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1222,plain,
% 3.01/0.97      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.01/0.97      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.01/0.97      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.01/0.97      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 3.01/0.97      inference(predicate_to_equality,[status(thm)],[c_722]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_1702,plain,
% 3.01/0.97      ( k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 3.01/0.97      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.01/0.97      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.01/0.97      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 3.01/0.97      inference(demodulation,[status(thm)],[c_1523,c_1222]) ).
% 3.01/0.97  
% 3.01/0.97  cnf(c_2256,plain,
% 3.01/0.97      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 3.01/0.97      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.01/0.98      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.01/0.98      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 3.01/0.98      inference(light_normalisation,[status(thm)],[c_1702,c_1524,c_1907]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_3022,plain,
% 3.01/0.98      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
% 3.01/0.98      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.01/0.98      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.01/0.98      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
% 3.01/0.98      inference(demodulation,[status(thm)],[c_3013,c_2256]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_6124,plain,
% 3.01/0.98      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 3.01/0.98      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.01/0.98      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.01/0.98      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 3.01/0.98      inference(demodulation,[status(thm)],[c_6122,c_3022]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_7,plain,
% 3.01/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.98      | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
% 3.01/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_739,plain,
% 3.01/0.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.01/0.98      | k3_relset_1(X0_55,X1_55,X0_54) = k4_relat_1(X0_54) ),
% 3.01/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1206,plain,
% 3.01/0.98      ( k3_relset_1(X0_55,X1_55,X0_54) = k4_relat_1(X0_54)
% 3.01/0.98      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 3.01/0.98      inference(predicate_to_equality,[status(thm)],[c_739]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_2150,plain,
% 3.01/0.98      ( k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k4_relat_1(sK2) ),
% 3.01/0.98      inference(superposition,[status(thm)],[c_2147,c_1206]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_8,plain,
% 3.01/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.98      | k2_relset_1(X2,X1,k3_relset_1(X1,X2,X0)) = k1_relset_1(X1,X2,X0) ),
% 3.01/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_738,plain,
% 3.01/0.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.01/0.98      | k2_relset_1(X1_55,X0_55,k3_relset_1(X0_55,X1_55,X0_54)) = k1_relset_1(X0_55,X1_55,X0_54) ),
% 3.01/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1207,plain,
% 3.01/0.98      ( k2_relset_1(X0_55,X1_55,k3_relset_1(X1_55,X0_55,X0_54)) = k1_relset_1(X1_55,X0_55,X0_54)
% 3.01/0.98      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) != iProver_top ),
% 3.01/0.98      inference(predicate_to_equality,[status(thm)],[c_738]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_2155,plain,
% 3.01/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
% 3.01/0.98      inference(superposition,[status(thm)],[c_2147,c_1207]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_2162,plain,
% 3.01/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
% 3.01/0.98      inference(demodulation,[status(thm)],[c_2150,c_2155]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_743,plain,
% 3.01/0.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.01/0.98      | v1_relat_1(X0_54) ),
% 3.01/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1202,plain,
% 3.01/0.98      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.01/0.98      | v1_relat_1(X0_54) = iProver_top ),
% 3.01/0.98      inference(predicate_to_equality,[status(thm)],[c_743]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1562,plain,
% 3.01/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 3.01/0.98      inference(superposition,[status(thm)],[c_1216,c_1202]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_0,plain,
% 3.01/0.98      ( ~ v1_relat_1(X0)
% 3.01/0.98      | ~ v1_funct_1(X0)
% 3.01/0.98      | ~ v2_funct_1(X0)
% 3.01/0.98      | k4_relat_1(X0) = k2_funct_1(X0) ),
% 3.01/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_745,plain,
% 3.01/0.98      ( ~ v1_relat_1(X0_54)
% 3.01/0.98      | ~ v1_funct_1(X0_54)
% 3.01/0.98      | ~ v2_funct_1(X0_54)
% 3.01/0.98      | k4_relat_1(X0_54) = k2_funct_1(X0_54) ),
% 3.01/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1200,plain,
% 3.01/0.98      ( k4_relat_1(X0_54) = k2_funct_1(X0_54)
% 3.01/0.98      | v1_relat_1(X0_54) != iProver_top
% 3.01/0.98      | v1_funct_1(X0_54) != iProver_top
% 3.01/0.98      | v2_funct_1(X0_54) != iProver_top ),
% 3.01/0.98      inference(predicate_to_equality,[status(thm)],[c_745]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1641,plain,
% 3.01/0.98      ( k4_relat_1(sK2) = k2_funct_1(sK2)
% 3.01/0.98      | v1_funct_1(sK2) != iProver_top
% 3.01/0.98      | v2_funct_1(sK2) != iProver_top ),
% 3.01/0.98      inference(superposition,[status(thm)],[c_1562,c_1200]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_779,plain,
% 3.01/0.98      ( ~ v1_relat_1(sK2)
% 3.01/0.98      | ~ v1_funct_1(sK2)
% 3.01/0.98      | ~ v2_funct_1(sK2)
% 3.01/0.98      | k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 3.01/0.98      inference(instantiation,[status(thm)],[c_745]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1420,plain,
% 3.01/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.01/0.98      | v1_relat_1(sK2) ),
% 3.01/0.98      inference(instantiation,[status(thm)],[c_743]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_2214,plain,
% 3.01/0.98      ( k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 3.01/0.98      inference(global_propositional_subsumption,
% 3.01/0.98                [status(thm)],
% 3.01/0.98                [c_1641,c_28,c_26,c_24,c_779,c_1420]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_5,plain,
% 3.01/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.01/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_741,plain,
% 3.01/0.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.01/0.98      | k1_relset_1(X0_55,X1_55,X0_54) = k1_relat_1(X0_54) ),
% 3.01/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1204,plain,
% 3.01/0.98      ( k1_relset_1(X0_55,X1_55,X0_54) = k1_relat_1(X0_54)
% 3.01/0.98      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 3.01/0.98      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1567,plain,
% 3.01/0.98      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 3.01/0.98      inference(superposition,[status(thm)],[c_1216,c_1204]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1869,plain,
% 3.01/0.98      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 3.01/0.98      inference(light_normalisation,[status(thm)],[c_1567,c_1523,c_1524]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1910,plain,
% 3.01/0.98      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
% 3.01/0.98      inference(demodulation,[status(thm)],[c_1907,c_1869]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_3019,plain,
% 3.01/0.98      ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
% 3.01/0.98      inference(demodulation,[status(thm)],[c_3013,c_1910]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_2934,plain,
% 3.01/0.98      ( k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 3.01/0.98      inference(light_normalisation,[status(thm)],[c_2150,c_2214]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_4,plain,
% 3.01/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.98      | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.01/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_742,plain,
% 3.01/0.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.01/0.98      | m1_subset_1(k3_relset_1(X0_55,X1_55,X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) ),
% 3.01/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1203,plain,
% 3.01/0.98      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.01/0.98      | m1_subset_1(k3_relset_1(X0_55,X1_55,X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top ),
% 3.01/0.98      inference(predicate_to_equality,[status(thm)],[c_742]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_2936,plain,
% 3.01/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 3.01/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 3.01/0.98      inference(superposition,[status(thm)],[c_2934,c_1203]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_16,plain,
% 3.01/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.98      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.01/0.98      | ~ v1_funct_1(X0)
% 3.01/0.98      | ~ v2_funct_1(X0)
% 3.01/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.01/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_736,plain,
% 3.01/0.98      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 3.01/0.98      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.01/0.98      | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55)))
% 3.01/0.98      | ~ v1_funct_1(X0_54)
% 3.01/0.98      | ~ v2_funct_1(X0_54)
% 3.01/0.98      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
% 3.01/0.98      inference(subtyping,[status(esa)],[c_16]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1209,plain,
% 3.01/0.98      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 3.01/0.98      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 3.01/0.98      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.01/0.98      | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top
% 3.01/0.98      | v1_funct_1(X0_54) != iProver_top
% 3.01/0.98      | v2_funct_1(X0_54) != iProver_top ),
% 3.01/0.98      inference(predicate_to_equality,[status(thm)],[c_736]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_2400,plain,
% 3.01/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.01/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 3.01/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.01/0.98      | v1_funct_1(sK2) != iProver_top
% 3.01/0.98      | v2_funct_1(sK2) != iProver_top ),
% 3.01/0.98      inference(superposition,[status(thm)],[c_1909,c_1209]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_4178,plain,
% 3.01/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 3.01/0.98      inference(global_propositional_subsumption,
% 3.01/0.98                [status(thm)],
% 3.01/0.98                [c_2936,c_35,c_38,c_1911,c_2147,c_2400]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_4182,plain,
% 3.01/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 3.01/0.98      inference(light_normalisation,[status(thm)],[c_4178,c_3013]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_4188,plain,
% 3.01/0.98      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 3.01/0.98      inference(superposition,[status(thm)],[c_4182,c_1205]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_5556,plain,
% 3.01/0.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.01/0.98      inference(light_normalisation,
% 3.01/0.98                [status(thm)],
% 3.01/0.98                [c_2162,c_2214,c_3013,c_3019,c_4188]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_5559,plain,
% 3.01/0.98      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.01/0.98      inference(demodulation,[status(thm)],[c_5556,c_4188]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_5571,plain,
% 3.01/0.98      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 3.01/0.98      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.01/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.01/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.01/0.98      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.01/0.98      inference(superposition,[status(thm)],[c_5559,c_1213]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1,plain,
% 3.01/0.98      ( ~ v1_relat_1(X0)
% 3.01/0.98      | ~ v1_funct_1(X0)
% 3.01/0.98      | ~ v2_funct_1(X0)
% 3.01/0.98      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.01/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_744,plain,
% 3.01/0.98      ( ~ v1_relat_1(X0_54)
% 3.01/0.98      | ~ v1_funct_1(X0_54)
% 3.01/0.98      | ~ v2_funct_1(X0_54)
% 3.01/0.98      | k2_funct_1(k2_funct_1(X0_54)) = X0_54 ),
% 3.01/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1201,plain,
% 3.01/0.98      ( k2_funct_1(k2_funct_1(X0_54)) = X0_54
% 3.01/0.98      | v1_relat_1(X0_54) != iProver_top
% 3.01/0.98      | v1_funct_1(X0_54) != iProver_top
% 3.01/0.98      | v2_funct_1(X0_54) != iProver_top ),
% 3.01/0.98      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1927,plain,
% 3.01/0.98      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.01/0.98      | v1_funct_1(sK2) != iProver_top
% 3.01/0.98      | v2_funct_1(sK2) != iProver_top ),
% 3.01/0.98      inference(superposition,[status(thm)],[c_1562,c_1201]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_782,plain,
% 3.01/0.98      ( ~ v1_relat_1(sK2)
% 3.01/0.98      | ~ v1_funct_1(sK2)
% 3.01/0.98      | ~ v2_funct_1(sK2)
% 3.01/0.98      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.01/0.98      inference(instantiation,[status(thm)],[c_744]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_2218,plain,
% 3.01/0.98      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.01/0.98      inference(global_propositional_subsumption,
% 3.01/0.98                [status(thm)],
% 3.01/0.98                [c_1927,c_28,c_26,c_24,c_782,c_1420]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_5609,plain,
% 3.01/0.98      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 3.01/0.98      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.01/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.01/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.01/0.98      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.01/0.98      inference(light_normalisation,[status(thm)],[c_5571,c_2218]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_32,plain,
% 3.01/0.98      ( l1_struct_0(sK0) = iProver_top ),
% 3.01/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_34,plain,
% 3.01/0.98      ( l1_struct_0(sK1) = iProver_top ),
% 3.01/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_36,plain,
% 3.01/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.01/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_37,plain,
% 3.01/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.01/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_753,plain,
% 3.01/0.98      ( X0_54 != X1_54 | k2_funct_1(X0_54) = k2_funct_1(X1_54) ),
% 3.01/0.98      theory(equality) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_763,plain,
% 3.01/0.98      ( k2_funct_1(sK2) = k2_funct_1(sK2) | sK2 != sK2 ),
% 3.01/0.98      inference(instantiation,[status(thm)],[c_753]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_747,plain,( X0_54 = X0_54 ),theory(equality) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_774,plain,
% 3.01/0.98      ( sK2 = sK2 ),
% 3.01/0.98      inference(instantiation,[status(thm)],[c_747]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_815,plain,
% 3.01/0.98      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.01/0.98      inference(instantiation,[status(thm)],[c_733]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1473,plain,
% 3.01/0.98      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.01/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.01/0.98      | ~ v1_funct_1(sK2)
% 3.01/0.98      | ~ v2_funct_1(sK2)
% 3.01/0.98      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 3.01/0.98      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 3.01/0.98      inference(instantiation,[status(thm)],[c_732]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_22,plain,
% 3.01/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.01/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.01/0.98      | ~ l1_struct_0(X1)
% 3.01/0.98      | ~ l1_struct_0(X2)
% 3.01/0.98      | ~ v1_funct_1(X0)
% 3.01/0.98      | ~ v2_funct_1(X0)
% 3.01/0.98      | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
% 3.01/0.98      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 3.01/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_731,plain,
% 3.01/0.98      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_56),u1_struct_0(X1_56))
% 3.01/0.98      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 3.01/0.98      | ~ l1_struct_0(X1_56)
% 3.01/0.98      | ~ l1_struct_0(X0_56)
% 3.01/0.98      | ~ v1_funct_1(X0_54)
% 3.01/0.98      | ~ v2_funct_1(X0_54)
% 3.01/0.98      | v2_funct_1(k2_tops_2(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_54))
% 3.01/0.98      | k2_relset_1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_54) != k2_struct_0(X1_56) ),
% 3.01/0.98      inference(subtyping,[status(esa)],[c_22]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1476,plain,
% 3.01/0.98      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.01/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.01/0.98      | ~ l1_struct_0(sK1)
% 3.01/0.98      | ~ l1_struct_0(sK0)
% 3.01/0.98      | ~ v1_funct_1(sK2)
% 3.01/0.98      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.01/0.98      | ~ v2_funct_1(sK2)
% 3.01/0.98      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
% 3.01/0.98      inference(instantiation,[status(thm)],[c_731]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1477,plain,
% 3.01/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 3.01/0.98      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.01/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.01/0.98      | l1_struct_0(sK1) != iProver_top
% 3.01/0.98      | l1_struct_0(sK0) != iProver_top
% 3.01/0.98      | v1_funct_1(sK2) != iProver_top
% 3.01/0.98      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
% 3.01/0.98      | v2_funct_1(sK2) != iProver_top ),
% 3.01/0.98      inference(predicate_to_equality,[status(thm)],[c_1476]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_752,plain,
% 3.01/0.98      ( X0_55 != X1_55 | X2_55 != X1_55 | X2_55 = X0_55 ),
% 3.01/0.98      theory(equality) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1512,plain,
% 3.01/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_55
% 3.01/0.98      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 3.01/0.98      | u1_struct_0(sK1) != X0_55 ),
% 3.01/0.98      inference(instantiation,[status(thm)],[c_752]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1604,plain,
% 3.01/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 3.01/0.98      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 3.01/0.98      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 3.01/0.98      inference(instantiation,[status(thm)],[c_1512]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_3021,plain,
% 3.01/0.98      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 3.01/0.98      inference(demodulation,[status(thm)],[c_3013,c_1911]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_3023,plain,
% 3.01/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 3.01/0.98      inference(demodulation,[status(thm)],[c_3013,c_2147]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_751,plain,
% 3.01/0.98      ( X0_54 != X1_54 | X2_54 != X1_54 | X2_54 = X0_54 ),
% 3.01/0.98      theory(equality) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_2470,plain,
% 3.01/0.98      ( X0_54 != X1_54
% 3.01/0.98      | k2_funct_1(sK2) != X1_54
% 3.01/0.98      | k2_funct_1(sK2) = X0_54 ),
% 3.01/0.98      inference(instantiation,[status(thm)],[c_751]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_3919,plain,
% 3.01/0.98      ( X0_54 != k2_funct_1(sK2)
% 3.01/0.98      | k2_funct_1(sK2) = X0_54
% 3.01/0.98      | k2_funct_1(sK2) != k2_funct_1(sK2) ),
% 3.01/0.98      inference(instantiation,[status(thm)],[c_2470]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_5138,plain,
% 3.01/0.98      ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2)
% 3.01/0.98      | k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
% 3.01/0.98      | k2_funct_1(sK2) != k2_funct_1(sK2) ),
% 3.01/0.98      inference(instantiation,[status(thm)],[c_3919]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_4835,plain,
% 3.01/0.98      ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
% 3.01/0.98      | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 3.01/0.98      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.01/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.01/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.01/0.98      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.01/0.98      inference(superposition,[status(thm)],[c_4188,c_1213]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_4879,plain,
% 3.01/0.98      ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
% 3.01/0.98      | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 3.01/0.98      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.01/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.01/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.01/0.98      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.01/0.98      inference(light_normalisation,[status(thm)],[c_4835,c_2218]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_18,plain,
% 3.01/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.98      | ~ v1_funct_1(X0)
% 3.01/0.98      | v1_funct_1(k2_funct_1(X0))
% 3.01/0.98      | ~ v2_funct_1(X0)
% 3.01/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.01/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_734,plain,
% 3.01/0.98      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 3.01/0.98      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.01/0.98      | ~ v1_funct_1(X0_54)
% 3.01/0.98      | v1_funct_1(k2_funct_1(X0_54))
% 3.01/0.98      | ~ v2_funct_1(X0_54)
% 3.01/0.98      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
% 3.01/0.98      inference(subtyping,[status(esa)],[c_18]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1464,plain,
% 3.01/0.98      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.01/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.01/0.98      | v1_funct_1(k2_funct_1(sK2))
% 3.01/0.98      | ~ v1_funct_1(sK2)
% 3.01/0.98      | ~ v2_funct_1(sK2)
% 3.01/0.98      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 3.01/0.98      inference(instantiation,[status(thm)],[c_734]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1465,plain,
% 3.01/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 3.01/0.98      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.01/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.01/0.98      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.01/0.98      | v1_funct_1(sK2) != iProver_top
% 3.01/0.98      | v2_funct_1(sK2) != iProver_top ),
% 3.01/0.98      inference(predicate_to_equality,[status(thm)],[c_1464]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_5169,plain,
% 3.01/0.98      ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
% 3.01/0.98      | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 3.01/0.98      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.01/0.98      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.01/0.98      inference(global_propositional_subsumption,
% 3.01/0.98                [status(thm)],
% 3.01/0.98                [c_4879,c_29,c_35,c_36,c_37,c_38,c_815,c_729,c_1465,
% 3.01/0.98                 c_1604,c_4182]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_3020,plain,
% 3.01/0.98      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 3.01/0.98      inference(demodulation,[status(thm)],[c_3013,c_1909]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_17,plain,
% 3.01/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/0.98      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.01/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.98      | ~ v1_funct_1(X0)
% 3.01/0.98      | ~ v2_funct_1(X0)
% 3.01/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.01/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_735,plain,
% 3.01/0.98      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 3.01/0.98      | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55)
% 3.01/0.98      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.01/0.98      | ~ v1_funct_1(X0_54)
% 3.01/0.98      | ~ v2_funct_1(X0_54)
% 3.01/0.98      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
% 3.01/0.98      inference(subtyping,[status(esa)],[c_17]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_1210,plain,
% 3.01/0.98      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 3.01/0.98      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 3.01/0.98      | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55) = iProver_top
% 3.01/0.98      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.01/0.98      | v1_funct_1(X0_54) != iProver_top
% 3.01/0.98      | v2_funct_1(X0_54) != iProver_top ),
% 3.01/0.98      inference(predicate_to_equality,[status(thm)],[c_735]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_5179,plain,
% 3.01/0.98      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 3.01/0.98      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.01/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.01/0.98      | v1_funct_1(sK2) != iProver_top
% 3.01/0.98      | v2_funct_1(sK2) != iProver_top ),
% 3.01/0.98      inference(superposition,[status(thm)],[c_3020,c_1210]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_754,plain,
% 3.01/0.98      ( ~ v2_funct_1(X0_54) | v2_funct_1(X1_54) | X1_54 != X0_54 ),
% 3.01/0.98      theory(equality) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_2047,plain,
% 3.01/0.98      ( ~ v2_funct_1(X0_54)
% 3.01/0.98      | v2_funct_1(k2_funct_1(sK2))
% 3.01/0.98      | k2_funct_1(sK2) != X0_54 ),
% 3.01/0.98      inference(instantiation,[status(thm)],[c_754]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_5511,plain,
% 3.01/0.98      ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.01/0.98      | v2_funct_1(k2_funct_1(sK2))
% 3.01/0.98      | k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
% 3.01/0.98      inference(instantiation,[status(thm)],[c_2047]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_5512,plain,
% 3.01/0.98      ( k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
% 3.01/0.98      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
% 3.01/0.98      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.01/0.98      inference(predicate_to_equality,[status(thm)],[c_5511]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_5629,plain,
% 3.01/0.98      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 3.01/0.98      inference(global_propositional_subsumption,
% 3.01/0.98                [status(thm)],
% 3.01/0.98                [c_5609,c_32,c_29,c_34,c_28,c_35,c_27,c_36,c_26,c_37,
% 3.01/0.98                 c_24,c_38,c_763,c_774,c_815,c_729,c_1473,c_1477,c_1604,
% 3.01/0.98                 c_3021,c_3023,c_5138,c_5169,c_5179,c_5512,c_5556]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_6125,plain,
% 3.01/0.98      ( sK2 != sK2
% 3.01/0.98      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.01/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.01/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.01/0.98      inference(light_normalisation,[status(thm)],[c_6124,c_5629]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(c_6126,plain,
% 3.01/0.98      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.01/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.01/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.01/0.98      inference(equality_resolution_simp,[status(thm)],[c_6125]) ).
% 3.01/0.98  
% 3.01/0.98  cnf(contradiction,plain,
% 3.01/0.98      ( $false ),
% 3.01/0.98      inference(minisat,[status(thm)],[c_6126,c_3023,c_3021,c_35]) ).
% 3.01/0.98  
% 3.01/0.98  
% 3.01/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.01/0.98  
% 3.01/0.98  ------                               Statistics
% 3.01/0.98  
% 3.01/0.98  ------ General
% 3.01/0.98  
% 3.01/0.98  abstr_ref_over_cycles:                  0
% 3.01/0.98  abstr_ref_under_cycles:                 0
% 3.01/0.98  gc_basic_clause_elim:                   0
% 3.01/0.98  forced_gc_time:                         0
% 3.01/0.98  parsing_time:                           0.014
% 3.01/0.98  unif_index_cands_time:                  0.
% 3.01/0.98  unif_index_add_time:                    0.
% 3.01/0.98  orderings_time:                         0.
% 3.01/0.98  out_proof_time:                         0.015
% 3.01/0.98  total_time:                             0.228
% 3.01/0.98  num_of_symbols:                         59
% 3.01/0.98  num_of_terms:                           5487
% 3.01/0.98  
% 3.01/0.98  ------ Preprocessing
% 3.01/0.98  
% 3.01/0.98  num_of_splits:                          0
% 3.01/0.98  num_of_split_atoms:                     0
% 3.01/0.98  num_of_reused_defs:                     0
% 3.01/0.98  num_eq_ax_congr_red:                    32
% 3.01/0.98  num_of_sem_filtered_clauses:            1
% 3.01/0.98  num_of_subtypes:                        5
% 3.01/0.98  monotx_restored_types:                  1
% 3.01/0.98  sat_num_of_epr_types:                   0
% 3.01/0.98  sat_num_of_non_cyclic_types:            0
% 3.01/0.98  sat_guarded_non_collapsed_types:        1
% 3.01/0.98  num_pure_diseq_elim:                    0
% 3.01/0.98  simp_replaced_by:                       0
% 3.01/0.98  res_preprocessed:                       136
% 3.01/0.98  prep_upred:                             0
% 3.01/0.98  prep_unflattend:                        13
% 3.01/0.98  smt_new_axioms:                         0
% 3.01/0.98  pred_elim_cands:                        6
% 3.01/0.98  pred_elim:                              5
% 3.01/0.98  pred_elim_cl:                           7
% 3.01/0.98  pred_elim_cycles:                       8
% 3.01/0.98  merged_defs:                            0
% 3.01/0.98  merged_defs_ncl:                        0
% 3.01/0.98  bin_hyper_res:                          0
% 3.01/0.98  prep_cycles:                            4
% 3.01/0.98  pred_elim_time:                         0.005
% 3.01/0.98  splitting_time:                         0.
% 3.01/0.98  sem_filter_time:                        0.
% 3.01/0.98  monotx_time:                            0.001
% 3.01/0.98  subtype_inf_time:                       0.003
% 3.01/0.98  
% 3.01/0.98  ------ Problem properties
% 3.01/0.98  
% 3.01/0.98  clauses:                                24
% 3.01/0.98  conjectures:                            7
% 3.01/0.98  epr:                                    4
% 3.01/0.98  horn:                                   24
% 3.01/0.98  ground:                                 8
% 3.01/0.98  unary:                                  7
% 3.01/0.98  binary:                                 8
% 3.01/0.98  lits:                                   72
% 3.01/0.98  lits_eq:                                17
% 3.01/0.98  fd_pure:                                0
% 3.01/0.98  fd_pseudo:                              0
% 3.01/0.98  fd_cond:                                0
% 3.01/0.98  fd_pseudo_cond:                         1
% 3.01/0.98  ac_symbols:                             0
% 3.01/0.98  
% 3.01/0.98  ------ Propositional Solver
% 3.01/0.98  
% 3.01/0.98  prop_solver_calls:                      31
% 3.01/0.98  prop_fast_solver_calls:                 1230
% 3.01/0.98  smt_solver_calls:                       0
% 3.01/0.98  smt_fast_solver_calls:                  0
% 3.01/0.98  prop_num_of_clauses:                    2185
% 3.01/0.98  prop_preprocess_simplified:             6244
% 3.01/0.98  prop_fo_subsumed:                       43
% 3.01/0.98  prop_solver_time:                       0.
% 3.01/0.98  smt_solver_time:                        0.
% 3.01/0.98  smt_fast_solver_time:                   0.
% 3.01/0.98  prop_fast_solver_time:                  0.
% 3.01/0.98  prop_unsat_core_time:                   0.
% 3.01/0.98  
% 3.01/0.98  ------ QBF
% 3.01/0.98  
% 3.01/0.98  qbf_q_res:                              0
% 3.01/0.98  qbf_num_tautologies:                    0
% 3.01/0.98  qbf_prep_cycles:                        0
% 3.01/0.98  
% 3.01/0.98  ------ BMC1
% 3.01/0.98  
% 3.01/0.98  bmc1_current_bound:                     -1
% 3.01/0.98  bmc1_last_solved_bound:                 -1
% 3.01/0.98  bmc1_unsat_core_size:                   -1
% 3.01/0.98  bmc1_unsat_core_parents_size:           -1
% 3.01/0.98  bmc1_merge_next_fun:                    0
% 3.01/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.01/0.98  
% 3.01/0.98  ------ Instantiation
% 3.01/0.98  
% 3.01/0.98  inst_num_of_clauses:                    798
% 3.01/0.98  inst_num_in_passive:                    236
% 3.01/0.98  inst_num_in_active:                     439
% 3.01/0.98  inst_num_in_unprocessed:                123
% 3.01/0.98  inst_num_of_loops:                      460
% 3.01/0.98  inst_num_of_learning_restarts:          0
% 3.01/0.98  inst_num_moves_active_passive:          15
% 3.01/0.98  inst_lit_activity:                      0
% 3.01/0.98  inst_lit_activity_moves:                0
% 3.01/0.98  inst_num_tautologies:                   0
% 3.01/0.98  inst_num_prop_implied:                  0
% 3.01/0.98  inst_num_existing_simplified:           0
% 3.01/0.98  inst_num_eq_res_simplified:             0
% 3.01/0.98  inst_num_child_elim:                    0
% 3.01/0.98  inst_num_of_dismatching_blockings:      137
% 3.01/0.98  inst_num_of_non_proper_insts:           687
% 3.01/0.98  inst_num_of_duplicates:                 0
% 3.01/0.98  inst_inst_num_from_inst_to_res:         0
% 3.01/0.98  inst_dismatching_checking_time:         0.
% 3.01/0.98  
% 3.01/0.98  ------ Resolution
% 3.01/0.98  
% 3.01/0.98  res_num_of_clauses:                     0
% 3.01/0.98  res_num_in_passive:                     0
% 3.01/0.98  res_num_in_active:                      0
% 3.01/0.98  res_num_of_loops:                       140
% 3.01/0.98  res_forward_subset_subsumed:            72
% 3.01/0.98  res_backward_subset_subsumed:           0
% 3.01/0.98  res_forward_subsumed:                   0
% 3.01/0.98  res_backward_subsumed:                  0
% 3.01/0.98  res_forward_subsumption_resolution:     1
% 3.01/0.98  res_backward_subsumption_resolution:    0
% 3.01/0.98  res_clause_to_clause_subsumption:       247
% 3.01/0.98  res_orphan_elimination:                 0
% 3.01/0.98  res_tautology_del:                      95
% 3.01/0.98  res_num_eq_res_simplified:              0
% 3.01/0.98  res_num_sel_changes:                    0
% 3.01/0.98  res_moves_from_active_to_pass:          0
% 3.01/0.98  
% 3.01/0.98  ------ Superposition
% 3.01/0.98  
% 3.01/0.98  sup_time_total:                         0.
% 3.01/0.98  sup_time_generating:                    0.
% 3.01/0.98  sup_time_sim_full:                      0.
% 3.01/0.98  sup_time_sim_immed:                     0.
% 3.01/0.98  
% 3.01/0.98  sup_num_of_clauses:                     115
% 3.01/0.98  sup_num_in_active:                      64
% 3.01/0.98  sup_num_in_passive:                     51
% 3.01/0.98  sup_num_of_loops:                       91
% 3.01/0.98  sup_fw_superposition:                   49
% 3.01/0.98  sup_bw_superposition:                   82
% 3.01/0.98  sup_immediate_simplified:               63
% 3.01/0.98  sup_given_eliminated:                   0
% 3.01/0.98  comparisons_done:                       0
% 3.01/0.98  comparisons_avoided:                    0
% 3.01/0.98  
% 3.01/0.98  ------ Simplifications
% 3.01/0.98  
% 3.01/0.98  
% 3.01/0.98  sim_fw_subset_subsumed:                 2
% 3.01/0.98  sim_bw_subset_subsumed:                 6
% 3.01/0.98  sim_fw_subsumed:                        12
% 3.01/0.98  sim_bw_subsumed:                        0
% 3.01/0.98  sim_fw_subsumption_res:                 0
% 3.01/0.98  sim_bw_subsumption_res:                 0
% 3.01/0.98  sim_tautology_del:                      0
% 3.01/0.98  sim_eq_tautology_del:                   4
% 3.01/0.98  sim_eq_res_simp:                        2
% 3.01/0.98  sim_fw_demodulated:                     0
% 3.01/0.98  sim_bw_demodulated:                     41
% 3.01/0.98  sim_light_normalised:                   63
% 3.01/0.98  sim_joinable_taut:                      0
% 3.01/0.98  sim_joinable_simp:                      0
% 3.01/0.98  sim_ac_normalised:                      0
% 3.01/0.98  sim_smt_subsumption:                    0
% 3.01/0.98  
%------------------------------------------------------------------------------
