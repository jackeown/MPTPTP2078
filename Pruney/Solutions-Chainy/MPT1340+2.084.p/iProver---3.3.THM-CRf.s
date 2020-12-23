%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:39 EST 2020

% Result     : Theorem 11.80s
% Output     : CNFRefutation 11.80s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_5939)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f19,plain,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

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
          & l1_struct_0(X1) )
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
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

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
          & l1_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2)
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_struct_0(sK1) ) ) ),
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
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
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
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f54,f53,f52])).

fof(f93,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f84,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f89,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f94,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
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

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f91,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f55])).

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

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f95,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f10,axiom,(
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

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

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
    inference(nnf_transformation,[],[f35])).

fof(f75,plain,(
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

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f75])).

fof(f96,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f62,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f83,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

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

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f58,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f63,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f82,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f99,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f104,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f77])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1302,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_28,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_39,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_443,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_39])).

cnf(c_444,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_40,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_448,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_40])).

cnf(c_449,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_1330,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1302,c_444,c_449])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1319,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1767,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1330,c_1319])).

cnf(c_35,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1329,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_35,c_444,c_449])).

cnf(c_1816,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1767,c_1329])).

cnf(c_1906,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1816,c_1330])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_17,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_517,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_21,c_17])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_521,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_517,c_8])).

cnf(c_1298,plain,
    ( k1_relat_1(X0) = X1
    | k1_xboole_0 = X2
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_521])).

cnf(c_2094,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1906,c_1298])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1301,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_1328,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1301,c_444,c_449])).

cnf(c_1907,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1816,c_1328])).

cnf(c_1911,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1907])).

cnf(c_2095,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2094])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1529,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1754,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(c_2113,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1754])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2184,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2359,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2094,c_38,c_36,c_1911,c_2095,c_2113,c_2184])).

cnf(c_2360,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2359])).

cnf(c_1904,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1816,c_1767])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1307,plain,
    ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4102,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1904,c_1307])).

cnf(c_43,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_34,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_46,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4568,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4102,c_43,c_46,c_1906,c_1907])).

cnf(c_18,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_33,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_496,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_33])).

cnf(c_497,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_1299,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_497])).

cnf(c_1331,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1299,c_444,c_449])).

cnf(c_1905,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1816,c_1331])).

cnf(c_4572,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4568,c_1905])).

cnf(c_5010,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2360,c_4572])).

cnf(c_1300,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1322,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3353,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1300,c_1322])).

cnf(c_45,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2114,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2113])).

cnf(c_2185,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2184])).

cnf(c_3579,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3353,c_45,c_46,c_2114,c_2185])).

cnf(c_25,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1309,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3581,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3579,c_1309])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1321,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3285,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1300,c_1321])).

cnf(c_3483,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3285,c_45,c_46,c_2114,c_2185])).

cnf(c_3584,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3581,c_3483])).

cnf(c_44,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1667,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1684,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1667])).

cnf(c_1685,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1684])).

cnf(c_794,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1724,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_2084,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1724])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2336,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2337,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2336])).

cnf(c_3718,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3584,c_43,c_44,c_45,c_35,c_46,c_444,c_1685,c_2084,c_2114,c_2185,c_2337])).

cnf(c_3726,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3718,c_1319])).

cnf(c_3727,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3726,c_3579])).

cnf(c_4103,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3727,c_1307])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1320,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2146,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1300,c_1320])).

cnf(c_1546,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2263,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2146,c_38,c_36,c_34,c_1546,c_2113,c_2184])).

cnf(c_4104,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4103,c_2263])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3129,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3130,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3129])).

cnf(c_26,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1308,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3582,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3579,c_1308])).

cnf(c_3583,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3582,c_3483])).

cnf(c_4409,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4104,c_43,c_44,c_45,c_35,c_46,c_444,c_1685,c_2084,c_2114,c_2185,c_2337,c_3130,c_3583,c_3584])).

cnf(c_5011,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | sK2 != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5010,c_4409])).

cnf(c_5012,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5011])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1311,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4110,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1904,c_1311])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1306,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4575,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4568,c_1306])).

cnf(c_5099,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4575,c_43,c_1906,c_1907])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1304,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_tops_2(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5105,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5099,c_1304])).

cnf(c_5935,plain,
    ( m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5012,c_43,c_44,c_45,c_35,c_46,c_444,c_1685,c_1906,c_1907,c_2084,c_4110,c_5105])).

cnf(c_5936,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5935])).

cnf(c_5941,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2360,c_5936])).

cnf(c_5943,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5941,c_4409])).

cnf(c_5108,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_5099,c_1319])).

cnf(c_5109,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5108,c_3579])).

cnf(c_5201,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5109,c_1307])).

cnf(c_5204,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5201,c_2263])).

cnf(c_5868,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5204,c_43,c_44,c_45,c_35,c_46,c_444,c_1685,c_1906,c_1907,c_2084,c_2114,c_2185,c_3130,c_4110,c_4575])).

cnf(c_5870,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2360,c_5868])).

cnf(c_5940,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5870,c_5936])).

cnf(c_5948,plain,
    ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5943,c_43,c_44,c_45,c_35,c_46,c_444,c_1685,c_1906,c_1907,c_2084,c_4110,c_4575,c_5939])).

cnf(c_5949,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5948])).

cnf(c_5954,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2360,c_5949])).

cnf(c_5956,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5954,c_4409])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1305,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5952,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_5949])).

cnf(c_6234,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5956,c_43,c_44,c_45,c_35,c_46,c_444,c_1685,c_1906,c_1907,c_2084,c_4110,c_4575,c_5952])).

cnf(c_6257,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6234,c_1906])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1317,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7296,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6257,c_1317])).

cnf(c_6259,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6234,c_1907])).

cnf(c_7657,plain,
    ( sK2 = k1_xboole_0
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7296,c_6259])).

cnf(c_7658,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_7657])).

cnf(c_6237,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_6234,c_5868])).

cnf(c_7662,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | k1_relat_1(sK2) != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7658,c_6237])).

cnf(c_2365,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2360,c_1907])).

cnf(c_1726,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1727,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1726])).

cnf(c_2402,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2365,c_43,c_45,c_1727,c_2114,c_2185])).

cnf(c_6256,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6234,c_2402])).

cnf(c_4411,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4409,c_1306])).

cnf(c_4557,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4411,c_43,c_44,c_45,c_35,c_46,c_444,c_1685,c_2084,c_2114,c_2185,c_2337,c_3583,c_3584])).

cnf(c_6248,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6234,c_4557])).

cnf(c_8019,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6248,c_1317])).

cnf(c_8876,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7662,c_6256,c_8019])).

cnf(c_6243,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6234,c_4572])).

cnf(c_5306,plain,
    ( v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5105,c_43,c_44,c_45,c_35,c_46,c_444,c_1685,c_1906,c_1907,c_2084,c_4110])).

cnf(c_6238,plain,
    ( v1_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6234,c_5306])).

cnf(c_8390,plain,
    ( m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6243,c_6238])).

cnf(c_8391,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8390])).

cnf(c_8881,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8876,c_8391])).

cnf(c_9585,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8876,c_8881])).

cnf(c_9592,plain,
    ( v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9585,c_43,c_44,c_45,c_35,c_46,c_444,c_1685,c_2084,c_6241,c_6242,c_9584])).

cnf(c_9593,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9592])).

cnf(c_9597,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8876,c_9593])).

cnf(c_6241,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6234,c_5099])).

cnf(c_4576,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4568,c_1305])).

cnf(c_5089,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4576,c_43,c_46,c_1906,c_1907,c_4110])).

cnf(c_6242,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6234,c_5089])).

cnf(c_9596,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_9593])).

cnf(c_9702,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9597,c_43,c_44,c_45,c_35,c_46,c_444,c_1685,c_2084,c_6241,c_6242,c_9596])).

cnf(c_9714,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9702,c_6241])).

cnf(c_3831,plain,
    ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | v1_funct_2(k2_tops_2(k1_xboole_0,X0,X1),X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1306,c_1317])).

cnf(c_13565,plain,
    ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_3831])).

cnf(c_13570,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9714,c_13565])).

cnf(c_793,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_826,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_1453,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_1454,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1453])).

cnf(c_801,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2226,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | X0 != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_3084,plain,
    ( v1_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(X0) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2226])).

cnf(c_3086,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | v1_funct_1(k2_funct_1(k1_xboole_0))
    | k2_funct_1(k1_xboole_0) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3084])).

cnf(c_799,plain,
    ( X0 != X1
    | k2_funct_1(X0) = k2_funct_1(X1) ),
    theory(equality)).

cnf(c_3763,plain,
    ( X0 != sK2
    | k2_funct_1(X0) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_799])).

cnf(c_3764,plain,
    ( k2_funct_1(k1_xboole_0) = k2_funct_1(sK2)
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_3763])).

cnf(c_9722,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9702,c_6242])).

cnf(c_9750,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9722])).

cnf(c_13573,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13570])).

cnf(c_20768,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13570,c_38,c_43,c_37,c_44,c_36,c_45,c_35,c_34,c_46,c_444,c_826,c_1454,c_1684,c_1685,c_2084,c_3086,c_3764,c_6241,c_6242,c_9596,c_9750,c_13573])).

cnf(c_5315,plain,
    ( k2_funct_1(k2_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)))) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | v2_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top
    | v1_relat_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5306,c_1320])).

cnf(c_7087,plain,
    ( k2_funct_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)))) = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))
    | v2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top
    | v1_relat_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5315,c_6234])).

cnf(c_9727,plain,
    ( k2_funct_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)))) = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))
    | v2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))) != iProver_top
    | v1_relat_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9702,c_7087])).

cnf(c_20813,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | k2_funct_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)))) = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))
    | v2_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20768,c_9727])).

cnf(c_3085,plain,
    ( k2_funct_1(X0) != k2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3084])).

cnf(c_3087,plain,
    ( k2_funct_1(k1_xboole_0) != k2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3085])).

cnf(c_9713,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) != k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9702,c_8391])).

cnf(c_20812,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20768,c_9713])).

cnf(c_22151,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1306,c_20812])).

cnf(c_9726,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9702,c_6257])).

cnf(c_22152,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20768,c_20812])).

cnf(c_22669,plain,
    ( v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22151,c_9726,c_22152])).

cnf(c_22670,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_22669])).

cnf(c_22673,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_22670])).

cnf(c_22690,plain,
    ( k2_struct_0(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20813,c_43,c_44,c_45,c_35,c_46,c_444,c_826,c_1454,c_1685,c_2084,c_3087,c_3764,c_6241,c_6242,c_9596,c_9714,c_9722,c_22673])).

cnf(c_22734,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22690,c_9713])).

cnf(c_118,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_120,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_548,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ v4_relat_1(X2,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X2)
    | X0 != X2
    | k1_relat_1(X2) = X3
    | k1_xboole_0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_549,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ v4_relat_1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_550,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
    | v4_relat_1(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_549])).

cnf(c_552,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
    | v4_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_1434,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_1435,plain,
    ( X0 != sK2
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1434])).

cnf(c_1437,plain,
    ( k1_xboole_0 != sK2
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1435])).

cnf(c_2209,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_2210,plain,
    ( u1_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2209])).

cnf(c_795,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2906,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_2909,plain,
    ( X0 != sK2
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2906])).

cnf(c_2911,plain,
    ( k1_xboole_0 != sK2
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2909])).

cnf(c_3055,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK0)
    | u1_struct_0(sK0) != X1 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_4047,plain,
    ( X0 = u1_struct_0(sK0)
    | X0 != k2_struct_0(sK0)
    | u1_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3055])).

cnf(c_4048,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_4047])).

cnf(c_6213,plain,
    ( X0 != X1
    | X0 = k2_struct_0(sK0)
    | k2_struct_0(sK0) != X1 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_6214,plain,
    ( k2_struct_0(sK0) != k1_xboole_0
    | k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6213])).

cnf(c_1908,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1816,c_444])).

cnf(c_6260,plain,
    ( u1_struct_0(sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6234,c_1908])).

cnf(c_13139,plain,
    ( ~ v1_funct_2(k2_funct_1(X0),X1,X2)
    | m1_subset_1(k2_tops_2(X1,X2,k2_funct_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(k2_funct_1(X0)) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_13140,plain,
    ( v1_funct_2(k2_funct_1(X0),X1,X2) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,k2_funct_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13139])).

cnf(c_13142,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13140])).

cnf(c_805,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_13299,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | X2 != u1_struct_0(sK1)
    | X1 != u1_struct_0(sK0)
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_13300,plain,
    ( X0 != u1_struct_0(sK1)
    | X1 != u1_struct_0(sK0)
    | X2 != sK2
    | v1_funct_2(X2,X1,X0) = iProver_top
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13299])).

cnf(c_13302,plain,
    ( k1_xboole_0 != u1_struct_0(sK1)
    | k1_xboole_0 != u1_struct_0(sK0)
    | k1_xboole_0 != sK2
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_13300])).

cnf(c_22738,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_22690,c_9714])).

cnf(c_22740,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_22690,c_9722])).

cnf(c_9724,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | k2_struct_0(sK0) != k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_9702,c_6237])).

cnf(c_22742,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_22690,c_9724])).

cnf(c_22744,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_22690,c_9726])).

cnf(c_24228,plain,
    ( v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22734,c_43,c_44,c_45,c_35,c_46,c_120,c_444,c_449,c_552,c_826,c_1437,c_1454,c_1685,c_2084,c_2114,c_2185,c_2210,c_2911,c_3087,c_3764,c_4048,c_6214,c_6241,c_6242,c_6260,c_9596,c_9714,c_9722,c_13142,c_13302,c_22673,c_22738,c_22740,c_22742,c_22744])).

cnf(c_23090,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22742,c_43,c_44,c_45,c_35,c_46,c_120,c_444,c_449,c_552,c_826,c_1437,c_1454,c_1685,c_2084,c_2114,c_2185,c_2210,c_2911,c_3087,c_3764,c_4048,c_6214,c_6241,c_6242,c_6260,c_9596,c_9714,c_9722,c_13302,c_22673,c_22744])).

cnf(c_24232,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_24228,c_23090])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24232,c_22673,c_13302,c_9722,c_9714,c_9596,c_6260,c_6242,c_6241,c_6214,c_4048,c_3764,c_3087,c_2210,c_2084,c_1685,c_1454,c_826,c_449,c_444,c_46,c_35,c_45,c_44,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.80/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.80/1.99  
% 11.80/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.80/1.99  
% 11.80/1.99  ------  iProver source info
% 11.80/1.99  
% 11.80/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.80/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.80/1.99  git: non_committed_changes: false
% 11.80/1.99  git: last_make_outside_of_git: false
% 11.80/1.99  
% 11.80/1.99  ------ 
% 11.80/1.99  
% 11.80/1.99  ------ Input Options
% 11.80/1.99  
% 11.80/1.99  --out_options                           all
% 11.80/1.99  --tptp_safe_out                         true
% 11.80/1.99  --problem_path                          ""
% 11.80/1.99  --include_path                          ""
% 11.80/1.99  --clausifier                            res/vclausify_rel
% 11.80/1.99  --clausifier_options                    ""
% 11.80/1.99  --stdin                                 false
% 11.80/1.99  --stats_out                             all
% 11.80/1.99  
% 11.80/1.99  ------ General Options
% 11.80/1.99  
% 11.80/1.99  --fof                                   false
% 11.80/1.99  --time_out_real                         305.
% 11.80/1.99  --time_out_virtual                      -1.
% 11.80/1.99  --symbol_type_check                     false
% 11.80/1.99  --clausify_out                          false
% 11.80/1.99  --sig_cnt_out                           false
% 11.80/1.99  --trig_cnt_out                          false
% 11.80/1.99  --trig_cnt_out_tolerance                1.
% 11.80/1.99  --trig_cnt_out_sk_spl                   false
% 11.80/1.99  --abstr_cl_out                          false
% 11.80/1.99  
% 11.80/1.99  ------ Global Options
% 11.80/1.99  
% 11.80/1.99  --schedule                              default
% 11.80/1.99  --add_important_lit                     false
% 11.80/1.99  --prop_solver_per_cl                    1000
% 11.80/1.99  --min_unsat_core                        false
% 11.80/1.99  --soft_assumptions                      false
% 11.80/1.99  --soft_lemma_size                       3
% 11.80/1.99  --prop_impl_unit_size                   0
% 11.80/1.99  --prop_impl_unit                        []
% 11.80/1.99  --share_sel_clauses                     true
% 11.80/1.99  --reset_solvers                         false
% 11.80/1.99  --bc_imp_inh                            [conj_cone]
% 11.80/1.99  --conj_cone_tolerance                   3.
% 11.80/1.99  --extra_neg_conj                        none
% 11.80/1.99  --large_theory_mode                     true
% 11.80/1.99  --prolific_symb_bound                   200
% 11.80/1.99  --lt_threshold                          2000
% 11.80/1.99  --clause_weak_htbl                      true
% 11.80/1.99  --gc_record_bc_elim                     false
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing Options
% 11.80/1.99  
% 11.80/1.99  --preprocessing_flag                    true
% 11.80/1.99  --time_out_prep_mult                    0.1
% 11.80/1.99  --splitting_mode                        input
% 11.80/1.99  --splitting_grd                         true
% 11.80/1.99  --splitting_cvd                         false
% 11.80/1.99  --splitting_cvd_svl                     false
% 11.80/1.99  --splitting_nvd                         32
% 11.80/1.99  --sub_typing                            true
% 11.80/1.99  --prep_gs_sim                           true
% 11.80/1.99  --prep_unflatten                        true
% 11.80/1.99  --prep_res_sim                          true
% 11.80/1.99  --prep_upred                            true
% 11.80/1.99  --prep_sem_filter                       exhaustive
% 11.80/1.99  --prep_sem_filter_out                   false
% 11.80/1.99  --pred_elim                             true
% 11.80/1.99  --res_sim_input                         true
% 11.80/1.99  --eq_ax_congr_red                       true
% 11.80/1.99  --pure_diseq_elim                       true
% 11.80/1.99  --brand_transform                       false
% 11.80/1.99  --non_eq_to_eq                          false
% 11.80/1.99  --prep_def_merge                        true
% 11.80/1.99  --prep_def_merge_prop_impl              false
% 11.80/1.99  --prep_def_merge_mbd                    true
% 11.80/1.99  --prep_def_merge_tr_red                 false
% 11.80/1.99  --prep_def_merge_tr_cl                  false
% 11.80/1.99  --smt_preprocessing                     true
% 11.80/1.99  --smt_ac_axioms                         fast
% 11.80/1.99  --preprocessed_out                      false
% 11.80/1.99  --preprocessed_stats                    false
% 11.80/1.99  
% 11.80/1.99  ------ Abstraction refinement Options
% 11.80/1.99  
% 11.80/1.99  --abstr_ref                             []
% 11.80/1.99  --abstr_ref_prep                        false
% 11.80/1.99  --abstr_ref_until_sat                   false
% 11.80/1.99  --abstr_ref_sig_restrict                funpre
% 11.80/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.80/1.99  --abstr_ref_under                       []
% 11.80/1.99  
% 11.80/1.99  ------ SAT Options
% 11.80/1.99  
% 11.80/1.99  --sat_mode                              false
% 11.80/1.99  --sat_fm_restart_options                ""
% 11.80/1.99  --sat_gr_def                            false
% 11.80/1.99  --sat_epr_types                         true
% 11.80/1.99  --sat_non_cyclic_types                  false
% 11.80/1.99  --sat_finite_models                     false
% 11.80/1.99  --sat_fm_lemmas                         false
% 11.80/1.99  --sat_fm_prep                           false
% 11.80/1.99  --sat_fm_uc_incr                        true
% 11.80/1.99  --sat_out_model                         small
% 11.80/1.99  --sat_out_clauses                       false
% 11.80/1.99  
% 11.80/1.99  ------ QBF Options
% 11.80/1.99  
% 11.80/1.99  --qbf_mode                              false
% 11.80/1.99  --qbf_elim_univ                         false
% 11.80/1.99  --qbf_dom_inst                          none
% 11.80/1.99  --qbf_dom_pre_inst                      false
% 11.80/1.99  --qbf_sk_in                             false
% 11.80/1.99  --qbf_pred_elim                         true
% 11.80/1.99  --qbf_split                             512
% 11.80/1.99  
% 11.80/1.99  ------ BMC1 Options
% 11.80/1.99  
% 11.80/1.99  --bmc1_incremental                      false
% 11.80/1.99  --bmc1_axioms                           reachable_all
% 11.80/1.99  --bmc1_min_bound                        0
% 11.80/1.99  --bmc1_max_bound                        -1
% 11.80/1.99  --bmc1_max_bound_default                -1
% 11.80/1.99  --bmc1_symbol_reachability              true
% 11.80/1.99  --bmc1_property_lemmas                  false
% 11.80/1.99  --bmc1_k_induction                      false
% 11.80/1.99  --bmc1_non_equiv_states                 false
% 11.80/1.99  --bmc1_deadlock                         false
% 11.80/1.99  --bmc1_ucm                              false
% 11.80/1.99  --bmc1_add_unsat_core                   none
% 11.80/1.99  --bmc1_unsat_core_children              false
% 11.80/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.80/1.99  --bmc1_out_stat                         full
% 11.80/1.99  --bmc1_ground_init                      false
% 11.80/1.99  --bmc1_pre_inst_next_state              false
% 11.80/1.99  --bmc1_pre_inst_state                   false
% 11.80/1.99  --bmc1_pre_inst_reach_state             false
% 11.80/1.99  --bmc1_out_unsat_core                   false
% 11.80/1.99  --bmc1_aig_witness_out                  false
% 11.80/1.99  --bmc1_verbose                          false
% 11.80/1.99  --bmc1_dump_clauses_tptp                false
% 11.80/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.80/1.99  --bmc1_dump_file                        -
% 11.80/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.80/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.80/1.99  --bmc1_ucm_extend_mode                  1
% 11.80/1.99  --bmc1_ucm_init_mode                    2
% 11.80/1.99  --bmc1_ucm_cone_mode                    none
% 11.80/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.80/1.99  --bmc1_ucm_relax_model                  4
% 11.80/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.80/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.80/1.99  --bmc1_ucm_layered_model                none
% 11.80/1.99  --bmc1_ucm_max_lemma_size               10
% 11.80/1.99  
% 11.80/1.99  ------ AIG Options
% 11.80/1.99  
% 11.80/1.99  --aig_mode                              false
% 11.80/1.99  
% 11.80/1.99  ------ Instantiation Options
% 11.80/1.99  
% 11.80/1.99  --instantiation_flag                    true
% 11.80/1.99  --inst_sos_flag                         true
% 11.80/1.99  --inst_sos_phase                        true
% 11.80/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.80/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.80/1.99  --inst_lit_sel_side                     num_symb
% 11.80/1.99  --inst_solver_per_active                1400
% 11.80/1.99  --inst_solver_calls_frac                1.
% 11.80/1.99  --inst_passive_queue_type               priority_queues
% 11.80/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.80/1.99  --inst_passive_queues_freq              [25;2]
% 11.80/1.99  --inst_dismatching                      true
% 11.80/1.99  --inst_eager_unprocessed_to_passive     true
% 11.80/1.99  --inst_prop_sim_given                   true
% 11.80/1.99  --inst_prop_sim_new                     false
% 11.80/1.99  --inst_subs_new                         false
% 11.80/1.99  --inst_eq_res_simp                      false
% 11.80/1.99  --inst_subs_given                       false
% 11.80/1.99  --inst_orphan_elimination               true
% 11.80/1.99  --inst_learning_loop_flag               true
% 11.80/1.99  --inst_learning_start                   3000
% 11.80/1.99  --inst_learning_factor                  2
% 11.80/1.99  --inst_start_prop_sim_after_learn       3
% 11.80/1.99  --inst_sel_renew                        solver
% 11.80/1.99  --inst_lit_activity_flag                true
% 11.80/1.99  --inst_restr_to_given                   false
% 11.80/1.99  --inst_activity_threshold               500
% 11.80/1.99  --inst_out_proof                        true
% 11.80/1.99  
% 11.80/1.99  ------ Resolution Options
% 11.80/1.99  
% 11.80/1.99  --resolution_flag                       true
% 11.80/1.99  --res_lit_sel                           adaptive
% 11.80/1.99  --res_lit_sel_side                      none
% 11.80/1.99  --res_ordering                          kbo
% 11.80/1.99  --res_to_prop_solver                    active
% 11.80/1.99  --res_prop_simpl_new                    false
% 11.80/1.99  --res_prop_simpl_given                  true
% 11.80/1.99  --res_passive_queue_type                priority_queues
% 11.80/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.80/1.99  --res_passive_queues_freq               [15;5]
% 11.80/1.99  --res_forward_subs                      full
% 11.80/1.99  --res_backward_subs                     full
% 11.80/1.99  --res_forward_subs_resolution           true
% 11.80/1.99  --res_backward_subs_resolution          true
% 11.80/1.99  --res_orphan_elimination                true
% 11.80/1.99  --res_time_limit                        2.
% 11.80/1.99  --res_out_proof                         true
% 11.80/1.99  
% 11.80/1.99  ------ Superposition Options
% 11.80/1.99  
% 11.80/1.99  --superposition_flag                    true
% 11.80/1.99  --sup_passive_queue_type                priority_queues
% 11.80/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.80/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.80/1.99  --demod_completeness_check              fast
% 11.80/1.99  --demod_use_ground                      true
% 11.80/1.99  --sup_to_prop_solver                    passive
% 11.80/1.99  --sup_prop_simpl_new                    true
% 11.80/1.99  --sup_prop_simpl_given                  true
% 11.80/1.99  --sup_fun_splitting                     true
% 11.80/1.99  --sup_smt_interval                      50000
% 11.80/1.99  
% 11.80/1.99  ------ Superposition Simplification Setup
% 11.80/1.99  
% 11.80/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.80/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.80/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.80/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.80/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.80/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.80/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.80/1.99  --sup_immed_triv                        [TrivRules]
% 11.80/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.80/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.80/1.99  --sup_immed_bw_main                     []
% 11.80/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.80/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.80/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.80/1.99  --sup_input_bw                          []
% 11.80/1.99  
% 11.80/1.99  ------ Combination Options
% 11.80/1.99  
% 11.80/1.99  --comb_res_mult                         3
% 11.80/1.99  --comb_sup_mult                         2
% 11.80/1.99  --comb_inst_mult                        10
% 11.80/1.99  
% 11.80/1.99  ------ Debug Options
% 11.80/1.99  
% 11.80/1.99  --dbg_backtrace                         false
% 11.80/1.99  --dbg_dump_prop_clauses                 false
% 11.80/1.99  --dbg_dump_prop_clauses_file            -
% 11.80/1.99  --dbg_out_stat                          false
% 11.80/1.99  ------ Parsing...
% 11.80/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.99  ------ Proving...
% 11.80/1.99  ------ Problem Properties 
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  clauses                                 34
% 11.80/1.99  conjectures                             5
% 11.80/1.99  EPR                                     2
% 11.80/1.99  Horn                                    29
% 11.80/1.99  unary                                   8
% 11.80/1.99  binary                                  1
% 11.80/1.99  lits                                    115
% 11.80/1.99  lits eq                                 25
% 11.80/1.99  fd_pure                                 0
% 11.80/1.99  fd_pseudo                               0
% 11.80/1.99  fd_cond                                 3
% 11.80/1.99  fd_pseudo_cond                          1
% 11.80/1.99  AC symbols                              0
% 11.80/1.99  
% 11.80/1.99  ------ Schedule dynamic 5 is on 
% 11.80/1.99  
% 11.80/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ 
% 11.80/1.99  Current options:
% 11.80/1.99  ------ 
% 11.80/1.99  
% 11.80/1.99  ------ Input Options
% 11.80/1.99  
% 11.80/1.99  --out_options                           all
% 11.80/1.99  --tptp_safe_out                         true
% 11.80/1.99  --problem_path                          ""
% 11.80/1.99  --include_path                          ""
% 11.80/1.99  --clausifier                            res/vclausify_rel
% 11.80/1.99  --clausifier_options                    ""
% 11.80/1.99  --stdin                                 false
% 11.80/1.99  --stats_out                             all
% 11.80/1.99  
% 11.80/1.99  ------ General Options
% 11.80/1.99  
% 11.80/1.99  --fof                                   false
% 11.80/1.99  --time_out_real                         305.
% 11.80/1.99  --time_out_virtual                      -1.
% 11.80/1.99  --symbol_type_check                     false
% 11.80/1.99  --clausify_out                          false
% 11.80/1.99  --sig_cnt_out                           false
% 11.80/1.99  --trig_cnt_out                          false
% 11.80/1.99  --trig_cnt_out_tolerance                1.
% 11.80/1.99  --trig_cnt_out_sk_spl                   false
% 11.80/1.99  --abstr_cl_out                          false
% 11.80/1.99  
% 11.80/1.99  ------ Global Options
% 11.80/1.99  
% 11.80/1.99  --schedule                              default
% 11.80/1.99  --add_important_lit                     false
% 11.80/1.99  --prop_solver_per_cl                    1000
% 11.80/1.99  --min_unsat_core                        false
% 11.80/1.99  --soft_assumptions                      false
% 11.80/1.99  --soft_lemma_size                       3
% 11.80/1.99  --prop_impl_unit_size                   0
% 11.80/1.99  --prop_impl_unit                        []
% 11.80/1.99  --share_sel_clauses                     true
% 11.80/1.99  --reset_solvers                         false
% 11.80/1.99  --bc_imp_inh                            [conj_cone]
% 11.80/1.99  --conj_cone_tolerance                   3.
% 11.80/1.99  --extra_neg_conj                        none
% 11.80/1.99  --large_theory_mode                     true
% 11.80/1.99  --prolific_symb_bound                   200
% 11.80/1.99  --lt_threshold                          2000
% 11.80/1.99  --clause_weak_htbl                      true
% 11.80/1.99  --gc_record_bc_elim                     false
% 11.80/1.99  
% 11.80/1.99  ------ Preprocessing Options
% 11.80/1.99  
% 11.80/1.99  --preprocessing_flag                    true
% 11.80/1.99  --time_out_prep_mult                    0.1
% 11.80/1.99  --splitting_mode                        input
% 11.80/1.99  --splitting_grd                         true
% 11.80/1.99  --splitting_cvd                         false
% 11.80/1.99  --splitting_cvd_svl                     false
% 11.80/1.99  --splitting_nvd                         32
% 11.80/1.99  --sub_typing                            true
% 11.80/1.99  --prep_gs_sim                           true
% 11.80/1.99  --prep_unflatten                        true
% 11.80/1.99  --prep_res_sim                          true
% 11.80/1.99  --prep_upred                            true
% 11.80/1.99  --prep_sem_filter                       exhaustive
% 11.80/1.99  --prep_sem_filter_out                   false
% 11.80/1.99  --pred_elim                             true
% 11.80/1.99  --res_sim_input                         true
% 11.80/1.99  --eq_ax_congr_red                       true
% 11.80/1.99  --pure_diseq_elim                       true
% 11.80/1.99  --brand_transform                       false
% 11.80/1.99  --non_eq_to_eq                          false
% 11.80/1.99  --prep_def_merge                        true
% 11.80/1.99  --prep_def_merge_prop_impl              false
% 11.80/1.99  --prep_def_merge_mbd                    true
% 11.80/1.99  --prep_def_merge_tr_red                 false
% 11.80/1.99  --prep_def_merge_tr_cl                  false
% 11.80/1.99  --smt_preprocessing                     true
% 11.80/1.99  --smt_ac_axioms                         fast
% 11.80/1.99  --preprocessed_out                      false
% 11.80/1.99  --preprocessed_stats                    false
% 11.80/1.99  
% 11.80/1.99  ------ Abstraction refinement Options
% 11.80/1.99  
% 11.80/1.99  --abstr_ref                             []
% 11.80/1.99  --abstr_ref_prep                        false
% 11.80/1.99  --abstr_ref_until_sat                   false
% 11.80/1.99  --abstr_ref_sig_restrict                funpre
% 11.80/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.80/1.99  --abstr_ref_under                       []
% 11.80/1.99  
% 11.80/1.99  ------ SAT Options
% 11.80/1.99  
% 11.80/1.99  --sat_mode                              false
% 11.80/1.99  --sat_fm_restart_options                ""
% 11.80/1.99  --sat_gr_def                            false
% 11.80/1.99  --sat_epr_types                         true
% 11.80/1.99  --sat_non_cyclic_types                  false
% 11.80/1.99  --sat_finite_models                     false
% 11.80/1.99  --sat_fm_lemmas                         false
% 11.80/1.99  --sat_fm_prep                           false
% 11.80/1.99  --sat_fm_uc_incr                        true
% 11.80/1.99  --sat_out_model                         small
% 11.80/1.99  --sat_out_clauses                       false
% 11.80/1.99  
% 11.80/1.99  ------ QBF Options
% 11.80/1.99  
% 11.80/1.99  --qbf_mode                              false
% 11.80/1.99  --qbf_elim_univ                         false
% 11.80/1.99  --qbf_dom_inst                          none
% 11.80/1.99  --qbf_dom_pre_inst                      false
% 11.80/1.99  --qbf_sk_in                             false
% 11.80/1.99  --qbf_pred_elim                         true
% 11.80/1.99  --qbf_split                             512
% 11.80/1.99  
% 11.80/1.99  ------ BMC1 Options
% 11.80/1.99  
% 11.80/1.99  --bmc1_incremental                      false
% 11.80/1.99  --bmc1_axioms                           reachable_all
% 11.80/1.99  --bmc1_min_bound                        0
% 11.80/1.99  --bmc1_max_bound                        -1
% 11.80/1.99  --bmc1_max_bound_default                -1
% 11.80/1.99  --bmc1_symbol_reachability              true
% 11.80/1.99  --bmc1_property_lemmas                  false
% 11.80/1.99  --bmc1_k_induction                      false
% 11.80/1.99  --bmc1_non_equiv_states                 false
% 11.80/1.99  --bmc1_deadlock                         false
% 11.80/1.99  --bmc1_ucm                              false
% 11.80/1.99  --bmc1_add_unsat_core                   none
% 11.80/1.99  --bmc1_unsat_core_children              false
% 11.80/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.80/1.99  --bmc1_out_stat                         full
% 11.80/1.99  --bmc1_ground_init                      false
% 11.80/1.99  --bmc1_pre_inst_next_state              false
% 11.80/1.99  --bmc1_pre_inst_state                   false
% 11.80/1.99  --bmc1_pre_inst_reach_state             false
% 11.80/1.99  --bmc1_out_unsat_core                   false
% 11.80/1.99  --bmc1_aig_witness_out                  false
% 11.80/1.99  --bmc1_verbose                          false
% 11.80/1.99  --bmc1_dump_clauses_tptp                false
% 11.80/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.80/1.99  --bmc1_dump_file                        -
% 11.80/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.80/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.80/1.99  --bmc1_ucm_extend_mode                  1
% 11.80/1.99  --bmc1_ucm_init_mode                    2
% 11.80/1.99  --bmc1_ucm_cone_mode                    none
% 11.80/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.80/1.99  --bmc1_ucm_relax_model                  4
% 11.80/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.80/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.80/1.99  --bmc1_ucm_layered_model                none
% 11.80/1.99  --bmc1_ucm_max_lemma_size               10
% 11.80/1.99  
% 11.80/1.99  ------ AIG Options
% 11.80/1.99  
% 11.80/1.99  --aig_mode                              false
% 11.80/1.99  
% 11.80/1.99  ------ Instantiation Options
% 11.80/1.99  
% 11.80/1.99  --instantiation_flag                    true
% 11.80/1.99  --inst_sos_flag                         true
% 11.80/1.99  --inst_sos_phase                        true
% 11.80/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.80/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.80/1.99  --inst_lit_sel_side                     none
% 11.80/1.99  --inst_solver_per_active                1400
% 11.80/1.99  --inst_solver_calls_frac                1.
% 11.80/1.99  --inst_passive_queue_type               priority_queues
% 11.80/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.80/1.99  --inst_passive_queues_freq              [25;2]
% 11.80/1.99  --inst_dismatching                      true
% 11.80/1.99  --inst_eager_unprocessed_to_passive     true
% 11.80/1.99  --inst_prop_sim_given                   true
% 11.80/1.99  --inst_prop_sim_new                     false
% 11.80/1.99  --inst_subs_new                         false
% 11.80/1.99  --inst_eq_res_simp                      false
% 11.80/1.99  --inst_subs_given                       false
% 11.80/1.99  --inst_orphan_elimination               true
% 11.80/1.99  --inst_learning_loop_flag               true
% 11.80/1.99  --inst_learning_start                   3000
% 11.80/1.99  --inst_learning_factor                  2
% 11.80/1.99  --inst_start_prop_sim_after_learn       3
% 11.80/1.99  --inst_sel_renew                        solver
% 11.80/1.99  --inst_lit_activity_flag                true
% 11.80/1.99  --inst_restr_to_given                   false
% 11.80/1.99  --inst_activity_threshold               500
% 11.80/1.99  --inst_out_proof                        true
% 11.80/1.99  
% 11.80/1.99  ------ Resolution Options
% 11.80/1.99  
% 11.80/1.99  --resolution_flag                       false
% 11.80/1.99  --res_lit_sel                           adaptive
% 11.80/1.99  --res_lit_sel_side                      none
% 11.80/1.99  --res_ordering                          kbo
% 11.80/1.99  --res_to_prop_solver                    active
% 11.80/1.99  --res_prop_simpl_new                    false
% 11.80/1.99  --res_prop_simpl_given                  true
% 11.80/1.99  --res_passive_queue_type                priority_queues
% 11.80/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.80/1.99  --res_passive_queues_freq               [15;5]
% 11.80/1.99  --res_forward_subs                      full
% 11.80/1.99  --res_backward_subs                     full
% 11.80/1.99  --res_forward_subs_resolution           true
% 11.80/1.99  --res_backward_subs_resolution          true
% 11.80/1.99  --res_orphan_elimination                true
% 11.80/1.99  --res_time_limit                        2.
% 11.80/1.99  --res_out_proof                         true
% 11.80/1.99  
% 11.80/1.99  ------ Superposition Options
% 11.80/1.99  
% 11.80/1.99  --superposition_flag                    true
% 11.80/1.99  --sup_passive_queue_type                priority_queues
% 11.80/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.80/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.80/1.99  --demod_completeness_check              fast
% 11.80/1.99  --demod_use_ground                      true
% 11.80/1.99  --sup_to_prop_solver                    passive
% 11.80/1.99  --sup_prop_simpl_new                    true
% 11.80/1.99  --sup_prop_simpl_given                  true
% 11.80/1.99  --sup_fun_splitting                     true
% 11.80/1.99  --sup_smt_interval                      50000
% 11.80/1.99  
% 11.80/1.99  ------ Superposition Simplification Setup
% 11.80/1.99  
% 11.80/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.80/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.80/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.80/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.80/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.80/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.80/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.80/1.99  --sup_immed_triv                        [TrivRules]
% 11.80/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.80/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.80/1.99  --sup_immed_bw_main                     []
% 11.80/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.80/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.80/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.80/1.99  --sup_input_bw                          []
% 11.80/1.99  
% 11.80/1.99  ------ Combination Options
% 11.80/1.99  
% 11.80/1.99  --comb_res_mult                         3
% 11.80/1.99  --comb_sup_mult                         2
% 11.80/1.99  --comb_inst_mult                        10
% 11.80/1.99  
% 11.80/1.99  ------ Debug Options
% 11.80/1.99  
% 11.80/1.99  --dbg_backtrace                         false
% 11.80/1.99  --dbg_dump_prop_clauses                 false
% 11.80/1.99  --dbg_dump_prop_clauses_file            -
% 11.80/1.99  --dbg_out_stat                          false
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  ------ Proving...
% 11.80/1.99  
% 11.80/1.99  
% 11.80/1.99  % SZS status Theorem for theBenchmark.p
% 11.80/1.99  
% 11.80/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.80/1.99  
% 11.80/1.99  fof(f17,conjecture,(
% 11.80/1.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f18,negated_conjecture,(
% 11.80/1.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 11.80/1.99    inference(negated_conjecture,[],[f17])).
% 11.80/1.99  
% 11.80/1.99  fof(f19,plain,(
% 11.80/1.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 11.80/1.99    inference(pure_predicate_removal,[],[f18])).
% 11.80/1.99  
% 11.80/1.99  fof(f47,plain,(
% 11.80/1.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 11.80/1.99    inference(ennf_transformation,[],[f19])).
% 11.80/1.99  
% 11.80/1.99  fof(f48,plain,(
% 11.80/1.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 11.80/1.99    inference(flattening,[],[f47])).
% 11.80/1.99  
% 11.80/1.99  fof(f54,plain,(
% 11.80/1.99    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 11.80/1.99    introduced(choice_axiom,[])).
% 11.80/1.99  
% 11.80/1.99  fof(f53,plain,(
% 11.80/1.99    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))) )),
% 11.80/1.99    introduced(choice_axiom,[])).
% 11.80/1.99  
% 11.80/1.99  fof(f52,plain,(
% 11.80/1.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 11.80/1.99    introduced(choice_axiom,[])).
% 11.80/1.99  
% 11.80/1.99  fof(f55,plain,(
% 11.80/1.99    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 11.80/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f54,f53,f52])).
% 11.80/1.99  
% 11.80/1.99  fof(f93,plain,(
% 11.80/1.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 11.80/1.99    inference(cnf_transformation,[],[f55])).
% 11.80/1.99  
% 11.80/1.99  fof(f14,axiom,(
% 11.80/1.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f42,plain,(
% 11.80/1.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 11.80/1.99    inference(ennf_transformation,[],[f14])).
% 11.80/1.99  
% 11.80/1.99  fof(f84,plain,(
% 11.80/1.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f42])).
% 11.80/1.99  
% 11.80/1.99  fof(f90,plain,(
% 11.80/1.99    l1_struct_0(sK1)),
% 11.80/1.99    inference(cnf_transformation,[],[f55])).
% 11.80/1.99  
% 11.80/1.99  fof(f89,plain,(
% 11.80/1.99    l1_struct_0(sK0)),
% 11.80/1.99    inference(cnf_transformation,[],[f55])).
% 11.80/1.99  
% 11.80/1.99  fof(f7,axiom,(
% 11.80/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f29,plain,(
% 11.80/1.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.80/1.99    inference(ennf_transformation,[],[f7])).
% 11.80/1.99  
% 11.80/1.99  fof(f65,plain,(
% 11.80/1.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.80/1.99    inference(cnf_transformation,[],[f29])).
% 11.80/1.99  
% 11.80/1.99  fof(f94,plain,(
% 11.80/1.99    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 11.80/1.99    inference(cnf_transformation,[],[f55])).
% 11.80/1.99  
% 11.80/1.99  fof(f11,axiom,(
% 11.80/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f36,plain,(
% 11.80/1.99    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.80/1.99    inference(ennf_transformation,[],[f11])).
% 11.80/1.99  
% 11.80/1.99  fof(f37,plain,(
% 11.80/1.99    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.80/1.99    inference(flattening,[],[f36])).
% 11.80/1.99  
% 11.80/1.99  fof(f76,plain,(
% 11.80/1.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f37])).
% 11.80/1.99  
% 11.80/1.99  fof(f9,axiom,(
% 11.80/1.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f32,plain,(
% 11.80/1.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.80/1.99    inference(ennf_transformation,[],[f9])).
% 11.80/1.99  
% 11.80/1.99  fof(f33,plain,(
% 11.80/1.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.80/1.99    inference(flattening,[],[f32])).
% 11.80/1.99  
% 11.80/1.99  fof(f50,plain,(
% 11.80/1.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.80/1.99    inference(nnf_transformation,[],[f33])).
% 11.80/1.99  
% 11.80/1.99  fof(f72,plain,(
% 11.80/1.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f50])).
% 11.80/1.99  
% 11.80/1.99  fof(f6,axiom,(
% 11.80/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f20,plain,(
% 11.80/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 11.80/1.99    inference(pure_predicate_removal,[],[f6])).
% 11.80/1.99  
% 11.80/1.99  fof(f28,plain,(
% 11.80/1.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.80/1.99    inference(ennf_transformation,[],[f20])).
% 11.80/1.99  
% 11.80/1.99  fof(f64,plain,(
% 11.80/1.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.80/1.99    inference(cnf_transformation,[],[f28])).
% 11.80/1.99  
% 11.80/1.99  fof(f91,plain,(
% 11.80/1.99    v1_funct_1(sK2)),
% 11.80/1.99    inference(cnf_transformation,[],[f55])).
% 11.80/1.99  
% 11.80/1.99  fof(f92,plain,(
% 11.80/1.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 11.80/1.99    inference(cnf_transformation,[],[f55])).
% 11.80/1.99  
% 11.80/1.99  fof(f1,axiom,(
% 11.80/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f21,plain,(
% 11.80/1.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.80/1.99    inference(ennf_transformation,[],[f1])).
% 11.80/1.99  
% 11.80/1.99  fof(f56,plain,(
% 11.80/1.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f21])).
% 11.80/1.99  
% 11.80/1.99  fof(f2,axiom,(
% 11.80/1.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f57,plain,(
% 11.80/1.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.80/1.99    inference(cnf_transformation,[],[f2])).
% 11.80/1.99  
% 11.80/1.99  fof(f15,axiom,(
% 11.80/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f43,plain,(
% 11.80/1.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.80/1.99    inference(ennf_transformation,[],[f15])).
% 11.80/1.99  
% 11.80/1.99  fof(f44,plain,(
% 11.80/1.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.80/1.99    inference(flattening,[],[f43])).
% 11.80/1.99  
% 11.80/1.99  fof(f85,plain,(
% 11.80/1.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f44])).
% 11.80/1.99  
% 11.80/1.99  fof(f95,plain,(
% 11.80/1.99    v2_funct_1(sK2)),
% 11.80/1.99    inference(cnf_transformation,[],[f55])).
% 11.80/1.99  
% 11.80/1.99  fof(f10,axiom,(
% 11.80/1.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f34,plain,(
% 11.80/1.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.80/1.99    inference(ennf_transformation,[],[f10])).
% 11.80/1.99  
% 11.80/1.99  fof(f35,plain,(
% 11.80/1.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.80/1.99    inference(flattening,[],[f34])).
% 11.80/1.99  
% 11.80/1.99  fof(f51,plain,(
% 11.80/1.99    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.80/1.99    inference(nnf_transformation,[],[f35])).
% 11.80/1.99  
% 11.80/1.99  fof(f75,plain,(
% 11.80/1.99    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f51])).
% 11.80/1.99  
% 11.80/1.99  fof(f103,plain,(
% 11.80/1.99    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 11.80/1.99    inference(equality_resolution,[],[f75])).
% 11.80/1.99  
% 11.80/1.99  fof(f96,plain,(
% 11.80/1.99    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 11.80/1.99    inference(cnf_transformation,[],[f55])).
% 11.80/1.99  
% 11.80/1.99  fof(f4,axiom,(
% 11.80/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f24,plain,(
% 11.80/1.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.80/1.99    inference(ennf_transformation,[],[f4])).
% 11.80/1.99  
% 11.80/1.99  fof(f25,plain,(
% 11.80/1.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.80/1.99    inference(flattening,[],[f24])).
% 11.80/1.99  
% 11.80/1.99  fof(f62,plain,(
% 11.80/1.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f25])).
% 11.80/1.99  
% 11.80/1.99  fof(f13,axiom,(
% 11.80/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f40,plain,(
% 11.80/1.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.80/1.99    inference(ennf_transformation,[],[f13])).
% 11.80/1.99  
% 11.80/1.99  fof(f41,plain,(
% 11.80/1.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.80/1.99    inference(flattening,[],[f40])).
% 11.80/1.99  
% 11.80/1.99  fof(f83,plain,(
% 11.80/1.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f41])).
% 11.80/1.99  
% 11.80/1.99  fof(f61,plain,(
% 11.80/1.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f25])).
% 11.80/1.99  
% 11.80/1.99  fof(f12,axiom,(
% 11.80/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f38,plain,(
% 11.80/1.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.80/1.99    inference(ennf_transformation,[],[f12])).
% 11.80/1.99  
% 11.80/1.99  fof(f39,plain,(
% 11.80/1.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.80/1.99    inference(flattening,[],[f38])).
% 11.80/1.99  
% 11.80/1.99  fof(f78,plain,(
% 11.80/1.99    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f39])).
% 11.80/1.99  
% 11.80/1.99  fof(f3,axiom,(
% 11.80/1.99    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f22,plain,(
% 11.80/1.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.80/1.99    inference(ennf_transformation,[],[f3])).
% 11.80/1.99  
% 11.80/1.99  fof(f23,plain,(
% 11.80/1.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.80/1.99    inference(flattening,[],[f22])).
% 11.80/1.99  
% 11.80/1.99  fof(f58,plain,(
% 11.80/1.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f23])).
% 11.80/1.99  
% 11.80/1.99  fof(f5,axiom,(
% 11.80/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f26,plain,(
% 11.80/1.99    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.80/1.99    inference(ennf_transformation,[],[f5])).
% 11.80/1.99  
% 11.80/1.99  fof(f27,plain,(
% 11.80/1.99    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.80/1.99    inference(flattening,[],[f26])).
% 11.80/1.99  
% 11.80/1.99  fof(f63,plain,(
% 11.80/1.99    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f27])).
% 11.80/1.99  
% 11.80/1.99  fof(f60,plain,(
% 11.80/1.99    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f23])).
% 11.80/1.99  
% 11.80/1.99  fof(f82,plain,(
% 11.80/1.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f41])).
% 11.80/1.99  
% 11.80/1.99  fof(f79,plain,(
% 11.80/1.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f39])).
% 11.80/1.99  
% 11.80/1.99  fof(f16,axiom,(
% 11.80/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f45,plain,(
% 11.80/1.99    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.80/1.99    inference(ennf_transformation,[],[f16])).
% 11.80/1.99  
% 11.80/1.99  fof(f46,plain,(
% 11.80/1.99    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.80/1.99    inference(flattening,[],[f45])).
% 11.80/1.99  
% 11.80/1.99  fof(f88,plain,(
% 11.80/1.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f46])).
% 11.80/1.99  
% 11.80/1.99  fof(f86,plain,(
% 11.80/1.99    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f46])).
% 11.80/1.99  
% 11.80/1.99  fof(f87,plain,(
% 11.80/1.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f46])).
% 11.80/1.99  
% 11.80/1.99  fof(f8,axiom,(
% 11.80/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 11.80/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.99  
% 11.80/1.99  fof(f30,plain,(
% 11.80/1.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.80/1.99    inference(ennf_transformation,[],[f8])).
% 11.80/1.99  
% 11.80/1.99  fof(f31,plain,(
% 11.80/1.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.80/1.99    inference(flattening,[],[f30])).
% 11.80/1.99  
% 11.80/1.99  fof(f49,plain,(
% 11.80/1.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.80/1.99    inference(nnf_transformation,[],[f31])).
% 11.80/1.99  
% 11.80/1.99  fof(f70,plain,(
% 11.80/1.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.80/1.99    inference(cnf_transformation,[],[f49])).
% 11.80/1.99  
% 11.80/1.99  fof(f99,plain,(
% 11.80/1.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 11.80/1.99    inference(equality_resolution,[],[f70])).
% 11.80/1.99  
% 11.80/1.99  fof(f77,plain,(
% 11.80/1.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.80/1.99    inference(cnf_transformation,[],[f37])).
% 11.80/1.99  
% 11.80/1.99  fof(f104,plain,(
% 11.80/1.99    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 11.80/1.99    inference(equality_resolution,[],[f77])).
% 11.80/1.99  
% 11.80/1.99  cnf(c_36,negated_conjecture,
% 11.80/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 11.80/1.99      inference(cnf_transformation,[],[f93]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1302,plain,
% 11.80/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_28,plain,
% 11.80/1.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 11.80/1.99      inference(cnf_transformation,[],[f84]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_39,negated_conjecture,
% 11.80/1.99      ( l1_struct_0(sK1) ),
% 11.80/1.99      inference(cnf_transformation,[],[f90]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_443,plain,
% 11.80/1.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 11.80/1.99      inference(resolution_lifted,[status(thm)],[c_28,c_39]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_444,plain,
% 11.80/1.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 11.80/1.99      inference(unflattening,[status(thm)],[c_443]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_40,negated_conjecture,
% 11.80/1.99      ( l1_struct_0(sK0) ),
% 11.80/1.99      inference(cnf_transformation,[],[f89]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_448,plain,
% 11.80/1.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 11.80/1.99      inference(resolution_lifted,[status(thm)],[c_28,c_40]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_449,plain,
% 11.80/1.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 11.80/1.99      inference(unflattening,[status(thm)],[c_448]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1330,plain,
% 11.80/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 11.80/1.99      inference(light_normalisation,[status(thm)],[c_1302,c_444,c_449]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_9,plain,
% 11.80/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/1.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.80/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1319,plain,
% 11.80/1.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.80/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1767,plain,
% 11.80/1.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 11.80/1.99      inference(superposition,[status(thm)],[c_1330,c_1319]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_35,negated_conjecture,
% 11.80/1.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 11.80/1.99      inference(cnf_transformation,[],[f94]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1329,plain,
% 11.80/1.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 11.80/1.99      inference(light_normalisation,[status(thm)],[c_35,c_444,c_449]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1816,plain,
% 11.80/1.99      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 11.80/1.99      inference(demodulation,[status(thm)],[c_1767,c_1329]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1906,plain,
% 11.80/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 11.80/1.99      inference(demodulation,[status(thm)],[c_1816,c_1330]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_21,plain,
% 11.80/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.80/1.99      | v1_partfun1(X0,X1)
% 11.80/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/1.99      | ~ v1_funct_1(X0)
% 11.80/1.99      | k1_xboole_0 = X2 ),
% 11.80/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_17,plain,
% 11.80/1.99      ( ~ v1_partfun1(X0,X1)
% 11.80/1.99      | ~ v4_relat_1(X0,X1)
% 11.80/1.99      | ~ v1_relat_1(X0)
% 11.80/1.99      | k1_relat_1(X0) = X1 ),
% 11.80/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_517,plain,
% 11.80/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.80/1.99      | ~ v4_relat_1(X0,X1)
% 11.80/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/1.99      | ~ v1_funct_1(X0)
% 11.80/1.99      | ~ v1_relat_1(X0)
% 11.80/1.99      | k1_relat_1(X0) = X1
% 11.80/1.99      | k1_xboole_0 = X2 ),
% 11.80/1.99      inference(resolution,[status(thm)],[c_21,c_17]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_8,plain,
% 11.80/1.99      ( v4_relat_1(X0,X1)
% 11.80/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.80/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_521,plain,
% 11.80/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.80/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/1.99      | ~ v1_funct_1(X0)
% 11.80/1.99      | ~ v1_relat_1(X0)
% 11.80/1.99      | k1_relat_1(X0) = X1
% 11.80/1.99      | k1_xboole_0 = X2 ),
% 11.80/1.99      inference(global_propositional_subsumption,
% 11.80/1.99                [status(thm)],
% 11.80/1.99                [c_517,c_8]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1298,plain,
% 11.80/1.99      ( k1_relat_1(X0) = X1
% 11.80/1.99      | k1_xboole_0 = X2
% 11.80/1.99      | v1_funct_2(X0,X1,X2) != iProver_top
% 11.80/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.80/1.99      | v1_funct_1(X0) != iProver_top
% 11.80/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_521]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_2094,plain,
% 11.80/1.99      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 11.80/1.99      | k2_relat_1(sK2) = k1_xboole_0
% 11.80/1.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.80/1.99      | v1_funct_1(sK2) != iProver_top
% 11.80/1.99      | v1_relat_1(sK2) != iProver_top ),
% 11.80/1.99      inference(superposition,[status(thm)],[c_1906,c_1298]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_38,negated_conjecture,
% 11.80/1.99      ( v1_funct_1(sK2) ),
% 11.80/1.99      inference(cnf_transformation,[],[f91]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_37,negated_conjecture,
% 11.80/1.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 11.80/1.99      inference(cnf_transformation,[],[f92]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1301,plain,
% 11.80/1.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1328,plain,
% 11.80/1.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 11.80/1.99      inference(light_normalisation,[status(thm)],[c_1301,c_444,c_449]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1907,plain,
% 11.80/1.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 11.80/1.99      inference(demodulation,[status(thm)],[c_1816,c_1328]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1911,plain,
% 11.80/1.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
% 11.80/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_1907]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_2095,plain,
% 11.80/1.99      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
% 11.80/1.99      | ~ v1_funct_1(sK2)
% 11.80/1.99      | ~ v1_relat_1(sK2)
% 11.80/1.99      | k2_struct_0(sK0) = k1_relat_1(sK2)
% 11.80/1.99      | k2_relat_1(sK2) = k1_xboole_0 ),
% 11.80/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_2094]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_0,plain,
% 11.80/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.80/1.99      | ~ v1_relat_1(X1)
% 11.80/1.99      | v1_relat_1(X0) ),
% 11.80/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1529,plain,
% 11.80/1.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 11.80/1.99      | ~ v1_relat_1(X0)
% 11.80/1.99      | v1_relat_1(sK2) ),
% 11.80/1.99      inference(instantiation,[status(thm)],[c_0]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1754,plain,
% 11.80/1.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.80/1.99      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 11.80/1.99      | v1_relat_1(sK2) ),
% 11.80/1.99      inference(instantiation,[status(thm)],[c_1529]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_2113,plain,
% 11.80/1.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 11.80/1.99      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 11.80/1.99      | v1_relat_1(sK2) ),
% 11.80/1.99      inference(instantiation,[status(thm)],[c_1754]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1,plain,
% 11.80/1.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.80/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_2184,plain,
% 11.80/1.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 11.80/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_2359,plain,
% 11.80/1.99      ( k2_relat_1(sK2) = k1_xboole_0
% 11.80/1.99      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 11.80/1.99      inference(global_propositional_subsumption,
% 11.80/1.99                [status(thm)],
% 11.80/1.99                [c_2094,c_38,c_36,c_1911,c_2095,c_2113,c_2184]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_2360,plain,
% 11.80/1.99      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 11.80/1.99      | k2_relat_1(sK2) = k1_xboole_0 ),
% 11.80/1.99      inference(renaming,[status(thm)],[c_2359]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1904,plain,
% 11.80/1.99      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 11.80/1.99      inference(demodulation,[status(thm)],[c_1816,c_1767]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_29,plain,
% 11.80/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.80/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/1.99      | ~ v1_funct_1(X0)
% 11.80/1.99      | ~ v2_funct_1(X0)
% 11.80/1.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 11.80/1.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 11.80/1.99      inference(cnf_transformation,[],[f85]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1307,plain,
% 11.80/1.99      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
% 11.80/1.99      | k2_relset_1(X0,X1,X2) != X1
% 11.80/1.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.80/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.80/1.99      | v1_funct_1(X2) != iProver_top
% 11.80/1.99      | v2_funct_1(X2) != iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_4102,plain,
% 11.80/1.99      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 11.80/1.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.80/1.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 11.80/1.99      | v1_funct_1(sK2) != iProver_top
% 11.80/1.99      | v2_funct_1(sK2) != iProver_top ),
% 11.80/1.99      inference(superposition,[status(thm)],[c_1904,c_1307]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_43,plain,
% 11.80/1.99      ( v1_funct_1(sK2) = iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_34,negated_conjecture,
% 11.80/1.99      ( v2_funct_1(sK2) ),
% 11.80/1.99      inference(cnf_transformation,[],[f95]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_46,plain,
% 11.80/1.99      ( v2_funct_1(sK2) = iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_4568,plain,
% 11.80/1.99      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 11.80/1.99      inference(global_propositional_subsumption,
% 11.80/1.99                [status(thm)],
% 11.80/1.99                [c_4102,c_43,c_46,c_1906,c_1907]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_18,plain,
% 11.80/1.99      ( r2_funct_2(X0,X1,X2,X2)
% 11.80/1.99      | ~ v1_funct_2(X2,X0,X1)
% 11.80/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.80/1.99      | ~ v1_funct_1(X2) ),
% 11.80/1.99      inference(cnf_transformation,[],[f103]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_33,negated_conjecture,
% 11.80/1.99      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 11.80/1.99      inference(cnf_transformation,[],[f96]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_496,plain,
% 11.80/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.80/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/1.99      | ~ v1_funct_1(X0)
% 11.80/1.99      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 11.80/1.99      | u1_struct_0(sK1) != X2
% 11.80/1.99      | u1_struct_0(sK0) != X1
% 11.80/1.99      | sK2 != X0 ),
% 11.80/1.99      inference(resolution_lifted,[status(thm)],[c_18,c_33]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_497,plain,
% 11.80/1.99      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 11.80/1.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 11.80/1.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 11.80/1.99      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 11.80/1.99      inference(unflattening,[status(thm)],[c_496]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1299,plain,
% 11.80/1.99      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 11.80/1.99      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 11.80/1.99      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 11.80/1.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_497]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1331,plain,
% 11.80/1.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 11.80/1.99      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 11.80/1.99      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 11.80/1.99      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 11.80/1.99      inference(light_normalisation,[status(thm)],[c_1299,c_444,c_449]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1905,plain,
% 11.80/1.99      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 11.80/1.99      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.80/1.99      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 11.80/1.99      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 11.80/1.99      inference(demodulation,[status(thm)],[c_1816,c_1331]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_4572,plain,
% 11.80/1.99      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 11.80/1.99      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.80/1.99      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 11.80/1.99      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 11.80/1.99      inference(demodulation,[status(thm)],[c_4568,c_1905]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_5010,plain,
% 11.80/1.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 11.80/1.99      | k2_relat_1(sK2) = k1_xboole_0
% 11.80/1.99      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.80/1.99      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 11.80/1.99      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 11.80/1.99      inference(superposition,[status(thm)],[c_2360,c_4572]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1300,plain,
% 11.80/1.99      ( v1_funct_1(sK2) = iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_5,plain,
% 11.80/1.99      ( ~ v1_funct_1(X0)
% 11.80/1.99      | ~ v2_funct_1(X0)
% 11.80/1.99      | ~ v1_relat_1(X0)
% 11.80/1.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 11.80/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_1322,plain,
% 11.80/1.99      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 11.80/1.99      | v1_funct_1(X0) != iProver_top
% 11.80/1.99      | v2_funct_1(X0) != iProver_top
% 11.80/1.99      | v1_relat_1(X0) != iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_3353,plain,
% 11.80/1.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 11.80/1.99      | v2_funct_1(sK2) != iProver_top
% 11.80/1.99      | v1_relat_1(sK2) != iProver_top ),
% 11.80/1.99      inference(superposition,[status(thm)],[c_1300,c_1322]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_45,plain,
% 11.80/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_2114,plain,
% 11.80/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 11.80/1.99      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 11.80/1.99      | v1_relat_1(sK2) = iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_2113]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_2185,plain,
% 11.80/1.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 11.80/1.99      inference(predicate_to_equality,[status(thm)],[c_2184]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_3579,plain,
% 11.80/1.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.80/1.99      inference(global_propositional_subsumption,
% 11.80/1.99                [status(thm)],
% 11.80/1.99                [c_3353,c_45,c_46,c_2114,c_2185]) ).
% 11.80/1.99  
% 11.80/1.99  cnf(c_25,plain,
% 11.80/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 11.80/2.00      | ~ v1_funct_1(X0)
% 11.80/2.00      | ~ v1_relat_1(X0) ),
% 11.80/2.00      inference(cnf_transformation,[],[f83]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1309,plain,
% 11.80/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 11.80/2.00      | v1_funct_1(X0) != iProver_top
% 11.80/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.80/2.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_3581,plain,
% 11.80/2.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 11.80/2.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.80/2.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_3579,c_1309]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_6,plain,
% 11.80/2.00      ( ~ v1_funct_1(X0)
% 11.80/2.00      | ~ v2_funct_1(X0)
% 11.80/2.00      | ~ v1_relat_1(X0)
% 11.80/2.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 11.80/2.00      inference(cnf_transformation,[],[f61]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1321,plain,
% 11.80/2.00      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 11.80/2.00      | v1_funct_1(X0) != iProver_top
% 11.80/2.00      | v2_funct_1(X0) != iProver_top
% 11.80/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.80/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_3285,plain,
% 11.80/2.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 11.80/2.00      | v2_funct_1(sK2) != iProver_top
% 11.80/2.00      | v1_relat_1(sK2) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_1300,c_1321]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_3483,plain,
% 11.80/2.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_3285,c_45,c_46,c_2114,c_2185]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_3584,plain,
% 11.80/2.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 11.80/2.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.80/2.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 11.80/2.00      inference(light_normalisation,[status(thm)],[c_3581,c_3483]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_44,plain,
% 11.80/2.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 11.80/2.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_24,plain,
% 11.80/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.80/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/2.00      | ~ v1_funct_1(X0)
% 11.80/2.00      | v1_funct_1(k2_funct_1(X0))
% 11.80/2.00      | ~ v2_funct_1(X0)
% 11.80/2.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 11.80/2.00      inference(cnf_transformation,[],[f78]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1667,plain,
% 11.80/2.00      ( ~ v1_funct_2(sK2,X0,X1)
% 11.80/2.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.80/2.00      | v1_funct_1(k2_funct_1(sK2))
% 11.80/2.00      | ~ v1_funct_1(sK2)
% 11.80/2.00      | ~ v2_funct_1(sK2)
% 11.80/2.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_24]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1684,plain,
% 11.80/2.00      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 11.80/2.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 11.80/2.00      | v1_funct_1(k2_funct_1(sK2))
% 11.80/2.00      | ~ v1_funct_1(sK2)
% 11.80/2.00      | ~ v2_funct_1(sK2)
% 11.80/2.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_1667]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1685,plain,
% 11.80/2.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 11.80/2.00      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 11.80/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 11.80/2.00      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 11.80/2.00      | v1_funct_1(sK2) != iProver_top
% 11.80/2.00      | v2_funct_1(sK2) != iProver_top ),
% 11.80/2.00      inference(predicate_to_equality,[status(thm)],[c_1684]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_794,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1724,plain,
% 11.80/2.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
% 11.80/2.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 11.80/2.00      | u1_struct_0(sK1) != X0 ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_794]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_2084,plain,
% 11.80/2.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 11.80/2.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 11.80/2.00      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_1724]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_4,plain,
% 11.80/2.00      ( ~ v1_funct_1(X0)
% 11.80/2.00      | ~ v2_funct_1(X0)
% 11.80/2.00      | ~ v1_relat_1(X0)
% 11.80/2.00      | v1_relat_1(k2_funct_1(X0)) ),
% 11.80/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_2336,plain,
% 11.80/2.00      ( ~ v1_funct_1(sK2)
% 11.80/2.00      | ~ v2_funct_1(sK2)
% 11.80/2.00      | v1_relat_1(k2_funct_1(sK2))
% 11.80/2.00      | ~ v1_relat_1(sK2) ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_4]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_2337,plain,
% 11.80/2.00      ( v1_funct_1(sK2) != iProver_top
% 11.80/2.00      | v2_funct_1(sK2) != iProver_top
% 11.80/2.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 11.80/2.00      | v1_relat_1(sK2) != iProver_top ),
% 11.80/2.00      inference(predicate_to_equality,[status(thm)],[c_2336]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_3718,plain,
% 11.80/2.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_3584,c_43,c_44,c_45,c_35,c_46,c_444,c_1685,c_2084,
% 11.80/2.00                 c_2114,c_2185,c_2337]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_3726,plain,
% 11.80/2.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_3718,c_1319]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_3727,plain,
% 11.80/2.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.80/2.00      inference(light_normalisation,[status(thm)],[c_3726,c_3579]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_4103,plain,
% 11.80/2.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 11.80/2.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 11.80/2.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.80/2.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_3727,c_1307]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_7,plain,
% 11.80/2.00      ( ~ v1_funct_1(X0)
% 11.80/2.00      | ~ v2_funct_1(X0)
% 11.80/2.00      | ~ v1_relat_1(X0)
% 11.80/2.00      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 11.80/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1320,plain,
% 11.80/2.00      ( k2_funct_1(k2_funct_1(X0)) = X0
% 11.80/2.00      | v1_funct_1(X0) != iProver_top
% 11.80/2.00      | v2_funct_1(X0) != iProver_top
% 11.80/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.80/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_2146,plain,
% 11.80/2.00      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 11.80/2.00      | v2_funct_1(sK2) != iProver_top
% 11.80/2.00      | v1_relat_1(sK2) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_1300,c_1320]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1546,plain,
% 11.80/2.00      ( ~ v1_funct_1(sK2)
% 11.80/2.00      | ~ v2_funct_1(sK2)
% 11.80/2.00      | ~ v1_relat_1(sK2)
% 11.80/2.00      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_7]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_2263,plain,
% 11.80/2.00      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_2146,c_38,c_36,c_34,c_1546,c_2113,c_2184]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_4104,plain,
% 11.80/2.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 11.80/2.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 11.80/2.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.80/2.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.80/2.00      inference(light_normalisation,[status(thm)],[c_4103,c_2263]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_2,plain,
% 11.80/2.00      ( ~ v1_funct_1(X0)
% 11.80/2.00      | ~ v2_funct_1(X0)
% 11.80/2.00      | v2_funct_1(k2_funct_1(X0))
% 11.80/2.00      | ~ v1_relat_1(X0) ),
% 11.80/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_3129,plain,
% 11.80/2.00      ( ~ v1_funct_1(sK2)
% 11.80/2.00      | v2_funct_1(k2_funct_1(sK2))
% 11.80/2.00      | ~ v2_funct_1(sK2)
% 11.80/2.00      | ~ v1_relat_1(sK2) ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_2]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_3130,plain,
% 11.80/2.00      ( v1_funct_1(sK2) != iProver_top
% 11.80/2.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 11.80/2.00      | v2_funct_1(sK2) != iProver_top
% 11.80/2.00      | v1_relat_1(sK2) != iProver_top ),
% 11.80/2.00      inference(predicate_to_equality,[status(thm)],[c_3129]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_26,plain,
% 11.80/2.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 11.80/2.00      | ~ v1_funct_1(X0)
% 11.80/2.00      | ~ v1_relat_1(X0) ),
% 11.80/2.00      inference(cnf_transformation,[],[f82]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1308,plain,
% 11.80/2.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 11.80/2.00      | v1_funct_1(X0) != iProver_top
% 11.80/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.80/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_3582,plain,
% 11.80/2.00      ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) = iProver_top
% 11.80/2.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.80/2.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_3579,c_1308]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_3583,plain,
% 11.80/2.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 11.80/2.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.80/2.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 11.80/2.00      inference(light_normalisation,[status(thm)],[c_3582,c_3483]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_4409,plain,
% 11.80/2.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_4104,c_43,c_44,c_45,c_35,c_46,c_444,c_1685,c_2084,
% 11.80/2.00                 c_2114,c_2185,c_2337,c_3130,c_3583,c_3584]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5011,plain,
% 11.80/2.00      ( k2_relat_1(sK2) = k1_xboole_0
% 11.80/2.00      | sK2 != sK2
% 11.80/2.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 11.80/2.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 11.80/2.00      inference(light_normalisation,[status(thm)],[c_5010,c_4409]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5012,plain,
% 11.80/2.00      ( k2_relat_1(sK2) = k1_xboole_0
% 11.80/2.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 11.80/2.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 11.80/2.00      inference(equality_resolution_simp,[status(thm)],[c_5011]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_23,plain,
% 11.80/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.80/2.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 11.80/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/2.00      | ~ v1_funct_1(X0)
% 11.80/2.00      | ~ v2_funct_1(X0)
% 11.80/2.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 11.80/2.00      inference(cnf_transformation,[],[f79]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1311,plain,
% 11.80/2.00      ( k2_relset_1(X0,X1,X2) != X1
% 11.80/2.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.80/2.00      | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
% 11.80/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.80/2.00      | v1_funct_1(X2) != iProver_top
% 11.80/2.00      | v2_funct_1(X2) != iProver_top ),
% 11.80/2.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_4110,plain,
% 11.80/2.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 11.80/2.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.80/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 11.80/2.00      | v1_funct_1(sK2) != iProver_top
% 11.80/2.00      | v2_funct_1(sK2) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_1904,c_1311]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_30,plain,
% 11.80/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.80/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/2.00      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.80/2.00      | ~ v1_funct_1(X0) ),
% 11.80/2.00      inference(cnf_transformation,[],[f88]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1306,plain,
% 11.80/2.00      ( v1_funct_2(X0,X1,X2) != iProver_top
% 11.80/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 11.80/2.00      | v1_funct_1(X0) != iProver_top ),
% 11.80/2.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_4575,plain,
% 11.80/2.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 11.80/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 11.80/2.00      | v1_funct_1(sK2) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_4568,c_1306]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5099,plain,
% 11.80/2.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_4575,c_43,c_1906,c_1907]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_32,plain,
% 11.80/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.80/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/2.00      | ~ v1_funct_1(X0)
% 11.80/2.00      | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
% 11.80/2.00      inference(cnf_transformation,[],[f86]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1304,plain,
% 11.80/2.00      ( v1_funct_2(X0,X1,X2) != iProver_top
% 11.80/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.80/2.00      | v1_funct_1(X0) != iProver_top
% 11.80/2.00      | v1_funct_1(k2_tops_2(X1,X2,X0)) = iProver_top ),
% 11.80/2.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5105,plain,
% 11.80/2.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 11.80/2.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top
% 11.80/2.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_5099,c_1304]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5935,plain,
% 11.80/2.00      ( m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 11.80/2.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.80/2.00      | k2_relat_1(sK2) = k1_xboole_0 ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_5012,c_43,c_44,c_45,c_35,c_46,c_444,c_1685,c_1906,
% 11.80/2.00                 c_1907,c_2084,c_4110,c_5105]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5936,plain,
% 11.80/2.00      ( k2_relat_1(sK2) = k1_xboole_0
% 11.80/2.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 11.80/2.00      inference(renaming,[status(thm)],[c_5935]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5941,plain,
% 11.80/2.00      ( k2_relat_1(sK2) = k1_xboole_0
% 11.80/2.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_2360,c_5936]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5943,plain,
% 11.80/2.00      ( k2_relat_1(sK2) = k1_xboole_0
% 11.80/2.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.80/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top ),
% 11.80/2.00      inference(light_normalisation,[status(thm)],[c_5941,c_4409]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5108,plain,
% 11.80/2.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_5099,c_1319]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5109,plain,
% 11.80/2.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.80/2.00      inference(light_normalisation,[status(thm)],[c_5108,c_3579]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5201,plain,
% 11.80/2.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 11.80/2.00      | k2_struct_0(sK0) != k1_relat_1(sK2)
% 11.80/2.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 11.80/2.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.80/2.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_5109,c_1307]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5204,plain,
% 11.80/2.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 11.80/2.00      | k2_struct_0(sK0) != k1_relat_1(sK2)
% 11.80/2.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 11.80/2.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.80/2.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.80/2.00      inference(light_normalisation,[status(thm)],[c_5201,c_2263]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5868,plain,
% 11.80/2.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 11.80/2.00      | k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_5204,c_43,c_44,c_45,c_35,c_46,c_444,c_1685,c_1906,
% 11.80/2.00                 c_1907,c_2084,c_2114,c_2185,c_3130,c_4110,c_4575]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5870,plain,
% 11.80/2.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 11.80/2.00      | k2_relat_1(sK2) = k1_xboole_0 ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_2360,c_5868]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5940,plain,
% 11.80/2.00      ( k2_relat_1(sK2) = k1_xboole_0
% 11.80/2.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.80/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_5870,c_5936]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5948,plain,
% 11.80/2.00      ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.80/2.00      | k2_relat_1(sK2) = k1_xboole_0 ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_5943,c_43,c_44,c_45,c_35,c_46,c_444,c_1685,c_1906,
% 11.80/2.00                 c_1907,c_2084,c_4110,c_4575,c_5939]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5949,plain,
% 11.80/2.00      ( k2_relat_1(sK2) = k1_xboole_0
% 11.80/2.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 11.80/2.00      inference(renaming,[status(thm)],[c_5948]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5954,plain,
% 11.80/2.00      ( k2_relat_1(sK2) = k1_xboole_0
% 11.80/2.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_2360,c_5949]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5956,plain,
% 11.80/2.00      ( k2_relat_1(sK2) = k1_xboole_0
% 11.80/2.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top ),
% 11.80/2.00      inference(light_normalisation,[status(thm)],[c_5954,c_4409]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_31,plain,
% 11.80/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.80/2.00      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 11.80/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/2.00      | ~ v1_funct_1(X0) ),
% 11.80/2.00      inference(cnf_transformation,[],[f87]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1305,plain,
% 11.80/2.00      ( v1_funct_2(X0,X1,X2) != iProver_top
% 11.80/2.00      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
% 11.80/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.80/2.00      | v1_funct_1(X0) != iProver_top ),
% 11.80/2.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5952,plain,
% 11.80/2.00      ( k2_relat_1(sK2) = k1_xboole_0
% 11.80/2.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 11.80/2.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_1305,c_5949]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_6234,plain,
% 11.80/2.00      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_5956,c_43,c_44,c_45,c_35,c_46,c_444,c_1685,c_1906,
% 11.80/2.00                 c_1907,c_2084,c_4110,c_4575,c_5952]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_6257,plain,
% 11.80/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) = iProver_top ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_6234,c_1906]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_11,plain,
% 11.80/2.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 11.80/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 11.80/2.00      | k1_xboole_0 = X1
% 11.80/2.00      | k1_xboole_0 = X0 ),
% 11.80/2.00      inference(cnf_transformation,[],[f99]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1317,plain,
% 11.80/2.00      ( k1_xboole_0 = X0
% 11.80/2.00      | k1_xboole_0 = X1
% 11.80/2.00      | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
% 11.80/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
% 11.80/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_7296,plain,
% 11.80/2.00      ( k2_struct_0(sK0) = k1_xboole_0
% 11.80/2.00      | sK2 = k1_xboole_0
% 11.80/2.00      | v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_6257,c_1317]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_6259,plain,
% 11.80/2.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) = iProver_top ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_6234,c_1907]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_7657,plain,
% 11.80/2.00      ( sK2 = k1_xboole_0 | k2_struct_0(sK0) = k1_xboole_0 ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_7296,c_6259]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_7658,plain,
% 11.80/2.00      ( k2_struct_0(sK0) = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 11.80/2.00      inference(renaming,[status(thm)],[c_7657]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_6237,plain,
% 11.80/2.00      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 11.80/2.00      | k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_6234,c_5868]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_7662,plain,
% 11.80/2.00      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 11.80/2.00      | k1_relat_1(sK2) != k1_xboole_0
% 11.80/2.00      | sK2 = k1_xboole_0 ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_7658,c_6237]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_2365,plain,
% 11.80/2.00      ( k2_relat_1(sK2) = k1_xboole_0
% 11.80/2.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_2360,c_1907]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1726,plain,
% 11.80/2.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 11.80/2.00      | ~ v1_funct_1(sK2)
% 11.80/2.00      | ~ v1_relat_1(sK2) ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_26]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1727,plain,
% 11.80/2.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
% 11.80/2.00      | v1_funct_1(sK2) != iProver_top
% 11.80/2.00      | v1_relat_1(sK2) != iProver_top ),
% 11.80/2.00      inference(predicate_to_equality,[status(thm)],[c_1726]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_2402,plain,
% 11.80/2.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_2365,c_43,c_45,c_1727,c_2114,c_2185]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_6256,plain,
% 11.80/2.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) = iProver_top ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_6234,c_2402]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_4411,plain,
% 11.80/2.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 11.80/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 11.80/2.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_4409,c_1306]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_4557,plain,
% 11.80/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_4411,c_43,c_44,c_45,c_35,c_46,c_444,c_1685,c_2084,
% 11.80/2.00                 c_2114,c_2185,c_2337,c_3583,c_3584]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_6248,plain,
% 11.80/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) = iProver_top ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_6234,c_4557]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_8019,plain,
% 11.80/2.00      ( k1_relat_1(sK2) = k1_xboole_0
% 11.80/2.00      | sK2 = k1_xboole_0
% 11.80/2.00      | v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_6248,c_1317]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_8876,plain,
% 11.80/2.00      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 11.80/2.00      | sK2 = k1_xboole_0 ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_7662,c_6256,c_8019]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_6243,plain,
% 11.80/2.00      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 11.80/2.00      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top
% 11.80/2.00      | v1_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_6234,c_4572]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5306,plain,
% 11.80/2.00      ( v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_5105,c_43,c_44,c_45,c_35,c_46,c_444,c_1685,c_1906,
% 11.80/2.00                 c_1907,c_2084,c_4110]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_6238,plain,
% 11.80/2.00      ( v1_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_6234,c_5306]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_8390,plain,
% 11.80/2.00      ( m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top
% 11.80/2.00      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 11.80/2.00      | k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) != sK2 ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_6243,c_6238]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_8391,plain,
% 11.80/2.00      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 11.80/2.00      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 11.80/2.00      inference(renaming,[status(thm)],[c_8390]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_8881,plain,
% 11.80/2.00      ( sK2 = k1_xboole_0
% 11.80/2.00      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_8876,c_8391]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_9585,plain,
% 11.80/2.00      ( sK2 = k1_xboole_0
% 11.80/2.00      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 11.80/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_8876,c_8881]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_9592,plain,
% 11.80/2.00      ( v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 11.80/2.00      | sK2 = k1_xboole_0 ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_9585,c_43,c_44,c_45,c_35,c_46,c_444,c_1685,c_2084,
% 11.80/2.00                 c_6241,c_6242,c_9584]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_9593,plain,
% 11.80/2.00      ( sK2 = k1_xboole_0
% 11.80/2.00      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 11.80/2.00      inference(renaming,[status(thm)],[c_9592]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_9597,plain,
% 11.80/2.00      ( sK2 = k1_xboole_0
% 11.80/2.00      | v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_8876,c_9593]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_6241,plain,
% 11.80/2.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) = iProver_top ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_6234,c_5099]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_4576,plain,
% 11.80/2.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 11.80/2.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.80/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 11.80/2.00      | v1_funct_1(sK2) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_4568,c_1305]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5089,plain,
% 11.80/2.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_4576,c_43,c_46,c_1906,c_1907,c_4110]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_6242,plain,
% 11.80/2.00      ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) = iProver_top ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_6234,c_5089]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_9596,plain,
% 11.80/2.00      ( sK2 = k1_xboole_0
% 11.80/2.00      | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
% 11.80/2.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_1305,c_9593]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_9702,plain,
% 11.80/2.00      ( sK2 = k1_xboole_0 ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_9597,c_43,c_44,c_45,c_35,c_46,c_444,c_1685,c_2084,
% 11.80/2.00                 c_6241,c_6242,c_9596]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_9714,plain,
% 11.80/2.00      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) = iProver_top ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_9702,c_6241]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_3831,plain,
% 11.80/2.00      ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
% 11.80/2.00      | k1_xboole_0 = X0
% 11.80/2.00      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 11.80/2.00      | v1_funct_2(k2_tops_2(k1_xboole_0,X0,X1),X0,k1_xboole_0) != iProver_top
% 11.80/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 11.80/2.00      | v1_funct_1(X1) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_1306,c_1317]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_13565,plain,
% 11.80/2.00      ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
% 11.80/2.00      | k1_xboole_0 = X0
% 11.80/2.00      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 11.80/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 11.80/2.00      | v1_funct_1(X1) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_1305,c_3831]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_13570,plain,
% 11.80/2.00      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
% 11.80/2.00      | k2_struct_0(sK0) = k1_xboole_0
% 11.80/2.00      | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
% 11.80/2.00      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_9714,c_13565]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_793,plain,( X0 = X0 ),theory(equality) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_826,plain,
% 11.80/2.00      ( k1_xboole_0 = k1_xboole_0 ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_793]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1453,plain,
% 11.80/2.00      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_794]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1454,plain,
% 11.80/2.00      ( sK2 != k1_xboole_0
% 11.80/2.00      | k1_xboole_0 = sK2
% 11.80/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_1453]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_801,plain,
% 11.80/2.00      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 11.80/2.00      theory(equality) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_2226,plain,
% 11.80/2.00      ( v1_funct_1(X0)
% 11.80/2.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 11.80/2.00      | X0 != k2_funct_1(sK2) ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_801]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_3084,plain,
% 11.80/2.00      ( v1_funct_1(k2_funct_1(X0))
% 11.80/2.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 11.80/2.00      | k2_funct_1(X0) != k2_funct_1(sK2) ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_2226]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_3086,plain,
% 11.80/2.00      ( ~ v1_funct_1(k2_funct_1(sK2))
% 11.80/2.00      | v1_funct_1(k2_funct_1(k1_xboole_0))
% 11.80/2.00      | k2_funct_1(k1_xboole_0) != k2_funct_1(sK2) ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_3084]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_799,plain,
% 11.80/2.00      ( X0 != X1 | k2_funct_1(X0) = k2_funct_1(X1) ),
% 11.80/2.00      theory(equality) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_3763,plain,
% 11.80/2.00      ( X0 != sK2 | k2_funct_1(X0) = k2_funct_1(sK2) ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_799]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_3764,plain,
% 11.80/2.00      ( k2_funct_1(k1_xboole_0) = k2_funct_1(sK2) | k1_xboole_0 != sK2 ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_3763]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_9722,plain,
% 11.80/2.00      ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) = iProver_top ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_9702,c_6242]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_9750,plain,
% 11.80/2.00      ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) ),
% 11.80/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_9722]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_13573,plain,
% 11.80/2.00      ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
% 11.80/2.00      | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
% 11.80/2.00      | k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
% 11.80/2.00      | k2_struct_0(sK0) = k1_xboole_0 ),
% 11.80/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_13570]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_20768,plain,
% 11.80/2.00      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
% 11.80/2.00      | k2_struct_0(sK0) = k1_xboole_0 ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_13570,c_38,c_43,c_37,c_44,c_36,c_45,c_35,c_34,c_46,
% 11.80/2.00                 c_444,c_826,c_1454,c_1684,c_1685,c_2084,c_3086,c_3764,
% 11.80/2.00                 c_6241,c_6242,c_9596,c_9750,c_13573]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_5315,plain,
% 11.80/2.00      ( k2_funct_1(k2_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)))) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
% 11.80/2.00      | v2_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top
% 11.80/2.00      | v1_relat_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_5306,c_1320]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_7087,plain,
% 11.80/2.00      ( k2_funct_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)))) = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))
% 11.80/2.00      | v2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top
% 11.80/2.00      | v1_relat_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 11.80/2.00      inference(light_normalisation,[status(thm)],[c_5315,c_6234]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_9727,plain,
% 11.80/2.00      ( k2_funct_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)))) = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))
% 11.80/2.00      | v2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))) != iProver_top
% 11.80/2.00      | v1_relat_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))) != iProver_top ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_9702,c_7087]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_20813,plain,
% 11.80/2.00      ( k2_struct_0(sK0) = k1_xboole_0
% 11.80/2.00      | k2_funct_1(k2_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)))) = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))
% 11.80/2.00      | v2_funct_1(k1_xboole_0) != iProver_top
% 11.80/2.00      | v1_relat_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_20768,c_9727]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_3085,plain,
% 11.80/2.00      ( k2_funct_1(X0) != k2_funct_1(sK2)
% 11.80/2.00      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 11.80/2.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 11.80/2.00      inference(predicate_to_equality,[status(thm)],[c_3084]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_3087,plain,
% 11.80/2.00      ( k2_funct_1(k1_xboole_0) != k2_funct_1(sK2)
% 11.80/2.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.80/2.00      | v1_funct_1(k2_funct_1(k1_xboole_0)) = iProver_top ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_3085]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_9713,plain,
% 11.80/2.00      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) != k1_xboole_0
% 11.80/2.00      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_9702,c_8391]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_20812,plain,
% 11.80/2.00      ( k2_struct_0(sK0) = k1_xboole_0
% 11.80/2.00      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_20768,c_9713]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_22151,plain,
% 11.80/2.00      ( k2_struct_0(sK0) = k1_xboole_0
% 11.80/2.00      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 11.80/2.00      | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
% 11.80/2.00      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_1306,c_20812]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_9726,plain,
% 11.80/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) = iProver_top ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_9702,c_6257]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_22152,plain,
% 11.80/2.00      ( k2_struct_0(sK0) = k1_xboole_0
% 11.80/2.00      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 11.80/2.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_20768,c_20812]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_22669,plain,
% 11.80/2.00      ( v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top
% 11.80/2.00      | k2_struct_0(sK0) = k1_xboole_0 ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_22151,c_9726,c_22152]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_22670,plain,
% 11.80/2.00      ( k2_struct_0(sK0) = k1_xboole_0
% 11.80/2.00      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 11.80/2.00      inference(renaming,[status(thm)],[c_22669]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_22673,plain,
% 11.80/2.00      ( k2_struct_0(sK0) = k1_xboole_0
% 11.80/2.00      | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) != iProver_top
% 11.80/2.00      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 11.80/2.00      inference(superposition,[status(thm)],[c_1305,c_22670]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_22690,plain,
% 11.80/2.00      ( k2_struct_0(sK0) = k1_xboole_0 ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_20813,c_43,c_44,c_45,c_35,c_46,c_444,c_826,c_1454,
% 11.80/2.00                 c_1685,c_2084,c_3087,c_3764,c_6241,c_6242,c_9596,c_9714,
% 11.80/2.00                 c_9722,c_22673]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_22734,plain,
% 11.80/2.00      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != k1_xboole_0
% 11.80/2.00      | v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_xboole_0,k1_xboole_0) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_22690,c_9713]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_118,plain,
% 11.80/2.00      ( v4_relat_1(X0,X1) = iProver_top
% 11.80/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 11.80/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_120,plain,
% 11.80/2.00      ( v4_relat_1(k1_xboole_0,k1_xboole_0) = iProver_top
% 11.80/2.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_118]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_20,plain,
% 11.80/2.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 11.80/2.00      | v1_partfun1(X0,k1_xboole_0)
% 11.80/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.80/2.00      | ~ v1_funct_1(X0) ),
% 11.80/2.00      inference(cnf_transformation,[],[f104]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_548,plain,
% 11.80/2.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 11.80/2.00      | ~ v4_relat_1(X2,X3)
% 11.80/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.80/2.00      | ~ v1_funct_1(X0)
% 11.80/2.00      | ~ v1_relat_1(X2)
% 11.80/2.00      | X0 != X2
% 11.80/2.00      | k1_relat_1(X2) = X3
% 11.80/2.00      | k1_xboole_0 != X3 ),
% 11.80/2.00      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_549,plain,
% 11.80/2.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 11.80/2.00      | ~ v4_relat_1(X0,k1_xboole_0)
% 11.80/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.80/2.00      | ~ v1_funct_1(X0)
% 11.80/2.00      | ~ v1_relat_1(X0)
% 11.80/2.00      | k1_relat_1(X0) = k1_xboole_0 ),
% 11.80/2.00      inference(unflattening,[status(thm)],[c_548]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_550,plain,
% 11.80/2.00      ( k1_relat_1(X0) = k1_xboole_0
% 11.80/2.00      | v1_funct_2(X0,k1_xboole_0,X1) != iProver_top
% 11.80/2.00      | v4_relat_1(X0,k1_xboole_0) != iProver_top
% 11.80/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 11.80/2.00      | v1_funct_1(X0) != iProver_top
% 11.80/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.80/2.00      inference(predicate_to_equality,[status(thm)],[c_549]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_552,plain,
% 11.80/2.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 11.80/2.00      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
% 11.80/2.00      | v4_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top
% 11.80/2.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 11.80/2.00      | v1_funct_1(k1_xboole_0) != iProver_top
% 11.80/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_550]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1434,plain,
% 11.80/2.00      ( v1_funct_1(X0) | ~ v1_funct_1(sK2) | X0 != sK2 ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_801]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1435,plain,
% 11.80/2.00      ( X0 != sK2
% 11.80/2.00      | v1_funct_1(X0) = iProver_top
% 11.80/2.00      | v1_funct_1(sK2) != iProver_top ),
% 11.80/2.00      inference(predicate_to_equality,[status(thm)],[c_1434]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1437,plain,
% 11.80/2.00      ( k1_xboole_0 != sK2
% 11.80/2.00      | v1_funct_1(sK2) != iProver_top
% 11.80/2.00      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_1435]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_2209,plain,
% 11.80/2.00      ( X0 != X1 | X0 = u1_struct_0(sK1) | u1_struct_0(sK1) != X1 ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_794]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_2210,plain,
% 11.80/2.00      ( u1_struct_0(sK1) != k1_xboole_0
% 11.80/2.00      | k1_xboole_0 = u1_struct_0(sK1)
% 11.80/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_2209]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_795,plain,
% 11.80/2.00      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 11.80/2.00      theory(equality) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_2906,plain,
% 11.80/2.00      ( v1_relat_1(X0) | ~ v1_relat_1(sK2) | X0 != sK2 ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_795]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_2909,plain,
% 11.80/2.00      ( X0 != sK2
% 11.80/2.00      | v1_relat_1(X0) = iProver_top
% 11.80/2.00      | v1_relat_1(sK2) != iProver_top ),
% 11.80/2.00      inference(predicate_to_equality,[status(thm)],[c_2906]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_2911,plain,
% 11.80/2.00      ( k1_xboole_0 != sK2
% 11.80/2.00      | v1_relat_1(sK2) != iProver_top
% 11.80/2.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_2909]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_3055,plain,
% 11.80/2.00      ( X0 != X1 | X0 = u1_struct_0(sK0) | u1_struct_0(sK0) != X1 ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_794]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_4047,plain,
% 11.80/2.00      ( X0 = u1_struct_0(sK0)
% 11.80/2.00      | X0 != k2_struct_0(sK0)
% 11.80/2.00      | u1_struct_0(sK0) != k2_struct_0(sK0) ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_3055]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_4048,plain,
% 11.80/2.00      ( u1_struct_0(sK0) != k2_struct_0(sK0)
% 11.80/2.00      | k1_xboole_0 = u1_struct_0(sK0)
% 11.80/2.00      | k1_xboole_0 != k2_struct_0(sK0) ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_4047]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_6213,plain,
% 11.80/2.00      ( X0 != X1 | X0 = k2_struct_0(sK0) | k2_struct_0(sK0) != X1 ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_794]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_6214,plain,
% 11.80/2.00      ( k2_struct_0(sK0) != k1_xboole_0
% 11.80/2.00      | k1_xboole_0 = k2_struct_0(sK0)
% 11.80/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_6213]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_1908,plain,
% 11.80/2.00      ( u1_struct_0(sK1) = k2_relat_1(sK2) ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_1816,c_444]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_6260,plain,
% 11.80/2.00      ( u1_struct_0(sK1) = k1_xboole_0 ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_6234,c_1908]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_13139,plain,
% 11.80/2.00      ( ~ v1_funct_2(k2_funct_1(X0),X1,X2)
% 11.80/2.00      | m1_subset_1(k2_tops_2(X1,X2,k2_funct_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.80/2.00      | ~ m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.80/2.00      | ~ v1_funct_1(k2_funct_1(X0)) ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_30]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_13140,plain,
% 11.80/2.00      ( v1_funct_2(k2_funct_1(X0),X1,X2) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_tops_2(X1,X2,k2_funct_1(X0)),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 11.80/2.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.80/2.00      | v1_funct_1(k2_funct_1(X0)) != iProver_top ),
% 11.80/2.00      inference(predicate_to_equality,[status(thm)],[c_13139]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_13142,plain,
% 11.80/2.00      ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) != iProver_top
% 11.80/2.00      | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 11.80/2.00      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 11.80/2.00      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_13140]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_805,plain,
% 11.80/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.80/2.00      | v1_funct_2(X3,X4,X5)
% 11.80/2.00      | X3 != X0
% 11.80/2.00      | X4 != X1
% 11.80/2.00      | X5 != X2 ),
% 11.80/2.00      theory(equality) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_13299,plain,
% 11.80/2.00      ( v1_funct_2(X0,X1,X2)
% 11.80/2.00      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 11.80/2.00      | X2 != u1_struct_0(sK1)
% 11.80/2.00      | X1 != u1_struct_0(sK0)
% 11.80/2.00      | X0 != sK2 ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_805]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_13300,plain,
% 11.80/2.00      ( X0 != u1_struct_0(sK1)
% 11.80/2.00      | X1 != u1_struct_0(sK0)
% 11.80/2.00      | X2 != sK2
% 11.80/2.00      | v1_funct_2(X2,X1,X0) = iProver_top
% 11.80/2.00      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 11.80/2.00      inference(predicate_to_equality,[status(thm)],[c_13299]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_13302,plain,
% 11.80/2.00      ( k1_xboole_0 != u1_struct_0(sK1)
% 11.80/2.00      | k1_xboole_0 != u1_struct_0(sK0)
% 11.80/2.00      | k1_xboole_0 != sK2
% 11.80/2.00      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 11.80/2.00      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.80/2.00      inference(instantiation,[status(thm)],[c_13300]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_22738,plain,
% 11.80/2.00      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_22690,c_9714]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_22740,plain,
% 11.80/2.00      ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_22690,c_9722]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_9724,plain,
% 11.80/2.00      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
% 11.80/2.00      | k2_struct_0(sK0) != k1_relat_1(k1_xboole_0) ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_9702,c_6237]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_22742,plain,
% 11.80/2.00      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_xboole_0
% 11.80/2.00      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_22690,c_9724]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_22744,plain,
% 11.80/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 11.80/2.00      inference(demodulation,[status(thm)],[c_22690,c_9726]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_24228,plain,
% 11.80/2.00      ( v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_22734,c_43,c_44,c_45,c_35,c_46,c_120,c_444,c_449,
% 11.80/2.00                 c_552,c_826,c_1437,c_1454,c_1685,c_2084,c_2114,c_2185,
% 11.80/2.00                 c_2210,c_2911,c_3087,c_3764,c_4048,c_6214,c_6241,c_6242,
% 11.80/2.00                 c_6260,c_9596,c_9714,c_9722,c_13142,c_13302,c_22673,
% 11.80/2.00                 c_22738,c_22740,c_22742,c_22744]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_23090,plain,
% 11.80/2.00      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 11.80/2.00      inference(global_propositional_subsumption,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_22742,c_43,c_44,c_45,c_35,c_46,c_120,c_444,c_449,
% 11.80/2.00                 c_552,c_826,c_1437,c_1454,c_1685,c_2084,c_2114,c_2185,
% 11.80/2.00                 c_2210,c_2911,c_3087,c_3764,c_4048,c_6214,c_6241,c_6242,
% 11.80/2.00                 c_6260,c_9596,c_9714,c_9722,c_13302,c_22673,c_22744]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(c_24232,plain,
% 11.80/2.00      ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.80/2.00      inference(light_normalisation,[status(thm)],[c_24228,c_23090]) ).
% 11.80/2.00  
% 11.80/2.00  cnf(contradiction,plain,
% 11.80/2.00      ( $false ),
% 11.80/2.00      inference(minisat,
% 11.80/2.00                [status(thm)],
% 11.80/2.00                [c_24232,c_22673,c_13302,c_9722,c_9714,c_9596,c_6260,
% 11.80/2.00                 c_6242,c_6241,c_6214,c_4048,c_3764,c_3087,c_2210,c_2084,
% 11.80/2.00                 c_1685,c_1454,c_826,c_449,c_444,c_46,c_35,c_45,c_44,
% 11.80/2.00                 c_43]) ).
% 11.80/2.00  
% 11.80/2.00  
% 11.80/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.80/2.00  
% 11.80/2.00  ------                               Statistics
% 11.80/2.00  
% 11.80/2.00  ------ General
% 11.80/2.00  
% 11.80/2.00  abstr_ref_over_cycles:                  0
% 11.80/2.00  abstr_ref_under_cycles:                 0
% 11.80/2.00  gc_basic_clause_elim:                   0
% 11.80/2.00  forced_gc_time:                         0
% 11.80/2.00  parsing_time:                           0.011
% 11.80/2.00  unif_index_cands_time:                  0.
% 11.80/2.00  unif_index_add_time:                    0.
% 11.80/2.00  orderings_time:                         0.
% 11.80/2.00  out_proof_time:                         0.041
% 11.80/2.00  total_time:                             1.188
% 11.80/2.00  num_of_symbols:                         54
% 11.80/2.00  num_of_terms:                           20610
% 11.80/2.00  
% 11.80/2.00  ------ Preprocessing
% 11.80/2.00  
% 11.80/2.00  num_of_splits:                          0
% 11.80/2.00  num_of_split_atoms:                     0
% 11.80/2.00  num_of_reused_defs:                     0
% 11.80/2.00  num_eq_ax_congr_red:                    8
% 11.80/2.00  num_of_sem_filtered_clauses:            1
% 11.80/2.00  num_of_subtypes:                        0
% 11.80/2.00  monotx_restored_types:                  0
% 11.80/2.00  sat_num_of_epr_types:                   0
% 11.80/2.00  sat_num_of_non_cyclic_types:            0
% 11.80/2.00  sat_guarded_non_collapsed_types:        0
% 11.80/2.00  num_pure_diseq_elim:                    0
% 11.80/2.00  simp_replaced_by:                       0
% 11.80/2.00  res_preprocessed:                       177
% 11.80/2.00  prep_upred:                             0
% 11.80/2.00  prep_unflattend:                        15
% 11.80/2.00  smt_new_axioms:                         0
% 11.80/2.00  pred_elim_cands:                        5
% 11.80/2.00  pred_elim:                              4
% 11.80/2.00  pred_elim_cl:                           6
% 11.80/2.00  pred_elim_cycles:                       7
% 11.80/2.00  merged_defs:                            0
% 11.80/2.00  merged_defs_ncl:                        0
% 11.80/2.00  bin_hyper_res:                          0
% 11.80/2.00  prep_cycles:                            4
% 11.80/2.00  pred_elim_time:                         0.006
% 11.80/2.00  splitting_time:                         0.
% 11.80/2.00  sem_filter_time:                        0.
% 11.80/2.00  monotx_time:                            0.001
% 11.80/2.00  subtype_inf_time:                       0.
% 11.80/2.00  
% 11.80/2.00  ------ Problem properties
% 11.80/2.00  
% 11.80/2.00  clauses:                                34
% 11.80/2.00  conjectures:                            5
% 11.80/2.00  epr:                                    2
% 11.80/2.00  horn:                                   29
% 11.80/2.00  ground:                                 8
% 11.80/2.00  unary:                                  8
% 11.80/2.00  binary:                                 1
% 11.80/2.00  lits:                                   115
% 11.80/2.00  lits_eq:                                25
% 11.80/2.00  fd_pure:                                0
% 11.80/2.00  fd_pseudo:                              0
% 11.80/2.00  fd_cond:                                3
% 11.80/2.00  fd_pseudo_cond:                         1
% 11.80/2.00  ac_symbols:                             0
% 11.80/2.00  
% 11.80/2.00  ------ Propositional Solver
% 11.80/2.00  
% 11.80/2.00  prop_solver_calls:                      35
% 11.80/2.00  prop_fast_solver_calls:                 2623
% 11.80/2.00  smt_solver_calls:                       0
% 11.80/2.00  smt_fast_solver_calls:                  0
% 11.80/2.00  prop_num_of_clauses:                    10076
% 11.80/2.00  prop_preprocess_simplified:             22409
% 11.80/2.00  prop_fo_subsumed:                       264
% 11.80/2.00  prop_solver_time:                       0.
% 11.80/2.00  smt_solver_time:                        0.
% 11.80/2.00  smt_fast_solver_time:                   0.
% 11.80/2.00  prop_fast_solver_time:                  0.
% 11.80/2.00  prop_unsat_core_time:                   0.002
% 11.80/2.00  
% 11.80/2.00  ------ QBF
% 11.80/2.00  
% 11.80/2.00  qbf_q_res:                              0
% 11.80/2.00  qbf_num_tautologies:                    0
% 11.80/2.00  qbf_prep_cycles:                        0
% 11.80/2.00  
% 11.80/2.00  ------ BMC1
% 11.80/2.00  
% 11.80/2.00  bmc1_current_bound:                     -1
% 11.80/2.00  bmc1_last_solved_bound:                 -1
% 11.80/2.00  bmc1_unsat_core_size:                   -1
% 11.80/2.00  bmc1_unsat_core_parents_size:           -1
% 11.80/2.00  bmc1_merge_next_fun:                    0
% 11.80/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.80/2.00  
% 11.80/2.00  ------ Instantiation
% 11.80/2.00  
% 11.80/2.00  inst_num_of_clauses:                    3258
% 11.80/2.00  inst_num_in_passive:                    1828
% 11.80/2.00  inst_num_in_active:                     1139
% 11.80/2.00  inst_num_in_unprocessed:                291
% 11.80/2.00  inst_num_of_loops:                      1460
% 11.80/2.00  inst_num_of_learning_restarts:          0
% 11.80/2.00  inst_num_moves_active_passive:          315
% 11.80/2.00  inst_lit_activity:                      0
% 11.80/2.00  inst_lit_activity_moves:                0
% 11.80/2.00  inst_num_tautologies:                   0
% 11.80/2.00  inst_num_prop_implied:                  0
% 11.80/2.00  inst_num_existing_simplified:           0
% 11.80/2.00  inst_num_eq_res_simplified:             0
% 11.80/2.00  inst_num_child_elim:                    0
% 11.80/2.00  inst_num_of_dismatching_blockings:      1809
% 11.80/2.00  inst_num_of_non_proper_insts:           2579
% 11.80/2.00  inst_num_of_duplicates:                 0
% 11.80/2.00  inst_inst_num_from_inst_to_res:         0
% 11.80/2.00  inst_dismatching_checking_time:         0.
% 11.80/2.00  
% 11.80/2.00  ------ Resolution
% 11.80/2.00  
% 11.80/2.00  res_num_of_clauses:                     0
% 11.80/2.00  res_num_in_passive:                     0
% 11.80/2.00  res_num_in_active:                      0
% 11.80/2.00  res_num_of_loops:                       181
% 11.80/2.00  res_forward_subset_subsumed:            158
% 11.80/2.00  res_backward_subset_subsumed:           0
% 11.80/2.00  res_forward_subsumed:                   0
% 11.80/2.00  res_backward_subsumed:                  0
% 11.80/2.00  res_forward_subsumption_resolution:     1
% 11.80/2.00  res_backward_subsumption_resolution:    0
% 11.80/2.00  res_clause_to_clause_subsumption:       2860
% 11.80/2.00  res_orphan_elimination:                 0
% 11.80/2.00  res_tautology_del:                      154
% 11.80/2.00  res_num_eq_res_simplified:              0
% 11.80/2.00  res_num_sel_changes:                    0
% 11.80/2.00  res_moves_from_active_to_pass:          0
% 11.80/2.00  
% 11.80/2.00  ------ Superposition
% 11.80/2.00  
% 11.80/2.00  sup_time_total:                         0.
% 11.80/2.00  sup_time_generating:                    0.
% 11.80/2.00  sup_time_sim_full:                      0.
% 11.80/2.00  sup_time_sim_immed:                     0.
% 11.80/2.00  
% 11.80/2.00  sup_num_of_clauses:                     315
% 11.80/2.00  sup_num_in_active:                      116
% 11.80/2.00  sup_num_in_passive:                     199
% 11.80/2.00  sup_num_of_loops:                       291
% 11.80/2.00  sup_fw_superposition:                   426
% 11.80/2.00  sup_bw_superposition:                   532
% 11.80/2.00  sup_immediate_simplified:               475
% 11.80/2.00  sup_given_eliminated:                   7
% 11.80/2.00  comparisons_done:                       0
% 11.80/2.00  comparisons_avoided:                    64
% 11.80/2.00  
% 11.80/2.00  ------ Simplifications
% 11.80/2.00  
% 11.80/2.00  
% 11.80/2.00  sim_fw_subset_subsumed:                 166
% 11.80/2.00  sim_bw_subset_subsumed:                 99
% 11.80/2.00  sim_fw_subsumed:                        71
% 11.80/2.00  sim_bw_subsumed:                        12
% 11.80/2.00  sim_fw_subsumption_res:                 0
% 11.80/2.00  sim_bw_subsumption_res:                 0
% 11.80/2.00  sim_tautology_del:                      9
% 11.80/2.00  sim_eq_tautology_del:                   265
% 11.80/2.00  sim_eq_res_simp:                        2
% 11.80/2.00  sim_fw_demodulated:                     1
% 11.80/2.00  sim_bw_demodulated:                     146
% 11.80/2.00  sim_light_normalised:                   340
% 11.80/2.00  sim_joinable_taut:                      0
% 11.80/2.00  sim_joinable_simp:                      0
% 11.80/2.00  sim_ac_normalised:                      0
% 11.80/2.00  sim_smt_subsumption:                    0
% 11.80/2.00  
%------------------------------------------------------------------------------
