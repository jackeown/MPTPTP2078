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
% DateTime   : Thu Dec  3 12:17:25 EST 2020

% Result     : Theorem 6.84s
% Output     : CNFRefutation 6.84s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_7242)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
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
    inference(pure_predicate_removal,[],[f17])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f18])).

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
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK3)),sK3)
        & v2_funct_1(sK3)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3) = k2_struct_0(X1)
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
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
          & l1_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK2),X2)),X2)
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2) = k2_struct_0(sK2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X2) )
        & l1_struct_0(sK2) ) ) ),
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
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3)
    & v2_funct_1(sK3)
    & k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_struct_0(sK2)
    & l1_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f46,f52,f51,f50])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f80,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f86,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f90,plain,(
    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f88,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f53])).

fof(f11,axiom,(
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

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f87,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f91,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f60,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f61,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f58,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f55,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f92,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f95,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f97,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1275,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1276,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1272,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_26,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_37,negated_conjecture,
    ( l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_435,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_37])).

cnf(c_436,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_38,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_440,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_38])).

cnf(c_441,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_1320,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1272,c_436,c_441])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1291,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2219,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1320,c_1291])).

cnf(c_33,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1317,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_33,c_436,c_441])).

cnf(c_2660,plain,
    ( k2_struct_0(sK2) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_2219,c_1317])).

cnf(c_2684,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2660,c_1320])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1285,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4425,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_struct_0(sK1)
    | k2_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2684,c_1285])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1292,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2385,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1320,c_1292])).

cnf(c_2845,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_2385,c_2660])).

cnf(c_4429,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4425,c_2845])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1271,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1312,plain,
    ( v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1271,c_436,c_441])).

cnf(c_2685,plain,
    ( v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2660,c_1312])).

cnf(c_4599,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | k2_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4429,c_2685])).

cnf(c_4600,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4599])).

cnf(c_2681,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_2660,c_2219])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1280,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5594,plain,
    ( v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2681,c_1280])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_41,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_32,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_44,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5989,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5594,c_41,c_44,c_2684,c_2685])).

cnf(c_6000,plain,
    ( k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = k2_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[status(thm)],[c_5989,c_1291])).

cnf(c_1273,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1296,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4250,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1273,c_1296])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1597,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1633,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4560,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4250,c_36,c_34,c_32,c_1597,c_1633])).

cnf(c_6002,plain,
    ( k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_6000,c_4560])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1277,plain,
    ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6167,plain,
    ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = k2_funct_1(k2_funct_1(sK3))
    | k2_struct_0(sK1) != k1_relat_1(sK3)
    | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6002,c_1277])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1294,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3209,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1273,c_1294])).

cnf(c_1642,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3372,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3209,c_36,c_34,c_32,c_1597,c_1642])).

cnf(c_6174,plain,
    ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = sK3
    | k2_struct_0(sK1) != k1_relat_1(sK3)
    | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6167,c_3372])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1594,plain,
    ( v2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1595,plain,
    ( v2_funct_1(k2_funct_1(sK3)) = iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1594])).

cnf(c_1598,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1597])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_229,plain,
    ( v1_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_8,c_0])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(renaming,[status(thm)],[c_229])).

cnf(c_1269,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_230])).

cnf(c_1758,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1320,c_1269])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1279,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5545,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2681,c_1279])).

cnf(c_6272,plain,
    ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = sK3
    | k2_struct_0(sK1) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6174,c_41,c_43,c_44,c_1595,c_1598,c_1758,c_2684,c_2685,c_5545,c_5594])).

cnf(c_6276,plain,
    ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = sK3
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4600,c_6272])).

cnf(c_5360,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3)
    | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2681,c_1277])).

cnf(c_5828,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5360,c_41,c_44,c_2684,c_2685])).

cnf(c_21,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_31,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_447,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != X0
    | u1_struct_0(sK2) != X2
    | u1_struct_0(sK1) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_448,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)))
    | sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_696,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)))
    | sP0_iProver_split
    | sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_448])).

cnf(c_1267,plain,
    ( sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_696])).

cnf(c_1506,plain,
    ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != sK3
    | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1267,c_436,c_441])).

cnf(c_695,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(X0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_448])).

cnf(c_1268,plain,
    ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_695])).

cnf(c_1445,plain,
    ( v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1268,c_436,c_441])).

cnf(c_1512,plain,
    ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != sK3
    | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1506,c_1445])).

cnf(c_2682,plain,
    ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) != sK3
    | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2660,c_1512])).

cnf(c_5832,plain,
    ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) != sK3
    | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5828,c_2682])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1274,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_tops_2(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5995,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5989,c_1274])).

cnf(c_6278,plain,
    ( m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
    | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5832,c_41,c_44,c_1758,c_2684,c_2685,c_5545,c_5995])).

cnf(c_6279,plain,
    ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) != sK3
    | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6278])).

cnf(c_6442,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6276,c_6279])).

cnf(c_7243,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6276,c_6442])).

cnf(c_7272,plain,
    ( v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7243,c_41,c_44,c_1758,c_2684,c_2685,c_5545,c_5594,c_7242])).

cnf(c_7273,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7272])).

cnf(c_7279,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6276,c_7273])).

cnf(c_7278,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1275,c_7273])).

cnf(c_7682,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7279,c_41,c_44,c_1758,c_2684,c_2685,c_5545,c_5594,c_7278])).

cnf(c_7693,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7682,c_5989])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1289,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4279,plain,
    ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | v1_funct_2(k2_tops_2(k1_xboole_0,X0,X1),X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1276,c_1289])).

cnf(c_12744,plain,
    ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4279,c_1275])).

cnf(c_12750,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) = k1_xboole_0
    | k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK3),k1_xboole_0,k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7693,c_12744])).

cnf(c_5981,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5545,c_41,c_44,c_2684,c_2685])).

cnf(c_7694,plain,
    ( v1_funct_2(k2_funct_1(sK3),k1_xboole_0,k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7682,c_5981])).

cnf(c_21007,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) = k1_xboole_0
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12750,c_41,c_1758,c_7694])).

cnf(c_7699,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7682,c_2684])).

cnf(c_9478,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,k2_struct_0(sK1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7699,c_1289])).

cnf(c_7702,plain,
    ( v1_funct_2(sK3,k2_struct_0(sK1),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7682,c_2685])).

cnf(c_10216,plain,
    ( sK3 = k1_xboole_0
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9478,c_7702])).

cnf(c_10217,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_10216])).

cnf(c_7690,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) = sK3
    | k2_struct_0(sK1) != k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_7682,c_6272])).

cnf(c_10224,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) = sK3
    | k1_relat_1(sK3) != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10217,c_7690])).

cnf(c_10225,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10217,c_7699])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1286,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_11388,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10225,c_1286])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1719,plain,
    ( ~ v1_funct_2(sK3,X0,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK3)
    | k1_relset_1(X0,X0,sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1720,plain,
    ( k1_relset_1(X0,X0,sK3) = X0
    | v1_funct_2(sK3,X0,X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1719])).

cnf(c_1722,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1720])).

cnf(c_10229,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10217,c_7702])).

cnf(c_11769,plain,
    ( sK3 = k1_xboole_0
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11388,c_41,c_1722,c_10225,c_10229])).

cnf(c_11770,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_11769])).

cnf(c_7701,plain,
    ( k1_relset_1(k2_struct_0(sK1),k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_7682,c_2845])).

cnf(c_10227,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10217,c_7701])).

cnf(c_11776,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11770,c_10227])).

cnf(c_12596,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) = sK3
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10224,c_11776])).

cnf(c_7689,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) != sK3
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7682,c_6279])).

cnf(c_12605,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12596,c_7689])).

cnf(c_12943,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12596,c_12605])).

cnf(c_13283,plain,
    ( v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12943,c_7699])).

cnf(c_13284,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13283])).

cnf(c_13290,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK3,k2_struct_0(sK1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12596,c_13284])).

cnf(c_13289,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK3),k1_xboole_0,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1275,c_13284])).

cnf(c_13315,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13290,c_41,c_1758,c_7693,c_7694,c_13289])).

cnf(c_21009,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_21007,c_13315])).

cnf(c_13328,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)) != k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13315,c_7689])).

cnf(c_21016,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_21009,c_13328])).

cnf(c_23649,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
    | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1276,c_21016])).

cnf(c_13333,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13315,c_7699])).

cnf(c_23650,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_21009,c_21016])).

cnf(c_23881,plain,
    ( v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23649,c_13333,c_23650])).

cnf(c_23882,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)),k2_struct_0(sK1),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_23881])).

cnf(c_23887,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1275,c_23882])).

cnf(c_136,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_138,plain,
    ( v1_relat_1(k1_xboole_0) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_698,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_731,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_701,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1606,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_701])).

cnf(c_1607,plain,
    ( X0 != sK3
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1606])).

cnf(c_1609,plain,
    ( k1_xboole_0 != sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1607])).

cnf(c_702,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1811,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_702])).

cnf(c_1818,plain,
    ( X0 != sK3
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1811])).

cnf(c_1820,plain,
    ( k1_xboole_0 != sK3
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1818])).

cnf(c_699,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1835,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_1836,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1835])).

cnf(c_13329,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13315,c_7693])).

cnf(c_13331,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13315,c_7694])).

cnf(c_23906,plain,
    ( k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23887,c_41,c_43,c_138,c_731,c_1598,c_1609,c_1758,c_1820,c_1836,c_7693,c_7694,c_13289,c_13329,c_13331])).

cnf(c_23913,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_23906,c_13328])).

cnf(c_42,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2811,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_2816,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK2)
    | u1_struct_0(sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_2817,plain,
    ( u1_struct_0(sK2) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2816])).

cnf(c_711,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1749,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | X2 != u1_struct_0(sK2)
    | X1 != u1_struct_0(sK1)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_1949,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1(sK3)),X0,X1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | X1 != u1_struct_0(sK2)
    | X0 != u1_struct_0(sK1)
    | k2_funct_1(k2_funct_1(sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_1749])).

cnf(c_2810,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1(sK3)),X0,u1_struct_0(sK2))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | X0 != u1_struct_0(sK1)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | k2_funct_1(k2_funct_1(sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_1949])).

cnf(c_4784,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1(sK3)),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_funct_1(k2_funct_1(sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_2810])).

cnf(c_4786,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | k2_funct_1(k2_funct_1(sK3)) != sK3
    | v1_funct_2(k2_funct_1(k2_funct_1(sK3)),u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4784])).

cnf(c_4785,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_3161,plain,
    ( X0 != X1
    | X0 = k2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(k2_funct_1(sK3)) != X1 ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_6705,plain,
    ( X0 = k2_funct_1(k2_funct_1(sK3))
    | X0 != sK3
    | k2_funct_1(k2_funct_1(sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_3161])).

cnf(c_6706,plain,
    ( k2_funct_1(k2_funct_1(sK3)) != sK3
    | k1_xboole_0 = k2_funct_1(k2_funct_1(sK3))
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_6705])).

cnf(c_2686,plain,
    ( u1_struct_0(sK2) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_2660,c_436])).

cnf(c_7703,plain,
    ( u1_struct_0(sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7682,c_2686])).

cnf(c_8795,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(k2_funct_1(k2_funct_1(sK3)),u1_struct_0(sK1),u1_struct_0(sK2))
    | X2 != u1_struct_0(sK2)
    | X1 != u1_struct_0(sK1)
    | X0 != k2_funct_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_8796,plain,
    ( X0 != u1_struct_0(sK2)
    | X1 != u1_struct_0(sK1)
    | X2 != k2_funct_1(k2_funct_1(sK3))
    | v1_funct_2(X2,X1,X0) = iProver_top
    | v1_funct_2(k2_funct_1(k2_funct_1(sK3)),u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8795])).

cnf(c_8798,plain,
    ( k1_xboole_0 != u1_struct_0(sK2)
    | k1_xboole_0 != u1_struct_0(sK1)
    | k1_xboole_0 != k2_funct_1(k2_funct_1(sK3))
    | v1_funct_2(k2_funct_1(k2_funct_1(sK3)),u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8796])).

cnf(c_4788,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_12520,plain,
    ( X0 = u1_struct_0(sK1)
    | X0 != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4788])).

cnf(c_12521,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k1_xboole_0 = u1_struct_0(sK1)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_12520])).

cnf(c_23562,plain,
    ( X0 != X1
    | X0 = k2_struct_0(sK1)
    | k2_struct_0(sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_23563,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 = k2_struct_0(sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_23562])).

cnf(c_13332,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | k2_struct_0(sK1) != k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_13315,c_7690])).

cnf(c_23919,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_23906,c_13332])).

cnf(c_23921,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_23906,c_13333])).

cnf(c_24858,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_23921,c_1286])).

cnf(c_13335,plain,
    ( k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_13315,c_7701])).

cnf(c_23923,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_23906,c_13335])).

cnf(c_24876,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24858,c_23923])).

cnf(c_25963,plain,
    ( v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23913,c_36,c_41,c_42,c_34,c_43,c_32,c_138,c_441,c_731,c_1597,c_1598,c_1609,c_1642,c_1758,c_1820,c_1836,c_2811,c_2817,c_4786,c_4785,c_6706,c_7693,c_7694,c_7703,c_8798,c_12521,c_13289,c_13329,c_13331,c_23563,c_23887,c_23919,c_24876])).

cnf(c_24923,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23919,c_36,c_41,c_42,c_34,c_43,c_32,c_138,c_441,c_731,c_1597,c_1598,c_1609,c_1642,c_1758,c_1820,c_1836,c_2811,c_2817,c_4786,c_4785,c_6706,c_7693,c_7694,c_7703,c_8798,c_12521,c_13289,c_13329,c_13331,c_23563,c_23887,c_24876])).

cnf(c_25967,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_25963,c_24923])).

cnf(c_13337,plain,
    ( v1_funct_2(k1_xboole_0,k2_struct_0(sK1),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13315,c_7702])).

cnf(c_23925,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_23906,c_13337])).

cnf(c_25970,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_25967,c_23921,c_23925])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:22:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 6.84/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.84/1.49  
% 6.84/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.84/1.49  
% 6.84/1.49  ------  iProver source info
% 6.84/1.49  
% 6.84/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.84/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.84/1.49  git: non_committed_changes: false
% 6.84/1.49  git: last_make_outside_of_git: false
% 6.84/1.49  
% 6.84/1.49  ------ 
% 6.84/1.49  
% 6.84/1.49  ------ Input Options
% 6.84/1.49  
% 6.84/1.49  --out_options                           all
% 6.84/1.49  --tptp_safe_out                         true
% 6.84/1.49  --problem_path                          ""
% 6.84/1.49  --include_path                          ""
% 6.84/1.49  --clausifier                            res/vclausify_rel
% 6.84/1.49  --clausifier_options                    --mode clausify
% 6.84/1.49  --stdin                                 false
% 6.84/1.49  --stats_out                             all
% 6.84/1.49  
% 6.84/1.49  ------ General Options
% 6.84/1.49  
% 6.84/1.49  --fof                                   false
% 6.84/1.49  --time_out_real                         305.
% 6.84/1.49  --time_out_virtual                      -1.
% 6.84/1.49  --symbol_type_check                     false
% 6.84/1.49  --clausify_out                          false
% 6.84/1.49  --sig_cnt_out                           false
% 6.84/1.49  --trig_cnt_out                          false
% 6.84/1.49  --trig_cnt_out_tolerance                1.
% 6.84/1.49  --trig_cnt_out_sk_spl                   false
% 6.84/1.49  --abstr_cl_out                          false
% 6.84/1.49  
% 6.84/1.49  ------ Global Options
% 6.84/1.49  
% 6.84/1.49  --schedule                              default
% 6.84/1.49  --add_important_lit                     false
% 6.84/1.49  --prop_solver_per_cl                    1000
% 6.84/1.49  --min_unsat_core                        false
% 6.84/1.49  --soft_assumptions                      false
% 6.84/1.49  --soft_lemma_size                       3
% 6.84/1.49  --prop_impl_unit_size                   0
% 6.84/1.49  --prop_impl_unit                        []
% 6.84/1.49  --share_sel_clauses                     true
% 6.84/1.49  --reset_solvers                         false
% 6.84/1.49  --bc_imp_inh                            [conj_cone]
% 6.84/1.49  --conj_cone_tolerance                   3.
% 6.84/1.49  --extra_neg_conj                        none
% 6.84/1.49  --large_theory_mode                     true
% 6.84/1.49  --prolific_symb_bound                   200
% 6.84/1.49  --lt_threshold                          2000
% 6.84/1.49  --clause_weak_htbl                      true
% 6.84/1.49  --gc_record_bc_elim                     false
% 6.84/1.49  
% 6.84/1.49  ------ Preprocessing Options
% 6.84/1.49  
% 6.84/1.49  --preprocessing_flag                    true
% 6.84/1.49  --time_out_prep_mult                    0.1
% 6.84/1.49  --splitting_mode                        input
% 6.84/1.49  --splitting_grd                         true
% 6.84/1.49  --splitting_cvd                         false
% 6.84/1.49  --splitting_cvd_svl                     false
% 6.84/1.49  --splitting_nvd                         32
% 6.84/1.49  --sub_typing                            true
% 6.84/1.49  --prep_gs_sim                           true
% 6.84/1.49  --prep_unflatten                        true
% 6.84/1.49  --prep_res_sim                          true
% 6.84/1.49  --prep_upred                            true
% 6.84/1.49  --prep_sem_filter                       exhaustive
% 6.84/1.49  --prep_sem_filter_out                   false
% 6.84/1.49  --pred_elim                             true
% 6.84/1.49  --res_sim_input                         true
% 6.84/1.49  --eq_ax_congr_red                       true
% 6.84/1.49  --pure_diseq_elim                       true
% 6.84/1.49  --brand_transform                       false
% 6.84/1.49  --non_eq_to_eq                          false
% 6.84/1.49  --prep_def_merge                        true
% 6.84/1.49  --prep_def_merge_prop_impl              false
% 6.84/1.49  --prep_def_merge_mbd                    true
% 6.84/1.49  --prep_def_merge_tr_red                 false
% 6.84/1.49  --prep_def_merge_tr_cl                  false
% 6.84/1.49  --smt_preprocessing                     true
% 6.84/1.49  --smt_ac_axioms                         fast
% 6.84/1.49  --preprocessed_out                      false
% 6.84/1.49  --preprocessed_stats                    false
% 6.84/1.49  
% 6.84/1.49  ------ Abstraction refinement Options
% 6.84/1.49  
% 6.84/1.49  --abstr_ref                             []
% 6.84/1.49  --abstr_ref_prep                        false
% 6.84/1.49  --abstr_ref_until_sat                   false
% 6.84/1.49  --abstr_ref_sig_restrict                funpre
% 6.84/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.84/1.49  --abstr_ref_under                       []
% 6.84/1.49  
% 6.84/1.49  ------ SAT Options
% 6.84/1.49  
% 6.84/1.49  --sat_mode                              false
% 6.84/1.49  --sat_fm_restart_options                ""
% 6.84/1.49  --sat_gr_def                            false
% 6.84/1.49  --sat_epr_types                         true
% 6.84/1.49  --sat_non_cyclic_types                  false
% 6.84/1.49  --sat_finite_models                     false
% 6.84/1.49  --sat_fm_lemmas                         false
% 6.84/1.49  --sat_fm_prep                           false
% 6.84/1.49  --sat_fm_uc_incr                        true
% 6.84/1.49  --sat_out_model                         small
% 6.84/1.49  --sat_out_clauses                       false
% 6.84/1.49  
% 6.84/1.49  ------ QBF Options
% 6.84/1.49  
% 6.84/1.49  --qbf_mode                              false
% 6.84/1.49  --qbf_elim_univ                         false
% 6.84/1.49  --qbf_dom_inst                          none
% 6.84/1.49  --qbf_dom_pre_inst                      false
% 6.84/1.49  --qbf_sk_in                             false
% 6.84/1.49  --qbf_pred_elim                         true
% 6.84/1.49  --qbf_split                             512
% 6.84/1.49  
% 6.84/1.49  ------ BMC1 Options
% 6.84/1.49  
% 6.84/1.49  --bmc1_incremental                      false
% 6.84/1.49  --bmc1_axioms                           reachable_all
% 6.84/1.49  --bmc1_min_bound                        0
% 6.84/1.49  --bmc1_max_bound                        -1
% 6.84/1.49  --bmc1_max_bound_default                -1
% 6.84/1.49  --bmc1_symbol_reachability              true
% 6.84/1.49  --bmc1_property_lemmas                  false
% 6.84/1.49  --bmc1_k_induction                      false
% 6.84/1.49  --bmc1_non_equiv_states                 false
% 6.84/1.49  --bmc1_deadlock                         false
% 6.84/1.49  --bmc1_ucm                              false
% 6.84/1.49  --bmc1_add_unsat_core                   none
% 6.84/1.49  --bmc1_unsat_core_children              false
% 6.84/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.84/1.49  --bmc1_out_stat                         full
% 6.84/1.49  --bmc1_ground_init                      false
% 6.84/1.49  --bmc1_pre_inst_next_state              false
% 6.84/1.49  --bmc1_pre_inst_state                   false
% 6.84/1.49  --bmc1_pre_inst_reach_state             false
% 6.84/1.49  --bmc1_out_unsat_core                   false
% 6.84/1.49  --bmc1_aig_witness_out                  false
% 6.84/1.49  --bmc1_verbose                          false
% 6.84/1.49  --bmc1_dump_clauses_tptp                false
% 6.84/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.84/1.49  --bmc1_dump_file                        -
% 6.84/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.84/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.84/1.49  --bmc1_ucm_extend_mode                  1
% 6.84/1.49  --bmc1_ucm_init_mode                    2
% 6.84/1.49  --bmc1_ucm_cone_mode                    none
% 6.84/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.84/1.49  --bmc1_ucm_relax_model                  4
% 6.84/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.84/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.84/1.49  --bmc1_ucm_layered_model                none
% 6.84/1.49  --bmc1_ucm_max_lemma_size               10
% 6.84/1.49  
% 6.84/1.49  ------ AIG Options
% 6.84/1.49  
% 6.84/1.49  --aig_mode                              false
% 6.84/1.49  
% 6.84/1.49  ------ Instantiation Options
% 6.84/1.49  
% 6.84/1.49  --instantiation_flag                    true
% 6.84/1.49  --inst_sos_flag                         false
% 6.84/1.49  --inst_sos_phase                        true
% 6.84/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.84/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.84/1.49  --inst_lit_sel_side                     num_symb
% 6.84/1.49  --inst_solver_per_active                1400
% 6.84/1.49  --inst_solver_calls_frac                1.
% 6.84/1.49  --inst_passive_queue_type               priority_queues
% 6.84/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.84/1.49  --inst_passive_queues_freq              [25;2]
% 6.84/1.49  --inst_dismatching                      true
% 6.84/1.49  --inst_eager_unprocessed_to_passive     true
% 6.84/1.49  --inst_prop_sim_given                   true
% 6.84/1.49  --inst_prop_sim_new                     false
% 6.84/1.49  --inst_subs_new                         false
% 6.84/1.49  --inst_eq_res_simp                      false
% 6.84/1.49  --inst_subs_given                       false
% 6.84/1.49  --inst_orphan_elimination               true
% 6.84/1.49  --inst_learning_loop_flag               true
% 6.84/1.49  --inst_learning_start                   3000
% 6.84/1.49  --inst_learning_factor                  2
% 6.84/1.49  --inst_start_prop_sim_after_learn       3
% 6.84/1.49  --inst_sel_renew                        solver
% 6.84/1.49  --inst_lit_activity_flag                true
% 6.84/1.49  --inst_restr_to_given                   false
% 6.84/1.49  --inst_activity_threshold               500
% 6.84/1.49  --inst_out_proof                        true
% 6.84/1.49  
% 6.84/1.49  ------ Resolution Options
% 6.84/1.49  
% 6.84/1.49  --resolution_flag                       true
% 6.84/1.49  --res_lit_sel                           adaptive
% 6.84/1.49  --res_lit_sel_side                      none
% 6.84/1.49  --res_ordering                          kbo
% 6.84/1.49  --res_to_prop_solver                    active
% 6.84/1.49  --res_prop_simpl_new                    false
% 6.84/1.49  --res_prop_simpl_given                  true
% 6.84/1.49  --res_passive_queue_type                priority_queues
% 6.84/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.84/1.49  --res_passive_queues_freq               [15;5]
% 6.84/1.49  --res_forward_subs                      full
% 6.84/1.49  --res_backward_subs                     full
% 6.84/1.49  --res_forward_subs_resolution           true
% 6.84/1.49  --res_backward_subs_resolution          true
% 6.84/1.49  --res_orphan_elimination                true
% 6.84/1.49  --res_time_limit                        2.
% 6.84/1.49  --res_out_proof                         true
% 6.84/1.49  
% 6.84/1.49  ------ Superposition Options
% 6.84/1.49  
% 6.84/1.49  --superposition_flag                    true
% 6.84/1.49  --sup_passive_queue_type                priority_queues
% 6.84/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.84/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.84/1.49  --demod_completeness_check              fast
% 6.84/1.49  --demod_use_ground                      true
% 6.84/1.49  --sup_to_prop_solver                    passive
% 6.84/1.49  --sup_prop_simpl_new                    true
% 6.84/1.49  --sup_prop_simpl_given                  true
% 6.84/1.49  --sup_fun_splitting                     false
% 6.84/1.49  --sup_smt_interval                      50000
% 6.84/1.49  
% 6.84/1.49  ------ Superposition Simplification Setup
% 6.84/1.49  
% 6.84/1.49  --sup_indices_passive                   []
% 6.84/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.84/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.84/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.84/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.84/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.84/1.49  --sup_full_bw                           [BwDemod]
% 6.84/1.49  --sup_immed_triv                        [TrivRules]
% 6.84/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.84/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.84/1.49  --sup_immed_bw_main                     []
% 6.84/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.84/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.84/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.84/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.84/1.49  
% 6.84/1.49  ------ Combination Options
% 6.84/1.49  
% 6.84/1.49  --comb_res_mult                         3
% 6.84/1.49  --comb_sup_mult                         2
% 6.84/1.49  --comb_inst_mult                        10
% 6.84/1.49  
% 6.84/1.49  ------ Debug Options
% 6.84/1.49  
% 6.84/1.49  --dbg_backtrace                         false
% 6.84/1.49  --dbg_dump_prop_clauses                 false
% 6.84/1.49  --dbg_dump_prop_clauses_file            -
% 6.84/1.49  --dbg_out_stat                          false
% 6.84/1.49  ------ Parsing...
% 6.84/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.84/1.49  
% 6.84/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 6.84/1.49  
% 6.84/1.49  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.84/1.49  
% 6.84/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.84/1.49  ------ Proving...
% 6.84/1.49  ------ Problem Properties 
% 6.84/1.49  
% 6.84/1.49  
% 6.84/1.49  clauses                                 36
% 6.84/1.49  conjectures                             5
% 6.84/1.49  EPR                                     2
% 6.84/1.49  Horn                                    32
% 6.84/1.49  unary                                   11
% 6.84/1.49  binary                                  3
% 6.84/1.49  lits                                    106
% 6.84/1.49  lits eq                                 23
% 6.84/1.49  fd_pure                                 0
% 6.84/1.49  fd_pseudo                               0
% 6.84/1.49  fd_cond                                 3
% 6.84/1.49  fd_pseudo_cond                          0
% 6.84/1.49  AC symbols                              0
% 6.84/1.49  
% 6.84/1.49  ------ Schedule dynamic 5 is on 
% 6.84/1.49  
% 6.84/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.84/1.49  
% 6.84/1.49  
% 6.84/1.49  ------ 
% 6.84/1.49  Current options:
% 6.84/1.49  ------ 
% 6.84/1.49  
% 6.84/1.49  ------ Input Options
% 6.84/1.49  
% 6.84/1.49  --out_options                           all
% 6.84/1.49  --tptp_safe_out                         true
% 6.84/1.49  --problem_path                          ""
% 6.84/1.49  --include_path                          ""
% 6.84/1.49  --clausifier                            res/vclausify_rel
% 6.84/1.49  --clausifier_options                    --mode clausify
% 6.84/1.49  --stdin                                 false
% 6.84/1.49  --stats_out                             all
% 6.84/1.49  
% 6.84/1.49  ------ General Options
% 6.84/1.49  
% 6.84/1.49  --fof                                   false
% 6.84/1.49  --time_out_real                         305.
% 6.84/1.49  --time_out_virtual                      -1.
% 6.84/1.49  --symbol_type_check                     false
% 6.84/1.49  --clausify_out                          false
% 6.84/1.49  --sig_cnt_out                           false
% 6.84/1.49  --trig_cnt_out                          false
% 6.84/1.49  --trig_cnt_out_tolerance                1.
% 6.84/1.49  --trig_cnt_out_sk_spl                   false
% 6.84/1.49  --abstr_cl_out                          false
% 6.84/1.49  
% 6.84/1.49  ------ Global Options
% 6.84/1.49  
% 6.84/1.49  --schedule                              default
% 6.84/1.49  --add_important_lit                     false
% 6.84/1.49  --prop_solver_per_cl                    1000
% 6.84/1.49  --min_unsat_core                        false
% 6.84/1.49  --soft_assumptions                      false
% 6.84/1.49  --soft_lemma_size                       3
% 6.84/1.49  --prop_impl_unit_size                   0
% 6.84/1.49  --prop_impl_unit                        []
% 6.84/1.49  --share_sel_clauses                     true
% 6.84/1.49  --reset_solvers                         false
% 6.84/1.49  --bc_imp_inh                            [conj_cone]
% 6.84/1.49  --conj_cone_tolerance                   3.
% 6.84/1.49  --extra_neg_conj                        none
% 6.84/1.49  --large_theory_mode                     true
% 6.84/1.49  --prolific_symb_bound                   200
% 6.84/1.49  --lt_threshold                          2000
% 6.84/1.49  --clause_weak_htbl                      true
% 6.84/1.49  --gc_record_bc_elim                     false
% 6.84/1.49  
% 6.84/1.49  ------ Preprocessing Options
% 6.84/1.49  
% 6.84/1.49  --preprocessing_flag                    true
% 6.84/1.49  --time_out_prep_mult                    0.1
% 6.84/1.49  --splitting_mode                        input
% 6.84/1.49  --splitting_grd                         true
% 6.84/1.49  --splitting_cvd                         false
% 6.84/1.49  --splitting_cvd_svl                     false
% 6.84/1.49  --splitting_nvd                         32
% 6.84/1.49  --sub_typing                            true
% 6.84/1.49  --prep_gs_sim                           true
% 6.84/1.49  --prep_unflatten                        true
% 6.84/1.49  --prep_res_sim                          true
% 6.84/1.49  --prep_upred                            true
% 6.84/1.49  --prep_sem_filter                       exhaustive
% 6.84/1.49  --prep_sem_filter_out                   false
% 6.84/1.49  --pred_elim                             true
% 6.84/1.49  --res_sim_input                         true
% 6.84/1.49  --eq_ax_congr_red                       true
% 6.84/1.49  --pure_diseq_elim                       true
% 6.84/1.49  --brand_transform                       false
% 6.84/1.49  --non_eq_to_eq                          false
% 6.84/1.49  --prep_def_merge                        true
% 6.84/1.49  --prep_def_merge_prop_impl              false
% 6.84/1.49  --prep_def_merge_mbd                    true
% 6.84/1.49  --prep_def_merge_tr_red                 false
% 6.84/1.49  --prep_def_merge_tr_cl                  false
% 6.84/1.49  --smt_preprocessing                     true
% 6.84/1.49  --smt_ac_axioms                         fast
% 6.84/1.49  --preprocessed_out                      false
% 6.84/1.49  --preprocessed_stats                    false
% 6.84/1.49  
% 6.84/1.49  ------ Abstraction refinement Options
% 6.84/1.49  
% 6.84/1.49  --abstr_ref                             []
% 6.84/1.49  --abstr_ref_prep                        false
% 6.84/1.49  --abstr_ref_until_sat                   false
% 6.84/1.49  --abstr_ref_sig_restrict                funpre
% 6.84/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.84/1.49  --abstr_ref_under                       []
% 6.84/1.49  
% 6.84/1.49  ------ SAT Options
% 6.84/1.49  
% 6.84/1.49  --sat_mode                              false
% 6.84/1.49  --sat_fm_restart_options                ""
% 6.84/1.49  --sat_gr_def                            false
% 6.84/1.49  --sat_epr_types                         true
% 6.84/1.49  --sat_non_cyclic_types                  false
% 6.84/1.49  --sat_finite_models                     false
% 6.84/1.49  --sat_fm_lemmas                         false
% 6.84/1.49  --sat_fm_prep                           false
% 6.84/1.49  --sat_fm_uc_incr                        true
% 6.84/1.49  --sat_out_model                         small
% 6.84/1.49  --sat_out_clauses                       false
% 6.84/1.49  
% 6.84/1.49  ------ QBF Options
% 6.84/1.49  
% 6.84/1.49  --qbf_mode                              false
% 6.84/1.49  --qbf_elim_univ                         false
% 6.84/1.49  --qbf_dom_inst                          none
% 6.84/1.49  --qbf_dom_pre_inst                      false
% 6.84/1.49  --qbf_sk_in                             false
% 6.84/1.49  --qbf_pred_elim                         true
% 6.84/1.49  --qbf_split                             512
% 6.84/1.49  
% 6.84/1.49  ------ BMC1 Options
% 6.84/1.49  
% 6.84/1.49  --bmc1_incremental                      false
% 6.84/1.49  --bmc1_axioms                           reachable_all
% 6.84/1.49  --bmc1_min_bound                        0
% 6.84/1.49  --bmc1_max_bound                        -1
% 6.84/1.49  --bmc1_max_bound_default                -1
% 6.84/1.49  --bmc1_symbol_reachability              true
% 6.84/1.49  --bmc1_property_lemmas                  false
% 6.84/1.49  --bmc1_k_induction                      false
% 6.84/1.49  --bmc1_non_equiv_states                 false
% 6.84/1.49  --bmc1_deadlock                         false
% 6.84/1.49  --bmc1_ucm                              false
% 6.84/1.49  --bmc1_add_unsat_core                   none
% 6.84/1.49  --bmc1_unsat_core_children              false
% 6.84/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.84/1.49  --bmc1_out_stat                         full
% 6.84/1.49  --bmc1_ground_init                      false
% 6.84/1.49  --bmc1_pre_inst_next_state              false
% 6.84/1.49  --bmc1_pre_inst_state                   false
% 6.84/1.49  --bmc1_pre_inst_reach_state             false
% 6.84/1.49  --bmc1_out_unsat_core                   false
% 6.84/1.49  --bmc1_aig_witness_out                  false
% 6.84/1.49  --bmc1_verbose                          false
% 6.84/1.49  --bmc1_dump_clauses_tptp                false
% 6.84/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.84/1.49  --bmc1_dump_file                        -
% 6.84/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.84/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.84/1.49  --bmc1_ucm_extend_mode                  1
% 6.84/1.49  --bmc1_ucm_init_mode                    2
% 6.84/1.49  --bmc1_ucm_cone_mode                    none
% 6.84/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.84/1.49  --bmc1_ucm_relax_model                  4
% 6.84/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.84/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.84/1.49  --bmc1_ucm_layered_model                none
% 6.84/1.49  --bmc1_ucm_max_lemma_size               10
% 6.84/1.49  
% 6.84/1.49  ------ AIG Options
% 6.84/1.49  
% 6.84/1.49  --aig_mode                              false
% 6.84/1.49  
% 6.84/1.49  ------ Instantiation Options
% 6.84/1.49  
% 6.84/1.49  --instantiation_flag                    true
% 6.84/1.49  --inst_sos_flag                         false
% 6.84/1.49  --inst_sos_phase                        true
% 6.84/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.84/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.84/1.49  --inst_lit_sel_side                     none
% 6.84/1.49  --inst_solver_per_active                1400
% 6.84/1.49  --inst_solver_calls_frac                1.
% 6.84/1.49  --inst_passive_queue_type               priority_queues
% 6.84/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.84/1.49  --inst_passive_queues_freq              [25;2]
% 6.84/1.49  --inst_dismatching                      true
% 6.84/1.49  --inst_eager_unprocessed_to_passive     true
% 6.84/1.49  --inst_prop_sim_given                   true
% 6.84/1.49  --inst_prop_sim_new                     false
% 6.84/1.49  --inst_subs_new                         false
% 6.84/1.49  --inst_eq_res_simp                      false
% 6.84/1.49  --inst_subs_given                       false
% 6.84/1.49  --inst_orphan_elimination               true
% 6.84/1.49  --inst_learning_loop_flag               true
% 6.84/1.49  --inst_learning_start                   3000
% 6.84/1.49  --inst_learning_factor                  2
% 6.84/1.49  --inst_start_prop_sim_after_learn       3
% 6.84/1.49  --inst_sel_renew                        solver
% 6.84/1.49  --inst_lit_activity_flag                true
% 6.84/1.49  --inst_restr_to_given                   false
% 6.84/1.49  --inst_activity_threshold               500
% 6.84/1.49  --inst_out_proof                        true
% 6.84/1.49  
% 6.84/1.49  ------ Resolution Options
% 6.84/1.49  
% 6.84/1.49  --resolution_flag                       false
% 6.84/1.49  --res_lit_sel                           adaptive
% 6.84/1.49  --res_lit_sel_side                      none
% 6.84/1.49  --res_ordering                          kbo
% 6.84/1.49  --res_to_prop_solver                    active
% 6.84/1.49  --res_prop_simpl_new                    false
% 6.84/1.49  --res_prop_simpl_given                  true
% 6.84/1.49  --res_passive_queue_type                priority_queues
% 6.84/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.84/1.49  --res_passive_queues_freq               [15;5]
% 6.84/1.49  --res_forward_subs                      full
% 6.84/1.49  --res_backward_subs                     full
% 6.84/1.49  --res_forward_subs_resolution           true
% 6.84/1.49  --res_backward_subs_resolution          true
% 6.84/1.49  --res_orphan_elimination                true
% 6.84/1.49  --res_time_limit                        2.
% 6.84/1.49  --res_out_proof                         true
% 6.84/1.49  
% 6.84/1.49  ------ Superposition Options
% 6.84/1.49  
% 6.84/1.49  --superposition_flag                    true
% 6.84/1.49  --sup_passive_queue_type                priority_queues
% 6.84/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.84/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.84/1.49  --demod_completeness_check              fast
% 6.84/1.49  --demod_use_ground                      true
% 6.84/1.49  --sup_to_prop_solver                    passive
% 6.84/1.49  --sup_prop_simpl_new                    true
% 6.84/1.49  --sup_prop_simpl_given                  true
% 6.84/1.49  --sup_fun_splitting                     false
% 6.84/1.49  --sup_smt_interval                      50000
% 6.84/1.49  
% 6.84/1.49  ------ Superposition Simplification Setup
% 6.84/1.49  
% 6.84/1.49  --sup_indices_passive                   []
% 6.84/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.84/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.84/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.84/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.84/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.84/1.49  --sup_full_bw                           [BwDemod]
% 6.84/1.49  --sup_immed_triv                        [TrivRules]
% 6.84/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.84/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.84/1.49  --sup_immed_bw_main                     []
% 6.84/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.84/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.84/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.84/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.84/1.49  
% 6.84/1.49  ------ Combination Options
% 6.84/1.49  
% 6.84/1.49  --comb_res_mult                         3
% 6.84/1.49  --comb_sup_mult                         2
% 6.84/1.49  --comb_inst_mult                        10
% 6.84/1.49  
% 6.84/1.49  ------ Debug Options
% 6.84/1.49  
% 6.84/1.49  --dbg_backtrace                         false
% 6.84/1.49  --dbg_dump_prop_clauses                 false
% 6.84/1.49  --dbg_dump_prop_clauses_file            -
% 6.84/1.49  --dbg_out_stat                          false
% 6.84/1.49  
% 6.84/1.49  
% 6.84/1.49  
% 6.84/1.49  
% 6.84/1.49  ------ Proving...
% 6.84/1.49  
% 6.84/1.49  
% 6.84/1.49  % SZS status Theorem for theBenchmark.p
% 6.84/1.49  
% 6.84/1.49   Resolution empty clause
% 6.84/1.49  
% 6.84/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.84/1.49  
% 6.84/1.49  fof(f15,axiom,(
% 6.84/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 6.84/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.49  
% 6.84/1.49  fof(f43,plain,(
% 6.84/1.49    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.84/1.49    inference(ennf_transformation,[],[f15])).
% 6.84/1.49  
% 6.84/1.49  fof(f44,plain,(
% 6.84/1.49    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.84/1.49    inference(flattening,[],[f43])).
% 6.84/1.49  
% 6.84/1.49  fof(f83,plain,(
% 6.84/1.49    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.84/1.49    inference(cnf_transformation,[],[f44])).
% 6.84/1.49  
% 6.84/1.49  fof(f84,plain,(
% 6.84/1.49    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.84/1.49    inference(cnf_transformation,[],[f44])).
% 6.84/1.49  
% 6.84/1.49  fof(f16,conjecture,(
% 6.84/1.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 6.84/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.49  
% 6.84/1.49  fof(f17,negated_conjecture,(
% 6.84/1.49    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 6.84/1.49    inference(negated_conjecture,[],[f16])).
% 6.84/1.49  
% 6.84/1.49  fof(f18,plain,(
% 6.84/1.49    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 6.84/1.49    inference(pure_predicate_removal,[],[f17])).
% 6.84/1.49  
% 6.84/1.49  fof(f45,plain,(
% 6.84/1.49    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 6.84/1.49    inference(ennf_transformation,[],[f18])).
% 6.84/1.49  
% 6.84/1.49  fof(f46,plain,(
% 6.84/1.49    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 6.84/1.49    inference(flattening,[],[f45])).
% 6.84/1.49  
% 6.84/1.49  fof(f52,plain,(
% 6.84/1.49    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK3)),sK3) & v2_funct_1(sK3) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3) = k2_struct_0(X1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 6.84/1.49    introduced(choice_axiom,[])).
% 6.84/1.49  
% 6.84/1.49  fof(f51,plain,(
% 6.84/1.49    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK2),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2) = k2_struct_0(sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_struct_0(sK2))) )),
% 6.84/1.49    introduced(choice_axiom,[])).
% 6.84/1.49  
% 6.84/1.49  fof(f50,plain,(
% 6.84/1.49    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK1))),
% 6.84/1.49    introduced(choice_axiom,[])).
% 6.84/1.49  
% 6.84/1.49  fof(f53,plain,(
% 6.84/1.49    ((~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3) & v2_funct_1(sK3) & k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_struct_0(sK2)) & l1_struct_0(sK1)),
% 6.84/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f46,f52,f51,f50])).
% 6.84/1.49  
% 6.84/1.49  fof(f89,plain,(
% 6.84/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 6.84/1.49    inference(cnf_transformation,[],[f53])).
% 6.84/1.49  
% 6.84/1.49  fof(f13,axiom,(
% 6.84/1.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 6.84/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.49  
% 6.84/1.49  fof(f40,plain,(
% 6.84/1.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 6.84/1.49    inference(ennf_transformation,[],[f13])).
% 6.84/1.49  
% 6.84/1.49  fof(f80,plain,(
% 6.84/1.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 6.84/1.49    inference(cnf_transformation,[],[f40])).
% 6.84/1.49  
% 6.84/1.49  fof(f86,plain,(
% 6.84/1.49    l1_struct_0(sK2)),
% 6.84/1.49    inference(cnf_transformation,[],[f53])).
% 6.84/1.49  
% 6.84/1.49  fof(f85,plain,(
% 6.84/1.49    l1_struct_0(sK1)),
% 6.84/1.49    inference(cnf_transformation,[],[f53])).
% 6.84/1.49  
% 6.84/1.49  fof(f7,axiom,(
% 6.84/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 6.84/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.49  
% 6.84/1.49  fof(f31,plain,(
% 6.84/1.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.84/1.49    inference(ennf_transformation,[],[f7])).
% 6.84/1.49  
% 6.84/1.49  fof(f64,plain,(
% 6.84/1.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.84/1.49    inference(cnf_transformation,[],[f31])).
% 6.84/1.49  
% 6.84/1.49  fof(f90,plain,(
% 6.84/1.49    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2)),
% 6.84/1.49    inference(cnf_transformation,[],[f53])).
% 6.84/1.49  
% 6.84/1.49  fof(f8,axiom,(
% 6.84/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 6.84/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.49  
% 6.84/1.49  fof(f32,plain,(
% 6.84/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.84/1.49    inference(ennf_transformation,[],[f8])).
% 6.84/1.49  
% 6.84/1.49  fof(f33,plain,(
% 6.84/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.84/1.49    inference(flattening,[],[f32])).
% 6.84/1.49  
% 6.84/1.49  fof(f47,plain,(
% 6.84/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.84/1.49    inference(nnf_transformation,[],[f33])).
% 6.84/1.49  
% 6.84/1.49  fof(f65,plain,(
% 6.84/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.84/1.49    inference(cnf_transformation,[],[f47])).
% 6.84/1.49  
% 6.84/1.49  fof(f6,axiom,(
% 6.84/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 6.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.50  
% 6.84/1.50  fof(f30,plain,(
% 6.84/1.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.84/1.50    inference(ennf_transformation,[],[f6])).
% 6.84/1.50  
% 6.84/1.50  fof(f63,plain,(
% 6.84/1.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.84/1.50    inference(cnf_transformation,[],[f30])).
% 6.84/1.50  
% 6.84/1.50  fof(f88,plain,(
% 6.84/1.50    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 6.84/1.50    inference(cnf_transformation,[],[f53])).
% 6.84/1.50  
% 6.84/1.50  fof(f11,axiom,(
% 6.84/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 6.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.50  
% 6.84/1.50  fof(f36,plain,(
% 6.84/1.50    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.84/1.50    inference(ennf_transformation,[],[f11])).
% 6.84/1.50  
% 6.84/1.50  fof(f37,plain,(
% 6.84/1.50    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.84/1.50    inference(flattening,[],[f36])).
% 6.84/1.50  
% 6.84/1.50  fof(f78,plain,(
% 6.84/1.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.84/1.50    inference(cnf_transformation,[],[f37])).
% 6.84/1.50  
% 6.84/1.50  fof(f87,plain,(
% 6.84/1.50    v1_funct_1(sK3)),
% 6.84/1.50    inference(cnf_transformation,[],[f53])).
% 6.84/1.50  
% 6.84/1.50  fof(f91,plain,(
% 6.84/1.50    v2_funct_1(sK3)),
% 6.84/1.50    inference(cnf_transformation,[],[f53])).
% 6.84/1.50  
% 6.84/1.50  fof(f3,axiom,(
% 6.84/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 6.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.50  
% 6.84/1.50  fof(f25,plain,(
% 6.84/1.50    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.84/1.50    inference(ennf_transformation,[],[f3])).
% 6.84/1.50  
% 6.84/1.50  fof(f26,plain,(
% 6.84/1.50    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.84/1.50    inference(flattening,[],[f25])).
% 6.84/1.50  
% 6.84/1.50  fof(f60,plain,(
% 6.84/1.50    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.84/1.50    inference(cnf_transformation,[],[f26])).
% 6.84/1.50  
% 6.84/1.50  fof(f5,axiom,(
% 6.84/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.50  
% 6.84/1.50  fof(f29,plain,(
% 6.84/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.84/1.50    inference(ennf_transformation,[],[f5])).
% 6.84/1.50  
% 6.84/1.50  fof(f62,plain,(
% 6.84/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.84/1.50    inference(cnf_transformation,[],[f29])).
% 6.84/1.50  
% 6.84/1.50  fof(f14,axiom,(
% 6.84/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 6.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.50  
% 6.84/1.50  fof(f41,plain,(
% 6.84/1.50    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.84/1.50    inference(ennf_transformation,[],[f14])).
% 6.84/1.50  
% 6.84/1.50  fof(f42,plain,(
% 6.84/1.50    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.84/1.50    inference(flattening,[],[f41])).
% 6.84/1.50  
% 6.84/1.50  fof(f81,plain,(
% 6.84/1.50    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.84/1.50    inference(cnf_transformation,[],[f42])).
% 6.84/1.50  
% 6.84/1.50  fof(f4,axiom,(
% 6.84/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 6.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.50  
% 6.84/1.50  fof(f27,plain,(
% 6.84/1.50    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.84/1.50    inference(ennf_transformation,[],[f4])).
% 6.84/1.50  
% 6.84/1.50  fof(f28,plain,(
% 6.84/1.50    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.84/1.50    inference(flattening,[],[f27])).
% 6.84/1.50  
% 6.84/1.50  fof(f61,plain,(
% 6.84/1.50    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.84/1.50    inference(cnf_transformation,[],[f28])).
% 6.84/1.50  
% 6.84/1.50  fof(f2,axiom,(
% 6.84/1.50    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 6.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.50  
% 6.84/1.50  fof(f23,plain,(
% 6.84/1.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.84/1.50    inference(ennf_transformation,[],[f2])).
% 6.84/1.50  
% 6.84/1.50  fof(f24,plain,(
% 6.84/1.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.84/1.50    inference(flattening,[],[f23])).
% 6.84/1.50  
% 6.84/1.50  fof(f58,plain,(
% 6.84/1.50    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.84/1.50    inference(cnf_transformation,[],[f24])).
% 6.84/1.50  
% 6.84/1.50  fof(f76,plain,(
% 6.84/1.50    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.84/1.50    inference(cnf_transformation,[],[f37])).
% 6.84/1.50  
% 6.84/1.50  fof(f1,axiom,(
% 6.84/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 6.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.50  
% 6.84/1.50  fof(f21,plain,(
% 6.84/1.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.84/1.50    inference(ennf_transformation,[],[f1])).
% 6.84/1.50  
% 6.84/1.50  fof(f22,plain,(
% 6.84/1.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.84/1.50    inference(flattening,[],[f21])).
% 6.84/1.50  
% 6.84/1.50  fof(f55,plain,(
% 6.84/1.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.84/1.50    inference(cnf_transformation,[],[f22])).
% 6.84/1.50  
% 6.84/1.50  fof(f77,plain,(
% 6.84/1.50    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.84/1.50    inference(cnf_transformation,[],[f37])).
% 6.84/1.50  
% 6.84/1.50  fof(f10,axiom,(
% 6.84/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 6.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.50  
% 6.84/1.50  fof(f34,plain,(
% 6.84/1.50    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.84/1.50    inference(ennf_transformation,[],[f10])).
% 6.84/1.50  
% 6.84/1.50  fof(f35,plain,(
% 6.84/1.50    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.84/1.50    inference(flattening,[],[f34])).
% 6.84/1.50  
% 6.84/1.50  fof(f75,plain,(
% 6.84/1.50    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.84/1.50    inference(cnf_transformation,[],[f35])).
% 6.84/1.50  
% 6.84/1.50  fof(f92,plain,(
% 6.84/1.50    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3)),
% 6.84/1.50    inference(cnf_transformation,[],[f53])).
% 6.84/1.50  
% 6.84/1.50  fof(f82,plain,(
% 6.84/1.50    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.84/1.50    inference(cnf_transformation,[],[f44])).
% 6.84/1.50  
% 6.84/1.50  fof(f69,plain,(
% 6.84/1.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.84/1.50    inference(cnf_transformation,[],[f47])).
% 6.84/1.50  
% 6.84/1.50  fof(f95,plain,(
% 6.84/1.50    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 6.84/1.50    inference(equality_resolution,[],[f69])).
% 6.84/1.50  
% 6.84/1.50  fof(f66,plain,(
% 6.84/1.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.84/1.50    inference(cnf_transformation,[],[f47])).
% 6.84/1.50  
% 6.84/1.50  fof(f97,plain,(
% 6.84/1.50    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 6.84/1.50    inference(equality_resolution,[],[f66])).
% 6.84/1.50  
% 6.84/1.50  fof(f12,axiom,(
% 6.84/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 6.84/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.84/1.50  
% 6.84/1.50  fof(f38,plain,(
% 6.84/1.50    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 6.84/1.50    inference(ennf_transformation,[],[f12])).
% 6.84/1.50  
% 6.84/1.50  fof(f39,plain,(
% 6.84/1.50    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 6.84/1.50    inference(flattening,[],[f38])).
% 6.84/1.50  
% 6.84/1.50  fof(f79,plain,(
% 6.84/1.50    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 6.84/1.50    inference(cnf_transformation,[],[f39])).
% 6.84/1.50  
% 6.84/1.50  cnf(c_29,plain,
% 6.84/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 6.84/1.50      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 6.84/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.50      | ~ v1_funct_1(X0) ),
% 6.84/1.50      inference(cnf_transformation,[],[f83]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1275,plain,
% 6.84/1.50      ( v1_funct_2(X0,X1,X2) != iProver_top
% 6.84/1.50      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
% 6.84/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.84/1.50      | v1_funct_1(X0) != iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_28,plain,
% 6.84/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 6.84/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.50      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 6.84/1.50      | ~ v1_funct_1(X0) ),
% 6.84/1.50      inference(cnf_transformation,[],[f84]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1276,plain,
% 6.84/1.50      ( v1_funct_2(X0,X1,X2) != iProver_top
% 6.84/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 6.84/1.50      | v1_funct_1(X0) != iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_34,negated_conjecture,
% 6.84/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 6.84/1.50      inference(cnf_transformation,[],[f89]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1272,plain,
% 6.84/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_26,plain,
% 6.84/1.50      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 6.84/1.50      inference(cnf_transformation,[],[f80]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_37,negated_conjecture,
% 6.84/1.50      ( l1_struct_0(sK2) ),
% 6.84/1.50      inference(cnf_transformation,[],[f86]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_435,plain,
% 6.84/1.50      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 6.84/1.50      inference(resolution_lifted,[status(thm)],[c_26,c_37]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_436,plain,
% 6.84/1.50      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 6.84/1.50      inference(unflattening,[status(thm)],[c_435]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_38,negated_conjecture,
% 6.84/1.50      ( l1_struct_0(sK1) ),
% 6.84/1.50      inference(cnf_transformation,[],[f85]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_440,plain,
% 6.84/1.50      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 6.84/1.50      inference(resolution_lifted,[status(thm)],[c_26,c_38]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_441,plain,
% 6.84/1.50      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 6.84/1.50      inference(unflattening,[status(thm)],[c_440]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1320,plain,
% 6.84/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) = iProver_top ),
% 6.84/1.50      inference(light_normalisation,[status(thm)],[c_1272,c_436,c_441]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_10,plain,
% 6.84/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 6.84/1.50      inference(cnf_transformation,[],[f64]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1291,plain,
% 6.84/1.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 6.84/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_2219,plain,
% 6.84/1.50      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3) ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_1320,c_1291]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_33,negated_conjecture,
% 6.84/1.50      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
% 6.84/1.50      inference(cnf_transformation,[],[f90]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1317,plain,
% 6.84/1.50      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
% 6.84/1.50      inference(light_normalisation,[status(thm)],[c_33,c_436,c_441]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_2660,plain,
% 6.84/1.50      ( k2_struct_0(sK2) = k2_relat_1(sK3) ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_2219,c_1317]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_2684,plain,
% 6.84/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) = iProver_top ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_2660,c_1320]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_16,plain,
% 6.84/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 6.84/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.50      | k1_relset_1(X1,X2,X0) = X1
% 6.84/1.50      | k1_xboole_0 = X2 ),
% 6.84/1.50      inference(cnf_transformation,[],[f65]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1285,plain,
% 6.84/1.50      ( k1_relset_1(X0,X1,X2) = X0
% 6.84/1.50      | k1_xboole_0 = X1
% 6.84/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.84/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_4425,plain,
% 6.84/1.50      ( k1_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_struct_0(sK1)
% 6.84/1.50      | k2_relat_1(sK3) = k1_xboole_0
% 6.84/1.50      | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_2684,c_1285]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_9,plain,
% 6.84/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 6.84/1.50      inference(cnf_transformation,[],[f63]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1292,plain,
% 6.84/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 6.84/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_2385,plain,
% 6.84/1.50      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k1_relat_1(sK3) ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_1320,c_1292]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_2845,plain,
% 6.84/1.50      ( k1_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k1_relat_1(sK3) ),
% 6.84/1.50      inference(light_normalisation,[status(thm)],[c_2385,c_2660]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_4429,plain,
% 6.84/1.50      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 6.84/1.50      | k2_relat_1(sK3) = k1_xboole_0
% 6.84/1.50      | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top ),
% 6.84/1.50      inference(light_normalisation,[status(thm)],[c_4425,c_2845]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_35,negated_conjecture,
% 6.84/1.50      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 6.84/1.50      inference(cnf_transformation,[],[f88]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1271,plain,
% 6.84/1.50      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1312,plain,
% 6.84/1.50      ( v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) = iProver_top ),
% 6.84/1.50      inference(light_normalisation,[status(thm)],[c_1271,c_436,c_441]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_2685,plain,
% 6.84/1.50      ( v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) = iProver_top ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_2660,c_1312]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_4599,plain,
% 6.84/1.50      ( k2_relat_1(sK3) = k1_xboole_0 | k2_struct_0(sK1) = k1_relat_1(sK3) ),
% 6.84/1.50      inference(global_propositional_subsumption,[status(thm)],[c_4429,c_2685]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_4600,plain,
% 6.84/1.50      ( k2_struct_0(sK1) = k1_relat_1(sK3) | k2_relat_1(sK3) = k1_xboole_0 ),
% 6.84/1.50      inference(renaming,[status(thm)],[c_4599]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_2681,plain,
% 6.84/1.50      ( k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_relat_1(sK3) ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_2660,c_2219]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_22,plain,
% 6.84/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 6.84/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.50      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 6.84/1.50      | ~ v2_funct_1(X0)
% 6.84/1.50      | ~ v1_funct_1(X0)
% 6.84/1.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 6.84/1.50      inference(cnf_transformation,[],[f78]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1280,plain,
% 6.84/1.50      ( k2_relset_1(X0,X1,X2) != X1
% 6.84/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.84/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 6.84/1.50      | v2_funct_1(X2) != iProver_top
% 6.84/1.50      | v1_funct_1(X2) != iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_5594,plain,
% 6.84/1.50      ( v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) = iProver_top
% 6.84/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
% 6.84/1.50      | v2_funct_1(sK3) != iProver_top
% 6.84/1.50      | v1_funct_1(sK3) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_2681,c_1280]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_36,negated_conjecture,
% 6.84/1.50      ( v1_funct_1(sK3) ),
% 6.84/1.50      inference(cnf_transformation,[],[f87]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_41,plain,
% 6.84/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_32,negated_conjecture,
% 6.84/1.50      ( v2_funct_1(sK3) ),
% 6.84/1.50      inference(cnf_transformation,[],[f91]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_44,plain,
% 6.84/1.50      ( v2_funct_1(sK3) = iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_5989,plain,
% 6.84/1.50      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) = iProver_top ),
% 6.84/1.50      inference(global_propositional_subsumption,
% 6.84/1.50                [status(thm)],
% 6.84/1.50                [c_5594,c_41,c_44,c_2684,c_2685]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_6000,plain,
% 6.84/1.50      ( k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = k2_relat_1(k2_funct_1(sK3)) ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_5989,c_1291]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1273,plain,
% 6.84/1.50      ( v2_funct_1(sK3) = iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_5,plain,
% 6.84/1.50      ( ~ v2_funct_1(X0)
% 6.84/1.50      | ~ v1_relat_1(X0)
% 6.84/1.50      | ~ v1_funct_1(X0)
% 6.84/1.50      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 6.84/1.50      inference(cnf_transformation,[],[f60]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1296,plain,
% 6.84/1.50      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 6.84/1.50      | v2_funct_1(X0) != iProver_top
% 6.84/1.50      | v1_relat_1(X0) != iProver_top
% 6.84/1.50      | v1_funct_1(X0) != iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_4250,plain,
% 6.84/1.50      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 6.84/1.50      | v1_relat_1(sK3) != iProver_top
% 6.84/1.50      | v1_funct_1(sK3) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_1273,c_1296]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_8,plain,
% 6.84/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 6.84/1.50      inference(cnf_transformation,[],[f62]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1597,plain,
% 6.84/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 6.84/1.50      | v1_relat_1(sK3) ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1633,plain,
% 6.84/1.50      ( ~ v2_funct_1(sK3)
% 6.84/1.50      | ~ v1_relat_1(sK3)
% 6.84/1.50      | ~ v1_funct_1(sK3)
% 6.84/1.50      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_4560,plain,
% 6.84/1.50      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 6.84/1.50      inference(global_propositional_subsumption,
% 6.84/1.50                [status(thm)],
% 6.84/1.50                [c_4250,c_36,c_34,c_32,c_1597,c_1633]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_6002,plain,
% 6.84/1.50      ( k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 6.84/1.50      inference(light_normalisation,[status(thm)],[c_6000,c_4560]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_27,plain,
% 6.84/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 6.84/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.50      | ~ v2_funct_1(X0)
% 6.84/1.50      | ~ v1_funct_1(X0)
% 6.84/1.50      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 6.84/1.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 6.84/1.50      inference(cnf_transformation,[],[f81]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1277,plain,
% 6.84/1.50      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
% 6.84/1.50      | k2_relset_1(X0,X1,X2) != X1
% 6.84/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.84/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.84/1.50      | v2_funct_1(X2) != iProver_top
% 6.84/1.50      | v1_funct_1(X2) != iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_6167,plain,
% 6.84/1.50      ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = k2_funct_1(k2_funct_1(sK3))
% 6.84/1.50      | k2_struct_0(sK1) != k1_relat_1(sK3)
% 6.84/1.50      | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) != iProver_top
% 6.84/1.50      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 6.84/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_6002,c_1277]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_7,plain,
% 6.84/1.50      ( ~ v2_funct_1(X0)
% 6.84/1.50      | ~ v1_relat_1(X0)
% 6.84/1.50      | ~ v1_funct_1(X0)
% 6.84/1.50      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 6.84/1.50      inference(cnf_transformation,[],[f61]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1294,plain,
% 6.84/1.50      ( k2_funct_1(k2_funct_1(X0)) = X0
% 6.84/1.50      | v2_funct_1(X0) != iProver_top
% 6.84/1.50      | v1_relat_1(X0) != iProver_top
% 6.84/1.50      | v1_funct_1(X0) != iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_3209,plain,
% 6.84/1.50      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 6.84/1.50      | v1_relat_1(sK3) != iProver_top
% 6.84/1.50      | v1_funct_1(sK3) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_1273,c_1294]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1642,plain,
% 6.84/1.50      ( ~ v2_funct_1(sK3)
% 6.84/1.50      | ~ v1_relat_1(sK3)
% 6.84/1.50      | ~ v1_funct_1(sK3)
% 6.84/1.50      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_3372,plain,
% 6.84/1.50      ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 6.84/1.50      inference(global_propositional_subsumption,
% 6.84/1.50                [status(thm)],
% 6.84/1.50                [c_3209,c_36,c_34,c_32,c_1597,c_1642]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_6174,plain,
% 6.84/1.50      ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = sK3
% 6.84/1.50      | k2_struct_0(sK1) != k1_relat_1(sK3)
% 6.84/1.50      | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) != iProver_top
% 6.84/1.50      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 6.84/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 6.84/1.50      inference(light_normalisation,[status(thm)],[c_6167,c_3372]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_43,plain,
% 6.84/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_2,plain,
% 6.84/1.50      ( ~ v2_funct_1(X0)
% 6.84/1.50      | v2_funct_1(k2_funct_1(X0))
% 6.84/1.50      | ~ v1_relat_1(X0)
% 6.84/1.50      | ~ v1_funct_1(X0) ),
% 6.84/1.50      inference(cnf_transformation,[],[f58]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1594,plain,
% 6.84/1.50      ( v2_funct_1(k2_funct_1(sK3))
% 6.84/1.50      | ~ v2_funct_1(sK3)
% 6.84/1.50      | ~ v1_relat_1(sK3)
% 6.84/1.50      | ~ v1_funct_1(sK3) ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1595,plain,
% 6.84/1.50      ( v2_funct_1(k2_funct_1(sK3)) = iProver_top
% 6.84/1.50      | v2_funct_1(sK3) != iProver_top
% 6.84/1.50      | v1_relat_1(sK3) != iProver_top
% 6.84/1.50      | v1_funct_1(sK3) != iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_1594]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1598,plain,
% 6.84/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 6.84/1.50      | v1_relat_1(sK3) = iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_1597]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_24,plain,
% 6.84/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 6.84/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.50      | ~ v2_funct_1(X0)
% 6.84/1.50      | ~ v1_funct_1(X0)
% 6.84/1.50      | v1_funct_1(k2_funct_1(X0))
% 6.84/1.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 6.84/1.50      inference(cnf_transformation,[],[f76]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_0,plain,
% 6.84/1.50      ( ~ v1_relat_1(X0) | ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) ),
% 6.84/1.50      inference(cnf_transformation,[],[f55]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_229,plain,
% 6.84/1.50      ( v1_funct_1(k2_funct_1(X0))
% 6.84/1.50      | ~ v1_funct_1(X0)
% 6.84/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 6.84/1.50      inference(global_propositional_subsumption,[status(thm)],[c_24,c_8,c_0]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_230,plain,
% 6.84/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.50      | ~ v1_funct_1(X0)
% 6.84/1.50      | v1_funct_1(k2_funct_1(X0)) ),
% 6.84/1.50      inference(renaming,[status(thm)],[c_229]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1269,plain,
% 6.84/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.84/1.50      | v1_funct_1(X0) != iProver_top
% 6.84/1.50      | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_230]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1758,plain,
% 6.84/1.50      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 6.84/1.50      | v1_funct_1(sK3) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_1320,c_1269]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_23,plain,
% 6.84/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 6.84/1.50      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 6.84/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.50      | ~ v2_funct_1(X0)
% 6.84/1.50      | ~ v1_funct_1(X0)
% 6.84/1.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 6.84/1.50      inference(cnf_transformation,[],[f77]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1279,plain,
% 6.84/1.50      ( k2_relset_1(X0,X1,X2) != X1
% 6.84/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.84/1.50      | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
% 6.84/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.84/1.50      | v2_funct_1(X2) != iProver_top
% 6.84/1.50      | v1_funct_1(X2) != iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_5545,plain,
% 6.84/1.50      ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) = iProver_top
% 6.84/1.50      | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 6.84/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
% 6.84/1.50      | v2_funct_1(sK3) != iProver_top
% 6.84/1.50      | v1_funct_1(sK3) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_2681,c_1279]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_6272,plain,
% 6.84/1.50      ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = sK3
% 6.84/1.50      | k2_struct_0(sK1) != k1_relat_1(sK3) ),
% 6.84/1.50      inference(global_propositional_subsumption,
% 6.84/1.50                [status(thm)],
% 6.84/1.50                [c_6174,c_41,c_43,c_44,c_1595,c_1598,c_1758,c_2684,c_2685,
% 6.84/1.50                 c_5545,c_5594]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_6276,plain,
% 6.84/1.50      ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = sK3
% 6.84/1.50      | k2_relat_1(sK3) = k1_xboole_0 ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_4600,c_6272]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_5360,plain,
% 6.84/1.50      ( k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3)
% 6.84/1.50      | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 6.84/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
% 6.84/1.50      | v2_funct_1(sK3) != iProver_top
% 6.84/1.50      | v1_funct_1(sK3) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_2681,c_1277]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_5828,plain,
% 6.84/1.50      ( k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3) ),
% 6.84/1.50      inference(global_propositional_subsumption,
% 6.84/1.50                [status(thm)],
% 6.84/1.50                [c_5360,c_41,c_44,c_2684,c_2685]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_21,plain,
% 6.84/1.50      ( r2_funct_2(X0,X1,X2,X2)
% 6.84/1.50      | ~ v1_funct_2(X2,X0,X1)
% 6.84/1.50      | ~ v1_funct_2(X3,X0,X1)
% 6.84/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.84/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.84/1.50      | ~ v1_funct_1(X3)
% 6.84/1.50      | ~ v1_funct_1(X2) ),
% 6.84/1.50      inference(cnf_transformation,[],[f75]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_31,negated_conjecture,
% 6.84/1.50      ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3) ),
% 6.84/1.50      inference(cnf_transformation,[],[f92]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_447,plain,
% 6.84/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 6.84/1.50      | ~ v1_funct_2(X3,X1,X2)
% 6.84/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.50      | ~ v1_funct_1(X3)
% 6.84/1.50      | ~ v1_funct_1(X0)
% 6.84/1.50      | k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != X0
% 6.84/1.50      | u1_struct_0(sK2) != X2
% 6.84/1.50      | u1_struct_0(sK1) != X1
% 6.84/1.50      | sK3 != X0 ),
% 6.84/1.50      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_448,plain,
% 6.84/1.50      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
% 6.84/1.50      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2))
% 6.84/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 6.84/1.50      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 6.84/1.50      | ~ v1_funct_1(X0)
% 6.84/1.50      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)))
% 6.84/1.50      | sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
% 6.84/1.50      inference(unflattening,[status(thm)],[c_447]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_696,plain,
% 6.84/1.50      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2))
% 6.84/1.50      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 6.84/1.50      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)))
% 6.84/1.50      | sP0_iProver_split
% 6.84/1.50      | sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
% 6.84/1.50      inference(splitting,
% 6.84/1.50                [splitting(split),new_symbols(definition,[])],
% 6.84/1.50                [c_448]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1267,plain,
% 6.84/1.50      ( sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
% 6.84/1.50      | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 6.84/1.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) != iProver_top
% 6.84/1.50      | sP0_iProver_split = iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_696]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1506,plain,
% 6.84/1.50      ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != sK3
% 6.84/1.50      | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
% 6.84/1.50      | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))) != iProver_top
% 6.84/1.50      | sP0_iProver_split = iProver_top ),
% 6.84/1.50      inference(light_normalisation,[status(thm)],[c_1267,c_436,c_441]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_695,plain,
% 6.84/1.50      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
% 6.84/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 6.84/1.50      | ~ v1_funct_1(X0)
% 6.84/1.50      | ~ sP0_iProver_split ),
% 6.84/1.50      inference(splitting,
% 6.84/1.50                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 6.84/1.50                [c_448]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1268,plain,
% 6.84/1.50      ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 6.84/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 6.84/1.50      | v1_funct_1(X0) != iProver_top
% 6.84/1.50      | sP0_iProver_split != iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_695]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1445,plain,
% 6.84/1.50      ( v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
% 6.84/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
% 6.84/1.50      | v1_funct_1(X0) != iProver_top
% 6.84/1.50      | sP0_iProver_split != iProver_top ),
% 6.84/1.50      inference(light_normalisation,[status(thm)],[c_1268,c_436,c_441]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1512,plain,
% 6.84/1.50      ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != sK3
% 6.84/1.50      | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
% 6.84/1.50      | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))) != iProver_top ),
% 6.84/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_1506,c_1445]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_2682,plain,
% 6.84/1.50      ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) != sK3
% 6.84/1.50      | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
% 6.84/1.50      | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))) != iProver_top ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_2660,c_1512]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_5832,plain,
% 6.84/1.50      ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) != sK3
% 6.84/1.50      | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
% 6.84/1.50      | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))) != iProver_top ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_5828,c_2682]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_30,plain,
% 6.84/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 6.84/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.84/1.50      | ~ v1_funct_1(X0)
% 6.84/1.50      | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
% 6.84/1.50      inference(cnf_transformation,[],[f82]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1274,plain,
% 6.84/1.50      ( v1_funct_2(X0,X1,X2) != iProver_top
% 6.84/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.84/1.50      | v1_funct_1(X0) != iProver_top
% 6.84/1.50      | v1_funct_1(k2_tops_2(X1,X2,X0)) = iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_5995,plain,
% 6.84/1.50      ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) != iProver_top
% 6.84/1.50      | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))) = iProver_top
% 6.84/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_5989,c_1274]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_6278,plain,
% 6.84/1.50      ( m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
% 6.84/1.50      | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 6.84/1.50      | k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) != sK3 ),
% 6.84/1.50      inference(global_propositional_subsumption,
% 6.84/1.50                [status(thm)],
% 6.84/1.50                [c_5832,c_41,c_44,c_1758,c_2684,c_2685,c_5545,c_5995]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_6279,plain,
% 6.84/1.50      ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) != sK3
% 6.84/1.50      | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top ),
% 6.84/1.50      inference(renaming,[status(thm)],[c_6278]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_6442,plain,
% 6.84/1.50      ( k2_relat_1(sK3) = k1_xboole_0
% 6.84/1.50      | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_6276,c_6279]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_7243,plain,
% 6.84/1.50      ( k2_relat_1(sK3) = k1_xboole_0
% 6.84/1.50      | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 6.84/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_6276,c_6442]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_7272,plain,
% 6.84/1.50      ( v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 6.84/1.50      | k2_relat_1(sK3) = k1_xboole_0 ),
% 6.84/1.50      inference(global_propositional_subsumption,
% 6.84/1.50                [status(thm)],
% 6.84/1.50                [c_7243,c_41,c_44,c_1758,c_2684,c_2685,c_5545,c_5594,c_7242]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_7273,plain,
% 6.84/1.50      ( k2_relat_1(sK3) = k1_xboole_0
% 6.84/1.50      | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top ),
% 6.84/1.50      inference(renaming,[status(thm)],[c_7272]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_7279,plain,
% 6.84/1.50      ( k2_relat_1(sK3) = k1_xboole_0
% 6.84/1.50      | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_6276,c_7273]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_7278,plain,
% 6.84/1.50      ( k2_relat_1(sK3) = k1_xboole_0
% 6.84/1.50      | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) != iProver_top
% 6.84/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_1275,c_7273]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_7682,plain,
% 6.84/1.50      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 6.84/1.50      inference(global_propositional_subsumption,
% 6.84/1.50                [status(thm)],
% 6.84/1.50                [c_7279,c_41,c_44,c_1758,c_2684,c_2685,c_5545,c_5594,c_7278]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_7693,plain,
% 6.84/1.50      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) = iProver_top ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_7682,c_5989]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_12,plain,
% 6.84/1.50      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 6.84/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 6.84/1.50      | k1_xboole_0 = X1
% 6.84/1.50      | k1_xboole_0 = X0 ),
% 6.84/1.50      inference(cnf_transformation,[],[f95]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1289,plain,
% 6.84/1.50      ( k1_xboole_0 = X0
% 6.84/1.50      | k1_xboole_0 = X1
% 6.84/1.50      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 6.84/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_4279,plain,
% 6.84/1.50      ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
% 6.84/1.50      | k1_xboole_0 = X0
% 6.84/1.50      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 6.84/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,X0,X1),X0,k1_xboole_0) != iProver_top
% 6.84/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 6.84/1.50      | v1_funct_1(X1) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_1276,c_1289]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_12744,plain,
% 6.84/1.50      ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
% 6.84/1.50      | k1_xboole_0 = X0
% 6.84/1.50      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 6.84/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 6.84/1.50      | v1_funct_1(X1) != iProver_top ),
% 6.84/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_4279,c_1275]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_12750,plain,
% 6.84/1.50      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) = k1_xboole_0
% 6.84/1.50      | k2_struct_0(sK1) = k1_xboole_0
% 6.84/1.50      | v1_funct_2(k2_funct_1(sK3),k1_xboole_0,k2_struct_0(sK1)) != iProver_top
% 6.84/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_7693,c_12744]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_5981,plain,
% 6.84/1.50      ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) = iProver_top ),
% 6.84/1.50      inference(global_propositional_subsumption,
% 6.84/1.50                [status(thm)],
% 6.84/1.50                [c_5545,c_41,c_44,c_2684,c_2685]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_7694,plain,
% 6.84/1.50      ( v1_funct_2(k2_funct_1(sK3),k1_xboole_0,k2_struct_0(sK1)) = iProver_top ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_7682,c_5981]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_21007,plain,
% 6.84/1.50      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) = k1_xboole_0
% 6.84/1.50      | k2_struct_0(sK1) = k1_xboole_0 ),
% 6.84/1.50      inference(global_propositional_subsumption,
% 6.84/1.50                [status(thm)],
% 6.84/1.50                [c_12750,c_41,c_1758,c_7694]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_7699,plain,
% 6.84/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) = iProver_top ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_7682,c_2684]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_9478,plain,
% 6.84/1.50      ( k2_struct_0(sK1) = k1_xboole_0
% 6.84/1.50      | sK3 = k1_xboole_0
% 6.84/1.50      | v1_funct_2(sK3,k2_struct_0(sK1),k1_xboole_0) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_7699,c_1289]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_7702,plain,
% 6.84/1.50      ( v1_funct_2(sK3,k2_struct_0(sK1),k1_xboole_0) = iProver_top ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_7682,c_2685]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_10216,plain,
% 6.84/1.50      ( sK3 = k1_xboole_0 | k2_struct_0(sK1) = k1_xboole_0 ),
% 6.84/1.50      inference(global_propositional_subsumption,[status(thm)],[c_9478,c_7702]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_10217,plain,
% 6.84/1.50      ( k2_struct_0(sK1) = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 6.84/1.50      inference(renaming,[status(thm)],[c_10216]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_7690,plain,
% 6.84/1.50      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) = sK3
% 6.84/1.50      | k2_struct_0(sK1) != k1_relat_1(sK3) ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_7682,c_6272]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_10224,plain,
% 6.84/1.50      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) = sK3
% 6.84/1.50      | k1_relat_1(sK3) != k1_xboole_0
% 6.84/1.50      | sK3 = k1_xboole_0 ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_10217,c_7690]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_10225,plain,
% 6.84/1.50      ( sK3 = k1_xboole_0
% 6.84/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_10217,c_7699]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_15,plain,
% 6.84/1.50      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 6.84/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 6.84/1.50      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 6.84/1.50      inference(cnf_transformation,[],[f97]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1286,plain,
% 6.84/1.50      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 6.84/1.50      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 6.84/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_11388,plain,
% 6.84/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 6.84/1.50      | sK3 = k1_xboole_0
% 6.84/1.50      | v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_10225,c_1286]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_25,plain,
% 6.84/1.50      ( ~ v1_funct_2(X0,X1,X1)
% 6.84/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 6.84/1.50      | ~ v1_funct_1(X0)
% 6.84/1.50      | k1_relset_1(X1,X1,X0) = X1 ),
% 6.84/1.50      inference(cnf_transformation,[],[f79]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1719,plain,
% 6.84/1.50      ( ~ v1_funct_2(sK3,X0,X0)
% 6.84/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 6.84/1.50      | ~ v1_funct_1(sK3)
% 6.84/1.50      | k1_relset_1(X0,X0,sK3) = X0 ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_25]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1720,plain,
% 6.84/1.50      ( k1_relset_1(X0,X0,sK3) = X0
% 6.84/1.50      | v1_funct_2(sK3,X0,X0) != iProver_top
% 6.84/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 6.84/1.50      | v1_funct_1(sK3) != iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_1719]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1722,plain,
% 6.84/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 6.84/1.50      | v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) != iProver_top
% 6.84/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 6.84/1.50      | v1_funct_1(sK3) != iProver_top ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_1720]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_10229,plain,
% 6.84/1.50      ( sK3 = k1_xboole_0
% 6.84/1.50      | v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_10217,c_7702]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_11769,plain,
% 6.84/1.50      ( sK3 = k1_xboole_0
% 6.84/1.50      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
% 6.84/1.50      inference(global_propositional_subsumption,
% 6.84/1.50                [status(thm)],
% 6.84/1.50                [c_11388,c_41,c_1722,c_10225,c_10229]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_11770,plain,
% 6.84/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 6.84/1.50      | sK3 = k1_xboole_0 ),
% 6.84/1.50      inference(renaming,[status(thm)],[c_11769]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_7701,plain,
% 6.84/1.50      ( k1_relset_1(k2_struct_0(sK1),k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_7682,c_2845]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_10227,plain,
% 6.84/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3)
% 6.84/1.50      | sK3 = k1_xboole_0 ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_10217,c_7701]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_11776,plain,
% 6.84/1.50      ( k1_relat_1(sK3) = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_11770,c_10227]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_12596,plain,
% 6.84/1.50      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) = sK3
% 6.84/1.50      | sK3 = k1_xboole_0 ),
% 6.84/1.50      inference(global_propositional_subsumption,
% 6.84/1.50                [status(thm)],
% 6.84/1.50                [c_10224,c_11776]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_7689,plain,
% 6.84/1.50      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) != sK3
% 6.84/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_7682,c_6279]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_12605,plain,
% 6.84/1.50      ( sK3 = k1_xboole_0
% 6.84/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_12596,c_7689]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_12943,plain,
% 6.84/1.50      ( sK3 = k1_xboole_0
% 6.84/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
% 6.84/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_12596,c_12605]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_13283,plain,
% 6.84/1.50      ( v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
% 6.84/1.50      | sK3 = k1_xboole_0 ),
% 6.84/1.50      inference(global_propositional_subsumption,
% 6.84/1.50                [status(thm)],
% 6.84/1.50                [c_12943,c_7699]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_13284,plain,
% 6.84/1.50      ( sK3 = k1_xboole_0
% 6.84/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top ),
% 6.84/1.50      inference(renaming,[status(thm)],[c_13283]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_13290,plain,
% 6.84/1.50      ( sK3 = k1_xboole_0
% 6.84/1.50      | v1_funct_2(sK3,k2_struct_0(sK1),k1_xboole_0) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_12596,c_13284]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_13289,plain,
% 6.84/1.50      ( sK3 = k1_xboole_0
% 6.84/1.50      | v1_funct_2(k2_funct_1(sK3),k1_xboole_0,k2_struct_0(sK1)) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) != iProver_top
% 6.84/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_1275,c_13284]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_13315,plain,
% 6.84/1.50      ( sK3 = k1_xboole_0 ),
% 6.84/1.50      inference(global_propositional_subsumption,
% 6.84/1.50                [status(thm)],
% 6.84/1.50                [c_13290,c_41,c_1758,c_7693,c_7694,c_13289]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_21009,plain,
% 6.84/1.50      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)) = k1_xboole_0
% 6.84/1.50      | k2_struct_0(sK1) = k1_xboole_0 ),
% 6.84/1.50      inference(light_normalisation,[status(thm)],[c_21007,c_13315]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_13328,plain,
% 6.84/1.50      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)) != k1_xboole_0
% 6.84/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_13315,c_7689]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_21016,plain,
% 6.84/1.50      ( k2_struct_0(sK1) = k1_xboole_0
% 6.84/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_21009,c_13328]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_23649,plain,
% 6.84/1.50      ( k2_struct_0(sK1) = k1_xboole_0
% 6.84/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
% 6.84/1.50      | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK1)) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) != iProver_top
% 6.84/1.50      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_1276,c_21016]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_13333,plain,
% 6.84/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) = iProver_top ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_13315,c_7699]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_23650,plain,
% 6.84/1.50      ( k2_struct_0(sK1) = k1_xboole_0
% 6.84/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
% 6.84/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_21009,c_21016]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_23881,plain,
% 6.84/1.50      ( v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
% 6.84/1.50      | k2_struct_0(sK1) = k1_xboole_0 ),
% 6.84/1.50      inference(global_propositional_subsumption,
% 6.84/1.50                [status(thm)],
% 6.84/1.50                [c_23649,c_13333,c_23650]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_23882,plain,
% 6.84/1.50      ( k2_struct_0(sK1) = k1_xboole_0
% 6.84/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)),k2_struct_0(sK1),k1_xboole_0) != iProver_top ),
% 6.84/1.50      inference(renaming,[status(thm)],[c_23881]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_23887,plain,
% 6.84/1.50      ( k2_struct_0(sK1) = k1_xboole_0
% 6.84/1.50      | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK1)) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) != iProver_top
% 6.84/1.50      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_1275,c_23882]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_136,plain,
% 6.84/1.50      ( v1_relat_1(X0) != iProver_top
% 6.84/1.50      | v1_funct_1(X0) != iProver_top
% 6.84/1.50      | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_138,plain,
% 6.84/1.50      ( v1_relat_1(k1_xboole_0) != iProver_top
% 6.84/1.50      | v1_funct_1(k2_funct_1(k1_xboole_0)) = iProver_top
% 6.84/1.50      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_136]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_698,plain,( X0 = X0 ),theory(equality) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_731,plain,
% 6.84/1.50      ( k1_xboole_0 = k1_xboole_0 ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_698]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_701,plain,
% 6.84/1.50      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 6.84/1.50      theory(equality) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1606,plain,
% 6.84/1.50      ( v1_funct_1(X0) | ~ v1_funct_1(sK3) | X0 != sK3 ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_701]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1607,plain,
% 6.84/1.50      ( X0 != sK3
% 6.84/1.50      | v1_funct_1(X0) = iProver_top
% 6.84/1.50      | v1_funct_1(sK3) != iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_1606]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1609,plain,
% 6.84/1.50      ( k1_xboole_0 != sK3
% 6.84/1.50      | v1_funct_1(sK3) != iProver_top
% 6.84/1.50      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_1607]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_702,plain,
% 6.84/1.50      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 6.84/1.50      theory(equality) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1811,plain,
% 6.84/1.50      ( v1_relat_1(X0) | ~ v1_relat_1(sK3) | X0 != sK3 ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_702]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1818,plain,
% 6.84/1.50      ( X0 != sK3
% 6.84/1.50      | v1_relat_1(X0) = iProver_top
% 6.84/1.50      | v1_relat_1(sK3) != iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_1811]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1820,plain,
% 6.84/1.50      ( k1_xboole_0 != sK3
% 6.84/1.50      | v1_relat_1(sK3) != iProver_top
% 6.84/1.50      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_1818]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_699,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1835,plain,
% 6.84/1.50      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_699]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1836,plain,
% 6.84/1.50      ( sK3 != k1_xboole_0 | k1_xboole_0 = sK3 | k1_xboole_0 != k1_xboole_0 ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_1835]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_13329,plain,
% 6.84/1.50      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) = iProver_top ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_13315,c_7693]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_13331,plain,
% 6.84/1.50      ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK1)) = iProver_top ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_13315,c_7694]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_23906,plain,
% 6.84/1.50      ( k2_struct_0(sK1) = k1_xboole_0 ),
% 6.84/1.50      inference(global_propositional_subsumption,
% 6.84/1.50                [status(thm)],
% 6.84/1.50                [c_23887,c_41,c_43,c_138,c_731,c_1598,c_1609,c_1758,c_1820,
% 6.84/1.50                 c_1836,c_7693,c_7694,c_13289,c_13329,c_13331]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_23913,plain,
% 6.84/1.50      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) != k1_xboole_0
% 6.84/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_xboole_0,k1_xboole_0) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_23906,c_13328]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_42,plain,
% 6.84/1.50      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_2811,plain,
% 6.84/1.50      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_698]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_2816,plain,
% 6.84/1.50      ( X0 != X1 | X0 = u1_struct_0(sK2) | u1_struct_0(sK2) != X1 ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_699]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_2817,plain,
% 6.84/1.50      ( u1_struct_0(sK2) != k1_xboole_0
% 6.84/1.50      | k1_xboole_0 = u1_struct_0(sK2)
% 6.84/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_2816]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_711,plain,
% 6.84/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 6.84/1.50      | v1_funct_2(X3,X4,X5)
% 6.84/1.50      | X3 != X0
% 6.84/1.50      | X4 != X1
% 6.84/1.50      | X5 != X2 ),
% 6.84/1.50      theory(equality) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1749,plain,
% 6.84/1.50      ( v1_funct_2(X0,X1,X2)
% 6.84/1.50      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 6.84/1.50      | X2 != u1_struct_0(sK2)
% 6.84/1.50      | X1 != u1_struct_0(sK1)
% 6.84/1.50      | X0 != sK3 ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_711]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_1949,plain,
% 6.84/1.50      ( v1_funct_2(k2_funct_1(k2_funct_1(sK3)),X0,X1)
% 6.84/1.50      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 6.84/1.50      | X1 != u1_struct_0(sK2)
% 6.84/1.50      | X0 != u1_struct_0(sK1)
% 6.84/1.50      | k2_funct_1(k2_funct_1(sK3)) != sK3 ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_1749]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_2810,plain,
% 6.84/1.50      ( v1_funct_2(k2_funct_1(k2_funct_1(sK3)),X0,u1_struct_0(sK2))
% 6.84/1.50      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 6.84/1.50      | X0 != u1_struct_0(sK1)
% 6.84/1.50      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 6.84/1.50      | k2_funct_1(k2_funct_1(sK3)) != sK3 ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_1949]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_4784,plain,
% 6.84/1.50      ( v1_funct_2(k2_funct_1(k2_funct_1(sK3)),u1_struct_0(sK1),u1_struct_0(sK2))
% 6.84/1.50      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 6.84/1.50      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 6.84/1.50      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 6.84/1.50      | k2_funct_1(k2_funct_1(sK3)) != sK3 ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_2810]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_4786,plain,
% 6.84/1.50      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 6.84/1.50      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 6.84/1.50      | k2_funct_1(k2_funct_1(sK3)) != sK3
% 6.84/1.50      | v1_funct_2(k2_funct_1(k2_funct_1(sK3)),u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top
% 6.84/1.50      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_4784]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_4785,plain,
% 6.84/1.50      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_698]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_3161,plain,
% 6.84/1.50      ( X0 != X1
% 6.84/1.50      | X0 = k2_funct_1(k2_funct_1(sK3))
% 6.84/1.50      | k2_funct_1(k2_funct_1(sK3)) != X1 ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_699]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_6705,plain,
% 6.84/1.50      ( X0 = k2_funct_1(k2_funct_1(sK3))
% 6.84/1.50      | X0 != sK3
% 6.84/1.50      | k2_funct_1(k2_funct_1(sK3)) != sK3 ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_3161]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_6706,plain,
% 6.84/1.50      ( k2_funct_1(k2_funct_1(sK3)) != sK3
% 6.84/1.50      | k1_xboole_0 = k2_funct_1(k2_funct_1(sK3))
% 6.84/1.50      | k1_xboole_0 != sK3 ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_6705]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_2686,plain,
% 6.84/1.50      ( u1_struct_0(sK2) = k2_relat_1(sK3) ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_2660,c_436]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_7703,plain,
% 6.84/1.50      ( u1_struct_0(sK2) = k1_xboole_0 ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_7682,c_2686]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_8795,plain,
% 6.84/1.50      ( v1_funct_2(X0,X1,X2)
% 6.84/1.50      | ~ v1_funct_2(k2_funct_1(k2_funct_1(sK3)),u1_struct_0(sK1),u1_struct_0(sK2))
% 6.84/1.50      | X2 != u1_struct_0(sK2)
% 6.84/1.50      | X1 != u1_struct_0(sK1)
% 6.84/1.50      | X0 != k2_funct_1(k2_funct_1(sK3)) ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_711]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_8796,plain,
% 6.84/1.50      ( X0 != u1_struct_0(sK2)
% 6.84/1.50      | X1 != u1_struct_0(sK1)
% 6.84/1.50      | X2 != k2_funct_1(k2_funct_1(sK3))
% 6.84/1.50      | v1_funct_2(X2,X1,X0) = iProver_top
% 6.84/1.50      | v1_funct_2(k2_funct_1(k2_funct_1(sK3)),u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
% 6.84/1.50      inference(predicate_to_equality,[status(thm)],[c_8795]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_8798,plain,
% 6.84/1.50      ( k1_xboole_0 != u1_struct_0(sK2)
% 6.84/1.50      | k1_xboole_0 != u1_struct_0(sK1)
% 6.84/1.50      | k1_xboole_0 != k2_funct_1(k2_funct_1(sK3))
% 6.84/1.50      | v1_funct_2(k2_funct_1(k2_funct_1(sK3)),u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 6.84/1.50      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_8796]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_4788,plain,
% 6.84/1.50      ( X0 != X1 | X0 = u1_struct_0(sK1) | u1_struct_0(sK1) != X1 ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_699]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_12520,plain,
% 6.84/1.50      ( X0 = u1_struct_0(sK1)
% 6.84/1.50      | X0 != k2_struct_0(sK1)
% 6.84/1.50      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_4788]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_12521,plain,
% 6.84/1.50      ( u1_struct_0(sK1) != k2_struct_0(sK1)
% 6.84/1.50      | k1_xboole_0 = u1_struct_0(sK1)
% 6.84/1.50      | k1_xboole_0 != k2_struct_0(sK1) ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_12520]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_23562,plain,
% 6.84/1.50      ( X0 != X1 | X0 = k2_struct_0(sK1) | k2_struct_0(sK1) != X1 ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_699]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_23563,plain,
% 6.84/1.50      ( k2_struct_0(sK1) != k1_xboole_0
% 6.84/1.50      | k1_xboole_0 = k2_struct_0(sK1)
% 6.84/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 6.84/1.50      inference(instantiation,[status(thm)],[c_23562]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_13332,plain,
% 6.84/1.50      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(k1_xboole_0)) = k1_xboole_0
% 6.84/1.50      | k2_struct_0(sK1) != k1_relat_1(k1_xboole_0) ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_13315,c_7690]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_23919,plain,
% 6.84/1.50      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_xboole_0
% 6.84/1.50      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_23906,c_13332]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_23921,plain,
% 6.84/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_23906,c_13333]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_24858,plain,
% 6.84/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 6.84/1.50      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 6.84/1.50      inference(superposition,[status(thm)],[c_23921,c_1286]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_13335,plain,
% 6.84/1.50      ( k1_relset_1(k2_struct_0(sK1),k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_13315,c_7701]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_23923,plain,
% 6.84/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_23906,c_13335]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_24876,plain,
% 6.84/1.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 6.84/1.50      | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_24858,c_23923]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_25963,plain,
% 6.84/1.50      ( v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_xboole_0,k1_xboole_0) != iProver_top
% 6.84/1.50      | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 6.84/1.50      inference(global_propositional_subsumption,
% 6.84/1.50                [status(thm)],
% 6.84/1.50                [c_23913,c_36,c_41,c_42,c_34,c_43,c_32,c_138,c_441,c_731,
% 6.84/1.50                 c_1597,c_1598,c_1609,c_1642,c_1758,c_1820,c_1836,c_2811,
% 6.84/1.50                 c_2817,c_4786,c_4785,c_6706,c_7693,c_7694,c_7703,c_8798,
% 6.84/1.50                 c_12521,c_13289,c_13329,c_13331,c_23563,c_23887,c_23919,
% 6.84/1.50                 c_24876]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_24923,plain,
% 6.84/1.50      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 6.84/1.50      inference(global_propositional_subsumption,
% 6.84/1.50                [status(thm)],
% 6.84/1.50                [c_23919,c_36,c_41,c_42,c_34,c_43,c_32,c_138,c_441,c_731,
% 6.84/1.50                 c_1597,c_1598,c_1609,c_1642,c_1758,c_1820,c_1836,c_2811,
% 6.84/1.50                 c_2817,c_4786,c_4785,c_6706,c_7693,c_7694,c_7703,c_8798,
% 6.84/1.50                 c_12521,c_13289,c_13329,c_13331,c_23563,c_23887,c_24876]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_25967,plain,
% 6.84/1.50      ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top
% 6.84/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 6.84/1.50      inference(light_normalisation,[status(thm)],[c_25963,c_24923]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_13337,plain,
% 6.84/1.50      ( v1_funct_2(k1_xboole_0,k2_struct_0(sK1),k1_xboole_0) = iProver_top ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_13315,c_7702]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_23925,plain,
% 6.84/1.50      ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 6.84/1.50      inference(demodulation,[status(thm)],[c_23906,c_13337]) ).
% 6.84/1.50  
% 6.84/1.50  cnf(c_25970,plain,
% 6.84/1.50      ( $false ),
% 6.84/1.50      inference(forward_subsumption_resolution,
% 6.84/1.50                [status(thm)],
% 6.84/1.50                [c_25967,c_23921,c_23925]) ).
% 6.84/1.50  
% 6.84/1.50  
% 6.84/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 6.84/1.50  
% 6.84/1.50  ------                               Statistics
% 6.84/1.50  
% 6.84/1.50  ------ General
% 6.84/1.50  
% 6.84/1.50  abstr_ref_over_cycles:                  0
% 6.84/1.50  abstr_ref_under_cycles:                 0
% 6.84/1.50  gc_basic_clause_elim:                   0
% 6.84/1.50  forced_gc_time:                         0
% 6.84/1.50  parsing_time:                           0.008
% 6.84/1.50  unif_index_cands_time:                  0.
% 6.84/1.50  unif_index_add_time:                    0.
% 6.84/1.50  orderings_time:                         0.
% 6.84/1.50  out_proof_time:                         0.024
% 6.84/1.50  total_time:                             0.674
% 6.84/1.50  num_of_symbols:                         54
% 6.84/1.50  num_of_terms:                           27247
% 6.84/1.50  
% 6.84/1.50  ------ Preprocessing
% 6.84/1.50  
% 6.84/1.50  num_of_splits:                          1
% 6.84/1.50  num_of_split_atoms:                     1
% 6.84/1.50  num_of_reused_defs:                     0
% 6.84/1.50  num_eq_ax_congr_red:                    12
% 6.84/1.50  num_of_sem_filtered_clauses:            1
% 6.84/1.50  num_of_subtypes:                        0
% 6.84/1.50  monotx_restored_types:                  0
% 6.84/1.50  sat_num_of_epr_types:                   0
% 6.84/1.50  sat_num_of_non_cyclic_types:            0
% 6.84/1.50  sat_guarded_non_collapsed_types:        0
% 6.84/1.50  num_pure_diseq_elim:                    0
% 6.84/1.50  simp_replaced_by:                       0
% 6.84/1.50  res_preprocessed:                       179
% 6.84/1.50  prep_upred:                             0
% 6.84/1.50  prep_unflattend:                        5
% 6.84/1.50  smt_new_axioms:                         0
% 6.84/1.50  pred_elim_cands:                        5
% 6.84/1.50  pred_elim:                              2
% 6.84/1.50  pred_elim_cl:                           2
% 6.84/1.50  pred_elim_cycles:                       4
% 6.84/1.50  merged_defs:                            0
% 6.84/1.50  merged_defs_ncl:                        0
% 6.84/1.50  bin_hyper_res:                          0
% 6.84/1.50  prep_cycles:                            4
% 6.84/1.50  pred_elim_time:                         0.002
% 6.84/1.50  splitting_time:                         0.
% 6.84/1.50  sem_filter_time:                        0.
% 6.84/1.50  monotx_time:                            0.
% 6.84/1.50  subtype_inf_time:                       0.
% 6.84/1.50  
% 6.84/1.50  ------ Problem properties
% 6.84/1.50  
% 6.84/1.50  clauses:                                36
% 6.84/1.50  conjectures:                            5
% 6.84/1.50  epr:                                    2
% 6.84/1.50  horn:                                   32
% 6.84/1.50  ground:                                 8
% 6.84/1.50  unary:                                  11
% 6.84/1.50  binary:                                 3
% 6.84/1.50  lits:                                   106
% 6.84/1.50  lits_eq:                                23
% 6.84/1.50  fd_pure:                                0
% 6.84/1.50  fd_pseudo:                              0
% 6.84/1.50  fd_cond:                                3
% 6.84/1.50  fd_pseudo_cond:                         0
% 6.84/1.50  ac_symbols:                             0
% 6.84/1.50  
% 6.84/1.50  ------ Propositional Solver
% 6.84/1.50  
% 6.84/1.50  prop_solver_calls:                      30
% 6.84/1.50  prop_fast_solver_calls:                 2212
% 6.84/1.50  smt_solver_calls:                       0
% 6.84/1.50  smt_fast_solver_calls:                  0
% 6.84/1.50  prop_num_of_clauses:                    10318
% 6.84/1.50  prop_preprocess_simplified:             20861
% 6.84/1.50  prop_fo_subsumed:                       261
% 6.84/1.50  prop_solver_time:                       0.
% 6.84/1.50  smt_solver_time:                        0.
% 6.84/1.50  smt_fast_solver_time:                   0.
% 6.84/1.50  prop_fast_solver_time:                  0.
% 6.84/1.50  prop_unsat_core_time:                   0.
% 6.84/1.50  
% 6.84/1.50  ------ QBF
% 6.84/1.50  
% 6.84/1.50  qbf_q_res:                              0
% 6.84/1.50  qbf_num_tautologies:                    0
% 6.84/1.50  qbf_prep_cycles:                        0
% 6.84/1.50  
% 6.84/1.50  ------ BMC1
% 6.84/1.50  
% 6.84/1.50  bmc1_current_bound:                     -1
% 6.84/1.50  bmc1_last_solved_bound:                 -1
% 6.84/1.50  bmc1_unsat_core_size:                   -1
% 6.84/1.50  bmc1_unsat_core_parents_size:           -1
% 6.84/1.50  bmc1_merge_next_fun:                    0
% 6.84/1.50  bmc1_unsat_core_clauses_time:           0.
% 6.84/1.50  
% 6.84/1.50  ------ Instantiation
% 6.84/1.50  
% 6.84/1.50  inst_num_of_clauses:                    3054
% 6.84/1.50  inst_num_in_passive:                    879
% 6.84/1.50  inst_num_in_active:                     1005
% 6.84/1.50  inst_num_in_unprocessed:                1170
% 6.84/1.50  inst_num_of_loops:                      1180
% 6.84/1.50  inst_num_of_learning_restarts:          0
% 6.84/1.50  inst_num_moves_active_passive:          171
% 6.84/1.50  inst_lit_activity:                      0
% 6.84/1.50  inst_lit_activity_moves:                1
% 6.84/1.50  inst_num_tautologies:                   0
% 6.84/1.50  inst_num_prop_implied:                  0
% 6.84/1.50  inst_num_existing_simplified:           0
% 6.84/1.50  inst_num_eq_res_simplified:             0
% 6.84/1.50  inst_num_child_elim:                    0
% 6.84/1.50  inst_num_of_dismatching_blockings:      1364
% 6.84/1.50  inst_num_of_non_proper_insts:           2040
% 6.84/1.50  inst_num_of_duplicates:                 0
% 6.84/1.50  inst_inst_num_from_inst_to_res:         0
% 6.84/1.50  inst_dismatching_checking_time:         0.
% 6.84/1.50  
% 6.84/1.50  ------ Resolution
% 6.84/1.50  
% 6.84/1.50  res_num_of_clauses:                     0
% 6.84/1.50  res_num_in_passive:                     0
% 6.84/1.50  res_num_in_active:                      0
% 6.84/1.50  res_num_of_loops:                       183
% 6.84/1.50  res_forward_subset_subsumed:            120
% 6.84/1.50  res_backward_subset_subsumed:           8
% 6.84/1.50  res_forward_subsumed:                   0
% 6.84/1.50  res_backward_subsumed:                  0
% 6.84/1.50  res_forward_subsumption_resolution:     0
% 6.84/1.50  res_backward_subsumption_resolution:    0
% 6.84/1.50  res_clause_to_clause_subsumption:       1421
% 6.84/1.50  res_orphan_elimination:                 0
% 6.84/1.50  res_tautology_del:                      131
% 6.84/1.50  res_num_eq_res_simplified:              0
% 6.84/1.50  res_num_sel_changes:                    0
% 6.84/1.50  res_moves_from_active_to_pass:          0
% 6.84/1.50  
% 6.84/1.50  ------ Superposition
% 6.84/1.50  
% 6.84/1.50  sup_time_total:                         0.
% 6.84/1.50  sup_time_generating:                    0.
% 6.84/1.50  sup_time_sim_full:                      0.
% 6.84/1.50  sup_time_sim_immed:                     0.
% 6.84/1.50  
% 6.84/1.50  sup_num_of_clauses:                     191
% 6.84/1.50  sup_num_in_active:                      131
% 6.84/1.50  sup_num_in_passive:                     60
% 6.84/1.50  sup_num_of_loops:                       235
% 6.84/1.50  sup_fw_superposition:                   271
% 6.84/1.50  sup_bw_superposition:                   336
% 6.84/1.50  sup_immediate_simplified:               251
% 6.84/1.50  sup_given_eliminated:                   0
% 6.84/1.50  comparisons_done:                       0
% 6.84/1.50  comparisons_avoided:                    29
% 6.84/1.50  
% 6.84/1.50  ------ Simplifications
% 6.84/1.50  
% 6.84/1.50  
% 6.84/1.50  sim_fw_subset_subsumed:                 143
% 6.84/1.50  sim_bw_subset_subsumed:                 49
% 6.84/1.50  sim_fw_subsumed:                        34
% 6.84/1.50  sim_bw_subsumed:                        2
% 6.84/1.50  sim_fw_subsumption_res:                 27
% 6.84/1.50  sim_bw_subsumption_res:                 0
% 6.84/1.50  sim_tautology_del:                      6
% 6.84/1.50  sim_eq_tautology_del:                   130
% 6.84/1.50  sim_eq_res_simp:                        2
% 6.84/1.50  sim_fw_demodulated:                     7
% 6.84/1.50  sim_bw_demodulated:                     88
% 6.84/1.50  sim_light_normalised:                   116
% 6.84/1.50  sim_joinable_taut:                      0
% 6.84/1.50  sim_joinable_simp:                      0
% 6.84/1.50  sim_ac_normalised:                      0
% 6.84/1.50  sim_smt_subsumption:                    0
% 6.84/1.50  
%------------------------------------------------------------------------------
