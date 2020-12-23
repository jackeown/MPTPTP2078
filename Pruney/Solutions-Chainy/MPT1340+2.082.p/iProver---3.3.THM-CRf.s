%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:39 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_11000)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f20,plain,(
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
    inference(pure_predicate_removal,[],[f19])).

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
    inference(ennf_transformation,[],[f20])).

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

fof(f55,plain,(
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

fof(f54,plain,(
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

fof(f53,plain,
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

fof(f56,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3)
    & v2_funct_1(sK3)
    & k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_struct_0(sK2)
    & l1_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f48,f55,f54,f53])).

fof(f97,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f88,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f94,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f93,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f98,plain,(
    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f95,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f99,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f96,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f56])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f65,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f66,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f100,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f64,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f103,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f74])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f105,plain,(
    ! [X2,X1] :
      ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f71])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1654,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1651,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_31,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_42,negated_conjecture,
    ( l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_477,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_42])).

cnf(c_478,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_43,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_482,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_43])).

cnf(c_483,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_1706,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1651,c_478,c_483])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1672,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2715,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1706,c_1672])).

cnf(c_38,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1703,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_38,c_478,c_483])).

cnf(c_2785,plain,
    ( k2_struct_0(sK2) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_2715,c_1703])).

cnf(c_2787,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_2785,c_2715])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1656,plain,
    ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6006,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3)
    | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2787,c_1656])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_46,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_37,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_49,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2790,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2785,c_1706])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1650,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_1698,plain,
    ( v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1650,c_478,c_483])).

cnf(c_2791,plain,
    ( v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2785,c_1698])).

cnf(c_7187,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6006,c_46,c_49,c_2790,c_2791])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1655,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_7217,plain,
    ( v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7187,c_1655])).

cnf(c_8075,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7217,c_46,c_2790,c_2791])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_524,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_10,c_2])).

cnf(c_1646,plain,
    ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_8082,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK3)),k2_struct_0(sK1)) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8075,c_1646])).

cnf(c_1649,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1676,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5057,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1649,c_1676])).

cnf(c_2106,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2254,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_0,c_39])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2366,plain,
    ( v1_relat_1(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2254,c_3])).

cnf(c_5509,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5057,c_41,c_37,c_2106,c_2366])).

cnf(c_8101,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_struct_0(sK1)) = iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8082,c_5509])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2046,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2047,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2046])).

cnf(c_2367,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2366])).

cnf(c_9308,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8101,c_46,c_49,c_2047,c_2367])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1666,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5322,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_struct_0(sK1)
    | k2_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2790,c_1666])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1673,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3426,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2790,c_1673])).

cnf(c_5326,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5322,c_3426])).

cnf(c_5749,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | k2_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5326,c_2791])).

cnf(c_5750,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5749])).

cnf(c_8086,plain,
    ( k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = k2_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[status(thm)],[c_8075,c_1672])).

cnf(c_8088,plain,
    ( k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_8086,c_5509])).

cnf(c_8116,plain,
    ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = k2_funct_1(k2_funct_1(sK3))
    | k2_struct_0(sK1) != k1_relat_1(sK3)
    | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8088,c_1656])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1674,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3220,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1649,c_1674])).

cnf(c_2133,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3287,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3220,c_41,c_37,c_2133,c_2366])).

cnf(c_8123,plain,
    ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = sK3
    | k2_struct_0(sK1) != k1_relat_1(sK3)
    | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8116,c_3287])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2040,plain,
    ( ~ v1_funct_1(sK3)
    | v2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2041,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) = iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2040])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2043,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2044,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2043])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1660,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6388,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2787,c_1660])).

cnf(c_9322,plain,
    ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = sK3
    | k2_struct_0(sK1) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8123,c_46,c_49,c_2041,c_2044,c_2367,c_2790,c_2791,c_6388,c_7217])).

cnf(c_9326,plain,
    ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = sK3
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5750,c_9322])).

cnf(c_24,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_36,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_489,plain,
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
    inference(resolution_lifted,[status(thm)],[c_24,c_36])).

cnf(c_490,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)))
    | sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(unflattening,[status(thm)],[c_489])).

cnf(c_962,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)))
    | sP0_iProver_split
    | sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_490])).

cnf(c_1647,plain,
    ( sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_962])).

cnf(c_1918,plain,
    ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != sK3
    | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1647,c_478,c_483])).

cnf(c_961,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(X0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_490])).

cnf(c_1648,plain,
    ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_961])).

cnf(c_1845,plain,
    ( v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1648,c_478,c_483])).

cnf(c_1924,plain,
    ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != sK3
    | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1918,c_1845])).

cnf(c_2788,plain,
    ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) != sK3
    | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2785,c_1924])).

cnf(c_7195,plain,
    ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) != sK3
    | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7187,c_2788])).

cnf(c_9546,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9326,c_7195])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1653,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_tops_2(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_8083,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8075,c_1653])).

cnf(c_10993,plain,
    ( m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
    | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9546,c_46,c_49,c_2044,c_2367,c_2790,c_2791,c_6388,c_8083])).

cnf(c_10994,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_10993])).

cnf(c_11001,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9326,c_10994])).

cnf(c_11265,plain,
    ( v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11001,c_46,c_49,c_2044,c_2367,c_2790,c_2791,c_6388,c_7217,c_11000])).

cnf(c_11266,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_11265])).

cnf(c_11272,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9326,c_11266])).

cnf(c_11271,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1654,c_11266])).

cnf(c_11295,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11272,c_46,c_49,c_2044,c_2367,c_2790,c_2791,c_6388,c_7217,c_11271])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1675,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4651,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1649,c_1675])).

cnf(c_2130,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5501,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4651,c_41,c_37,c_2130,c_2366])).

cnf(c_28,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1658,plain,
    ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6148,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK3)),X0) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),X0))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5501,c_1658])).

cnf(c_6213,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),X0))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6148,c_5509])).

cnf(c_6416,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6213,c_46,c_49,c_2044,c_2047,c_2367])).

cnf(c_11316,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11295,c_6416])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1670,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5103,plain,
    ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | v1_funct_2(k2_tops_2(k1_xboole_0,X0,X1),X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1655,c_1670])).

cnf(c_23731,plain,
    ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5103,c_1654])).

cnf(c_23739,plain,
    ( k2_tops_2(k1_xboole_0,X0,k2_funct_1(sK3)) = k1_xboole_0
    | k1_xboole_0 = X0
    | v1_funct_2(k2_funct_1(sK3),k1_xboole_0,X0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11316,c_23731])).

cnf(c_29,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1657,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5504,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),X0) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5501,c_1657])).

cnf(c_5624,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),X0) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5504,c_46,c_49,c_2044,c_2047,c_2367])).

cnf(c_5630,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5624,c_5509])).

cnf(c_11317,plain,
    ( v1_funct_2(k2_funct_1(sK3),k1_xboole_0,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11295,c_5630])).

cnf(c_25389,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | k2_tops_2(k1_xboole_0,X0,k2_funct_1(sK3)) = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23739,c_46,c_49,c_2044,c_2367,c_11317])).

cnf(c_25390,plain,
    ( k2_tops_2(k1_xboole_0,X0,k2_funct_1(sK3)) = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_25389])).

cnf(c_25397,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) = k1_xboole_0
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9308,c_25390])).

cnf(c_11311,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) != sK3
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11295,c_7195])).

cnf(c_13527,plain,
    ( v1_funct_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8083,c_46,c_49,c_2044,c_2367,c_2790,c_2791,c_6388])).

cnf(c_13531,plain,
    ( v1_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13527,c_11295])).

cnf(c_14764,plain,
    ( m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
    | k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11311,c_13531])).

cnf(c_14765,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) != sK3
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_14764])).

cnf(c_25490,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | sK3 != k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_25397,c_14765])).

cnf(c_11322,plain,
    ( v1_funct_2(sK3,k2_struct_0(sK1),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11295,c_2791])).

cnf(c_11320,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11295,c_2790])).

cnf(c_12754,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,k2_struct_0(sK1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11320,c_1670])).

cnf(c_25625,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25490,c_11322,c_12754])).

cnf(c_25633,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_25397,c_25625])).

cnf(c_11307,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11295,c_8075])).

cnf(c_7218,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7187,c_1654])).

cnf(c_8016,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7218,c_46,c_49,c_2790,c_2791,c_6388])).

cnf(c_11308,plain,
    ( v1_funct_2(k2_funct_1(sK3),k1_xboole_0,k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11295,c_8016])).

cnf(c_25632,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
    | v1_funct_2(k2_funct_1(sK3),k1_xboole_0,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1655,c_25625])).

cnf(c_25976,plain,
    ( v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25633,c_46,c_49,c_2044,c_2367,c_11307,c_11308,c_25632])).

cnf(c_25977,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_25976])).

cnf(c_25982,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK3),k1_xboole_0,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1654,c_25977])).

cnf(c_26171,plain,
    ( k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25982,c_46,c_49,c_2044,c_2367,c_11307,c_11308])).

cnf(c_11319,plain,
    ( k1_relset_1(k2_struct_0(sK1),k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_11295,c_3426])).

cnf(c_26188,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_26171,c_11319])).

cnf(c_26192,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_26171,c_11320])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1667,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_26755,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_26192,c_1667])).

cnf(c_47,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_964,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_999,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_964])).

cnf(c_2688,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_964])).

cnf(c_965,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3511,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK2)
    | u1_struct_0(sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_3512,plain,
    ( u1_struct_0(sK2) != k1_xboole_0
    | k1_xboole_0 = u1_struct_0(sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3511])).

cnf(c_2527,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_3542,plain,
    ( X0 = u1_struct_0(sK1)
    | X0 != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2527])).

cnf(c_3543,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k1_xboole_0 = u1_struct_0(sK1)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3542])).

cnf(c_5493,plain,
    ( X0 != X1
    | X0 = k2_struct_0(sK1)
    | k2_struct_0(sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_5494,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 = k2_struct_0(sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5493])).

cnf(c_2792,plain,
    ( u1_struct_0(sK2) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_2785,c_478])).

cnf(c_11324,plain,
    ( u1_struct_0(sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11295,c_2792])).

cnf(c_978,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_2261,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | X2 != u1_struct_0(sK2)
    | X1 != u1_struct_0(sK1)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_978])).

cnf(c_22694,plain,
    ( v1_funct_2(sK3,X0,X1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | X1 != u1_struct_0(sK2)
    | X0 != u1_struct_0(sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2261])).

cnf(c_22695,plain,
    ( X0 != u1_struct_0(sK2)
    | X1 != u1_struct_0(sK1)
    | sK3 != sK3
    | v1_funct_2(sK3,X1,X0) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22694])).

cnf(c_22697,plain,
    ( sK3 != sK3
    | k1_xboole_0 != u1_struct_0(sK2)
    | k1_xboole_0 != u1_struct_0(sK1)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_22695])).

cnf(c_27391,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_26755,c_46,c_47,c_49,c_483,c_999,c_2044,c_2367,c_2688,c_3512,c_3543,c_5494,c_11307,c_11308,c_11324,c_22697,c_25982])).

cnf(c_30634,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_26188,c_27391])).

cnf(c_11304,plain,
    ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) = sK3
    | k2_struct_0(sK1) != k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_11295,c_9322])).

cnf(c_26191,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK3)) = sK3
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_26171,c_11304])).

cnf(c_48,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_2377,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),X0,X1)
    | m1_subset_1(k2_tops_2(X0,X1,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_2388,plain,
    ( v1_funct_2(k2_funct_1(sK3),X0,X1) != iProver_top
    | m1_subset_1(k2_tops_2(X0,X1,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2377])).

cnf(c_2390,plain,
    ( v1_funct_2(k2_funct_1(sK3),k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2388])).

cnf(c_2376,plain,
    ( v1_funct_2(k2_tops_2(X0,X1,k2_funct_1(sK3)),X1,X0)
    | ~ v1_funct_2(k2_funct_1(sK3),X0,X1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_2392,plain,
    ( v1_funct_2(k2_tops_2(X0,X1,k2_funct_1(sK3)),X1,X0) = iProver_top
    | v1_funct_2(k2_funct_1(sK3),X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2376])).

cnf(c_2394,plain,
    ( v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK3)),k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_funct_2(k2_funct_1(sK3),k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2392])).

cnf(c_2276,plain,
    ( v1_funct_2(k2_funct_1(sK3),X0,X1)
    | ~ v1_funct_2(sK3,X1,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k2_relset_1(X1,X0,sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2548,plain,
    ( v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2276])).

cnf(c_2549,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != u1_struct_0(sK2)
    | v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2548])).

cnf(c_972,plain,
    ( X0 != X1
    | k2_funct_1(X0) = k2_funct_1(X1) ),
    theory(equality)).

cnf(c_2701,plain,
    ( X0 != sK3
    | k2_funct_1(X0) = k2_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_4061,plain,
    ( k2_funct_1(sK3) = k2_funct_1(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2701])).

cnf(c_3205,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != X0
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
    | u1_struct_0(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_5251,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2)
    | u1_struct_0(sK2) != k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3205])).

cnf(c_3157,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1))
    | X1 != u1_struct_0(sK2)
    | X2 != u1_struct_0(sK1)
    | X0 != k2_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_978])).

cnf(c_24356,plain,
    ( v1_funct_2(k2_funct_1(sK3),X0,X1)
    | ~ v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1))
    | X0 != u1_struct_0(sK2)
    | X1 != u1_struct_0(sK1)
    | k2_funct_1(sK3) != k2_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3157])).

cnf(c_24357,plain,
    ( X0 != u1_struct_0(sK2)
    | X1 != u1_struct_0(sK1)
    | k2_funct_1(sK3) != k2_funct_1(sK3)
    | v1_funct_2(k2_funct_1(sK3),X0,X1) = iProver_top
    | v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24356])).

cnf(c_24359,plain,
    ( k2_funct_1(sK3) != k2_funct_1(sK3)
    | k1_xboole_0 != u1_struct_0(sK2)
    | k1_xboole_0 != u1_struct_0(sK1)
    | v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_funct_1(sK3),k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_24357])).

cnf(c_26184,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_26171,c_11307])).

cnf(c_26187,plain,
    ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK3)) != sK3
    | v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK3)),k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_26171,c_14765])).

cnf(c_28304,plain,
    ( k1_relat_1(sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_26191,c_46,c_47,c_48,c_38,c_49,c_478,c_483,c_999,c_2044,c_2367,c_2390,c_2394,c_2549,c_2688,c_3512,c_3543,c_4061,c_5251,c_5494,c_11307,c_11308,c_11324,c_24359,c_25982,c_26184,c_26187])).

cnf(c_30636,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_30634,c_28304])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.65/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/1.49  
% 7.65/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.65/1.49  
% 7.65/1.49  ------  iProver source info
% 7.65/1.49  
% 7.65/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.65/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.65/1.49  git: non_committed_changes: false
% 7.65/1.49  git: last_make_outside_of_git: false
% 7.65/1.49  
% 7.65/1.49  ------ 
% 7.65/1.49  ------ Parsing...
% 7.65/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.49  ------ Proving...
% 7.65/1.49  ------ Problem Properties 
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  clauses                                 40
% 7.65/1.49  conjectures                             5
% 7.65/1.49  EPR                                     2
% 7.65/1.49  Horn                                    36
% 7.65/1.49  unary                                   13
% 7.65/1.49  binary                                  2
% 7.65/1.49  lits                                    121
% 7.65/1.49  lits eq                                 23
% 7.65/1.49  fd_pure                                 0
% 7.65/1.49  fd_pseudo                               0
% 7.65/1.49  fd_cond                                 3
% 7.65/1.49  fd_pseudo_cond                          0
% 7.65/1.49  AC symbols                              0
% 7.65/1.49  
% 7.65/1.49  ------ Input Options Time Limit: Unbounded
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ 
% 7.65/1.49  Current options:
% 7.65/1.49  ------ 
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Proving...
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  % SZS status Theorem for theBenchmark.p
% 7.65/1.49  
% 7.65/1.49   Resolution empty clause
% 7.65/1.49  
% 7.65/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.65/1.49  
% 7.65/1.49  fof(f17,axiom,(
% 7.65/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 7.65/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f45,plain,(
% 7.65/1.49    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.65/1.49    inference(ennf_transformation,[],[f17])).
% 7.65/1.49  
% 7.65/1.49  fof(f46,plain,(
% 7.65/1.49    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.65/1.49    inference(flattening,[],[f45])).
% 7.65/1.49  
% 7.65/1.49  fof(f91,plain,(
% 7.65/1.49    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f46])).
% 7.65/1.49  
% 7.65/1.49  fof(f18,conjecture,(
% 7.65/1.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f19,negated_conjecture,(
% 7.65/1.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 7.65/1.50    inference(negated_conjecture,[],[f18])).
% 7.65/1.50  
% 7.65/1.50  fof(f20,plain,(
% 7.65/1.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 7.65/1.50    inference(pure_predicate_removal,[],[f19])).
% 7.65/1.50  
% 7.65/1.50  fof(f47,plain,(
% 7.65/1.50    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 7.65/1.50    inference(ennf_transformation,[],[f20])).
% 7.65/1.50  
% 7.65/1.50  fof(f48,plain,(
% 7.65/1.50    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 7.65/1.50    inference(flattening,[],[f47])).
% 7.65/1.50  
% 7.65/1.50  fof(f55,plain,(
% 7.65/1.50    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK3)),sK3) & v2_funct_1(sK3) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3) = k2_struct_0(X1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 7.65/1.50    introduced(choice_axiom,[])).
% 7.65/1.50  
% 7.65/1.50  fof(f54,plain,(
% 7.65/1.50    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK2),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2) = k2_struct_0(sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_struct_0(sK2))) )),
% 7.65/1.50    introduced(choice_axiom,[])).
% 7.65/1.50  
% 7.65/1.50  fof(f53,plain,(
% 7.65/1.50    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK1))),
% 7.65/1.50    introduced(choice_axiom,[])).
% 7.65/1.50  
% 7.65/1.50  fof(f56,plain,(
% 7.65/1.50    ((~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3) & v2_funct_1(sK3) & k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_struct_0(sK2)) & l1_struct_0(sK1)),
% 7.65/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f48,f55,f54,f53])).
% 7.65/1.50  
% 7.65/1.50  fof(f97,plain,(
% 7.65/1.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 7.65/1.50    inference(cnf_transformation,[],[f56])).
% 7.65/1.50  
% 7.65/1.50  fof(f15,axiom,(
% 7.65/1.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f42,plain,(
% 7.65/1.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.65/1.50    inference(ennf_transformation,[],[f15])).
% 7.65/1.50  
% 7.65/1.50  fof(f88,plain,(
% 7.65/1.50    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f42])).
% 7.65/1.50  
% 7.65/1.50  fof(f94,plain,(
% 7.65/1.50    l1_struct_0(sK2)),
% 7.65/1.50    inference(cnf_transformation,[],[f56])).
% 7.65/1.50  
% 7.65/1.50  fof(f93,plain,(
% 7.65/1.50    l1_struct_0(sK1)),
% 7.65/1.50    inference(cnf_transformation,[],[f56])).
% 7.65/1.50  
% 7.65/1.50  fof(f9,axiom,(
% 7.65/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f33,plain,(
% 7.65/1.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.50    inference(ennf_transformation,[],[f9])).
% 7.65/1.50  
% 7.65/1.50  fof(f69,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f33])).
% 7.65/1.50  
% 7.65/1.50  fof(f98,plain,(
% 7.65/1.50    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2)),
% 7.65/1.50    inference(cnf_transformation,[],[f56])).
% 7.65/1.50  
% 7.65/1.50  fof(f16,axiom,(
% 7.65/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f43,plain,(
% 7.65/1.50    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.65/1.50    inference(ennf_transformation,[],[f16])).
% 7.65/1.50  
% 7.65/1.50  fof(f44,plain,(
% 7.65/1.50    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.65/1.50    inference(flattening,[],[f43])).
% 7.65/1.50  
% 7.65/1.50  fof(f89,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f44])).
% 7.65/1.50  
% 7.65/1.50  fof(f95,plain,(
% 7.65/1.50    v1_funct_1(sK3)),
% 7.65/1.50    inference(cnf_transformation,[],[f56])).
% 7.65/1.50  
% 7.65/1.50  fof(f99,plain,(
% 7.65/1.50    v2_funct_1(sK3)),
% 7.65/1.50    inference(cnf_transformation,[],[f56])).
% 7.65/1.50  
% 7.65/1.50  fof(f96,plain,(
% 7.65/1.50    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 7.65/1.50    inference(cnf_transformation,[],[f56])).
% 7.65/1.50  
% 7.65/1.50  fof(f92,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f46])).
% 7.65/1.50  
% 7.65/1.50  fof(f7,axiom,(
% 7.65/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f21,plain,(
% 7.65/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.65/1.50    inference(pure_predicate_removal,[],[f7])).
% 7.65/1.50  
% 7.65/1.50  fof(f31,plain,(
% 7.65/1.50    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.50    inference(ennf_transformation,[],[f21])).
% 7.65/1.50  
% 7.65/1.50  fof(f67,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f31])).
% 7.65/1.50  
% 7.65/1.50  fof(f2,axiom,(
% 7.65/1.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f24,plain,(
% 7.65/1.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.65/1.50    inference(ennf_transformation,[],[f2])).
% 7.65/1.50  
% 7.65/1.50  fof(f49,plain,(
% 7.65/1.50    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.65/1.50    inference(nnf_transformation,[],[f24])).
% 7.65/1.50  
% 7.65/1.50  fof(f58,plain,(
% 7.65/1.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f49])).
% 7.65/1.50  
% 7.65/1.50  fof(f5,axiom,(
% 7.65/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f27,plain,(
% 7.65/1.50    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.65/1.50    inference(ennf_transformation,[],[f5])).
% 7.65/1.50  
% 7.65/1.50  fof(f28,plain,(
% 7.65/1.50    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(flattening,[],[f27])).
% 7.65/1.50  
% 7.65/1.50  fof(f65,plain,(
% 7.65/1.50    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f28])).
% 7.65/1.50  
% 7.65/1.50  fof(f1,axiom,(
% 7.65/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f23,plain,(
% 7.65/1.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(ennf_transformation,[],[f1])).
% 7.65/1.50  
% 7.65/1.50  fof(f57,plain,(
% 7.65/1.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f23])).
% 7.65/1.50  
% 7.65/1.50  fof(f3,axiom,(
% 7.65/1.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f60,plain,(
% 7.65/1.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f3])).
% 7.65/1.50  
% 7.65/1.50  fof(f4,axiom,(
% 7.65/1.50    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f25,plain,(
% 7.65/1.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.65/1.50    inference(ennf_transformation,[],[f4])).
% 7.65/1.50  
% 7.65/1.50  fof(f26,plain,(
% 7.65/1.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(flattening,[],[f25])).
% 7.65/1.50  
% 7.65/1.50  fof(f61,plain,(
% 7.65/1.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f26])).
% 7.65/1.50  
% 7.65/1.50  fof(f10,axiom,(
% 7.65/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f34,plain,(
% 7.65/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.50    inference(ennf_transformation,[],[f10])).
% 7.65/1.50  
% 7.65/1.50  fof(f35,plain,(
% 7.65/1.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.50    inference(flattening,[],[f34])).
% 7.65/1.50  
% 7.65/1.50  fof(f50,plain,(
% 7.65/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.50    inference(nnf_transformation,[],[f35])).
% 7.65/1.50  
% 7.65/1.50  fof(f70,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f50])).
% 7.65/1.50  
% 7.65/1.50  fof(f8,axiom,(
% 7.65/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f32,plain,(
% 7.65/1.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.50    inference(ennf_transformation,[],[f8])).
% 7.65/1.50  
% 7.65/1.50  fof(f68,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f32])).
% 7.65/1.50  
% 7.65/1.50  fof(f6,axiom,(
% 7.65/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f29,plain,(
% 7.65/1.50    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.65/1.50    inference(ennf_transformation,[],[f6])).
% 7.65/1.50  
% 7.65/1.50  fof(f30,plain,(
% 7.65/1.50    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(flattening,[],[f29])).
% 7.65/1.50  
% 7.65/1.50  fof(f66,plain,(
% 7.65/1.50    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f30])).
% 7.65/1.50  
% 7.65/1.50  fof(f63,plain,(
% 7.65/1.50    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f26])).
% 7.65/1.50  
% 7.65/1.50  fof(f62,plain,(
% 7.65/1.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f26])).
% 7.65/1.50  
% 7.65/1.50  fof(f13,axiom,(
% 7.65/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f38,plain,(
% 7.65/1.50    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.65/1.50    inference(ennf_transformation,[],[f13])).
% 7.65/1.50  
% 7.65/1.50  fof(f39,plain,(
% 7.65/1.50    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.65/1.50    inference(flattening,[],[f38])).
% 7.65/1.50  
% 7.65/1.50  fof(f83,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f39])).
% 7.65/1.50  
% 7.65/1.50  fof(f12,axiom,(
% 7.65/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f36,plain,(
% 7.65/1.50    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.65/1.50    inference(ennf_transformation,[],[f12])).
% 7.65/1.50  
% 7.65/1.50  fof(f37,plain,(
% 7.65/1.50    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.65/1.50    inference(flattening,[],[f36])).
% 7.65/1.50  
% 7.65/1.50  fof(f81,plain,(
% 7.65/1.50    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f37])).
% 7.65/1.50  
% 7.65/1.50  fof(f100,plain,(
% 7.65/1.50    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3)),
% 7.65/1.50    inference(cnf_transformation,[],[f56])).
% 7.65/1.50  
% 7.65/1.50  fof(f90,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f46])).
% 7.65/1.50  
% 7.65/1.50  fof(f64,plain,(
% 7.65/1.50    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f28])).
% 7.65/1.50  
% 7.65/1.50  fof(f14,axiom,(
% 7.65/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f40,plain,(
% 7.65/1.50    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.65/1.50    inference(ennf_transformation,[],[f14])).
% 7.65/1.50  
% 7.65/1.50  fof(f41,plain,(
% 7.65/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.65/1.50    inference(flattening,[],[f40])).
% 7.65/1.50  
% 7.65/1.50  fof(f87,plain,(
% 7.65/1.50    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f41])).
% 7.65/1.50  
% 7.65/1.50  fof(f74,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f50])).
% 7.65/1.50  
% 7.65/1.50  fof(f103,plain,(
% 7.65/1.50    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.65/1.50    inference(equality_resolution,[],[f74])).
% 7.65/1.50  
% 7.65/1.50  fof(f86,plain,(
% 7.65/1.50    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f41])).
% 7.65/1.50  
% 7.65/1.50  fof(f71,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f50])).
% 7.65/1.50  
% 7.65/1.50  fof(f105,plain,(
% 7.65/1.50    ( ! [X2,X1] : (k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0 | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.65/1.50    inference(equality_resolution,[],[f71])).
% 7.65/1.50  
% 7.65/1.50  cnf(c_34,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.65/1.50      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | ~ v1_funct_1(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1654,plain,
% 7.65/1.50      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.65/1.50      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
% 7.65/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.65/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_39,negated_conjecture,
% 7.65/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 7.65/1.50      inference(cnf_transformation,[],[f97]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1651,plain,
% 7.65/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_31,plain,
% 7.65/1.50      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_42,negated_conjecture,
% 7.65/1.50      ( l1_struct_0(sK2) ),
% 7.65/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_477,plain,
% 7.65/1.50      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 7.65/1.50      inference(resolution_lifted,[status(thm)],[c_31,c_42]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_478,plain,
% 7.65/1.50      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 7.65/1.50      inference(unflattening,[status(thm)],[c_477]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_43,negated_conjecture,
% 7.65/1.50      ( l1_struct_0(sK1) ),
% 7.65/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_482,plain,
% 7.65/1.50      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 7.65/1.50      inference(resolution_lifted,[status(thm)],[c_31,c_43]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_483,plain,
% 7.65/1.50      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 7.65/1.50      inference(unflattening,[status(thm)],[c_482]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1706,plain,
% 7.65/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) = iProver_top ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_1651,c_478,c_483]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_12,plain,
% 7.65/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1672,plain,
% 7.65/1.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.65/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2715,plain,
% 7.65/1.50      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3) ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1706,c_1672]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_38,negated_conjecture,
% 7.65/1.50      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
% 7.65/1.50      inference(cnf_transformation,[],[f98]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1703,plain,
% 7.65/1.50      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_38,c_478,c_483]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2785,plain,
% 7.65/1.50      ( k2_struct_0(sK2) = k2_relat_1(sK3) ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_2715,c_1703]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2787,plain,
% 7.65/1.50      ( k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_relat_1(sK3) ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_2785,c_2715]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_32,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | ~ v2_funct_1(X0)
% 7.65/1.50      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 7.65/1.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 7.65/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1656,plain,
% 7.65/1.50      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
% 7.65/1.50      | k2_relset_1(X0,X1,X2) != X1
% 7.65/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.65/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.50      | v1_funct_1(X2) != iProver_top
% 7.65/1.50      | v2_funct_1(X2) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6006,plain,
% 7.65/1.50      ( k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3)
% 7.65/1.50      | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 7.65/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
% 7.65/1.50      | v1_funct_1(sK3) != iProver_top
% 7.65/1.50      | v2_funct_1(sK3) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_2787,c_1656]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_41,negated_conjecture,
% 7.65/1.50      ( v1_funct_1(sK3) ),
% 7.65/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_46,plain,
% 7.65/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_37,negated_conjecture,
% 7.65/1.50      ( v2_funct_1(sK3) ),
% 7.65/1.50      inference(cnf_transformation,[],[f99]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_49,plain,
% 7.65/1.50      ( v2_funct_1(sK3) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2790,plain,
% 7.65/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) = iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_2785,c_1706]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_40,negated_conjecture,
% 7.65/1.50      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f96]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1650,plain,
% 7.65/1.50      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1698,plain,
% 7.65/1.50      ( v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) = iProver_top ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_1650,c_478,c_483]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2791,plain,
% 7.65/1.50      ( v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) = iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_2785,c_1698]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_7187,plain,
% 7.65/1.50      ( k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_funct_1(sK3) ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_6006,c_46,c_49,c_2790,c_2791]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_33,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.65/1.50      | ~ v1_funct_1(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1655,plain,
% 7.65/1.50      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.65/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 7.65/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_7217,plain,
% 7.65/1.50      ( v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) = iProver_top
% 7.65/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
% 7.65/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_7187,c_1655]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8075,plain,
% 7.65/1.50      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) = iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_7217,c_46,c_2790,c_2791]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_10,plain,
% 7.65/1.50      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.65/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2,plain,
% 7.65/1.50      ( r1_tarski(k2_relat_1(X0),X1) | ~ v5_relat_1(X0,X1) | ~ v1_relat_1(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_524,plain,
% 7.65/1.50      ( r1_tarski(k2_relat_1(X0),X1)
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.65/1.50      | ~ v1_relat_1(X0) ),
% 7.65/1.50      inference(resolution,[status(thm)],[c_10,c_2]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1646,plain,
% 7.65/1.50      ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 7.65/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 7.65/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8082,plain,
% 7.65/1.50      ( r1_tarski(k2_relat_1(k2_funct_1(sK3)),k2_struct_0(sK1)) = iProver_top
% 7.65/1.50      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_8075,c_1646]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1649,plain,
% 7.65/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_7,plain,
% 7.65/1.50      ( ~ v1_funct_1(X0)
% 7.65/1.50      | ~ v2_funct_1(X0)
% 7.65/1.50      | ~ v1_relat_1(X0)
% 7.65/1.50      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1676,plain,
% 7.65/1.50      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 7.65/1.50      | v1_funct_1(X0) != iProver_top
% 7.65/1.50      | v2_funct_1(X0) != iProver_top
% 7.65/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5057,plain,
% 7.65/1.50      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 7.65/1.50      | v2_funct_1(sK3) != iProver_top
% 7.65/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1649,c_1676]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2106,plain,
% 7.65/1.50      ( ~ v1_funct_1(sK3)
% 7.65/1.50      | ~ v2_funct_1(sK3)
% 7.65/1.50      | ~ v1_relat_1(sK3)
% 7.65/1.50      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_0,plain,
% 7.65/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2254,plain,
% 7.65/1.50      ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
% 7.65/1.50      | v1_relat_1(sK3) ),
% 7.65/1.50      inference(resolution,[status(thm)],[c_0,c_39]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3,plain,
% 7.65/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2366,plain,
% 7.65/1.50      ( v1_relat_1(sK3) ),
% 7.65/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_2254,c_3]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5509,plain,
% 7.65/1.50      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_5057,c_41,c_37,c_2106,c_2366]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8101,plain,
% 7.65/1.50      ( r1_tarski(k1_relat_1(sK3),k2_struct_0(sK1)) = iProver_top
% 7.65/1.50      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_8082,c_5509]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6,plain,
% 7.65/1.50      ( ~ v1_funct_1(X0)
% 7.65/1.50      | ~ v2_funct_1(X0)
% 7.65/1.50      | ~ v1_relat_1(X0)
% 7.65/1.50      | v1_relat_1(k2_funct_1(X0)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2046,plain,
% 7.65/1.50      ( ~ v1_funct_1(sK3)
% 7.65/1.50      | ~ v2_funct_1(sK3)
% 7.65/1.50      | v1_relat_1(k2_funct_1(sK3))
% 7.65/1.50      | ~ v1_relat_1(sK3) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2047,plain,
% 7.65/1.50      ( v1_funct_1(sK3) != iProver_top
% 7.65/1.50      | v2_funct_1(sK3) != iProver_top
% 7.65/1.50      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 7.65/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_2046]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2367,plain,
% 7.65/1.50      ( v1_relat_1(sK3) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_2366]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_9308,plain,
% 7.65/1.50      ( r1_tarski(k1_relat_1(sK3),k2_struct_0(sK1)) = iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_8101,c_46,c_49,c_2047,c_2367]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_18,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.65/1.50      | k1_xboole_0 = X2 ),
% 7.65/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1666,plain,
% 7.65/1.50      ( k1_relset_1(X0,X1,X2) = X0
% 7.65/1.50      | k1_xboole_0 = X1
% 7.65/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.65/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5322,plain,
% 7.65/1.50      ( k1_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k2_struct_0(sK1)
% 7.65/1.50      | k2_relat_1(sK3) = k1_xboole_0
% 7.65/1.50      | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_2790,c_1666]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11,plain,
% 7.65/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1673,plain,
% 7.65/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.65/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3426,plain,
% 7.65/1.50      ( k1_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) = k1_relat_1(sK3) ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_2790,c_1673]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5326,plain,
% 7.65/1.50      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 7.65/1.50      | k2_relat_1(sK3) = k1_xboole_0
% 7.65/1.50      | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_5322,c_3426]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5749,plain,
% 7.65/1.50      ( k2_relat_1(sK3) = k1_xboole_0 | k2_struct_0(sK1) = k1_relat_1(sK3) ),
% 7.65/1.50      inference(global_propositional_subsumption,[status(thm)],[c_5326,c_2791]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5750,plain,
% 7.65/1.50      ( k2_struct_0(sK1) = k1_relat_1(sK3) | k2_relat_1(sK3) = k1_xboole_0 ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_5749]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8086,plain,
% 7.65/1.50      ( k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = k2_relat_1(k2_funct_1(sK3)) ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_8075,c_1672]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8088,plain,
% 7.65/1.50      ( k2_relset_1(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_8086,c_5509]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8116,plain,
% 7.65/1.50      ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = k2_funct_1(k2_funct_1(sK3))
% 7.65/1.50      | k2_struct_0(sK1) != k1_relat_1(sK3)
% 7.65/1.50      | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) != iProver_top
% 7.65/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.65/1.50      | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_8088,c_1656]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_9,plain,
% 7.65/1.50      ( ~ v1_funct_1(X0)
% 7.65/1.50      | ~ v2_funct_1(X0)
% 7.65/1.50      | ~ v1_relat_1(X0)
% 7.65/1.50      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1674,plain,
% 7.65/1.50      ( k2_funct_1(k2_funct_1(X0)) = X0
% 7.65/1.50      | v1_funct_1(X0) != iProver_top
% 7.65/1.50      | v2_funct_1(X0) != iProver_top
% 7.65/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3220,plain,
% 7.65/1.50      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 7.65/1.50      | v2_funct_1(sK3) != iProver_top
% 7.65/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1649,c_1674]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2133,plain,
% 7.65/1.50      ( ~ v1_funct_1(sK3)
% 7.65/1.50      | ~ v2_funct_1(sK3)
% 7.65/1.50      | ~ v1_relat_1(sK3)
% 7.65/1.50      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3287,plain,
% 7.65/1.50      ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_3220,c_41,c_37,c_2133,c_2366]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8123,plain,
% 7.65/1.50      ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = sK3
% 7.65/1.50      | k2_struct_0(sK1) != k1_relat_1(sK3)
% 7.65/1.50      | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) != iProver_top
% 7.65/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.65/1.50      | v2_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_8116,c_3287]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4,plain,
% 7.65/1.50      ( ~ v1_funct_1(X0)
% 7.65/1.50      | ~ v2_funct_1(X0)
% 7.65/1.50      | v2_funct_1(k2_funct_1(X0))
% 7.65/1.50      | ~ v1_relat_1(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2040,plain,
% 7.65/1.50      ( ~ v1_funct_1(sK3)
% 7.65/1.50      | v2_funct_1(k2_funct_1(sK3))
% 7.65/1.50      | ~ v2_funct_1(sK3)
% 7.65/1.50      | ~ v1_relat_1(sK3) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2041,plain,
% 7.65/1.50      ( v1_funct_1(sK3) != iProver_top
% 7.65/1.50      | v2_funct_1(k2_funct_1(sK3)) = iProver_top
% 7.65/1.50      | v2_funct_1(sK3) != iProver_top
% 7.65/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_2040]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5,plain,
% 7.65/1.50      ( ~ v1_funct_1(X0)
% 7.65/1.50      | v1_funct_1(k2_funct_1(X0))
% 7.65/1.50      | ~ v2_funct_1(X0)
% 7.65/1.50      | ~ v1_relat_1(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2043,plain,
% 7.65/1.50      ( v1_funct_1(k2_funct_1(sK3))
% 7.65/1.50      | ~ v1_funct_1(sK3)
% 7.65/1.50      | ~ v2_funct_1(sK3)
% 7.65/1.50      | ~ v1_relat_1(sK3) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2044,plain,
% 7.65/1.50      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 7.65/1.50      | v1_funct_1(sK3) != iProver_top
% 7.65/1.50      | v2_funct_1(sK3) != iProver_top
% 7.65/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_2043]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_26,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.65/1.50      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | ~ v2_funct_1(X0)
% 7.65/1.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 7.65/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1660,plain,
% 7.65/1.50      ( k2_relset_1(X0,X1,X2) != X1
% 7.65/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.65/1.50      | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
% 7.65/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.50      | v1_funct_1(X2) != iProver_top
% 7.65/1.50      | v2_funct_1(X2) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6388,plain,
% 7.65/1.50      ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) = iProver_top
% 7.65/1.50      | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 7.65/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
% 7.65/1.50      | v1_funct_1(sK3) != iProver_top
% 7.65/1.50      | v2_funct_1(sK3) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_2787,c_1660]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_9322,plain,
% 7.65/1.50      ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = sK3
% 7.65/1.50      | k2_struct_0(sK1) != k1_relat_1(sK3) ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_8123,c_46,c_49,c_2041,c_2044,c_2367,c_2790,c_2791,c_6388,
% 7.65/1.50                 c_7217]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_9326,plain,
% 7.65/1.50      ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) = sK3
% 7.65/1.50      | k2_relat_1(sK3) = k1_xboole_0 ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_5750,c_9322]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_24,plain,
% 7.65/1.50      ( r2_funct_2(X0,X1,X2,X2)
% 7.65/1.50      | ~ v1_funct_2(X2,X0,X1)
% 7.65/1.50      | ~ v1_funct_2(X3,X0,X1)
% 7.65/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.65/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.65/1.50      | ~ v1_funct_1(X3)
% 7.65/1.50      | ~ v1_funct_1(X2) ),
% 7.65/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_36,negated_conjecture,
% 7.65/1.50      ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3) ),
% 7.65/1.50      inference(cnf_transformation,[],[f100]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_489,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.65/1.50      | ~ v1_funct_2(X3,X1,X2)
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | ~ v1_funct_1(X3)
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != X0
% 7.65/1.50      | u1_struct_0(sK2) != X2
% 7.65/1.50      | u1_struct_0(sK1) != X1
% 7.65/1.50      | sK3 != X0 ),
% 7.65/1.50      inference(resolution_lifted,[status(thm)],[c_24,c_36]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_490,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
% 7.65/1.50      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2))
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 7.65/1.50      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)))
% 7.65/1.50      | sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
% 7.65/1.50      inference(unflattening,[status(thm)],[c_489]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_962,plain,
% 7.65/1.50      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2))
% 7.65/1.50      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 7.65/1.50      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)))
% 7.65/1.50      | sP0_iProver_split
% 7.65/1.50      | sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
% 7.65/1.50      inference(splitting,
% 7.65/1.50                [splitting(split),new_symbols(definition,[])],
% 7.65/1.50                [c_490]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1647,plain,
% 7.65/1.50      ( sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
% 7.65/1.50      | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 7.65/1.50      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) != iProver_top
% 7.65/1.50      | sP0_iProver_split = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_962]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1918,plain,
% 7.65/1.50      ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != sK3
% 7.65/1.50      | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
% 7.65/1.50      | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))) != iProver_top
% 7.65/1.50      | sP0_iProver_split = iProver_top ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_1647,c_478,c_483]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_961,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | ~ sP0_iProver_split ),
% 7.65/1.50      inference(splitting,
% 7.65/1.50                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.65/1.50                [c_490]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1648,plain,
% 7.65/1.50      ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 7.65/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 7.65/1.50      | v1_funct_1(X0) != iProver_top
% 7.65/1.50      | sP0_iProver_split != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_961]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1845,plain,
% 7.65/1.50      ( v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
% 7.65/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
% 7.65/1.50      | v1_funct_1(X0) != iProver_top
% 7.65/1.50      | sP0_iProver_split != iProver_top ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_1648,c_478,c_483]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1924,plain,
% 7.65/1.50      ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != sK3
% 7.65/1.50      | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
% 7.65/1.50      | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))) != iProver_top ),
% 7.65/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_1918,c_1845]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2788,plain,
% 7.65/1.50      ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) != sK3
% 7.65/1.50      | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
% 7.65/1.50      | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))) != iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_2785,c_1924]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_7195,plain,
% 7.65/1.50      ( k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)) != sK3
% 7.65/1.50      | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
% 7.65/1.50      | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))) != iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_7187,c_2788]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_9546,plain,
% 7.65/1.50      ( k2_relat_1(sK3) = k1_xboole_0
% 7.65/1.50      | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
% 7.65/1.50      | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_9326,c_7195]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_35,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1653,plain,
% 7.65/1.50      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.65/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.65/1.50      | v1_funct_1(X0) != iProver_top
% 7.65/1.50      | v1_funct_1(k2_tops_2(X1,X2,X0)) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8083,plain,
% 7.65/1.50      ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) != iProver_top
% 7.65/1.50      | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))) = iProver_top
% 7.65/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_8075,c_1653]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_10993,plain,
% 7.65/1.50      ( m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
% 7.65/1.50      | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 7.65/1.50      | k2_relat_1(sK3) = k1_xboole_0 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_9546,c_46,c_49,c_2044,c_2367,c_2790,c_2791,c_6388,c_8083]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_10994,plain,
% 7.65/1.50      ( k2_relat_1(sK3) = k1_xboole_0
% 7.65/1.50      | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_10993]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11001,plain,
% 7.65/1.50      ( k2_relat_1(sK3) = k1_xboole_0
% 7.65/1.50      | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 7.65/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_9326,c_10994]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11265,plain,
% 7.65/1.50      ( v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 7.65/1.50      | k2_relat_1(sK3) = k1_xboole_0 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_11001,c_46,c_49,c_2044,c_2367,c_2790,c_2791,c_6388,c_7217,
% 7.65/1.50                 c_11000]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11266,plain,
% 7.65/1.50      ( k2_relat_1(sK3) = k1_xboole_0
% 7.65/1.50      | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_11265]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11272,plain,
% 7.65/1.50      ( k2_relat_1(sK3) = k1_xboole_0
% 7.65/1.50      | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_9326,c_11266]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11271,plain,
% 7.65/1.50      ( k2_relat_1(sK3) = k1_xboole_0
% 7.65/1.50      | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k2_struct_0(sK1)))) != iProver_top
% 7.65/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1654,c_11266]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11295,plain,
% 7.65/1.50      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_11272,c_46,c_49,c_2044,c_2367,c_2790,c_2791,c_6388,c_7217,
% 7.65/1.50                 c_11271]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8,plain,
% 7.65/1.50      ( ~ v1_funct_1(X0)
% 7.65/1.50      | ~ v2_funct_1(X0)
% 7.65/1.50      | ~ v1_relat_1(X0)
% 7.65/1.50      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1675,plain,
% 7.65/1.50      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 7.65/1.50      | v1_funct_1(X0) != iProver_top
% 7.65/1.50      | v2_funct_1(X0) != iProver_top
% 7.65/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4651,plain,
% 7.65/1.50      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 7.65/1.50      | v2_funct_1(sK3) != iProver_top
% 7.65/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1649,c_1675]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2130,plain,
% 7.65/1.50      ( ~ v1_funct_1(sK3)
% 7.65/1.50      | ~ v2_funct_1(sK3)
% 7.65/1.50      | ~ v1_relat_1(sK3)
% 7.65/1.50      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5501,plain,
% 7.65/1.50      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_4651,c_41,c_37,c_2130,c_2366]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_28,plain,
% 7.65/1.50      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.65/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | ~ v1_relat_1(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1658,plain,
% 7.65/1.50      ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.65/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 7.65/1.50      | v1_funct_1(X0) != iProver_top
% 7.65/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6148,plain,
% 7.65/1.50      ( r1_tarski(k2_relat_1(k2_funct_1(sK3)),X0) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),X0))) = iProver_top
% 7.65/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.65/1.50      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_5501,c_1658]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6213,plain,
% 7.65/1.50      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),X0))) = iProver_top
% 7.65/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.65/1.50      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_6148,c_5509]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6416,plain,
% 7.65/1.50      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),X0))) = iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_6213,c_46,c_49,c_2044,c_2047,c_2367]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11316,plain,
% 7.65/1.50      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_11295,c_6416]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_14,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.65/1.50      | k1_xboole_0 = X1
% 7.65/1.50      | k1_xboole_0 = X0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f103]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1670,plain,
% 7.65/1.50      ( k1_xboole_0 = X0
% 7.65/1.50      | k1_xboole_0 = X1
% 7.65/1.50      | v1_funct_2(X1,X0,k1_xboole_0) != iProver_top
% 7.65/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5103,plain,
% 7.65/1.50      ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
% 7.65/1.50      | k1_xboole_0 = X0
% 7.65/1.50      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 7.65/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,X0,X1),X0,k1_xboole_0) != iProver_top
% 7.65/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 7.65/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1655,c_1670]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_23731,plain,
% 7.65/1.50      ( k2_tops_2(k1_xboole_0,X0,X1) = k1_xboole_0
% 7.65/1.50      | k1_xboole_0 = X0
% 7.65/1.50      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 7.65/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 7.65/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.65/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_5103,c_1654]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_23739,plain,
% 7.65/1.50      ( k2_tops_2(k1_xboole_0,X0,k2_funct_1(sK3)) = k1_xboole_0
% 7.65/1.50      | k1_xboole_0 = X0
% 7.65/1.50      | v1_funct_2(k2_funct_1(sK3),k1_xboole_0,X0) != iProver_top
% 7.65/1.50      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.65/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_11316,c_23731]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_29,plain,
% 7.65/1.50      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 7.65/1.50      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | ~ v1_relat_1(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1657,plain,
% 7.65/1.50      ( v1_funct_2(X0,k1_relat_1(X0),X1) = iProver_top
% 7.65/1.50      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.65/1.50      | v1_funct_1(X0) != iProver_top
% 7.65/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5504,plain,
% 7.65/1.50      ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),X0) = iProver_top
% 7.65/1.50      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),X0) != iProver_top
% 7.65/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 7.65/1.50      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_5501,c_1657]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5624,plain,
% 7.65/1.50      ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),X0) = iProver_top
% 7.65/1.50      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),X0) != iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_5504,c_46,c_49,c_2044,c_2047,c_2367]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5630,plain,
% 7.65/1.50      ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),X0) = iProver_top
% 7.65/1.50      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_5624,c_5509]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11317,plain,
% 7.65/1.50      ( v1_funct_2(k2_funct_1(sK3),k1_xboole_0,X0) = iProver_top
% 7.65/1.50      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_11295,c_5630]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_25389,plain,
% 7.65/1.50      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 7.65/1.50      | k2_tops_2(k1_xboole_0,X0,k2_funct_1(sK3)) = k1_xboole_0
% 7.65/1.50      | k1_xboole_0 = X0 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_23739,c_46,c_49,c_2044,c_2367,c_11317]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_25390,plain,
% 7.65/1.50      ( k2_tops_2(k1_xboole_0,X0,k2_funct_1(sK3)) = k1_xboole_0
% 7.65/1.50      | k1_xboole_0 = X0
% 7.65/1.50      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_25389]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_25397,plain,
% 7.65/1.50      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) = k1_xboole_0
% 7.65/1.50      | k2_struct_0(sK1) = k1_xboole_0 ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_9308,c_25390]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11311,plain,
% 7.65/1.50      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) != sK3
% 7.65/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top
% 7.65/1.50      | v1_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3))) != iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_11295,c_7195]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_13527,plain,
% 7.65/1.50      ( v1_funct_1(k2_tops_2(k2_relat_1(sK3),k2_struct_0(sK1),k2_funct_1(sK3))) = iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_8083,c_46,c_49,c_2044,c_2367,c_2790,c_2791,c_6388]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_13531,plain,
% 7.65/1.50      ( v1_funct_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3))) = iProver_top ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_13527,c_11295]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_14764,plain,
% 7.65/1.50      ( m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top
% 7.65/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
% 7.65/1.50      | k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) != sK3 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_11311,c_13531]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_14765,plain,
% 7.65/1.50      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) != sK3
% 7.65/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_14764]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_25490,plain,
% 7.65/1.50      ( k2_struct_0(sK1) = k1_xboole_0
% 7.65/1.50      | sK3 != k1_xboole_0
% 7.65/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_25397,c_14765]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11322,plain,
% 7.65/1.50      ( v1_funct_2(sK3,k2_struct_0(sK1),k1_xboole_0) = iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_11295,c_2791]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11320,plain,
% 7.65/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) = iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_11295,c_2790]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_12754,plain,
% 7.65/1.50      ( k2_struct_0(sK1) = k1_xboole_0
% 7.65/1.50      | sK3 = k1_xboole_0
% 7.65/1.50      | v1_funct_2(sK3,k2_struct_0(sK1),k1_xboole_0) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_11320,c_1670]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_25625,plain,
% 7.65/1.50      ( k2_struct_0(sK1) = k1_xboole_0
% 7.65/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_25490,c_11322,c_12754]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_25633,plain,
% 7.65/1.50      ( k2_struct_0(sK1) = k1_xboole_0
% 7.65/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
% 7.65/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_25397,c_25625]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11307,plain,
% 7.65/1.50      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) = iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_11295,c_8075]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_7218,plain,
% 7.65/1.50      ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) = iProver_top
% 7.65/1.50      | v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) != iProver_top
% 7.65/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) != iProver_top
% 7.65/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_7187,c_1654]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8016,plain,
% 7.65/1.50      ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_struct_0(sK1)) = iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_7218,c_46,c_49,c_2790,c_2791,c_6388]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11308,plain,
% 7.65/1.50      ( v1_funct_2(k2_funct_1(sK3),k1_xboole_0,k2_struct_0(sK1)) = iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_11295,c_8016]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_25632,plain,
% 7.65/1.50      ( k2_struct_0(sK1) = k1_xboole_0
% 7.65/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
% 7.65/1.50      | v1_funct_2(k2_funct_1(sK3),k1_xboole_0,k2_struct_0(sK1)) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) != iProver_top
% 7.65/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1655,c_25625]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_25976,plain,
% 7.65/1.50      ( v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top
% 7.65/1.50      | k2_struct_0(sK1) = k1_xboole_0 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_25633,c_46,c_49,c_2044,c_2367,c_11307,c_11308,c_25632]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_25977,plain,
% 7.65/1.50      ( k2_struct_0(sK1) = k1_xboole_0
% 7.65/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)),k2_struct_0(sK1),k1_xboole_0) != iProver_top ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_25976]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_25982,plain,
% 7.65/1.50      ( k2_struct_0(sK1) = k1_xboole_0
% 7.65/1.50      | v1_funct_2(k2_funct_1(sK3),k1_xboole_0,k2_struct_0(sK1)) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) != iProver_top
% 7.65/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1654,c_25977]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_26171,plain,
% 7.65/1.50      ( k2_struct_0(sK1) = k1_xboole_0 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_25982,c_46,c_49,c_2044,c_2367,c_11307,c_11308]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11319,plain,
% 7.65/1.50      ( k1_relset_1(k2_struct_0(sK1),k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_11295,c_3426]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_26188,plain,
% 7.65/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_26171,c_11319]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_26192,plain,
% 7.65/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_26171,c_11320]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_17,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.65/1.50      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f105]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1667,plain,
% 7.65/1.50      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 7.65/1.50      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 7.65/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_26755,plain,
% 7.65/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 7.65/1.50      | v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_26192,c_1667]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_47,plain,
% 7.65/1.50      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_964,plain,( X0 = X0 ),theory(equality) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_999,plain,
% 7.65/1.50      ( k1_xboole_0 = k1_xboole_0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_964]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2688,plain,
% 7.65/1.50      ( sK3 = sK3 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_964]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_965,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3511,plain,
% 7.65/1.50      ( X0 != X1 | X0 = u1_struct_0(sK2) | u1_struct_0(sK2) != X1 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_965]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3512,plain,
% 7.65/1.50      ( u1_struct_0(sK2) != k1_xboole_0
% 7.65/1.50      | k1_xboole_0 = u1_struct_0(sK2)
% 7.65/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_3511]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2527,plain,
% 7.65/1.50      ( X0 != X1 | X0 = u1_struct_0(sK1) | u1_struct_0(sK1) != X1 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_965]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3542,plain,
% 7.65/1.50      ( X0 = u1_struct_0(sK1)
% 7.65/1.50      | X0 != k2_struct_0(sK1)
% 7.65/1.50      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_2527]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3543,plain,
% 7.65/1.50      ( u1_struct_0(sK1) != k2_struct_0(sK1)
% 7.65/1.50      | k1_xboole_0 = u1_struct_0(sK1)
% 7.65/1.50      | k1_xboole_0 != k2_struct_0(sK1) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_3542]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5493,plain,
% 7.65/1.50      ( X0 != X1 | X0 = k2_struct_0(sK1) | k2_struct_0(sK1) != X1 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_965]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5494,plain,
% 7.65/1.50      ( k2_struct_0(sK1) != k1_xboole_0
% 7.65/1.50      | k1_xboole_0 = k2_struct_0(sK1)
% 7.65/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_5493]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2792,plain,
% 7.65/1.50      ( u1_struct_0(sK2) = k2_relat_1(sK3) ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_2785,c_478]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11324,plain,
% 7.65/1.50      ( u1_struct_0(sK2) = k1_xboole_0 ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_11295,c_2792]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_978,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.65/1.50      | v1_funct_2(X3,X4,X5)
% 7.65/1.50      | X3 != X0
% 7.65/1.50      | X4 != X1
% 7.65/1.50      | X5 != X2 ),
% 7.65/1.50      theory(equality) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2261,plain,
% 7.65/1.50      ( v1_funct_2(X0,X1,X2)
% 7.65/1.50      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 7.65/1.50      | X2 != u1_struct_0(sK2)
% 7.65/1.50      | X1 != u1_struct_0(sK1)
% 7.65/1.50      | X0 != sK3 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_978]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_22694,plain,
% 7.65/1.50      ( v1_funct_2(sK3,X0,X1)
% 7.65/1.50      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 7.65/1.50      | X1 != u1_struct_0(sK2)
% 7.65/1.50      | X0 != u1_struct_0(sK1)
% 7.65/1.50      | sK3 != sK3 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_2261]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_22695,plain,
% 7.65/1.50      ( X0 != u1_struct_0(sK2)
% 7.65/1.50      | X1 != u1_struct_0(sK1)
% 7.65/1.50      | sK3 != sK3
% 7.65/1.50      | v1_funct_2(sK3,X1,X0) = iProver_top
% 7.65/1.50      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_22694]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_22697,plain,
% 7.65/1.50      ( sK3 != sK3
% 7.65/1.50      | k1_xboole_0 != u1_struct_0(sK2)
% 7.65/1.50      | k1_xboole_0 != u1_struct_0(sK1)
% 7.65/1.50      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 7.65/1.50      | v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_22695]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_27391,plain,
% 7.65/1.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_26755,c_46,c_47,c_49,c_483,c_999,c_2044,c_2367,c_2688,
% 7.65/1.50                 c_3512,c_3543,c_5494,c_11307,c_11308,c_11324,c_22697,c_25982]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_30634,plain,
% 7.65/1.50      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_26188,c_27391]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11304,plain,
% 7.65/1.50      ( k2_tops_2(k1_xboole_0,k2_struct_0(sK1),k2_funct_1(sK3)) = sK3
% 7.65/1.50      | k2_struct_0(sK1) != k1_relat_1(sK3) ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_11295,c_9322]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_26191,plain,
% 7.65/1.50      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK3)) = sK3
% 7.65/1.50      | k1_relat_1(sK3) != k1_xboole_0 ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_26171,c_11304]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_48,plain,
% 7.65/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2377,plain,
% 7.65/1.50      ( ~ v1_funct_2(k2_funct_1(sK3),X0,X1)
% 7.65/1.50      | m1_subset_1(k2_tops_2(X0,X1,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.65/1.50      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.65/1.50      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_33]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2388,plain,
% 7.65/1.50      ( v1_funct_2(k2_funct_1(sK3),X0,X1) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_tops_2(X0,X1,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 7.65/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_2377]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2390,plain,
% 7.65/1.50      ( v1_funct_2(k2_funct_1(sK3),k1_xboole_0,k1_xboole_0) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 7.65/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 7.65/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_2388]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2376,plain,
% 7.65/1.50      ( v1_funct_2(k2_tops_2(X0,X1,k2_funct_1(sK3)),X1,X0)
% 7.65/1.50      | ~ v1_funct_2(k2_funct_1(sK3),X0,X1)
% 7.65/1.50      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.65/1.50      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_34]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2392,plain,
% 7.65/1.50      ( v1_funct_2(k2_tops_2(X0,X1,k2_funct_1(sK3)),X1,X0) = iProver_top
% 7.65/1.50      | v1_funct_2(k2_funct_1(sK3),X0,X1) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_2376]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2394,plain,
% 7.65/1.50      ( v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK3)),k1_xboole_0,k1_xboole_0) = iProver_top
% 7.65/1.50      | v1_funct_2(k2_funct_1(sK3),k1_xboole_0,k1_xboole_0) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 7.65/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_2392]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2276,plain,
% 7.65/1.50      ( v1_funct_2(k2_funct_1(sK3),X0,X1)
% 7.65/1.50      | ~ v1_funct_2(sK3,X1,X0)
% 7.65/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.65/1.50      | ~ v1_funct_1(sK3)
% 7.65/1.50      | ~ v2_funct_1(sK3)
% 7.65/1.50      | k2_relset_1(X1,X0,sK3) != X0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_26]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2548,plain,
% 7.65/1.50      ( v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1))
% 7.65/1.50      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 7.65/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 7.65/1.50      | ~ v1_funct_1(sK3)
% 7.65/1.50      | ~ v2_funct_1(sK3)
% 7.65/1.50      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_2276]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2549,plain,
% 7.65/1.50      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != u1_struct_0(sK2)
% 7.65/1.50      | v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 7.65/1.50      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 7.65/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 7.65/1.50      | v1_funct_1(sK3) != iProver_top
% 7.65/1.50      | v2_funct_1(sK3) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_2548]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_972,plain,
% 7.65/1.50      ( X0 != X1 | k2_funct_1(X0) = k2_funct_1(X1) ),
% 7.65/1.50      theory(equality) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2701,plain,
% 7.65/1.50      ( X0 != sK3 | k2_funct_1(X0) = k2_funct_1(sK3) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_972]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4061,plain,
% 7.65/1.50      ( k2_funct_1(sK3) = k2_funct_1(sK3) | sK3 != sK3 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_2701]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3205,plain,
% 7.65/1.50      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != X0
% 7.65/1.50      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
% 7.65/1.50      | u1_struct_0(sK2) != X0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_965]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5251,plain,
% 7.65/1.50      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
% 7.65/1.50      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2)
% 7.65/1.50      | u1_struct_0(sK2) != k2_struct_0(sK2) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_3205]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3157,plain,
% 7.65/1.50      ( v1_funct_2(X0,X1,X2)
% 7.65/1.50      | ~ v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1))
% 7.65/1.50      | X1 != u1_struct_0(sK2)
% 7.65/1.50      | X2 != u1_struct_0(sK1)
% 7.65/1.50      | X0 != k2_funct_1(sK3) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_978]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_24356,plain,
% 7.65/1.50      ( v1_funct_2(k2_funct_1(sK3),X0,X1)
% 7.65/1.50      | ~ v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1))
% 7.65/1.50      | X0 != u1_struct_0(sK2)
% 7.65/1.50      | X1 != u1_struct_0(sK1)
% 7.65/1.50      | k2_funct_1(sK3) != k2_funct_1(sK3) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_3157]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_24357,plain,
% 7.65/1.50      ( X0 != u1_struct_0(sK2)
% 7.65/1.50      | X1 != u1_struct_0(sK1)
% 7.65/1.50      | k2_funct_1(sK3) != k2_funct_1(sK3)
% 7.65/1.50      | v1_funct_2(k2_funct_1(sK3),X0,X1) = iProver_top
% 7.65/1.50      | v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_24356]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_24359,plain,
% 7.65/1.50      ( k2_funct_1(sK3) != k2_funct_1(sK3)
% 7.65/1.50      | k1_xboole_0 != u1_struct_0(sK2)
% 7.65/1.50      | k1_xboole_0 != u1_struct_0(sK1)
% 7.65/1.50      | v1_funct_2(k2_funct_1(sK3),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 7.65/1.50      | v1_funct_2(k2_funct_1(sK3),k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_24357]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_26184,plain,
% 7.65/1.50      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_26171,c_11307]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_26187,plain,
% 7.65/1.50      ( k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK3)) != sK3
% 7.65/1.50      | v1_funct_2(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK3)),k1_xboole_0,k1_xboole_0) != iProver_top
% 7.65/1.50      | m1_subset_1(k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_26171,c_14765]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_28304,plain,
% 7.65/1.50      ( k1_relat_1(sK3) != k1_xboole_0 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_26191,c_46,c_47,c_48,c_38,c_49,c_478,c_483,c_999,c_2044,
% 7.65/1.50                 c_2367,c_2390,c_2394,c_2549,c_2688,c_3512,c_3543,c_4061,
% 7.65/1.50                 c_5251,c_5494,c_11307,c_11308,c_11324,c_24359,c_25982,
% 7.65/1.50                 c_26184,c_26187]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_30636,plain,
% 7.65/1.50      ( $false ),
% 7.65/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_30634,c_28304]) ).
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.65/1.50  
% 7.65/1.50  ------                               Statistics
% 7.65/1.50  
% 7.65/1.50  ------ Selected
% 7.65/1.50  
% 7.65/1.50  total_time:                             0.964
% 7.65/1.50  
%------------------------------------------------------------------------------
