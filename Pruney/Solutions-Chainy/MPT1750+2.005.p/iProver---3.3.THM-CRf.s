%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:22 EST 2020

% Result     : Theorem 7.75s
% Output     : CNFRefutation 7.75s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1730)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f82,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                   => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                     => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X3) )
     => ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),sK3,k2_tmap_1(X1,X0,sK3,X2))
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,X1)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,sK2))
            & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(X3) )
        & m1_pre_topc(sK2,X1)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(sK1,X0,X3,X2))
                & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
                & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,sK1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f49,f59,f58,f57,f56])).

fof(f95,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f60])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f85,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f86,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f87,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f88,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f89,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f90,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f93,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f94,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f60])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f26])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      | ~ r1_tarski(X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f96,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f60])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f103,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f75,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f72,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f92,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f30,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f70,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f102,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f97,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f60])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f71,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f39])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 != X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f101,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X5,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(equality_resolution,[],[f78])).

cnf(c_21,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1146,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1142,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1147,plain,
    ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
    | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | m1_pre_topc(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4057,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1142,c_1147])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_37,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_38,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_39,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_40,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_41,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_42,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_45,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_46,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4805,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4057,c_37,c_38,c_39,c_40,c_41,c_42,c_45,c_46,c_47,c_1730])).

cnf(c_4806,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4805])).

cnf(c_4814,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) = k2_tmap_1(sK1,sK0,sK3,sK1)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_4806])).

cnf(c_54,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1638,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1729,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1638])).

cnf(c_1731,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) = k2_tmap_1(sK1,sK0,sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_1729])).

cnf(c_5473,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) = k2_tmap_1(sK1,sK0,sK3,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4814,c_36,c_35,c_34,c_33,c_32,c_31,c_28,c_27,c_26,c_54,c_1731])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1160,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5476,plain,
    ( m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5473,c_1160])).

cnf(c_47,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_493,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2114,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_493])).

cnf(c_494,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2020,plain,
    ( X0 != X1
    | X0 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_494])).

cnf(c_2743,plain,
    ( X0 != k2_tmap_1(sK1,sK0,sK3,X1)
    | X0 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X1))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X1)) != k2_tmap_1(sK1,sK0,sK3,X1) ),
    inference(instantiation,[status(thm)],[c_2020])).

cnf(c_2981,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) != k2_tmap_1(sK1,sK0,sK3,X0)
    | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) != k2_tmap_1(sK1,sK0,sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2743])).

cnf(c_2983,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK1) != k2_tmap_1(sK1,sK0,sK3,sK1)
    | k2_tmap_1(sK1,sK0,sK3,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) != k2_tmap_1(sK1,sK0,sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_2981])).

cnf(c_2982,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) = k2_tmap_1(sK1,sK0,sK3,X0) ),
    inference(instantiation,[status(thm)],[c_493])).

cnf(c_2984,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK1) = k2_tmap_1(sK1,sK0,sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_2982])).

cnf(c_1578,plain,
    ( m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1714,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1578])).

cnf(c_3043,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1714])).

cnf(c_3044,plain,
    ( m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3043])).

cnf(c_499,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1823,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | X0 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2)
    | X1 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_499])).

cnf(c_2113,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | X0 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X1)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1823])).

cnf(c_4355,plain,
    ( m1_subset_1(k2_tmap_1(sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_tmap_1(sK1,sK0,sK3,X0) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_2113])).

cnf(c_4361,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4355])).

cnf(c_4363,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK1) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4361])).

cnf(c_14186,plain,
    ( m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5476,c_36,c_35,c_34,c_33,c_32,c_31,c_28,c_45,c_27,c_26,c_47,c_54,c_1731,c_2114,c_2983,c_2984,c_3044,c_4363])).

cnf(c_4,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X2 = X3 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1161,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4460,plain,
    ( sK3 = X0
    | r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1142,c_1161])).

cnf(c_14195,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK1) = sK3
    | r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14186,c_4460])).

cnf(c_22,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_51,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1670,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_493])).

cnf(c_7,plain,
    ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X2,X3),X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(X0,X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1628,plain,
    ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,sK3,X2),sK3)
    | ~ v1_funct_2(sK3,X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(X0,X2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1719,plain,
    ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0),sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ r1_tarski(u1_struct_0(sK1),X0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1628])).

cnf(c_2066,plain,
    ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1719])).

cnf(c_1653,plain,
    ( ~ r2_relset_1(X0,X1,X2,sK3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X2 = sK3 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1930,plain,
    ( ~ r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1653])).

cnf(c_1994,plain,
    ( ~ r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0),sK3)
    | ~ m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = sK3 ),
    inference(instantiation,[status(thm)],[c_1930])).

cnf(c_2504,plain,
    ( ~ r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),sK3)
    | ~ m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) = sK3 ),
    inference(instantiation,[status(thm)],[c_1994])).

cnf(c_1928,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_494])).

cnf(c_2215,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1928])).

cnf(c_4264,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) != sK3
    | sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2215])).

cnf(c_1664,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_494])).

cnf(c_6135,plain,
    ( X0 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
    | X0 = sK3
    | sK3 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1664])).

cnf(c_6599,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK1) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
    | k2_tmap_1(sK1,sK0,sK3,sK1) = sK3
    | sK3 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_6135])).

cnf(c_15083,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK1) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14195,c_36,c_35,c_34,c_33,c_32,c_31,c_28,c_27,c_26,c_51,c_54,c_1670,c_1731,c_2066,c_2504,c_2983,c_2984,c_3043,c_4264,c_6599])).

cnf(c_25,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_20,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_14,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_292,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_14])).

cnf(c_293,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v2_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_292])).

cnf(c_1130,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1154,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1321,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1130,c_1154])).

cnf(c_6437,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_1321])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1626,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_11,c_29])).

cnf(c_1627,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1626])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2502,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_8,c_29])).

cnf(c_2503,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2502])).

cnf(c_6485,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_pre_topc(sK2,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6437,c_41,c_42,c_1627,c_2503])).

cnf(c_6493,plain,
    ( m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_6485])).

cnf(c_12,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_77,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_79,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_77])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1494,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1495,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1494])).

cnf(c_1497,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_6625,plain,
    ( m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6493,c_42,c_79,c_1497])).

cnf(c_15,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1150,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3293,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_1150])).

cnf(c_3468,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3293,c_42,c_1627])).

cnf(c_3469,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_3468])).

cnf(c_6637,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6625,c_3469])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_283,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_14,c_11])).

cnf(c_284,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v2_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_283])).

cnf(c_1131,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_80,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_285,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_1589,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1131,c_77,c_80,c_285,c_1495])).

cnf(c_1590,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1589])).

cnf(c_1599,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_1590])).

cnf(c_6434,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK1,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1599,c_1321])).

cnf(c_7076,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK1,X0) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6434,c_41,c_42,c_2503])).

cnf(c_7077,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(sK1,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7076])).

cnf(c_7087,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6637,c_7077])).

cnf(c_3331,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3293])).

cnf(c_6433,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_1321])).

cnf(c_6477,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6433])).

cnf(c_7493,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7087,c_41,c_42,c_79,c_1497,c_1627,c_3331,c_6477])).

cnf(c_1139,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1145,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3130,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_1145])).

cnf(c_3628,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3130,c_41,c_42])).

cnf(c_3131,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1599,c_1145])).

cnf(c_3784,plain,
    ( v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0)) = iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3131,c_41,c_42,c_2503])).

cnf(c_3785,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3784])).

cnf(c_3797,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_3785])).

cnf(c_44,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3477,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_3469])).

cnf(c_3947,plain,
    ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3797,c_41,c_42,c_44,c_79,c_1497,c_3477])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1164,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3952,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK2)
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3947,c_1164])).

cnf(c_3962,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK2)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
    | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3628,c_3952])).

cnf(c_53,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_55,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_58,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_60,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_71,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_73,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_5644,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK2)
    | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3962,c_41,c_42,c_55,c_60,c_73,c_79,c_1497])).

cnf(c_6638,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_6625,c_5644])).

cnf(c_7303,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_pre_topc(sK2,X1) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6638,c_3785])).

cnf(c_87,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3796,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_3785])).

cnf(c_8733,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3796,c_41,c_42,c_1599,c_2503])).

cnf(c_8739,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8733,c_6638])).

cnf(c_8963,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7303,c_41,c_42,c_80,c_87,c_1627,c_2503,c_6437,c_8739])).

cnf(c_8964,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_8963])).

cnf(c_8975,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1599,c_8964])).

cnf(c_9677,plain,
    ( v2_pre_topc(X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8975,c_41,c_42,c_80,c_2503])).

cnf(c_9678,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9677])).

cnf(c_9694,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7493,c_9678])).

cnf(c_3185,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3130])).

cnf(c_9772,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9694,c_41,c_42,c_44,c_55,c_3185])).

cnf(c_9777,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9772,c_1164])).

cnf(c_5335,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X0,sK1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_22,c_29])).

cnf(c_5675,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X0,sK1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5335,c_32,c_31])).

cnf(c_5677,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5675])).

cnf(c_5679,plain,
    ( m1_pre_topc(sK1,sK2) != iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5677])).

cnf(c_10681,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9777,c_41,c_42,c_55,c_79,c_1497,c_1627,c_3331,c_5679,c_6477])).

cnf(c_4815,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1139,c_4806])).

cnf(c_10697,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_10681,c_4815])).

cnf(c_10721,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK1) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_10697,c_5473])).

cnf(c_24,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1143,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_10700,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10681,c_1143])).

cnf(c_10722,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10721,c_10700])).

cnf(c_15089,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15083,c_10722])).

cnf(c_1134,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_10,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1155,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2033,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1134,c_1155])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1985,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1986,plain,
    ( v2_struct_0(sK0) = iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) != iProver_top
    | l1_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1985])).

cnf(c_16,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1633,plain,
    ( r1_funct_2(X0,X1,X2,X3,sK3,sK3)
    | ~ v1_funct_2(sK3,X0,X1)
    | ~ v1_funct_2(sK3,X2,X3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1724,plain,
    ( r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | ~ v1_funct_2(sK3,X0,X1)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(X1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1633])).

cnf(c_1833,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1724])).

cnf(c_1834,plain,
    ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) = iProver_top
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1833])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15089,c_2033,c_1986,c_1834,c_47,c_46,c_45,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:23:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.75/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.75/1.50  
% 7.75/1.50  ------  iProver source info
% 7.75/1.50  
% 7.75/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.75/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.75/1.50  git: non_committed_changes: false
% 7.75/1.50  git: last_make_outside_of_git: false
% 7.75/1.50  
% 7.75/1.50  ------ 
% 7.75/1.50  ------ Parsing...
% 7.75/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.75/1.50  ------ Proving...
% 7.75/1.50  ------ Problem Properties 
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  clauses                                 36
% 7.75/1.50  conjectures                             13
% 7.75/1.50  EPR                                     15
% 7.75/1.50  Horn                                    33
% 7.75/1.50  unary                                   14
% 7.75/1.50  binary                                  5
% 7.75/1.50  lits                                    110
% 7.75/1.50  lits eq                                 5
% 7.75/1.50  fd_pure                                 0
% 7.75/1.50  fd_pseudo                               0
% 7.75/1.50  fd_cond                                 0
% 7.75/1.50  fd_pseudo_cond                          3
% 7.75/1.50  AC symbols                              0
% 7.75/1.50  
% 7.75/1.50  ------ Input Options Time Limit: Unbounded
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ 
% 7.75/1.50  Current options:
% 7.75/1.50  ------ 
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Proving...
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  % SZS status Theorem for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  fof(f16,axiom,(
% 7.75/1.50    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f45,plain,(
% 7.75/1.50    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f16])).
% 7.75/1.50  
% 7.75/1.50  fof(f82,plain,(
% 7.75/1.50    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f45])).
% 7.75/1.50  
% 7.75/1.50  fof(f18,conjecture,(
% 7.75/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f19,negated_conjecture,(
% 7.75/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 7.75/1.50    inference(negated_conjecture,[],[f18])).
% 7.75/1.50  
% 7.75/1.50  fof(f48,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f19])).
% 7.75/1.50  
% 7.75/1.50  fof(f49,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.75/1.50    inference(flattening,[],[f48])).
% 7.75/1.50  
% 7.75/1.50  fof(f59,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),sK3,k2_tmap_1(X1,X0,sK3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f58,plain,(
% 7.75/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(sK2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,sK2)) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f57,plain,(
% 7.75/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(sK1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f56,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(X2),u1_struct_0(sK0),X3,k2_tmap_1(X1,sK0,X3,X2)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f60,plain,(
% 7.75/1.50    (((~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.75/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f49,f59,f58,f57,f56])).
% 7.75/1.50  
% 7.75/1.50  fof(f95,plain,(
% 7.75/1.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 7.75/1.50    inference(cnf_transformation,[],[f60])).
% 7.75/1.50  
% 7.75/1.50  fof(f14,axiom,(
% 7.75/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f41,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f14])).
% 7.75/1.50  
% 7.75/1.50  fof(f42,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(flattening,[],[f41])).
% 7.75/1.50  
% 7.75/1.50  fof(f79,plain,(
% 7.75/1.50    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f42])).
% 7.75/1.50  
% 7.75/1.50  fof(f85,plain,(
% 7.75/1.50    ~v2_struct_0(sK0)),
% 7.75/1.50    inference(cnf_transformation,[],[f60])).
% 7.75/1.50  
% 7.75/1.50  fof(f86,plain,(
% 7.75/1.50    v2_pre_topc(sK0)),
% 7.75/1.50    inference(cnf_transformation,[],[f60])).
% 7.75/1.50  
% 7.75/1.50  fof(f87,plain,(
% 7.75/1.50    l1_pre_topc(sK0)),
% 7.75/1.50    inference(cnf_transformation,[],[f60])).
% 7.75/1.50  
% 7.75/1.50  fof(f88,plain,(
% 7.75/1.50    ~v2_struct_0(sK1)),
% 7.75/1.50    inference(cnf_transformation,[],[f60])).
% 7.75/1.50  
% 7.75/1.50  fof(f89,plain,(
% 7.75/1.50    v2_pre_topc(sK1)),
% 7.75/1.50    inference(cnf_transformation,[],[f60])).
% 7.75/1.50  
% 7.75/1.50  fof(f90,plain,(
% 7.75/1.50    l1_pre_topc(sK1)),
% 7.75/1.50    inference(cnf_transformation,[],[f60])).
% 7.75/1.50  
% 7.75/1.50  fof(f93,plain,(
% 7.75/1.50    v1_funct_1(sK3)),
% 7.75/1.50    inference(cnf_transformation,[],[f60])).
% 7.75/1.50  
% 7.75/1.50  fof(f94,plain,(
% 7.75/1.50    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 7.75/1.50    inference(cnf_transformation,[],[f60])).
% 7.75/1.50  
% 7.75/1.50  fof(f3,axiom,(
% 7.75/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f24,plain,(
% 7.75/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.75/1.50    inference(ennf_transformation,[],[f3])).
% 7.75/1.50  
% 7.75/1.50  fof(f25,plain,(
% 7.75/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.75/1.50    inference(flattening,[],[f24])).
% 7.75/1.50  
% 7.75/1.50  fof(f67,plain,(
% 7.75/1.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f25])).
% 7.75/1.50  
% 7.75/1.50  fof(f2,axiom,(
% 7.75/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f22,plain,(
% 7.75/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.75/1.50    inference(ennf_transformation,[],[f2])).
% 7.75/1.50  
% 7.75/1.50  fof(f23,plain,(
% 7.75/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.50    inference(flattening,[],[f22])).
% 7.75/1.50  
% 7.75/1.50  fof(f52,plain,(
% 7.75/1.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.50    inference(nnf_transformation,[],[f23])).
% 7.75/1.50  
% 7.75/1.50  fof(f64,plain,(
% 7.75/1.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f52])).
% 7.75/1.50  
% 7.75/1.50  fof(f17,axiom,(
% 7.75/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f46,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f17])).
% 7.75/1.50  
% 7.75/1.50  fof(f47,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.75/1.50    inference(flattening,[],[f46])).
% 7.75/1.50  
% 7.75/1.50  fof(f55,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.75/1.50    inference(nnf_transformation,[],[f47])).
% 7.75/1.50  
% 7.75/1.50  fof(f84,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f55])).
% 7.75/1.50  
% 7.75/1.50  fof(f4,axiom,(
% 7.75/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 7.75/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f26,plain,(
% 7.75/1.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) | ~r1_tarski(X0,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.75/1.51    inference(ennf_transformation,[],[f4])).
% 7.75/1.51  
% 7.75/1.51  fof(f27,plain,(
% 7.75/1.51    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) | ~r1_tarski(X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.75/1.51    inference(flattening,[],[f26])).
% 7.75/1.51  
% 7.75/1.51  fof(f68,plain,(
% 7.75/1.51    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) | ~r1_tarski(X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.75/1.51    inference(cnf_transformation,[],[f27])).
% 7.75/1.51  
% 7.75/1.51  fof(f96,plain,(
% 7.75/1.51    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 7.75/1.51    inference(cnf_transformation,[],[f60])).
% 7.75/1.51  
% 7.75/1.51  fof(f15,axiom,(
% 7.75/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 7.75/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.51  
% 7.75/1.51  fof(f43,plain,(
% 7.75/1.51    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 7.75/1.51    inference(ennf_transformation,[],[f15])).
% 7.75/1.51  
% 7.75/1.51  fof(f44,plain,(
% 7.75/1.51    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.75/1.51    inference(flattening,[],[f43])).
% 7.75/1.51  
% 7.75/1.51  fof(f54,plain,(
% 7.75/1.51    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.75/1.51    inference(nnf_transformation,[],[f44])).
% 7.75/1.51  
% 7.75/1.51  fof(f80,plain,(
% 7.75/1.51    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.75/1.51    inference(cnf_transformation,[],[f54])).
% 7.75/1.51  
% 7.75/1.51  fof(f103,plain,(
% 7.75/1.51    ( ! [X2,X0] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 7.75/1.51    inference(equality_resolution,[],[f80])).
% 7.75/1.51  
% 7.75/1.51  fof(f11,axiom,(
% 7.75/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 7.75/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.51  
% 7.75/1.51  fof(f21,plain,(
% 7.75/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 7.75/1.51    inference(pure_predicate_removal,[],[f11])).
% 7.75/1.51  
% 7.75/1.51  fof(f36,plain,(
% 7.75/1.51    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.75/1.51    inference(ennf_transformation,[],[f21])).
% 7.75/1.51  
% 7.75/1.51  fof(f37,plain,(
% 7.75/1.51    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.75/1.51    inference(flattening,[],[f36])).
% 7.75/1.51  
% 7.75/1.51  fof(f75,plain,(
% 7.75/1.51    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.75/1.51    inference(cnf_transformation,[],[f37])).
% 7.75/1.51  
% 7.75/1.51  fof(f8,axiom,(
% 7.75/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.75/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.51  
% 7.75/1.51  fof(f32,plain,(
% 7.75/1.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.75/1.51    inference(ennf_transformation,[],[f8])).
% 7.75/1.51  
% 7.75/1.51  fof(f72,plain,(
% 7.75/1.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.75/1.51    inference(cnf_transformation,[],[f32])).
% 7.75/1.51  
% 7.75/1.51  fof(f92,plain,(
% 7.75/1.51    m1_pre_topc(sK2,sK1)),
% 7.75/1.51    inference(cnf_transformation,[],[f60])).
% 7.75/1.51  
% 7.75/1.51  fof(f5,axiom,(
% 7.75/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 7.75/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.51  
% 7.75/1.51  fof(f28,plain,(
% 7.75/1.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.75/1.51    inference(ennf_transformation,[],[f5])).
% 7.75/1.51  
% 7.75/1.51  fof(f29,plain,(
% 7.75/1.51    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.75/1.51    inference(flattening,[],[f28])).
% 7.75/1.51  
% 7.75/1.51  fof(f69,plain,(
% 7.75/1.51    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.75/1.51    inference(cnf_transformation,[],[f29])).
% 7.75/1.51  
% 7.75/1.51  fof(f9,axiom,(
% 7.75/1.51    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.75/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.51  
% 7.75/1.51  fof(f33,plain,(
% 7.75/1.51    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.75/1.51    inference(ennf_transformation,[],[f9])).
% 7.75/1.51  
% 7.75/1.51  fof(f73,plain,(
% 7.75/1.51    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.75/1.51    inference(cnf_transformation,[],[f33])).
% 7.75/1.51  
% 7.75/1.51  fof(f6,axiom,(
% 7.75/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 7.75/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.51  
% 7.75/1.51  fof(f20,plain,(
% 7.75/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 7.75/1.51    inference(pure_predicate_removal,[],[f6])).
% 7.75/1.51  
% 7.75/1.51  fof(f30,plain,(
% 7.75/1.51    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.75/1.51    inference(ennf_transformation,[],[f20])).
% 7.75/1.51  
% 7.75/1.51  fof(f70,plain,(
% 7.75/1.51    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.75/1.51    inference(cnf_transformation,[],[f30])).
% 7.75/1.51  
% 7.75/1.51  fof(f12,axiom,(
% 7.75/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 7.75/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.51  
% 7.75/1.51  fof(f38,plain,(
% 7.75/1.51    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 7.75/1.51    inference(ennf_transformation,[],[f12])).
% 7.75/1.51  
% 7.75/1.51  fof(f76,plain,(
% 7.75/1.51    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 7.75/1.51    inference(cnf_transformation,[],[f38])).
% 7.75/1.51  
% 7.75/1.51  fof(f81,plain,(
% 7.75/1.51    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.75/1.51    inference(cnf_transformation,[],[f54])).
% 7.75/1.51  
% 7.75/1.51  fof(f102,plain,(
% 7.75/1.51    ( ! [X2,X0] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 7.75/1.51    inference(equality_resolution,[],[f81])).
% 7.75/1.51  
% 7.75/1.51  fof(f1,axiom,(
% 7.75/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.75/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.51  
% 7.75/1.51  fof(f50,plain,(
% 7.75/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.75/1.51    inference(nnf_transformation,[],[f1])).
% 7.75/1.51  
% 7.75/1.51  fof(f51,plain,(
% 7.75/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.75/1.51    inference(flattening,[],[f50])).
% 7.75/1.51  
% 7.75/1.51  fof(f63,plain,(
% 7.75/1.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.75/1.51    inference(cnf_transformation,[],[f51])).
% 7.75/1.51  
% 7.75/1.51  fof(f97,plain,(
% 7.75/1.51    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 7.75/1.51    inference(cnf_transformation,[],[f60])).
% 7.75/1.51  
% 7.75/1.51  fof(f7,axiom,(
% 7.75/1.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.75/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.51  
% 7.75/1.51  fof(f31,plain,(
% 7.75/1.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.75/1.51    inference(ennf_transformation,[],[f7])).
% 7.75/1.51  
% 7.75/1.51  fof(f71,plain,(
% 7.75/1.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.75/1.51    inference(cnf_transformation,[],[f31])).
% 7.75/1.51  
% 7.75/1.51  fof(f10,axiom,(
% 7.75/1.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 7.75/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.51  
% 7.75/1.51  fof(f34,plain,(
% 7.75/1.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.75/1.51    inference(ennf_transformation,[],[f10])).
% 7.75/1.51  
% 7.75/1.51  fof(f35,plain,(
% 7.75/1.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.75/1.51    inference(flattening,[],[f34])).
% 7.75/1.51  
% 7.75/1.51  fof(f74,plain,(
% 7.75/1.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.75/1.51    inference(cnf_transformation,[],[f35])).
% 7.75/1.51  
% 7.75/1.51  fof(f13,axiom,(
% 7.75/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 7.75/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.51  
% 7.75/1.51  fof(f39,plain,(
% 7.75/1.51    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 7.75/1.51    inference(ennf_transformation,[],[f13])).
% 7.75/1.51  
% 7.75/1.51  fof(f40,plain,(
% 7.75/1.51    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 7.75/1.51    inference(flattening,[],[f39])).
% 7.75/1.51  
% 7.75/1.51  fof(f53,plain,(
% 7.75/1.51    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 7.75/1.51    inference(nnf_transformation,[],[f40])).
% 7.75/1.51  
% 7.75/1.51  fof(f78,plain,(
% 7.75/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 7.75/1.51    inference(cnf_transformation,[],[f53])).
% 7.75/1.51  
% 7.75/1.51  fof(f101,plain,(
% 7.75/1.51    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 7.75/1.51    inference(equality_resolution,[],[f78])).
% 7.75/1.51  
% 7.75/1.51  cnf(c_21,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.75/1.51      inference(cnf_transformation,[],[f82]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1146,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X0) = iProver_top
% 7.75/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_26,negated_conjecture,
% 7.75/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 7.75/1.51      inference(cnf_transformation,[],[f95]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1142,plain,
% 7.75/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_18,plain,
% 7.75/1.51      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.75/1.51      | ~ m1_pre_topc(X3,X1)
% 7.75/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.75/1.51      | v2_struct_0(X1)
% 7.75/1.51      | v2_struct_0(X2)
% 7.75/1.51      | ~ l1_pre_topc(X1)
% 7.75/1.51      | ~ l1_pre_topc(X2)
% 7.75/1.51      | ~ v2_pre_topc(X1)
% 7.75/1.51      | ~ v2_pre_topc(X2)
% 7.75/1.51      | ~ v1_funct_1(X0)
% 7.75/1.51      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 7.75/1.51      inference(cnf_transformation,[],[f79]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1147,plain,
% 7.75/1.51      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
% 7.75/1.51      | v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 7.75/1.51      | m1_pre_topc(X3,X0) != iProver_top
% 7.75/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) != iProver_top
% 7.75/1.51      | v2_struct_0(X0) = iProver_top
% 7.75/1.51      | v2_struct_0(X1) = iProver_top
% 7.75/1.51      | l1_pre_topc(X0) != iProver_top
% 7.75/1.51      | l1_pre_topc(X1) != iProver_top
% 7.75/1.51      | v2_pre_topc(X0) != iProver_top
% 7.75/1.51      | v2_pre_topc(X1) != iProver_top
% 7.75/1.51      | v1_funct_1(X2) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_4057,plain,
% 7.75/1.51      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 7.75/1.51      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 7.75/1.51      | m1_pre_topc(X0,sK1) != iProver_top
% 7.75/1.51      | v2_struct_0(sK0) = iProver_top
% 7.75/1.51      | v2_struct_0(sK1) = iProver_top
% 7.75/1.51      | l1_pre_topc(sK0) != iProver_top
% 7.75/1.51      | l1_pre_topc(sK1) != iProver_top
% 7.75/1.51      | v2_pre_topc(sK0) != iProver_top
% 7.75/1.51      | v2_pre_topc(sK1) != iProver_top
% 7.75/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1142,c_1147]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_36,negated_conjecture,
% 7.75/1.51      ( ~ v2_struct_0(sK0) ),
% 7.75/1.51      inference(cnf_transformation,[],[f85]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_37,plain,
% 7.75/1.51      ( v2_struct_0(sK0) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_35,negated_conjecture,
% 7.75/1.51      ( v2_pre_topc(sK0) ),
% 7.75/1.51      inference(cnf_transformation,[],[f86]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_38,plain,
% 7.75/1.51      ( v2_pre_topc(sK0) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_34,negated_conjecture,
% 7.75/1.51      ( l1_pre_topc(sK0) ),
% 7.75/1.51      inference(cnf_transformation,[],[f87]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_39,plain,
% 7.75/1.51      ( l1_pre_topc(sK0) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_33,negated_conjecture,
% 7.75/1.51      ( ~ v2_struct_0(sK1) ),
% 7.75/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_40,plain,
% 7.75/1.51      ( v2_struct_0(sK1) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_32,negated_conjecture,
% 7.75/1.51      ( v2_pre_topc(sK1) ),
% 7.75/1.51      inference(cnf_transformation,[],[f89]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_41,plain,
% 7.75/1.51      ( v2_pre_topc(sK1) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_31,negated_conjecture,
% 7.75/1.51      ( l1_pre_topc(sK1) ),
% 7.75/1.51      inference(cnf_transformation,[],[f90]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_42,plain,
% 7.75/1.51      ( l1_pre_topc(sK1) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_28,negated_conjecture,
% 7.75/1.51      ( v1_funct_1(sK3) ),
% 7.75/1.51      inference(cnf_transformation,[],[f93]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_45,plain,
% 7.75/1.51      ( v1_funct_1(sK3) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_27,negated_conjecture,
% 7.75/1.51      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 7.75/1.51      inference(cnf_transformation,[],[f94]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_46,plain,
% 7.75/1.51      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_4805,plain,
% 7.75/1.51      ( m1_pre_topc(X0,sK1) != iProver_top
% 7.75/1.51      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0) ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_4057,c_37,c_38,c_39,c_40,c_41,c_42,c_45,c_46,c_47,
% 7.75/1.51                 c_1730]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_4806,plain,
% 7.75/1.51      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0)
% 7.75/1.51      | m1_pre_topc(X0,sK1) != iProver_top ),
% 7.75/1.51      inference(renaming,[status(thm)],[c_4805]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_4814,plain,
% 7.75/1.51      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) = k2_tmap_1(sK1,sK0,sK3,sK1)
% 7.75/1.51      | l1_pre_topc(sK1) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1146,c_4806]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_54,plain,
% 7.75/1.51      ( m1_pre_topc(sK1,sK1) | ~ l1_pre_topc(sK1) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_21]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1638,plain,
% 7.75/1.51      ( ~ v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
% 7.75/1.51      | ~ m1_pre_topc(X2,X0)
% 7.75/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 7.75/1.51      | v2_struct_0(X0)
% 7.75/1.51      | v2_struct_0(X1)
% 7.75/1.51      | ~ l1_pre_topc(X0)
% 7.75/1.51      | ~ l1_pre_topc(X1)
% 7.75/1.51      | ~ v2_pre_topc(X0)
% 7.75/1.51      | ~ v2_pre_topc(X1)
% 7.75/1.51      | ~ v1_funct_1(sK3)
% 7.75/1.51      | k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),sK3,u1_struct_0(X2)) = k2_tmap_1(X0,X1,sK3,X2) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_18]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1729,plain,
% 7.75/1.51      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 7.75/1.51      | ~ m1_pre_topc(X0,sK1)
% 7.75/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.51      | v2_struct_0(sK0)
% 7.75/1.51      | v2_struct_0(sK1)
% 7.75/1.51      | ~ l1_pre_topc(sK0)
% 7.75/1.51      | ~ l1_pre_topc(sK1)
% 7.75/1.51      | ~ v2_pre_topc(sK0)
% 7.75/1.51      | ~ v2_pre_topc(sK1)
% 7.75/1.51      | ~ v1_funct_1(sK3)
% 7.75/1.51      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) = k2_tmap_1(sK1,sK0,sK3,X0) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_1638]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1731,plain,
% 7.75/1.51      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 7.75/1.51      | ~ m1_pre_topc(sK1,sK1)
% 7.75/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.51      | v2_struct_0(sK0)
% 7.75/1.51      | v2_struct_0(sK1)
% 7.75/1.51      | ~ l1_pre_topc(sK0)
% 7.75/1.51      | ~ l1_pre_topc(sK1)
% 7.75/1.51      | ~ v2_pre_topc(sK0)
% 7.75/1.51      | ~ v2_pre_topc(sK1)
% 7.75/1.51      | ~ v1_funct_1(sK3)
% 7.75/1.51      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) = k2_tmap_1(sK1,sK0,sK3,sK1) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_1729]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_5473,plain,
% 7.75/1.51      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) = k2_tmap_1(sK1,sK0,sK3,sK1) ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_4814,c_36,c_35,c_34,c_33,c_32,c_31,c_28,c_27,c_26,
% 7.75/1.51                 c_54,c_1731]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_5,plain,
% 7.75/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.51      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.51      | ~ v1_funct_1(X0) ),
% 7.75/1.51      inference(cnf_transformation,[],[f67]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1160,plain,
% 7.75/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.75/1.51      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.75/1.51      | v1_funct_1(X0) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_5476,plain,
% 7.75/1.51      ( m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 7.75/1.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 7.75/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_5473,c_1160]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_47,plain,
% 7.75/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_493,plain,( X0 = X0 ),theory(equality) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2114,plain,
% 7.75/1.51      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_493]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_494,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2020,plain,
% 7.75/1.51      ( X0 != X1
% 7.75/1.51      | X0 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2)
% 7.75/1.51      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2) != X1 ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_494]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2743,plain,
% 7.75/1.51      ( X0 != k2_tmap_1(sK1,sK0,sK3,X1)
% 7.75/1.51      | X0 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X1))
% 7.75/1.51      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X1)) != k2_tmap_1(sK1,sK0,sK3,X1) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_2020]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2981,plain,
% 7.75/1.51      ( k2_tmap_1(sK1,sK0,sK3,X0) != k2_tmap_1(sK1,sK0,sK3,X0)
% 7.75/1.51      | k2_tmap_1(sK1,sK0,sK3,X0) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
% 7.75/1.51      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)) != k2_tmap_1(sK1,sK0,sK3,X0) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_2743]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2983,plain,
% 7.75/1.51      ( k2_tmap_1(sK1,sK0,sK3,sK1) != k2_tmap_1(sK1,sK0,sK3,sK1)
% 7.75/1.51      | k2_tmap_1(sK1,sK0,sK3,sK1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
% 7.75/1.51      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) != k2_tmap_1(sK1,sK0,sK3,sK1) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_2981]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2982,plain,
% 7.75/1.51      ( k2_tmap_1(sK1,sK0,sK3,X0) = k2_tmap_1(sK1,sK0,sK3,X0) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_493]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2984,plain,
% 7.75/1.51      ( k2_tmap_1(sK1,sK0,sK3,sK1) = k2_tmap_1(sK1,sK0,sK3,sK1) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_2982]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1578,plain,
% 7.75/1.51      ( m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.75/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.75/1.51      | ~ v1_funct_1(sK3) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_5]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1714,plain,
% 7.75/1.51      ( m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.51      | ~ v1_funct_1(sK3) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_1578]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3043,plain,
% 7.75/1.51      ( m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.51      | ~ v1_funct_1(sK3) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_1714]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3044,plain,
% 7.75/1.51      ( m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 7.75/1.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 7.75/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_3043]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_499,plain,
% 7.75/1.51      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.75/1.51      theory(equality) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1823,plain,
% 7.75/1.51      ( m1_subset_1(X0,X1)
% 7.75/1.51      | ~ m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.51      | X0 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X2)
% 7.75/1.51      | X1 != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_499]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2113,plain,
% 7.75/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.51      | ~ m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.51      | X0 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X1)
% 7.75/1.51      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_1823]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_4355,plain,
% 7.75/1.51      ( m1_subset_1(k2_tmap_1(sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.51      | ~ m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.51      | k2_tmap_1(sK1,sK0,sK3,X0) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
% 7.75/1.51      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_2113]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_4361,plain,
% 7.75/1.51      ( k2_tmap_1(sK1,sK0,sK3,X0) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0))
% 7.75/1.51      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 7.75/1.51      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 7.75/1.51      | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_4355]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_4363,plain,
% 7.75/1.51      ( k2_tmap_1(sK1,sK0,sK3,sK1) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
% 7.75/1.51      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 7.75/1.51      | m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 7.75/1.51      | m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_4361]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_14186,plain,
% 7.75/1.51      ( m1_subset_1(k2_tmap_1(sK1,sK0,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_5476,c_36,c_35,c_34,c_33,c_32,c_31,c_28,c_45,c_27,
% 7.75/1.51                 c_26,c_47,c_54,c_1731,c_2114,c_2983,c_2984,c_3044,
% 7.75/1.51                 c_4363]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_4,plain,
% 7.75/1.51      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.75/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.75/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.75/1.51      | X2 = X3 ),
% 7.75/1.51      inference(cnf_transformation,[],[f64]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1161,plain,
% 7.75/1.51      ( X0 = X1
% 7.75/1.51      | r2_relset_1(X2,X3,X0,X1) != iProver_top
% 7.75/1.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.75/1.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_4460,plain,
% 7.75/1.51      ( sK3 = X0
% 7.75/1.51      | r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) != iProver_top
% 7.75/1.51      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1142,c_1161]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_14195,plain,
% 7.75/1.51      ( k2_tmap_1(sK1,sK0,sK3,sK1) = sK3
% 7.75/1.51      | r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK1)) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_14186,c_4460]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_22,plain,
% 7.75/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.75/1.51      | ~ m1_pre_topc(X2,X1)
% 7.75/1.51      | ~ m1_pre_topc(X0,X2)
% 7.75/1.51      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 7.75/1.51      | ~ l1_pre_topc(X1)
% 7.75/1.51      | ~ v2_pre_topc(X1) ),
% 7.75/1.51      inference(cnf_transformation,[],[f84]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_51,plain,
% 7.75/1.51      ( ~ m1_pre_topc(sK1,sK1)
% 7.75/1.51      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1))
% 7.75/1.51      | ~ l1_pre_topc(sK1)
% 7.75/1.51      | ~ v2_pre_topc(sK1) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_22]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1670,plain,
% 7.75/1.51      ( sK3 = sK3 ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_493]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_7,plain,
% 7.75/1.51      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,X2,X3),X2)
% 7.75/1.51      | ~ v1_funct_2(X2,X0,X1)
% 7.75/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.75/1.51      | ~ r1_tarski(X0,X3)
% 7.75/1.51      | ~ v1_funct_1(X2) ),
% 7.75/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1628,plain,
% 7.75/1.51      ( r2_relset_1(X0,X1,k2_partfun1(X0,X1,sK3,X2),sK3)
% 7.75/1.51      | ~ v1_funct_2(sK3,X0,X1)
% 7.75/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.75/1.51      | ~ r1_tarski(X0,X2)
% 7.75/1.51      | ~ v1_funct_1(sK3) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_7]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1719,plain,
% 7.75/1.51      ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0),sK3)
% 7.75/1.51      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 7.75/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.51      | ~ r1_tarski(u1_struct_0(sK1),X0)
% 7.75/1.51      | ~ v1_funct_1(sK3) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_1628]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2066,plain,
% 7.75/1.51      ( r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),sK3)
% 7.75/1.51      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 7.75/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.51      | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1))
% 7.75/1.51      | ~ v1_funct_1(sK3) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_1719]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1653,plain,
% 7.75/1.51      ( ~ r2_relset_1(X0,X1,X2,sK3)
% 7.75/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.75/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.75/1.51      | X2 = sK3 ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1930,plain,
% 7.75/1.51      ( ~ r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,sK3)
% 7.75/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.51      | X0 = sK3 ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_1653]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1994,plain,
% 7.75/1.51      ( ~ r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0),sK3)
% 7.75/1.51      | ~ m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.51      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = sK3 ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_1930]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2504,plain,
% 7.75/1.51      ( ~ r2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),sK3)
% 7.75/1.51      | ~ m1_subset_1(k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.51      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) = sK3 ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_1994]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1928,plain,
% 7.75/1.51      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_494]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2215,plain,
% 7.75/1.51      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_1928]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_4264,plain,
% 7.75/1.51      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) != sK3
% 7.75/1.51      | sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
% 7.75/1.51      | sK3 != sK3 ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_2215]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1664,plain,
% 7.75/1.51      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_494]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_6135,plain,
% 7.75/1.51      ( X0 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
% 7.75/1.51      | X0 = sK3
% 7.75/1.51      | sK3 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_1664]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_6599,plain,
% 7.75/1.51      ( k2_tmap_1(sK1,sK0,sK3,sK1) != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
% 7.75/1.51      | k2_tmap_1(sK1,sK0,sK3,sK1) = sK3
% 7.75/1.51      | sK3 != k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_6135]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_15083,plain,
% 7.75/1.51      ( k2_tmap_1(sK1,sK0,sK3,sK1) = sK3 ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_14195,c_36,c_35,c_34,c_33,c_32,c_31,c_28,c_27,c_26,
% 7.75/1.51                 c_51,c_54,c_1670,c_1731,c_2066,c_2504,c_2983,c_2984,
% 7.75/1.51                 c_3043,c_4264,c_6599]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_25,negated_conjecture,
% 7.75/1.51      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 7.75/1.51      inference(cnf_transformation,[],[f96]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_20,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X1)
% 7.75/1.51      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.75/1.51      | ~ l1_pre_topc(X1)
% 7.75/1.51      | ~ l1_pre_topc(X0)
% 7.75/1.51      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.75/1.51      | ~ v2_pre_topc(X0)
% 7.75/1.51      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 7.75/1.51      inference(cnf_transformation,[],[f103]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_14,plain,
% 7.75/1.51      ( ~ l1_pre_topc(X0)
% 7.75/1.51      | ~ v2_pre_topc(X0)
% 7.75/1.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 7.75/1.51      inference(cnf_transformation,[],[f75]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_292,plain,
% 7.75/1.51      ( ~ v2_pre_topc(X0)
% 7.75/1.51      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.75/1.51      | ~ l1_pre_topc(X0)
% 7.75/1.51      | ~ l1_pre_topc(X1)
% 7.75/1.51      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.75/1.51      | m1_pre_topc(X0,X1) ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_20,c_14]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_293,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X1)
% 7.75/1.51      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.75/1.51      | ~ l1_pre_topc(X0)
% 7.75/1.51      | ~ l1_pre_topc(X1)
% 7.75/1.51      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.75/1.51      | ~ v2_pre_topc(X0) ),
% 7.75/1.51      inference(renaming,[status(thm)],[c_292]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1130,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X1) = iProver_top
% 7.75/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 7.75/1.51      | l1_pre_topc(X1) != iProver_top
% 7.75/1.51      | l1_pre_topc(X0) != iProver_top
% 7.75/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 7.75/1.51      | v2_pre_topc(X0) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_293]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_11,plain,
% 7.75/1.51      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.75/1.51      inference(cnf_transformation,[],[f72]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1154,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.75/1.51      | l1_pre_topc(X1) != iProver_top
% 7.75/1.51      | l1_pre_topc(X0) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1321,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X1) = iProver_top
% 7.75/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 7.75/1.51      | l1_pre_topc(X1) != iProver_top
% 7.75/1.51      | l1_pre_topc(X0) != iProver_top
% 7.75/1.51      | v2_pre_topc(X0) != iProver_top ),
% 7.75/1.51      inference(forward_subsumption_resolution,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_1130,c_1154]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_6437,plain,
% 7.75/1.51      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 7.75/1.51      | m1_pre_topc(sK2,X0) = iProver_top
% 7.75/1.51      | l1_pre_topc(X0) != iProver_top
% 7.75/1.51      | l1_pre_topc(sK2) != iProver_top
% 7.75/1.51      | v2_pre_topc(sK2) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_25,c_1321]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_29,negated_conjecture,
% 7.75/1.51      ( m1_pre_topc(sK2,sK1) ),
% 7.75/1.51      inference(cnf_transformation,[],[f92]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1626,plain,
% 7.75/1.51      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK1) ),
% 7.75/1.51      inference(resolution,[status(thm)],[c_11,c_29]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1627,plain,
% 7.75/1.51      ( l1_pre_topc(sK2) = iProver_top
% 7.75/1.51      | l1_pre_topc(sK1) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_1626]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_8,plain,
% 7.75/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.75/1.51      | ~ l1_pre_topc(X1)
% 7.75/1.51      | ~ v2_pre_topc(X1)
% 7.75/1.51      | v2_pre_topc(X0) ),
% 7.75/1.51      inference(cnf_transformation,[],[f69]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2502,plain,
% 7.75/1.51      ( ~ l1_pre_topc(sK1) | v2_pre_topc(sK2) | ~ v2_pre_topc(sK1) ),
% 7.75/1.51      inference(resolution,[status(thm)],[c_8,c_29]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2503,plain,
% 7.75/1.51      ( l1_pre_topc(sK1) != iProver_top
% 7.75/1.51      | v2_pre_topc(sK2) = iProver_top
% 7.75/1.51      | v2_pre_topc(sK1) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_2502]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_6485,plain,
% 7.75/1.51      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 7.75/1.51      | m1_pre_topc(sK2,X0) = iProver_top
% 7.75/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_6437,c_41,c_42,c_1627,c_2503]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_6493,plain,
% 7.75/1.51      ( m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.75/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1146,c_6485]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_12,plain,
% 7.75/1.51      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.75/1.51      | ~ l1_pre_topc(X0) ),
% 7.75/1.51      inference(cnf_transformation,[],[f73]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_77,plain,
% 7.75/1.51      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 7.75/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_79,plain,
% 7.75/1.51      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 7.75/1.51      | l1_pre_topc(sK1) != iProver_top ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_77]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_9,plain,
% 7.75/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.75/1.51      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 7.75/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1494,plain,
% 7.75/1.51      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.75/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_9]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1495,plain,
% 7.75/1.51      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 7.75/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_1494]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1497,plain,
% 7.75/1.51      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top
% 7.75/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_1495]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_6625,plain,
% 7.75/1.51      ( m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_6493,c_42,c_79,c_1497]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_15,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X1)
% 7.75/1.51      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.75/1.51      | ~ l1_pre_topc(X1) ),
% 7.75/1.51      inference(cnf_transformation,[],[f76]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1150,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X1) = iProver_top
% 7.75/1.51      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 7.75/1.51      | l1_pre_topc(X1) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3293,plain,
% 7.75/1.51      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.75/1.51      | m1_pre_topc(X0,sK2) = iProver_top
% 7.75/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_25,c_1150]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3468,plain,
% 7.75/1.51      ( m1_pre_topc(X0,sK2) = iProver_top
% 7.75/1.51      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_3293,c_42,c_1627]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3469,plain,
% 7.75/1.51      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.75/1.51      | m1_pre_topc(X0,sK2) = iProver_top ),
% 7.75/1.51      inference(renaming,[status(thm)],[c_3468]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_6637,plain,
% 7.75/1.51      ( m1_pre_topc(sK2,sK2) = iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_6625,c_3469]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_19,plain,
% 7.75/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.75/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.75/1.51      | ~ l1_pre_topc(X1)
% 7.75/1.51      | ~ l1_pre_topc(X0)
% 7.75/1.51      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.75/1.51      | ~ v2_pre_topc(X0)
% 7.75/1.51      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 7.75/1.51      inference(cnf_transformation,[],[f102]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_283,plain,
% 7.75/1.51      ( ~ v2_pre_topc(X0)
% 7.75/1.51      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.75/1.51      | ~ m1_pre_topc(X0,X1)
% 7.75/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.75/1.51      | ~ l1_pre_topc(X1) ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_19,c_14,c_11]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_284,plain,
% 7.75/1.51      ( ~ m1_pre_topc(X0,X1)
% 7.75/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.75/1.51      | ~ l1_pre_topc(X1)
% 7.75/1.51      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.75/1.51      | ~ v2_pre_topc(X0) ),
% 7.75/1.51      inference(renaming,[status(thm)],[c_283]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1131,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.75/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 7.75/1.51      | l1_pre_topc(X1) != iProver_top
% 7.75/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 7.75/1.51      | v2_pre_topc(X0) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_284]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_80,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.75/1.51      | l1_pre_topc(X1) != iProver_top
% 7.75/1.51      | l1_pre_topc(X0) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_285,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.75/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 7.75/1.51      | l1_pre_topc(X1) != iProver_top
% 7.75/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 7.75/1.51      | v2_pre_topc(X0) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_284]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1589,plain,
% 7.75/1.51      ( l1_pre_topc(X1) != iProver_top
% 7.75/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 7.75/1.51      | m1_pre_topc(X0,X1) != iProver_top
% 7.75/1.51      | v2_pre_topc(X0) != iProver_top ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_1131,c_77,c_80,c_285,c_1495]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1590,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.75/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 7.75/1.51      | l1_pre_topc(X1) != iProver_top
% 7.75/1.51      | v2_pre_topc(X0) != iProver_top ),
% 7.75/1.51      inference(renaming,[status(thm)],[c_1589]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1599,plain,
% 7.75/1.51      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) = iProver_top
% 7.75/1.51      | m1_pre_topc(sK2,X0) != iProver_top
% 7.75/1.51      | l1_pre_topc(X0) != iProver_top
% 7.75/1.51      | v2_pre_topc(sK2) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_25,c_1590]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_6434,plain,
% 7.75/1.51      ( m1_pre_topc(sK2,X0) != iProver_top
% 7.75/1.51      | m1_pre_topc(sK1,X0) = iProver_top
% 7.75/1.51      | l1_pre_topc(X0) != iProver_top
% 7.75/1.51      | l1_pre_topc(sK1) != iProver_top
% 7.75/1.51      | v2_pre_topc(sK2) != iProver_top
% 7.75/1.51      | v2_pre_topc(sK1) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1599,c_1321]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_7076,plain,
% 7.75/1.51      ( l1_pre_topc(X0) != iProver_top
% 7.75/1.51      | m1_pre_topc(sK1,X0) = iProver_top
% 7.75/1.51      | m1_pre_topc(sK2,X0) != iProver_top ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_6434,c_41,c_42,c_2503]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_7077,plain,
% 7.75/1.51      ( m1_pre_topc(sK2,X0) != iProver_top
% 7.75/1.51      | m1_pre_topc(sK1,X0) = iProver_top
% 7.75/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.75/1.51      inference(renaming,[status(thm)],[c_7076]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_7087,plain,
% 7.75/1.51      ( m1_pre_topc(sK1,sK2) = iProver_top
% 7.75/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_6637,c_7077]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3331,plain,
% 7.75/1.51      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.75/1.51      | m1_pre_topc(sK1,sK2) = iProver_top
% 7.75/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_3293]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_6433,plain,
% 7.75/1.51      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 7.75/1.51      | l1_pre_topc(X0) != iProver_top
% 7.75/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 7.75/1.51      | v2_pre_topc(X0) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1146,c_1321]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_6477,plain,
% 7.75/1.51      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.75/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.75/1.51      | l1_pre_topc(sK1) != iProver_top
% 7.75/1.51      | v2_pre_topc(sK1) != iProver_top ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_6433]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_7493,plain,
% 7.75/1.51      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_7087,c_41,c_42,c_79,c_1497,c_1627,c_3331,c_6477]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1139,plain,
% 7.75/1.51      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1145,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.75/1.51      | m1_pre_topc(X2,X1) != iProver_top
% 7.75/1.51      | m1_pre_topc(X0,X2) != iProver_top
% 7.75/1.51      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2)) = iProver_top
% 7.75/1.51      | l1_pre_topc(X1) != iProver_top
% 7.75/1.51      | v2_pre_topc(X1) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3130,plain,
% 7.75/1.51      ( m1_pre_topc(X0,sK1) != iProver_top
% 7.75/1.51      | m1_pre_topc(sK2,X0) != iProver_top
% 7.75/1.51      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
% 7.75/1.51      | l1_pre_topc(sK1) != iProver_top
% 7.75/1.51      | v2_pre_topc(sK1) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1139,c_1145]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3628,plain,
% 7.75/1.51      ( m1_pre_topc(X0,sK1) != iProver_top
% 7.75/1.51      | m1_pre_topc(sK2,X0) != iProver_top
% 7.75/1.51      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_3130,c_41,c_42]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3131,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.75/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 7.75/1.51      | m1_pre_topc(sK2,X1) != iProver_top
% 7.75/1.51      | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0)) = iProver_top
% 7.75/1.51      | l1_pre_topc(X1) != iProver_top
% 7.75/1.51      | v2_pre_topc(X1) != iProver_top
% 7.75/1.51      | v2_pre_topc(sK2) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1599,c_1145]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3784,plain,
% 7.75/1.51      ( v2_pre_topc(X1) != iProver_top
% 7.75/1.51      | l1_pre_topc(X1) != iProver_top
% 7.75/1.51      | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0)) = iProver_top
% 7.75/1.51      | m1_pre_topc(sK2,X1) != iProver_top
% 7.75/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 7.75/1.51      | m1_pre_topc(X0,X1) != iProver_top ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_3131,c_41,c_42,c_2503]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3785,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.75/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 7.75/1.51      | m1_pre_topc(sK2,X1) != iProver_top
% 7.75/1.51      | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0)) = iProver_top
% 7.75/1.51      | l1_pre_topc(X1) != iProver_top
% 7.75/1.51      | v2_pre_topc(X1) != iProver_top ),
% 7.75/1.51      inference(renaming,[status(thm)],[c_3784]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3797,plain,
% 7.75/1.51      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) != iProver_top
% 7.75/1.51      | m1_pre_topc(sK2,sK1) != iProver_top
% 7.75/1.51      | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) = iProver_top
% 7.75/1.51      | l1_pre_topc(sK1) != iProver_top
% 7.75/1.51      | v2_pre_topc(sK1) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1139,c_3785]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_44,plain,
% 7.75/1.51      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3477,plain,
% 7.75/1.51      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) = iProver_top
% 7.75/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1146,c_3469]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3947,plain,
% 7.75/1.51      ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) = iProver_top ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_3797,c_41,c_42,c_44,c_79,c_1497,c_3477]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_0,plain,
% 7.75/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.75/1.51      inference(cnf_transformation,[],[f63]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1164,plain,
% 7.75/1.51      ( X0 = X1
% 7.75/1.51      | r1_tarski(X0,X1) != iProver_top
% 7.75/1.51      | r1_tarski(X1,X0) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3952,plain,
% 7.75/1.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK2)
% 7.75/1.51      | r1_tarski(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_3947,c_1164]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3962,plain,
% 7.75/1.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK2)
% 7.75/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
% 7.75/1.51      | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_3628,c_3952]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_53,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X0) = iProver_top
% 7.75/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_55,plain,
% 7.75/1.51      ( m1_pre_topc(sK1,sK1) = iProver_top
% 7.75/1.51      | l1_pre_topc(sK1) != iProver_top ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_53]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_58,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.75/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 7.75/1.51      | l1_pre_topc(X1) != iProver_top
% 7.75/1.51      | l1_pre_topc(X0) != iProver_top
% 7.75/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 7.75/1.51      | v2_pre_topc(X0) != iProver_top
% 7.75/1.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_60,plain,
% 7.75/1.51      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) = iProver_top
% 7.75/1.51      | m1_pre_topc(sK1,sK1) != iProver_top
% 7.75/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.75/1.51      | l1_pre_topc(sK1) != iProver_top
% 7.75/1.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top
% 7.75/1.51      | v2_pre_topc(sK1) != iProver_top ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_58]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_71,plain,
% 7.75/1.51      ( l1_pre_topc(X0) != iProver_top
% 7.75/1.51      | v2_pre_topc(X0) != iProver_top
% 7.75/1.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_73,plain,
% 7.75/1.51      ( l1_pre_topc(sK1) != iProver_top
% 7.75/1.51      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top
% 7.75/1.51      | v2_pre_topc(sK1) != iProver_top ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_71]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_5644,plain,
% 7.75/1.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK2)
% 7.75/1.51      | m1_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_3962,c_41,c_42,c_55,c_60,c_73,c_79,c_1497]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_6638,plain,
% 7.75/1.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK2) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_6625,c_5644]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_7303,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.75/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 7.75/1.51      | m1_pre_topc(sK2,X1) != iProver_top
% 7.75/1.51      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
% 7.75/1.51      | l1_pre_topc(X1) != iProver_top
% 7.75/1.51      | v2_pre_topc(X1) != iProver_top ),
% 7.75/1.51      inference(demodulation,[status(thm)],[c_6638,c_3785]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_87,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.75/1.51      | l1_pre_topc(X1) != iProver_top
% 7.75/1.51      | v2_pre_topc(X1) != iProver_top
% 7.75/1.51      | v2_pre_topc(X0) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3796,plain,
% 7.75/1.51      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 7.75/1.51      | m1_pre_topc(sK2,X0) != iProver_top
% 7.75/1.51      | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0)) = iProver_top
% 7.75/1.51      | l1_pre_topc(X0) != iProver_top
% 7.75/1.51      | v2_pre_topc(X0) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1146,c_3785]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_8733,plain,
% 7.75/1.51      ( m1_pre_topc(sK2,X0) != iProver_top
% 7.75/1.51      | r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(X0)) = iProver_top
% 7.75/1.51      | l1_pre_topc(X0) != iProver_top
% 7.75/1.51      | v2_pre_topc(X0) != iProver_top ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_3796,c_41,c_42,c_1599,c_2503]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_8739,plain,
% 7.75/1.51      ( m1_pre_topc(sK2,X0) != iProver_top
% 7.75/1.51      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
% 7.75/1.51      | l1_pre_topc(X0) != iProver_top
% 7.75/1.51      | v2_pre_topc(X0) != iProver_top ),
% 7.75/1.51      inference(light_normalisation,[status(thm)],[c_8733,c_6638]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_8963,plain,
% 7.75/1.51      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 7.75/1.51      | m1_pre_topc(X0,X1) != iProver_top
% 7.75/1.51      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
% 7.75/1.51      | l1_pre_topc(X1) != iProver_top
% 7.75/1.51      | v2_pre_topc(X1) != iProver_top ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_7303,c_41,c_42,c_80,c_87,c_1627,c_2503,c_6437,c_8739]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_8964,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.75/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 7.75/1.51      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
% 7.75/1.51      | l1_pre_topc(X1) != iProver_top
% 7.75/1.51      | v2_pre_topc(X1) != iProver_top ),
% 7.75/1.51      inference(renaming,[status(thm)],[c_8963]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_8975,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.75/1.51      | m1_pre_topc(sK2,X0) != iProver_top
% 7.75/1.51      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
% 7.75/1.51      | l1_pre_topc(X1) != iProver_top
% 7.75/1.51      | l1_pre_topc(X0) != iProver_top
% 7.75/1.51      | v2_pre_topc(X1) != iProver_top
% 7.75/1.51      | v2_pre_topc(sK2) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1599,c_8964]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_9677,plain,
% 7.75/1.51      ( v2_pre_topc(X1) != iProver_top
% 7.75/1.51      | m1_pre_topc(X0,X1) != iProver_top
% 7.75/1.51      | m1_pre_topc(sK2,X0) != iProver_top
% 7.75/1.51      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
% 7.75/1.51      | l1_pre_topc(X1) != iProver_top ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_8975,c_41,c_42,c_80,c_2503]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_9678,plain,
% 7.75/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 7.75/1.51      | m1_pre_topc(sK2,X0) != iProver_top
% 7.75/1.51      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0)) = iProver_top
% 7.75/1.51      | l1_pre_topc(X1) != iProver_top
% 7.75/1.51      | v2_pre_topc(X1) != iProver_top ),
% 7.75/1.51      inference(renaming,[status(thm)],[c_9677]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_9694,plain,
% 7.75/1.51      ( m1_pre_topc(sK2,sK1) != iProver_top
% 7.75/1.51      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 7.75/1.51      | l1_pre_topc(sK2) != iProver_top
% 7.75/1.51      | v2_pre_topc(sK2) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_7493,c_9678]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3185,plain,
% 7.75/1.51      ( m1_pre_topc(sK2,sK1) != iProver_top
% 7.75/1.51      | m1_pre_topc(sK1,sK1) != iProver_top
% 7.75/1.51      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 7.75/1.51      | l1_pre_topc(sK1) != iProver_top
% 7.75/1.51      | v2_pre_topc(sK1) != iProver_top ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_3130]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_9772,plain,
% 7.75/1.51      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_9694,c_41,c_42,c_44,c_55,c_3185]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_9777,plain,
% 7.75/1.51      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 7.75/1.51      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_9772,c_1164]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_5335,plain,
% 7.75/1.51      ( ~ m1_pre_topc(X0,sK2)
% 7.75/1.51      | ~ m1_pre_topc(X0,sK1)
% 7.75/1.51      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
% 7.75/1.51      | ~ l1_pre_topc(sK1)
% 7.75/1.51      | ~ v2_pre_topc(sK1) ),
% 7.75/1.51      inference(resolution,[status(thm)],[c_22,c_29]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_5675,plain,
% 7.75/1.51      ( ~ m1_pre_topc(X0,sK2)
% 7.75/1.51      | ~ m1_pre_topc(X0,sK1)
% 7.75/1.51      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_5335,c_32,c_31]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_5677,plain,
% 7.75/1.51      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.75/1.51      | m1_pre_topc(X0,sK1) != iProver_top
% 7.75/1.51      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_5675]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_5679,plain,
% 7.75/1.51      ( m1_pre_topc(sK1,sK2) != iProver_top
% 7.75/1.51      | m1_pre_topc(sK1,sK1) != iProver_top
% 7.75/1.51      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_5677]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_10681,plain,
% 7.75/1.51      ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
% 7.75/1.51      inference(global_propositional_subsumption,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_9777,c_41,c_42,c_55,c_79,c_1497,c_1627,c_3331,c_5679,
% 7.75/1.51                 c_6477]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_4815,plain,
% 7.75/1.51      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1139,c_4806]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_10697,plain,
% 7.75/1.51      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 7.75/1.51      inference(demodulation,[status(thm)],[c_10681,c_4815]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_10721,plain,
% 7.75/1.51      ( k2_tmap_1(sK1,sK0,sK3,sK1) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 7.75/1.51      inference(light_normalisation,[status(thm)],[c_10697,c_5473]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_24,negated_conjecture,
% 7.75/1.51      ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
% 7.75/1.51      inference(cnf_transformation,[],[f97]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1143,plain,
% 7.75/1.51      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_10700,plain,
% 7.75/1.51      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) != iProver_top ),
% 7.75/1.51      inference(demodulation,[status(thm)],[c_10681,c_1143]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_10722,plain,
% 7.75/1.51      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK1)) != iProver_top ),
% 7.75/1.51      inference(demodulation,[status(thm)],[c_10721,c_10700]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_15089,plain,
% 7.75/1.51      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) != iProver_top ),
% 7.75/1.51      inference(demodulation,[status(thm)],[c_15083,c_10722]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1134,plain,
% 7.75/1.51      ( l1_pre_topc(sK0) = iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_10,plain,
% 7.75/1.51      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 7.75/1.51      inference(cnf_transformation,[],[f71]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1155,plain,
% 7.75/1.51      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2033,plain,
% 7.75/1.51      ( l1_struct_0(sK0) = iProver_top ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1134,c_1155]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_13,plain,
% 7.75/1.51      ( v2_struct_0(X0)
% 7.75/1.51      | ~ v1_xboole_0(u1_struct_0(X0))
% 7.75/1.51      | ~ l1_struct_0(X0) ),
% 7.75/1.51      inference(cnf_transformation,[],[f74]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1985,plain,
% 7.75/1.51      ( v2_struct_0(sK0)
% 7.75/1.51      | ~ v1_xboole_0(u1_struct_0(sK0))
% 7.75/1.51      | ~ l1_struct_0(sK0) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_13]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1986,plain,
% 7.75/1.51      ( v2_struct_0(sK0) = iProver_top
% 7.75/1.51      | v1_xboole_0(u1_struct_0(sK0)) != iProver_top
% 7.75/1.51      | l1_struct_0(sK0) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_1985]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_16,plain,
% 7.75/1.51      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 7.75/1.51      | ~ v1_funct_2(X4,X2,X3)
% 7.75/1.51      | ~ v1_funct_2(X4,X0,X1)
% 7.75/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.75/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.75/1.51      | v1_xboole_0(X1)
% 7.75/1.51      | v1_xboole_0(X3)
% 7.75/1.51      | ~ v1_funct_1(X4) ),
% 7.75/1.51      inference(cnf_transformation,[],[f101]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1633,plain,
% 7.75/1.51      ( r1_funct_2(X0,X1,X2,X3,sK3,sK3)
% 7.75/1.51      | ~ v1_funct_2(sK3,X0,X1)
% 7.75/1.51      | ~ v1_funct_2(sK3,X2,X3)
% 7.75/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.75/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.75/1.51      | v1_xboole_0(X1)
% 7.75/1.51      | v1_xboole_0(X3)
% 7.75/1.51      | ~ v1_funct_1(sK3) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_16]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1724,plain,
% 7.75/1.51      ( r1_funct_2(X0,X1,u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
% 7.75/1.51      | ~ v1_funct_2(sK3,X0,X1)
% 7.75/1.51      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 7.75/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.75/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.51      | v1_xboole_0(X1)
% 7.75/1.51      | v1_xboole_0(u1_struct_0(sK0))
% 7.75/1.51      | ~ v1_funct_1(sK3) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_1633]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1833,plain,
% 7.75/1.51      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
% 7.75/1.51      | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
% 7.75/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.51      | v1_xboole_0(u1_struct_0(sK0))
% 7.75/1.51      | ~ v1_funct_1(sK3) ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_1724]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1834,plain,
% 7.75/1.51      ( r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) = iProver_top
% 7.75/1.51      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 7.75/1.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 7.75/1.51      | v1_xboole_0(u1_struct_0(sK0)) = iProver_top
% 7.75/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.75/1.51      inference(predicate_to_equality,[status(thm)],[c_1833]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(contradiction,plain,
% 7.75/1.51      ( $false ),
% 7.75/1.51      inference(minisat,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_15089,c_2033,c_1986,c_1834,c_47,c_46,c_45,c_37]) ).
% 7.75/1.51  
% 7.75/1.51  
% 7.75/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.75/1.51  
% 7.75/1.51  ------                               Statistics
% 7.75/1.51  
% 7.75/1.51  ------ Selected
% 7.75/1.51  
% 7.75/1.51  total_time:                             0.666
% 7.75/1.51  
%------------------------------------------------------------------------------
