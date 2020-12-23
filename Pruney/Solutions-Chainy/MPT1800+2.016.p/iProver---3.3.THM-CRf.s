%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:05 EST 2020

% Result     : Theorem 7.37s
% Output     : CNFRefutation 7.37s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_3982)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_tsep_1(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
            | ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,sK3)
          | ~ m1_pre_topc(sK3,X0)
          | ~ v1_tsep_1(sK3,X0) )
        & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,sK3)
          | ( m1_pre_topc(sK3,X0)
            & v1_tsep_1(sK3,X0) ) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1)
              | ~ m1_pre_topc(X1,X0)
              | ~ v1_tsep_1(X1,X0) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)
              | ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) ) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,X1)
            | ~ m1_pre_topc(X1,sK2)
            | ~ v1_tsep_1(X1,sK2) )
          & ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,X1)
            | ( m1_pre_topc(X1,sK2)
              & v1_tsep_1(X1,sK2) ) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
      | ~ m1_pre_topc(sK3,sK2)
      | ~ v1_tsep_1(sK3,sK2) )
    & ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
      | ( m1_pre_topc(sK3,sK2)
        & v1_tsep_1(sK3,sK2) ) )
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f52,f54,f53])).

fof(f84,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f77,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK0(X0,X1,X2)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK0(X0,X1,X2)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k8_tmap_1(X0,X1) = X2
      | u1_struct_0(X1) = sK0(X0,X1,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f83,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k8_tmap_1(X0,X1) = X2
      | k6_tmap_1(X0,sK0(X0,X1,X2)) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK1(X0,X1),X0)
        & u1_struct_0(X1) = sK1(X0,X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tsep_1(X1,X0)
              | ( ~ v3_pre_topc(sK1(X0,X1),X0)
                & u1_struct_0(X1) = sK1(X0,X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tsep_1(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | v1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f72,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | u1_struct_0(X1) = sK1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f89,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ v1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(sK1(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3281,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_21,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3287,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3291,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4764,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3287,c_3291])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3290,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3292,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4278,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3290,c_3292])).

cnf(c_5589,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3287,c_4278])).

cnf(c_6770,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4764,c_5589])).

cnf(c_6771,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6770])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3293,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6780,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6771,c_3293])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3289,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4270,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3287,c_3289])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3282,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | sK0(X1,X0,X2) = u1_struct_0(X0)
    | k8_tmap_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1444,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | sK0(X1,X0,X2) = u1_struct_0(X0)
    | k8_tmap_1(X1,X0) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_33])).

cnf(c_1445,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ v1_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | sK0(sK2,X0,X1) = u1_struct_0(X0)
    | k8_tmap_1(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1444])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1449,plain,
    ( ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X0,sK2)
    | ~ v1_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0(sK2,X0,X1) = u1_struct_0(X0)
    | k8_tmap_1(sK2,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1445,c_32,c_31])).

cnf(c_1450,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ v1_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK0(sK2,X0,X1) = u1_struct_0(X0)
    | k8_tmap_1(sK2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1449])).

cnf(c_3256,plain,
    ( sK0(sK2,X0,X1) = u1_struct_0(X0)
    | k8_tmap_1(sK2,X0) = X1
    | m1_pre_topc(X0,sK2) != iProver_top
    | v1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1450])).

cnf(c_4118,plain,
    ( sK0(sK2,sK3,X0) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) = X0
    | v1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3282,c_3256])).

cnf(c_5535,plain,
    ( sK0(sK2,sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(sK3)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(sK2,sK3)
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4270,c_4118])).

cnf(c_6343,plain,
    ( l1_pre_topc(X0) != iProver_top
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(sK2,sK3)
    | sK0(sK2,sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(sK3)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5535,c_5589])).

cnf(c_6344,plain,
    ( sK0(sK2,sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(sK3)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(sK2,sK3)
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6343])).

cnf(c_6902,plain,
    ( sK0(sK2,sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(sK3)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(sK2,sK3)
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6780,c_6344])).

cnf(c_26981,plain,
    ( sK0(sK2,sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | v2_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3281,c_6902])).

cnf(c_35,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_36,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_50,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_52,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_59,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_61,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_3596,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3597,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3596])).

cnf(c_3599,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3597])).

cnf(c_3980,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3981,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3980])).

cnf(c_3983,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3981])).

cnf(c_5543,plain,
    ( sK0(sK2,sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5535])).

cnf(c_27014,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | sK0(sK2,sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26981,c_32,c_31,c_51,c_60,c_3598,c_3982,c_5544])).

cnf(c_27015,plain,
    ( sK0(sK2,sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_27014])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k6_tmap_1(X1,sK0(X1,X0,X2)) != X2
    | k8_tmap_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1472,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | k6_tmap_1(X1,sK0(X1,X0,X2)) != X2
    | k8_tmap_1(X1,X0) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_33])).

cnf(c_1473,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ v1_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | k6_tmap_1(sK2,sK0(sK2,X0,X1)) != X1
    | k8_tmap_1(sK2,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1472])).

cnf(c_1477,plain,
    ( ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X0,sK2)
    | ~ v1_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(sK2,sK0(sK2,X0,X1)) != X1
    | k8_tmap_1(sK2,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1473,c_32,c_31])).

cnf(c_1478,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ v1_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(sK2,sK0(sK2,X0,X1)) != X1
    | k8_tmap_1(sK2,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1477])).

cnf(c_3255,plain,
    ( k6_tmap_1(sK2,sK0(sK2,X0,X1)) != X1
    | k8_tmap_1(sK2,X0) = X1
    | m1_pre_topc(X0,sK2) != iProver_top
    | v1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1478])).

cnf(c_27019,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,u1_struct_0(sK3))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_27015,c_3255])).

cnf(c_38,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_56,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_58,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_15,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_20,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_201,plain,
    ( ~ v1_tsep_1(X0,X1)
    | v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_20])).

cnf(c_202,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_201])).

cnf(c_28,negated_conjecture,
    ( v1_tsep_1(sK3,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_272,plain,
    ( v1_tsep_1(sK3,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(prop_impl,[status(thm)],[c_28])).

cnf(c_642,plain,
    ( v3_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_202,c_272])).

cnf(c_643,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_642])).

cnf(c_645,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_643,c_31,c_29])).

cnf(c_3273,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_3288,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_17,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1402,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_33])).

cnf(c_1403,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_1402])).

cnf(c_1407,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1403,c_32,c_31])).

cnf(c_3258,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,X0)
    | v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1407])).

cnf(c_4213,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,u1_struct_0(X0))
    | v3_pre_topc(u1_struct_0(X0),sK2) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3288,c_3258])).

cnf(c_5264,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK2) != iProver_top
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4213,c_36])).

cnf(c_5265,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,u1_struct_0(X0))
    | v3_pre_topc(u1_struct_0(X0),sK2) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5264])).

cnf(c_5270,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,u1_struct_0(sK3))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
    | m1_pre_topc(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3273,c_5265])).

cnf(c_27408,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27019,c_35,c_36,c_38,c_52,c_58,c_61,c_3599,c_3983,c_5270])).

cnf(c_27543,plain,
    ( v1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_27408,c_4270])).

cnf(c_2564,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3614,plain,
    ( X0 != X1
    | X0 = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 ),
    inference(instantiation,[status(thm)],[c_2564])).

cnf(c_4109,plain,
    ( X0 != k8_tmap_1(sK2,sK3)
    | X0 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3614])).

cnf(c_5176,plain,
    ( k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_4109])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_6980,plain,
    ( r1_tarski(k8_tmap_1(sK2,sK3),k8_tmap_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_4970,plain,
    ( ~ r1_tarski(X0,k8_tmap_1(sK2,sK3))
    | ~ r1_tarski(k8_tmap_1(sK2,sK3),X0)
    | X0 = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6988,plain,
    ( ~ r1_tarski(k8_tmap_1(sK2,sK3),k8_tmap_1(sK2,sK3))
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_4970])).

cnf(c_2575,plain,
    ( ~ v1_pre_topc(X0)
    | v1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3402,plain,
    ( ~ v1_pre_topc(X0)
    | v1_pre_topc(k8_tmap_1(sK2,X1))
    | k8_tmap_1(sK2,X1) != X0 ),
    inference(instantiation,[status(thm)],[c_2575])).

cnf(c_3487,plain,
    ( v1_pre_topc(k8_tmap_1(sK2,X0))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | k8_tmap_1(sK2,X0) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(instantiation,[status(thm)],[c_3402])).

cnf(c_8570,plain,
    ( v1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_3487])).

cnf(c_8571,plain,
    ( k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | v1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8570])).

cnf(c_8573,plain,
    ( k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | v1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8571])).

cnf(c_28058,plain,
    ( v1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27543,c_35,c_36,c_38,c_52,c_58,c_61,c_3599,c_3983,c_5176,c_5270,c_6980,c_6988,c_8573,c_27019])).

cnf(c_11,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_211,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_20])).

cnf(c_1375,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_211,c_33])).

cnf(c_1376,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ v1_pre_topc(k8_tmap_1(sK2,X0))
    | ~ l1_pre_topc(k8_tmap_1(sK2,X0))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(k8_tmap_1(sK2,X0))
    | ~ v2_pre_topc(sK2)
    | k6_tmap_1(sK2,u1_struct_0(X0)) = k8_tmap_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_1375])).

cnf(c_1380,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK2,X0))
    | ~ m1_pre_topc(X0,sK2)
    | ~ v1_pre_topc(k8_tmap_1(sK2,X0))
    | ~ l1_pre_topc(k8_tmap_1(sK2,X0))
    | k6_tmap_1(sK2,u1_struct_0(X0)) = k8_tmap_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1376,c_32,c_31])).

cnf(c_1381,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ v1_pre_topc(k8_tmap_1(sK2,X0))
    | ~ l1_pre_topc(k8_tmap_1(sK2,X0))
    | ~ v2_pre_topc(k8_tmap_1(sK2,X0))
    | k6_tmap_1(sK2,u1_struct_0(X0)) = k8_tmap_1(sK2,X0) ),
    inference(renaming,[status(thm)],[c_1380])).

cnf(c_3259,plain,
    ( k6_tmap_1(sK2,u1_struct_0(X0)) = k8_tmap_1(sK2,X0)
    | m1_pre_topc(X0,sK2) != iProver_top
    | v1_pre_topc(k8_tmap_1(sK2,X0)) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,X0)) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1381])).

cnf(c_28072,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3)
    | m1_pre_topc(sK3,sK2) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28058,c_3259])).

cnf(c_51,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_57,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_60,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_100,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_104,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3598,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3596])).

cnf(c_2568,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4332,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(sK2,X1))
    | k8_tmap_1(sK2,X1) != X0 ),
    inference(instantiation,[status(thm)],[c_2568])).

cnf(c_5461,plain,
    ( l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_4332])).

cnf(c_5463,plain,
    ( l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_5461])).

cnf(c_7868,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
    | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1381])).

cnf(c_8572,plain,
    ( v1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_8570])).

cnf(c_2567,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5289,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(k8_tmap_1(sK2,X2),X3)
    | X3 != X1
    | k8_tmap_1(sK2,X2) != X0 ),
    inference(instantiation,[status(thm)],[c_2567])).

cnf(c_7809,plain,
    ( m1_pre_topc(k8_tmap_1(sK2,X0),X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | X1 != X3
    | k8_tmap_1(sK2,X0) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ),
    inference(instantiation,[status(thm)],[c_5289])).

cnf(c_8778,plain,
    ( m1_pre_topc(k8_tmap_1(sK2,sK3),X0)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | X0 != X2
    | k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(instantiation,[status(thm)],[c_7809])).

cnf(c_8780,plain,
    ( m1_pre_topc(k8_tmap_1(sK2,sK3),sK2)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
    | k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_8778])).

cnf(c_9075,plain,
    ( ~ m1_pre_topc(k8_tmap_1(sK2,sK3),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_9077,plain,
    ( ~ m1_pre_topc(k8_tmap_1(sK2,sK3),sK2)
    | ~ l1_pre_topc(sK2)
    | v2_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_9075])).

cnf(c_28084,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28072,c_32,c_35,c_31,c_36,c_29,c_38,c_51,c_52,c_57,c_58,c_60,c_61,c_100,c_104,c_3598,c_3599,c_3983,c_5176,c_5270,c_5463,c_6980,c_6988,c_7868,c_8572,c_8780,c_9077,c_27019])).

cnf(c_16,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k6_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1423,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k6_tmap_1(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_33])).

cnf(c_1424,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_1423])).

cnf(c_1428,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1424,c_32,c_31])).

cnf(c_3257,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,X0)
    | v3_pre_topc(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1428])).

cnf(c_27439,plain,
    ( k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3)
    | v3_pre_topc(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_27408,c_3257])).

cnf(c_28092,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_28084,c_27439])).

cnf(c_8010,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_8011,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8010])).

cnf(c_2579,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3384,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,sK2)
    | X2 != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_2579])).

cnf(c_3573,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | X0 != u1_struct_0(X1)
    | sK2 != X2 ),
    inference(instantiation,[status(thm)],[c_3384])).

cnf(c_6104,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK2)
    | X0 != u1_struct_0(sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3573])).

cnf(c_7715,plain,
    ( v3_pre_topc(sK1(sK2,sK3),sK2)
    | ~ v3_pre_topc(u1_struct_0(sK3),sK2)
    | sK1(sK2,sK3) != u1_struct_0(sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_6104])).

cnf(c_7716,plain,
    ( sK1(sK2,sK3) != u1_struct_0(sK3)
    | sK2 != sK2
    | v3_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
    | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7715])).

cnf(c_13,plain,
    ( v1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_26,negated_conjecture,
    ( ~ v1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_270,plain,
    ( ~ v1_tsep_1(sK3,sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(prop_impl,[status(thm)],[c_29,c_26])).

cnf(c_631,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_270])).

cnf(c_632,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,sK3) = u1_struct_0(sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_634,plain,
    ( sK1(sK2,sK3) = u1_struct_0(sK3)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_632,c_31,c_29])).

cnf(c_12,plain,
    ( ~ v3_pre_topc(sK1(X0,X1),X0)
    | v1_tsep_1(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_603,plain,
    ( ~ v3_pre_topc(sK1(X0,X1),X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_270])).

cnf(c_604,plain,
    ( ~ v3_pre_topc(sK1(sK2,sK3),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_603])).

cnf(c_606,plain,
    ( ~ v3_pre_topc(sK1(sK2,sK3),sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_604,c_31,c_29])).

cnf(c_608,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
    | v3_pre_topc(sK1(sK2,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28092,c_27408,c_8011,c_7716,c_634,c_608,c_104,c_100,c_38,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n022.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 19:12:56 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 7.37/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.37/1.47  
% 7.37/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.37/1.47  
% 7.37/1.47  ------  iProver source info
% 7.37/1.47  
% 7.37/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.37/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.37/1.47  git: non_committed_changes: false
% 7.37/1.47  git: last_make_outside_of_git: false
% 7.37/1.47  
% 7.37/1.47  ------ 
% 7.37/1.47  
% 7.37/1.47  ------ Input Options
% 7.37/1.47  
% 7.37/1.47  --out_options                           all
% 7.37/1.47  --tptp_safe_out                         true
% 7.37/1.47  --problem_path                          ""
% 7.37/1.47  --include_path                          ""
% 7.37/1.47  --clausifier                            res/vclausify_rel
% 7.37/1.47  --clausifier_options                    ""
% 7.37/1.47  --stdin                                 false
% 7.37/1.47  --stats_out                             all
% 7.37/1.47  
% 7.37/1.47  ------ General Options
% 7.37/1.47  
% 7.37/1.47  --fof                                   false
% 7.37/1.47  --time_out_real                         305.
% 7.37/1.47  --time_out_virtual                      -1.
% 7.37/1.47  --symbol_type_check                     false
% 7.37/1.47  --clausify_out                          false
% 7.37/1.47  --sig_cnt_out                           false
% 7.37/1.47  --trig_cnt_out                          false
% 7.37/1.47  --trig_cnt_out_tolerance                1.
% 7.37/1.47  --trig_cnt_out_sk_spl                   false
% 7.37/1.47  --abstr_cl_out                          false
% 7.37/1.47  
% 7.37/1.47  ------ Global Options
% 7.37/1.47  
% 7.37/1.47  --schedule                              default
% 7.37/1.47  --add_important_lit                     false
% 7.37/1.47  --prop_solver_per_cl                    1000
% 7.37/1.47  --min_unsat_core                        false
% 7.37/1.47  --soft_assumptions                      false
% 7.37/1.47  --soft_lemma_size                       3
% 7.37/1.47  --prop_impl_unit_size                   0
% 7.37/1.47  --prop_impl_unit                        []
% 7.37/1.47  --share_sel_clauses                     true
% 7.37/1.47  --reset_solvers                         false
% 7.37/1.47  --bc_imp_inh                            [conj_cone]
% 7.37/1.47  --conj_cone_tolerance                   3.
% 7.37/1.47  --extra_neg_conj                        none
% 7.37/1.47  --large_theory_mode                     true
% 7.37/1.47  --prolific_symb_bound                   200
% 7.37/1.47  --lt_threshold                          2000
% 7.37/1.47  --clause_weak_htbl                      true
% 7.37/1.47  --gc_record_bc_elim                     false
% 7.37/1.47  
% 7.37/1.47  ------ Preprocessing Options
% 7.37/1.47  
% 7.37/1.47  --preprocessing_flag                    true
% 7.37/1.47  --time_out_prep_mult                    0.1
% 7.37/1.47  --splitting_mode                        input
% 7.37/1.47  --splitting_grd                         true
% 7.37/1.47  --splitting_cvd                         false
% 7.37/1.47  --splitting_cvd_svl                     false
% 7.37/1.47  --splitting_nvd                         32
% 7.37/1.47  --sub_typing                            true
% 7.37/1.47  --prep_gs_sim                           true
% 7.37/1.47  --prep_unflatten                        true
% 7.37/1.47  --prep_res_sim                          true
% 7.37/1.47  --prep_upred                            true
% 7.37/1.47  --prep_sem_filter                       exhaustive
% 7.37/1.47  --prep_sem_filter_out                   false
% 7.37/1.47  --pred_elim                             true
% 7.37/1.47  --res_sim_input                         true
% 7.37/1.47  --eq_ax_congr_red                       true
% 7.37/1.47  --pure_diseq_elim                       true
% 7.37/1.47  --brand_transform                       false
% 7.37/1.47  --non_eq_to_eq                          false
% 7.37/1.47  --prep_def_merge                        true
% 7.37/1.47  --prep_def_merge_prop_impl              false
% 7.37/1.47  --prep_def_merge_mbd                    true
% 7.37/1.47  --prep_def_merge_tr_red                 false
% 7.37/1.47  --prep_def_merge_tr_cl                  false
% 7.37/1.47  --smt_preprocessing                     true
% 7.37/1.47  --smt_ac_axioms                         fast
% 7.37/1.47  --preprocessed_out                      false
% 7.37/1.47  --preprocessed_stats                    false
% 7.37/1.47  
% 7.37/1.47  ------ Abstraction refinement Options
% 7.37/1.47  
% 7.37/1.47  --abstr_ref                             []
% 7.37/1.47  --abstr_ref_prep                        false
% 7.37/1.47  --abstr_ref_until_sat                   false
% 7.37/1.47  --abstr_ref_sig_restrict                funpre
% 7.37/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.37/1.47  --abstr_ref_under                       []
% 7.37/1.47  
% 7.37/1.47  ------ SAT Options
% 7.37/1.47  
% 7.37/1.47  --sat_mode                              false
% 7.37/1.47  --sat_fm_restart_options                ""
% 7.37/1.47  --sat_gr_def                            false
% 7.37/1.47  --sat_epr_types                         true
% 7.37/1.47  --sat_non_cyclic_types                  false
% 7.37/1.47  --sat_finite_models                     false
% 7.37/1.47  --sat_fm_lemmas                         false
% 7.37/1.47  --sat_fm_prep                           false
% 7.37/1.47  --sat_fm_uc_incr                        true
% 7.37/1.47  --sat_out_model                         small
% 7.37/1.47  --sat_out_clauses                       false
% 7.37/1.47  
% 7.37/1.47  ------ QBF Options
% 7.37/1.47  
% 7.37/1.47  --qbf_mode                              false
% 7.37/1.47  --qbf_elim_univ                         false
% 7.37/1.47  --qbf_dom_inst                          none
% 7.37/1.47  --qbf_dom_pre_inst                      false
% 7.37/1.47  --qbf_sk_in                             false
% 7.37/1.47  --qbf_pred_elim                         true
% 7.37/1.47  --qbf_split                             512
% 7.37/1.47  
% 7.37/1.47  ------ BMC1 Options
% 7.37/1.47  
% 7.37/1.47  --bmc1_incremental                      false
% 7.37/1.47  --bmc1_axioms                           reachable_all
% 7.37/1.47  --bmc1_min_bound                        0
% 7.37/1.47  --bmc1_max_bound                        -1
% 7.37/1.47  --bmc1_max_bound_default                -1
% 7.37/1.47  --bmc1_symbol_reachability              true
% 7.37/1.47  --bmc1_property_lemmas                  false
% 7.37/1.47  --bmc1_k_induction                      false
% 7.37/1.47  --bmc1_non_equiv_states                 false
% 7.37/1.47  --bmc1_deadlock                         false
% 7.37/1.47  --bmc1_ucm                              false
% 7.37/1.47  --bmc1_add_unsat_core                   none
% 7.37/1.47  --bmc1_unsat_core_children              false
% 7.37/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.37/1.47  --bmc1_out_stat                         full
% 7.37/1.47  --bmc1_ground_init                      false
% 7.37/1.47  --bmc1_pre_inst_next_state              false
% 7.37/1.47  --bmc1_pre_inst_state                   false
% 7.37/1.47  --bmc1_pre_inst_reach_state             false
% 7.37/1.47  --bmc1_out_unsat_core                   false
% 7.37/1.47  --bmc1_aig_witness_out                  false
% 7.37/1.47  --bmc1_verbose                          false
% 7.37/1.47  --bmc1_dump_clauses_tptp                false
% 7.37/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.37/1.47  --bmc1_dump_file                        -
% 7.37/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.37/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.37/1.47  --bmc1_ucm_extend_mode                  1
% 7.37/1.47  --bmc1_ucm_init_mode                    2
% 7.37/1.47  --bmc1_ucm_cone_mode                    none
% 7.37/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.37/1.47  --bmc1_ucm_relax_model                  4
% 7.37/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.37/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.37/1.47  --bmc1_ucm_layered_model                none
% 7.37/1.47  --bmc1_ucm_max_lemma_size               10
% 7.37/1.47  
% 7.37/1.47  ------ AIG Options
% 7.37/1.47  
% 7.37/1.47  --aig_mode                              false
% 7.37/1.47  
% 7.37/1.47  ------ Instantiation Options
% 7.37/1.47  
% 7.37/1.47  --instantiation_flag                    true
% 7.37/1.47  --inst_sos_flag                         true
% 7.37/1.47  --inst_sos_phase                        true
% 7.37/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.37/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.37/1.47  --inst_lit_sel_side                     num_symb
% 7.37/1.47  --inst_solver_per_active                1400
% 7.37/1.47  --inst_solver_calls_frac                1.
% 7.37/1.47  --inst_passive_queue_type               priority_queues
% 7.37/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.37/1.47  --inst_passive_queues_freq              [25;2]
% 7.37/1.47  --inst_dismatching                      true
% 7.37/1.47  --inst_eager_unprocessed_to_passive     true
% 7.37/1.47  --inst_prop_sim_given                   true
% 7.37/1.47  --inst_prop_sim_new                     false
% 7.37/1.47  --inst_subs_new                         false
% 7.37/1.47  --inst_eq_res_simp                      false
% 7.37/1.47  --inst_subs_given                       false
% 7.37/1.47  --inst_orphan_elimination               true
% 7.37/1.47  --inst_learning_loop_flag               true
% 7.37/1.47  --inst_learning_start                   3000
% 7.37/1.47  --inst_learning_factor                  2
% 7.37/1.47  --inst_start_prop_sim_after_learn       3
% 7.37/1.47  --inst_sel_renew                        solver
% 7.37/1.47  --inst_lit_activity_flag                true
% 7.37/1.47  --inst_restr_to_given                   false
% 7.37/1.47  --inst_activity_threshold               500
% 7.37/1.47  --inst_out_proof                        true
% 7.37/1.47  
% 7.37/1.47  ------ Resolution Options
% 7.37/1.47  
% 7.37/1.47  --resolution_flag                       true
% 7.37/1.47  --res_lit_sel                           adaptive
% 7.37/1.47  --res_lit_sel_side                      none
% 7.37/1.47  --res_ordering                          kbo
% 7.37/1.47  --res_to_prop_solver                    active
% 7.37/1.47  --res_prop_simpl_new                    false
% 7.37/1.47  --res_prop_simpl_given                  true
% 7.37/1.47  --res_passive_queue_type                priority_queues
% 7.37/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.37/1.47  --res_passive_queues_freq               [15;5]
% 7.37/1.47  --res_forward_subs                      full
% 7.37/1.47  --res_backward_subs                     full
% 7.37/1.47  --res_forward_subs_resolution           true
% 7.37/1.47  --res_backward_subs_resolution          true
% 7.37/1.47  --res_orphan_elimination                true
% 7.37/1.47  --res_time_limit                        2.
% 7.37/1.47  --res_out_proof                         true
% 7.37/1.47  
% 7.37/1.47  ------ Superposition Options
% 7.37/1.47  
% 7.37/1.47  --superposition_flag                    true
% 7.37/1.47  --sup_passive_queue_type                priority_queues
% 7.37/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.37/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.37/1.47  --demod_completeness_check              fast
% 7.37/1.47  --demod_use_ground                      true
% 7.37/1.47  --sup_to_prop_solver                    passive
% 7.37/1.47  --sup_prop_simpl_new                    true
% 7.37/1.47  --sup_prop_simpl_given                  true
% 7.37/1.47  --sup_fun_splitting                     true
% 7.37/1.47  --sup_smt_interval                      50000
% 7.37/1.47  
% 7.37/1.47  ------ Superposition Simplification Setup
% 7.37/1.47  
% 7.37/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.37/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.37/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.37/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.37/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.37/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.37/1.47  --sup_immed_triv                        [TrivRules]
% 7.37/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.47  --sup_immed_bw_main                     []
% 7.37/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.37/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.37/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.47  --sup_input_bw                          []
% 7.37/1.47  
% 7.37/1.47  ------ Combination Options
% 7.37/1.47  
% 7.37/1.47  --comb_res_mult                         3
% 7.37/1.47  --comb_sup_mult                         2
% 7.37/1.47  --comb_inst_mult                        10
% 7.37/1.47  
% 7.37/1.47  ------ Debug Options
% 7.37/1.47  
% 7.37/1.47  --dbg_backtrace                         false
% 7.37/1.47  --dbg_dump_prop_clauses                 false
% 7.37/1.47  --dbg_dump_prop_clauses_file            -
% 7.37/1.47  --dbg_out_stat                          false
% 7.37/1.47  ------ Parsing...
% 7.37/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.37/1.47  
% 7.37/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 7.37/1.47  
% 7.37/1.47  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.37/1.47  
% 7.37/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.37/1.47  ------ Proving...
% 7.37/1.47  ------ Problem Properties 
% 7.37/1.47  
% 7.37/1.47  
% 7.37/1.47  clauses                                 42
% 7.37/1.47  conjectures                             3
% 7.37/1.47  EPR                                     15
% 7.37/1.47  Horn                                    35
% 7.37/1.47  unary                                   4
% 7.37/1.47  binary                                  5
% 7.37/1.47  lits                                    153
% 7.37/1.47  lits eq                                 23
% 7.37/1.47  fd_pure                                 0
% 7.37/1.47  fd_pseudo                               0
% 7.37/1.47  fd_cond                                 0
% 7.37/1.47  fd_pseudo_cond                          7
% 7.37/1.47  AC symbols                              0
% 7.37/1.47  
% 7.37/1.47  ------ Schedule dynamic 5 is on 
% 7.37/1.47  
% 7.37/1.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.37/1.47  
% 7.37/1.47  
% 7.37/1.47  ------ 
% 7.37/1.47  Current options:
% 7.37/1.47  ------ 
% 7.37/1.47  
% 7.37/1.47  ------ Input Options
% 7.37/1.47  
% 7.37/1.47  --out_options                           all
% 7.37/1.47  --tptp_safe_out                         true
% 7.37/1.47  --problem_path                          ""
% 7.37/1.47  --include_path                          ""
% 7.37/1.47  --clausifier                            res/vclausify_rel
% 7.37/1.47  --clausifier_options                    ""
% 7.37/1.47  --stdin                                 false
% 7.37/1.47  --stats_out                             all
% 7.37/1.47  
% 7.37/1.47  ------ General Options
% 7.37/1.47  
% 7.37/1.47  --fof                                   false
% 7.37/1.47  --time_out_real                         305.
% 7.37/1.47  --time_out_virtual                      -1.
% 7.37/1.47  --symbol_type_check                     false
% 7.37/1.47  --clausify_out                          false
% 7.37/1.47  --sig_cnt_out                           false
% 7.37/1.47  --trig_cnt_out                          false
% 7.37/1.47  --trig_cnt_out_tolerance                1.
% 7.37/1.47  --trig_cnt_out_sk_spl                   false
% 7.37/1.47  --abstr_cl_out                          false
% 7.37/1.47  
% 7.37/1.47  ------ Global Options
% 7.37/1.47  
% 7.37/1.47  --schedule                              default
% 7.37/1.47  --add_important_lit                     false
% 7.37/1.47  --prop_solver_per_cl                    1000
% 7.37/1.47  --min_unsat_core                        false
% 7.37/1.47  --soft_assumptions                      false
% 7.37/1.47  --soft_lemma_size                       3
% 7.37/1.47  --prop_impl_unit_size                   0
% 7.37/1.47  --prop_impl_unit                        []
% 7.37/1.47  --share_sel_clauses                     true
% 7.37/1.47  --reset_solvers                         false
% 7.37/1.47  --bc_imp_inh                            [conj_cone]
% 7.37/1.47  --conj_cone_tolerance                   3.
% 7.37/1.47  --extra_neg_conj                        none
% 7.37/1.47  --large_theory_mode                     true
% 7.37/1.47  --prolific_symb_bound                   200
% 7.37/1.47  --lt_threshold                          2000
% 7.37/1.47  --clause_weak_htbl                      true
% 7.37/1.47  --gc_record_bc_elim                     false
% 7.37/1.47  
% 7.37/1.47  ------ Preprocessing Options
% 7.37/1.47  
% 7.37/1.47  --preprocessing_flag                    true
% 7.37/1.47  --time_out_prep_mult                    0.1
% 7.37/1.47  --splitting_mode                        input
% 7.37/1.47  --splitting_grd                         true
% 7.37/1.47  --splitting_cvd                         false
% 7.37/1.47  --splitting_cvd_svl                     false
% 7.37/1.47  --splitting_nvd                         32
% 7.37/1.47  --sub_typing                            true
% 7.37/1.47  --prep_gs_sim                           true
% 7.37/1.47  --prep_unflatten                        true
% 7.37/1.47  --prep_res_sim                          true
% 7.37/1.47  --prep_upred                            true
% 7.37/1.47  --prep_sem_filter                       exhaustive
% 7.37/1.47  --prep_sem_filter_out                   false
% 7.37/1.47  --pred_elim                             true
% 7.37/1.47  --res_sim_input                         true
% 7.37/1.47  --eq_ax_congr_red                       true
% 7.37/1.47  --pure_diseq_elim                       true
% 7.37/1.47  --brand_transform                       false
% 7.37/1.47  --non_eq_to_eq                          false
% 7.37/1.47  --prep_def_merge                        true
% 7.37/1.47  --prep_def_merge_prop_impl              false
% 7.37/1.47  --prep_def_merge_mbd                    true
% 7.37/1.47  --prep_def_merge_tr_red                 false
% 7.37/1.47  --prep_def_merge_tr_cl                  false
% 7.37/1.47  --smt_preprocessing                     true
% 7.37/1.47  --smt_ac_axioms                         fast
% 7.37/1.47  --preprocessed_out                      false
% 7.37/1.47  --preprocessed_stats                    false
% 7.37/1.47  
% 7.37/1.47  ------ Abstraction refinement Options
% 7.37/1.47  
% 7.37/1.47  --abstr_ref                             []
% 7.37/1.47  --abstr_ref_prep                        false
% 7.37/1.47  --abstr_ref_until_sat                   false
% 7.37/1.47  --abstr_ref_sig_restrict                funpre
% 7.37/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.37/1.47  --abstr_ref_under                       []
% 7.37/1.47  
% 7.37/1.47  ------ SAT Options
% 7.37/1.47  
% 7.37/1.47  --sat_mode                              false
% 7.37/1.47  --sat_fm_restart_options                ""
% 7.37/1.47  --sat_gr_def                            false
% 7.37/1.47  --sat_epr_types                         true
% 7.37/1.47  --sat_non_cyclic_types                  false
% 7.37/1.47  --sat_finite_models                     false
% 7.37/1.47  --sat_fm_lemmas                         false
% 7.37/1.47  --sat_fm_prep                           false
% 7.37/1.47  --sat_fm_uc_incr                        true
% 7.37/1.47  --sat_out_model                         small
% 7.37/1.47  --sat_out_clauses                       false
% 7.37/1.47  
% 7.37/1.47  ------ QBF Options
% 7.37/1.47  
% 7.37/1.47  --qbf_mode                              false
% 7.37/1.47  --qbf_elim_univ                         false
% 7.37/1.47  --qbf_dom_inst                          none
% 7.37/1.47  --qbf_dom_pre_inst                      false
% 7.37/1.47  --qbf_sk_in                             false
% 7.37/1.47  --qbf_pred_elim                         true
% 7.37/1.47  --qbf_split                             512
% 7.37/1.47  
% 7.37/1.47  ------ BMC1 Options
% 7.37/1.47  
% 7.37/1.47  --bmc1_incremental                      false
% 7.37/1.47  --bmc1_axioms                           reachable_all
% 7.37/1.47  --bmc1_min_bound                        0
% 7.37/1.47  --bmc1_max_bound                        -1
% 7.37/1.47  --bmc1_max_bound_default                -1
% 7.37/1.47  --bmc1_symbol_reachability              true
% 7.37/1.47  --bmc1_property_lemmas                  false
% 7.37/1.47  --bmc1_k_induction                      false
% 7.37/1.47  --bmc1_non_equiv_states                 false
% 7.37/1.47  --bmc1_deadlock                         false
% 7.37/1.47  --bmc1_ucm                              false
% 7.37/1.47  --bmc1_add_unsat_core                   none
% 7.37/1.47  --bmc1_unsat_core_children              false
% 7.37/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.37/1.47  --bmc1_out_stat                         full
% 7.37/1.47  --bmc1_ground_init                      false
% 7.37/1.47  --bmc1_pre_inst_next_state              false
% 7.37/1.47  --bmc1_pre_inst_state                   false
% 7.37/1.47  --bmc1_pre_inst_reach_state             false
% 7.37/1.47  --bmc1_out_unsat_core                   false
% 7.37/1.47  --bmc1_aig_witness_out                  false
% 7.37/1.47  --bmc1_verbose                          false
% 7.37/1.47  --bmc1_dump_clauses_tptp                false
% 7.37/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.37/1.47  --bmc1_dump_file                        -
% 7.37/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.37/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.37/1.47  --bmc1_ucm_extend_mode                  1
% 7.37/1.47  --bmc1_ucm_init_mode                    2
% 7.37/1.47  --bmc1_ucm_cone_mode                    none
% 7.37/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.37/1.47  --bmc1_ucm_relax_model                  4
% 7.37/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.37/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.37/1.47  --bmc1_ucm_layered_model                none
% 7.37/1.47  --bmc1_ucm_max_lemma_size               10
% 7.37/1.47  
% 7.37/1.47  ------ AIG Options
% 7.37/1.47  
% 7.37/1.47  --aig_mode                              false
% 7.37/1.47  
% 7.37/1.47  ------ Instantiation Options
% 7.37/1.47  
% 7.37/1.47  --instantiation_flag                    true
% 7.37/1.47  --inst_sos_flag                         true
% 7.37/1.47  --inst_sos_phase                        true
% 7.37/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.37/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.37/1.47  --inst_lit_sel_side                     none
% 7.37/1.47  --inst_solver_per_active                1400
% 7.37/1.47  --inst_solver_calls_frac                1.
% 7.37/1.47  --inst_passive_queue_type               priority_queues
% 7.37/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.37/1.47  --inst_passive_queues_freq              [25;2]
% 7.37/1.47  --inst_dismatching                      true
% 7.37/1.47  --inst_eager_unprocessed_to_passive     true
% 7.37/1.47  --inst_prop_sim_given                   true
% 7.37/1.47  --inst_prop_sim_new                     false
% 7.37/1.47  --inst_subs_new                         false
% 7.37/1.47  --inst_eq_res_simp                      false
% 7.37/1.47  --inst_subs_given                       false
% 7.37/1.47  --inst_orphan_elimination               true
% 7.37/1.47  --inst_learning_loop_flag               true
% 7.37/1.47  --inst_learning_start                   3000
% 7.37/1.47  --inst_learning_factor                  2
% 7.37/1.47  --inst_start_prop_sim_after_learn       3
% 7.37/1.47  --inst_sel_renew                        solver
% 7.37/1.47  --inst_lit_activity_flag                true
% 7.37/1.47  --inst_restr_to_given                   false
% 7.37/1.47  --inst_activity_threshold               500
% 7.37/1.47  --inst_out_proof                        true
% 7.37/1.47  
% 7.37/1.47  ------ Resolution Options
% 7.37/1.47  
% 7.37/1.47  --resolution_flag                       false
% 7.37/1.47  --res_lit_sel                           adaptive
% 7.37/1.47  --res_lit_sel_side                      none
% 7.37/1.47  --res_ordering                          kbo
% 7.37/1.47  --res_to_prop_solver                    active
% 7.37/1.47  --res_prop_simpl_new                    false
% 7.37/1.47  --res_prop_simpl_given                  true
% 7.37/1.47  --res_passive_queue_type                priority_queues
% 7.37/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.37/1.47  --res_passive_queues_freq               [15;5]
% 7.37/1.47  --res_forward_subs                      full
% 7.37/1.47  --res_backward_subs                     full
% 7.37/1.47  --res_forward_subs_resolution           true
% 7.37/1.47  --res_backward_subs_resolution          true
% 7.37/1.47  --res_orphan_elimination                true
% 7.37/1.47  --res_time_limit                        2.
% 7.37/1.47  --res_out_proof                         true
% 7.37/1.47  
% 7.37/1.47  ------ Superposition Options
% 7.37/1.47  
% 7.37/1.47  --superposition_flag                    true
% 7.37/1.47  --sup_passive_queue_type                priority_queues
% 7.37/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.37/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.37/1.47  --demod_completeness_check              fast
% 7.37/1.47  --demod_use_ground                      true
% 7.37/1.47  --sup_to_prop_solver                    passive
% 7.37/1.47  --sup_prop_simpl_new                    true
% 7.37/1.47  --sup_prop_simpl_given                  true
% 7.37/1.47  --sup_fun_splitting                     true
% 7.37/1.47  --sup_smt_interval                      50000
% 7.37/1.47  
% 7.37/1.47  ------ Superposition Simplification Setup
% 7.37/1.47  
% 7.37/1.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.37/1.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.37/1.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.37/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.37/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.37/1.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.37/1.47  --sup_immed_triv                        [TrivRules]
% 7.37/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.47  --sup_immed_bw_main                     []
% 7.37/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.37/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.37/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.47  --sup_input_bw                          []
% 7.37/1.47  
% 7.37/1.47  ------ Combination Options
% 7.37/1.47  
% 7.37/1.47  --comb_res_mult                         3
% 7.37/1.47  --comb_sup_mult                         2
% 7.37/1.47  --comb_inst_mult                        10
% 7.37/1.47  
% 7.37/1.47  ------ Debug Options
% 7.37/1.47  
% 7.37/1.47  --dbg_backtrace                         false
% 7.37/1.47  --dbg_dump_prop_clauses                 false
% 7.37/1.47  --dbg_dump_prop_clauses_file            -
% 7.37/1.47  --dbg_out_stat                          false
% 7.37/1.47  
% 7.37/1.47  
% 7.37/1.47  
% 7.37/1.47  
% 7.37/1.47  ------ Proving...
% 7.37/1.47  
% 7.37/1.47  
% 7.37/1.47  % SZS status Theorem for theBenchmark.p
% 7.37/1.47  
% 7.37/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.37/1.47  
% 7.37/1.47  fof(f15,conjecture,(
% 7.37/1.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 7.37/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f16,negated_conjecture,(
% 7.37/1.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 7.37/1.47    inference(negated_conjecture,[],[f15])).
% 7.37/1.47  
% 7.37/1.47  fof(f36,plain,(
% 7.37/1.47    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.37/1.47    inference(ennf_transformation,[],[f16])).
% 7.37/1.47  
% 7.37/1.47  fof(f37,plain,(
% 7.37/1.47    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.37/1.47    inference(flattening,[],[f36])).
% 7.37/1.47  
% 7.37/1.47  fof(f51,plain,(
% 7.37/1.47    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.37/1.47    inference(nnf_transformation,[],[f37])).
% 7.37/1.47  
% 7.37/1.47  fof(f52,plain,(
% 7.37/1.47    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.37/1.47    inference(flattening,[],[f51])).
% 7.37/1.47  
% 7.37/1.47  fof(f54,plain,(
% 7.37/1.47    ( ! [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,sK3) | ~m1_pre_topc(sK3,X0) | ~v1_tsep_1(sK3,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,sK3) | (m1_pre_topc(sK3,X0) & v1_tsep_1(sK3,X0))) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 7.37/1.47    introduced(choice_axiom,[])).
% 7.37/1.47  
% 7.37/1.47  fof(f53,plain,(
% 7.37/1.47    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k8_tmap_1(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,X1) | ~m1_pre_topc(X1,sK2) | ~v1_tsep_1(X1,sK2)) & (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,X1) | (m1_pre_topc(X1,sK2) & v1_tsep_1(X1,sK2))) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 7.37/1.47    introduced(choice_axiom,[])).
% 7.37/1.47  
% 7.37/1.47  fof(f55,plain,(
% 7.37/1.47    ((g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) | ~m1_pre_topc(sK3,sK2) | ~v1_tsep_1(sK3,sK2)) & (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) | (m1_pre_topc(sK3,sK2) & v1_tsep_1(sK3,sK2))) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 7.37/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f52,f54,f53])).
% 7.37/1.47  
% 7.37/1.47  fof(f84,plain,(
% 7.37/1.47    l1_pre_topc(sK2)),
% 7.37/1.47    inference(cnf_transformation,[],[f55])).
% 7.37/1.47  
% 7.37/1.47  fof(f11,axiom,(
% 7.37/1.47    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.37/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f30,plain,(
% 7.37/1.47    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.37/1.47    inference(ennf_transformation,[],[f11])).
% 7.37/1.47  
% 7.37/1.47  fof(f77,plain,(
% 7.37/1.47    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f30])).
% 7.37/1.47  
% 7.37/1.47  fof(f4,axiom,(
% 7.37/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 7.37/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f20,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 7.37/1.47    inference(ennf_transformation,[],[f4])).
% 7.37/1.47  
% 7.37/1.47  fof(f61,plain,(
% 7.37/1.47    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f20])).
% 7.37/1.47  
% 7.37/1.47  fof(f9,axiom,(
% 7.37/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 7.37/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f28,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.37/1.47    inference(ennf_transformation,[],[f9])).
% 7.37/1.47  
% 7.37/1.47  fof(f75,plain,(
% 7.37/1.47    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f28])).
% 7.37/1.47  
% 7.37/1.47  fof(f3,axiom,(
% 7.37/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.37/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f19,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.37/1.47    inference(ennf_transformation,[],[f3])).
% 7.37/1.47  
% 7.37/1.47  fof(f60,plain,(
% 7.37/1.47    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f19])).
% 7.37/1.47  
% 7.37/1.47  fof(f2,axiom,(
% 7.37/1.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 7.37/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f17,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.37/1.47    inference(ennf_transformation,[],[f2])).
% 7.37/1.47  
% 7.37/1.47  fof(f18,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.37/1.47    inference(flattening,[],[f17])).
% 7.37/1.47  
% 7.37/1.47  fof(f59,plain,(
% 7.37/1.47    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f18])).
% 7.37/1.47  
% 7.37/1.47  fof(f74,plain,(
% 7.37/1.47    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f28])).
% 7.37/1.47  
% 7.37/1.47  fof(f86,plain,(
% 7.37/1.47    m1_pre_topc(sK3,sK2)),
% 7.37/1.47    inference(cnf_transformation,[],[f55])).
% 7.37/1.47  
% 7.37/1.47  fof(f6,axiom,(
% 7.37/1.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 7.37/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f22,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.37/1.47    inference(ennf_transformation,[],[f6])).
% 7.37/1.47  
% 7.37/1.47  fof(f23,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.47    inference(flattening,[],[f22])).
% 7.37/1.47  
% 7.37/1.47  fof(f41,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.47    inference(nnf_transformation,[],[f23])).
% 7.37/1.47  
% 7.37/1.47  fof(f42,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.47    inference(rectify,[],[f41])).
% 7.37/1.47  
% 7.37/1.47  fof(f43,plain,(
% 7.37/1.47    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.37/1.47    introduced(choice_axiom,[])).
% 7.37/1.47  
% 7.37/1.47  fof(f44,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK0(X0,X1,X2) & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 7.37/1.47  
% 7.37/1.47  fof(f66,plain,(
% 7.37/1.47    ( ! [X2,X0,X1] : (k8_tmap_1(X0,X1) = X2 | u1_struct_0(X1) = sK0(X0,X1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f44])).
% 7.37/1.47  
% 7.37/1.47  fof(f82,plain,(
% 7.37/1.47    ~v2_struct_0(sK2)),
% 7.37/1.47    inference(cnf_transformation,[],[f55])).
% 7.37/1.47  
% 7.37/1.47  fof(f83,plain,(
% 7.37/1.47    v2_pre_topc(sK2)),
% 7.37/1.47    inference(cnf_transformation,[],[f55])).
% 7.37/1.47  
% 7.37/1.47  fof(f67,plain,(
% 7.37/1.47    ( ! [X2,X0,X1] : (k8_tmap_1(X0,X1) = X2 | k6_tmap_1(X0,sK0(X0,X1,X2)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f44])).
% 7.37/1.47  
% 7.37/1.47  fof(f7,axiom,(
% 7.37/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 7.37/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f24,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.37/1.47    inference(ennf_transformation,[],[f7])).
% 7.37/1.47  
% 7.37/1.47  fof(f25,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.37/1.47    inference(flattening,[],[f24])).
% 7.37/1.47  
% 7.37/1.47  fof(f45,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.37/1.47    inference(nnf_transformation,[],[f25])).
% 7.37/1.47  
% 7.37/1.47  fof(f46,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.37/1.47    inference(rectify,[],[f45])).
% 7.37/1.47  
% 7.37/1.47  fof(f47,plain,(
% 7.37/1.47    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK1(X0,X1),X0) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.37/1.47    introduced(choice_axiom,[])).
% 7.37/1.47  
% 7.37/1.47  fof(f48,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : (((v1_tsep_1(X1,X0) | (~v3_pre_topc(sK1(X0,X1),X0) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tsep_1(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.37/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).
% 7.37/1.47  
% 7.37/1.47  fof(f68,plain,(
% 7.37/1.47    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f48])).
% 7.37/1.47  
% 7.37/1.47  fof(f94,plain,(
% 7.37/1.47    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.37/1.47    inference(equality_resolution,[],[f68])).
% 7.37/1.47  
% 7.37/1.47  fof(f10,axiom,(
% 7.37/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.37/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f29,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.37/1.47    inference(ennf_transformation,[],[f10])).
% 7.37/1.47  
% 7.37/1.47  fof(f76,plain,(
% 7.37/1.47    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f29])).
% 7.37/1.47  
% 7.37/1.47  fof(f87,plain,(
% 7.37/1.47    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) | v1_tsep_1(sK3,sK2)),
% 7.37/1.47    inference(cnf_transformation,[],[f55])).
% 7.37/1.47  
% 7.37/1.47  fof(f8,axiom,(
% 7.37/1.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 7.37/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f26,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.37/1.47    inference(ennf_transformation,[],[f8])).
% 7.37/1.47  
% 7.37/1.47  fof(f27,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.47    inference(flattening,[],[f26])).
% 7.37/1.47  
% 7.37/1.47  fof(f49,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.47    inference(nnf_transformation,[],[f27])).
% 7.37/1.47  
% 7.37/1.47  fof(f72,plain,(
% 7.37/1.47    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f49])).
% 7.37/1.47  
% 7.37/1.47  fof(f1,axiom,(
% 7.37/1.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.37/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f38,plain,(
% 7.37/1.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.37/1.47    inference(nnf_transformation,[],[f1])).
% 7.37/1.47  
% 7.37/1.47  fof(f39,plain,(
% 7.37/1.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.37/1.47    inference(flattening,[],[f38])).
% 7.37/1.47  
% 7.37/1.47  fof(f57,plain,(
% 7.37/1.47    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.37/1.47    inference(cnf_transformation,[],[f39])).
% 7.37/1.47  
% 7.37/1.47  fof(f90,plain,(
% 7.37/1.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.37/1.47    inference(equality_resolution,[],[f57])).
% 7.37/1.47  
% 7.37/1.47  fof(f58,plain,(
% 7.37/1.47    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f39])).
% 7.37/1.47  
% 7.37/1.47  fof(f64,plain,(
% 7.37/1.47    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f44])).
% 7.37/1.47  
% 7.37/1.47  fof(f92,plain,(
% 7.37/1.47    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.47    inference(equality_resolution,[],[f64])).
% 7.37/1.47  
% 7.37/1.47  fof(f93,plain,(
% 7.37/1.47    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.47    inference(equality_resolution,[],[f92])).
% 7.37/1.47  
% 7.37/1.47  fof(f56,plain,(
% 7.37/1.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.37/1.47    inference(cnf_transformation,[],[f39])).
% 7.37/1.47  
% 7.37/1.47  fof(f91,plain,(
% 7.37/1.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.37/1.47    inference(equality_resolution,[],[f56])).
% 7.37/1.47  
% 7.37/1.47  fof(f73,plain,(
% 7.37/1.47    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f49])).
% 7.37/1.47  
% 7.37/1.47  fof(f70,plain,(
% 7.37/1.47    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | u1_struct_0(X1) = sK1(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f48])).
% 7.37/1.47  
% 7.37/1.47  fof(f89,plain,(
% 7.37/1.47    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) | ~m1_pre_topc(sK3,sK2) | ~v1_tsep_1(sK3,sK2)),
% 7.37/1.47    inference(cnf_transformation,[],[f55])).
% 7.37/1.47  
% 7.37/1.47  fof(f71,plain,(
% 7.37/1.47    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(sK1(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f48])).
% 7.37/1.47  
% 7.37/1.47  cnf(c_31,negated_conjecture,
% 7.37/1.47      ( l1_pre_topc(sK2) ),
% 7.37/1.47      inference(cnf_transformation,[],[f84]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3281,plain,
% 7.37/1.47      ( l1_pre_topc(sK2) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_21,plain,
% 7.37/1.47      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.37/1.47      inference(cnf_transformation,[],[f77]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3287,plain,
% 7.37/1.47      ( m1_pre_topc(X0,X0) = iProver_top
% 7.37/1.47      | l1_pre_topc(X0) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_5,plain,
% 7.37/1.47      ( m1_pre_topc(X0,X1)
% 7.37/1.47      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.37/1.47      | ~ l1_pre_topc(X1) ),
% 7.37/1.47      inference(cnf_transformation,[],[f61]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3291,plain,
% 7.37/1.47      ( m1_pre_topc(X0,X1) = iProver_top
% 7.37/1.47      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 7.37/1.47      | l1_pre_topc(X1) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_4764,plain,
% 7.37/1.47      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top
% 7.37/1.47      | l1_pre_topc(X0) != iProver_top
% 7.37/1.47      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_3287,c_3291]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_18,plain,
% 7.37/1.47      ( ~ m1_pre_topc(X0,X1)
% 7.37/1.47      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.37/1.47      | ~ l1_pre_topc(X1) ),
% 7.37/1.47      inference(cnf_transformation,[],[f75]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3290,plain,
% 7.37/1.47      ( m1_pre_topc(X0,X1) != iProver_top
% 7.37/1.47      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 7.37/1.47      | l1_pre_topc(X1) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_4,plain,
% 7.37/1.47      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.37/1.47      inference(cnf_transformation,[],[f60]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3292,plain,
% 7.37/1.47      ( m1_pre_topc(X0,X1) != iProver_top
% 7.37/1.47      | l1_pre_topc(X1) != iProver_top
% 7.37/1.47      | l1_pre_topc(X0) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_4278,plain,
% 7.37/1.47      ( m1_pre_topc(X0,X1) != iProver_top
% 7.37/1.47      | l1_pre_topc(X1) != iProver_top
% 7.37/1.47      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_3290,c_3292]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_5589,plain,
% 7.37/1.47      ( l1_pre_topc(X0) != iProver_top
% 7.37/1.47      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_3287,c_4278]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_6770,plain,
% 7.37/1.47      ( l1_pre_topc(X0) != iProver_top
% 7.37/1.47      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_4764,c_5589]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_6771,plain,
% 7.37/1.47      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top
% 7.37/1.47      | l1_pre_topc(X0) != iProver_top ),
% 7.37/1.47      inference(renaming,[status(thm)],[c_6770]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3,plain,
% 7.37/1.47      ( ~ m1_pre_topc(X0,X1)
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | ~ v2_pre_topc(X1)
% 7.37/1.47      | v2_pre_topc(X0) ),
% 7.37/1.47      inference(cnf_transformation,[],[f59]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3293,plain,
% 7.37/1.47      ( m1_pre_topc(X0,X1) != iProver_top
% 7.37/1.47      | l1_pre_topc(X1) != iProver_top
% 7.37/1.47      | v2_pre_topc(X1) != iProver_top
% 7.37/1.47      | v2_pre_topc(X0) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_6780,plain,
% 7.37/1.47      ( l1_pre_topc(X0) != iProver_top
% 7.37/1.47      | v2_pre_topc(X0) != iProver_top
% 7.37/1.47      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_6771,c_3293]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_19,plain,
% 7.37/1.47      ( ~ m1_pre_topc(X0,X1)
% 7.37/1.47      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.37/1.47      | ~ l1_pre_topc(X1) ),
% 7.37/1.47      inference(cnf_transformation,[],[f74]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3289,plain,
% 7.37/1.47      ( m1_pre_topc(X0,X1) != iProver_top
% 7.37/1.47      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 7.37/1.47      | l1_pre_topc(X1) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_4270,plain,
% 7.37/1.47      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 7.37/1.47      | l1_pre_topc(X0) != iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_3287,c_3289]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_29,negated_conjecture,
% 7.37/1.47      ( m1_pre_topc(sK3,sK2) ),
% 7.37/1.47      inference(cnf_transformation,[],[f86]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3282,plain,
% 7.37/1.47      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_9,plain,
% 7.37/1.47      ( ~ m1_pre_topc(X0,X1)
% 7.37/1.47      | v2_struct_0(X1)
% 7.37/1.47      | ~ v1_pre_topc(X2)
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | ~ l1_pre_topc(X2)
% 7.37/1.47      | ~ v2_pre_topc(X1)
% 7.37/1.47      | ~ v2_pre_topc(X2)
% 7.37/1.47      | sK0(X1,X0,X2) = u1_struct_0(X0)
% 7.37/1.47      | k8_tmap_1(X1,X0) = X2 ),
% 7.37/1.47      inference(cnf_transformation,[],[f66]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_33,negated_conjecture,
% 7.37/1.47      ( ~ v2_struct_0(sK2) ),
% 7.37/1.47      inference(cnf_transformation,[],[f82]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1444,plain,
% 7.37/1.47      ( ~ m1_pre_topc(X0,X1)
% 7.37/1.47      | ~ v1_pre_topc(X2)
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | ~ l1_pre_topc(X2)
% 7.37/1.47      | ~ v2_pre_topc(X1)
% 7.37/1.47      | ~ v2_pre_topc(X2)
% 7.37/1.47      | sK0(X1,X0,X2) = u1_struct_0(X0)
% 7.37/1.47      | k8_tmap_1(X1,X0) = X2
% 7.37/1.47      | sK2 != X1 ),
% 7.37/1.47      inference(resolution_lifted,[status(thm)],[c_9,c_33]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1445,plain,
% 7.37/1.47      ( ~ m1_pre_topc(X0,sK2)
% 7.37/1.47      | ~ v1_pre_topc(X1)
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | ~ l1_pre_topc(sK2)
% 7.37/1.47      | ~ v2_pre_topc(X1)
% 7.37/1.47      | ~ v2_pre_topc(sK2)
% 7.37/1.47      | sK0(sK2,X0,X1) = u1_struct_0(X0)
% 7.37/1.47      | k8_tmap_1(sK2,X0) = X1 ),
% 7.37/1.47      inference(unflattening,[status(thm)],[c_1444]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_32,negated_conjecture,
% 7.37/1.47      ( v2_pre_topc(sK2) ),
% 7.37/1.47      inference(cnf_transformation,[],[f83]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1449,plain,
% 7.37/1.47      ( ~ v2_pre_topc(X1)
% 7.37/1.47      | ~ m1_pre_topc(X0,sK2)
% 7.37/1.47      | ~ v1_pre_topc(X1)
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | sK0(sK2,X0,X1) = u1_struct_0(X0)
% 7.37/1.47      | k8_tmap_1(sK2,X0) = X1 ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_1445,c_32,c_31]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1450,plain,
% 7.37/1.47      ( ~ m1_pre_topc(X0,sK2)
% 7.37/1.47      | ~ v1_pre_topc(X1)
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | ~ v2_pre_topc(X1)
% 7.37/1.47      | sK0(sK2,X0,X1) = u1_struct_0(X0)
% 7.37/1.47      | k8_tmap_1(sK2,X0) = X1 ),
% 7.37/1.47      inference(renaming,[status(thm)],[c_1449]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3256,plain,
% 7.37/1.47      ( sK0(sK2,X0,X1) = u1_struct_0(X0)
% 7.37/1.47      | k8_tmap_1(sK2,X0) = X1
% 7.37/1.47      | m1_pre_topc(X0,sK2) != iProver_top
% 7.37/1.47      | v1_pre_topc(X1) != iProver_top
% 7.37/1.47      | l1_pre_topc(X1) != iProver_top
% 7.37/1.47      | v2_pre_topc(X1) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_1450]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_4118,plain,
% 7.37/1.47      ( sK0(sK2,sK3,X0) = u1_struct_0(sK3)
% 7.37/1.47      | k8_tmap_1(sK2,sK3) = X0
% 7.37/1.47      | v1_pre_topc(X0) != iProver_top
% 7.37/1.47      | l1_pre_topc(X0) != iProver_top
% 7.37/1.47      | v2_pre_topc(X0) != iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_3282,c_3256]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_5535,plain,
% 7.37/1.47      ( sK0(sK2,sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(sK3)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(sK2,sK3)
% 7.37/1.47      | l1_pre_topc(X0) != iProver_top
% 7.37/1.47      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 7.37/1.47      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_4270,c_4118]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_6343,plain,
% 7.37/1.47      ( l1_pre_topc(X0) != iProver_top
% 7.37/1.47      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(sK2,sK3)
% 7.37/1.47      | sK0(sK2,sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(sK3)
% 7.37/1.47      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_5535,c_5589]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_6344,plain,
% 7.37/1.47      ( sK0(sK2,sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(sK3)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(sK2,sK3)
% 7.37/1.47      | l1_pre_topc(X0) != iProver_top
% 7.37/1.47      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 7.37/1.47      inference(renaming,[status(thm)],[c_6343]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_6902,plain,
% 7.37/1.47      ( sK0(sK2,sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(sK3)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(sK2,sK3)
% 7.37/1.47      | l1_pre_topc(X0) != iProver_top
% 7.37/1.47      | v2_pre_topc(X0) != iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_6780,c_6344]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_26981,plain,
% 7.37/1.47      ( sK0(sK2,sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK3)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 7.37/1.47      | v2_pre_topc(sK2) != iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_3281,c_6902]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_35,plain,
% 7.37/1.47      ( v2_pre_topc(sK2) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_36,plain,
% 7.37/1.47      ( l1_pre_topc(sK2) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_50,plain,
% 7.37/1.47      ( m1_pre_topc(X0,X0) = iProver_top
% 7.37/1.47      | l1_pre_topc(X0) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_52,plain,
% 7.37/1.47      ( m1_pre_topc(sK2,sK2) = iProver_top
% 7.37/1.47      | l1_pre_topc(sK2) != iProver_top ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_50]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_59,plain,
% 7.37/1.47      ( m1_pre_topc(X0,X1) != iProver_top
% 7.37/1.47      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 7.37/1.47      | l1_pre_topc(X1) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_61,plain,
% 7.37/1.47      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2) = iProver_top
% 7.37/1.47      | m1_pre_topc(sK2,sK2) != iProver_top
% 7.37/1.47      | l1_pre_topc(sK2) != iProver_top ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_59]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3596,plain,
% 7.37/1.47      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_4]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3597,plain,
% 7.37/1.47      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 7.37/1.47      | l1_pre_topc(X1) != iProver_top
% 7.37/1.47      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_3596]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3599,plain,
% 7.37/1.47      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2) != iProver_top
% 7.37/1.47      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.37/1.47      | l1_pre_topc(sK2) != iProver_top ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_3597]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3980,plain,
% 7.37/1.47      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | ~ v2_pre_topc(X1)
% 7.37/1.47      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_3]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3981,plain,
% 7.37/1.47      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) != iProver_top
% 7.37/1.47      | l1_pre_topc(X1) != iProver_top
% 7.37/1.47      | v2_pre_topc(X1) != iProver_top
% 7.37/1.47      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_3980]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3983,plain,
% 7.37/1.47      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2) != iProver_top
% 7.37/1.47      | l1_pre_topc(sK2) != iProver_top
% 7.37/1.47      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.37/1.47      | v2_pre_topc(sK2) != iProver_top ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_3981]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_5543,plain,
% 7.37/1.47      ( sK0(sK2,sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK3)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 7.37/1.47      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.37/1.47      | l1_pre_topc(sK2) != iProver_top
% 7.37/1.47      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_5535]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_27014,plain,
% 7.37/1.47      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 7.37/1.47      | sK0(sK2,sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK3) ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_26981,c_32,c_31,c_51,c_60,c_3598,c_3982,c_5544]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_27015,plain,
% 7.37/1.47      ( sK0(sK2,sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK3)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 7.37/1.47      inference(renaming,[status(thm)],[c_27014]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_8,plain,
% 7.37/1.47      ( ~ m1_pre_topc(X0,X1)
% 7.37/1.47      | v2_struct_0(X1)
% 7.37/1.47      | ~ v1_pre_topc(X2)
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | ~ l1_pre_topc(X2)
% 7.37/1.47      | ~ v2_pre_topc(X1)
% 7.37/1.47      | ~ v2_pre_topc(X2)
% 7.37/1.47      | k6_tmap_1(X1,sK0(X1,X0,X2)) != X2
% 7.37/1.47      | k8_tmap_1(X1,X0) = X2 ),
% 7.37/1.47      inference(cnf_transformation,[],[f67]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1472,plain,
% 7.37/1.47      ( ~ m1_pre_topc(X0,X1)
% 7.37/1.47      | ~ v1_pre_topc(X2)
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | ~ l1_pre_topc(X2)
% 7.37/1.47      | ~ v2_pre_topc(X1)
% 7.37/1.47      | ~ v2_pre_topc(X2)
% 7.37/1.47      | k6_tmap_1(X1,sK0(X1,X0,X2)) != X2
% 7.37/1.47      | k8_tmap_1(X1,X0) = X2
% 7.37/1.47      | sK2 != X1 ),
% 7.37/1.47      inference(resolution_lifted,[status(thm)],[c_8,c_33]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1473,plain,
% 7.37/1.47      ( ~ m1_pre_topc(X0,sK2)
% 7.37/1.47      | ~ v1_pre_topc(X1)
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | ~ l1_pre_topc(sK2)
% 7.37/1.47      | ~ v2_pre_topc(X1)
% 7.37/1.47      | ~ v2_pre_topc(sK2)
% 7.37/1.47      | k6_tmap_1(sK2,sK0(sK2,X0,X1)) != X1
% 7.37/1.47      | k8_tmap_1(sK2,X0) = X1 ),
% 7.37/1.47      inference(unflattening,[status(thm)],[c_1472]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1477,plain,
% 7.37/1.47      ( ~ v2_pre_topc(X1)
% 7.37/1.47      | ~ m1_pre_topc(X0,sK2)
% 7.37/1.47      | ~ v1_pre_topc(X1)
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | k6_tmap_1(sK2,sK0(sK2,X0,X1)) != X1
% 7.37/1.47      | k8_tmap_1(sK2,X0) = X1 ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_1473,c_32,c_31]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1478,plain,
% 7.37/1.47      ( ~ m1_pre_topc(X0,sK2)
% 7.37/1.47      | ~ v1_pre_topc(X1)
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | ~ v2_pre_topc(X1)
% 7.37/1.47      | k6_tmap_1(sK2,sK0(sK2,X0,X1)) != X1
% 7.37/1.47      | k8_tmap_1(sK2,X0) = X1 ),
% 7.37/1.47      inference(renaming,[status(thm)],[c_1477]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3255,plain,
% 7.37/1.47      ( k6_tmap_1(sK2,sK0(sK2,X0,X1)) != X1
% 7.37/1.47      | k8_tmap_1(sK2,X0) = X1
% 7.37/1.47      | m1_pre_topc(X0,sK2) != iProver_top
% 7.37/1.47      | v1_pre_topc(X1) != iProver_top
% 7.37/1.47      | l1_pre_topc(X1) != iProver_top
% 7.37/1.47      | v2_pre_topc(X1) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_1478]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_27019,plain,
% 7.37/1.47      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,u1_struct_0(sK3))
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 7.37/1.47      | m1_pre_topc(sK3,sK2) != iProver_top
% 7.37/1.47      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.37/1.47      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.37/1.47      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_27015,c_3255]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_38,plain,
% 7.37/1.47      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_56,plain,
% 7.37/1.47      ( m1_pre_topc(X0,X1) != iProver_top
% 7.37/1.47      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top
% 7.37/1.47      | l1_pre_topc(X1) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_58,plain,
% 7.37/1.47      ( m1_pre_topc(sK2,sK2) != iProver_top
% 7.37/1.47      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.37/1.47      | l1_pre_topc(sK2) != iProver_top ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_56]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_15,plain,
% 7.37/1.47      ( v3_pre_topc(u1_struct_0(X0),X1)
% 7.37/1.47      | ~ v1_tsep_1(X0,X1)
% 7.37/1.47      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.37/1.47      | ~ m1_pre_topc(X0,X1)
% 7.37/1.47      | ~ l1_pre_topc(X1) ),
% 7.37/1.47      inference(cnf_transformation,[],[f94]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_20,plain,
% 7.37/1.47      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.37/1.47      | ~ m1_pre_topc(X0,X1)
% 7.37/1.47      | ~ l1_pre_topc(X1) ),
% 7.37/1.47      inference(cnf_transformation,[],[f76]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_201,plain,
% 7.37/1.47      ( ~ v1_tsep_1(X0,X1)
% 7.37/1.47      | v3_pre_topc(u1_struct_0(X0),X1)
% 7.37/1.47      | ~ m1_pre_topc(X0,X1)
% 7.37/1.47      | ~ l1_pre_topc(X1) ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_15,c_20]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_202,plain,
% 7.37/1.47      ( v3_pre_topc(u1_struct_0(X0),X1)
% 7.37/1.47      | ~ v1_tsep_1(X0,X1)
% 7.37/1.47      | ~ m1_pre_topc(X0,X1)
% 7.37/1.47      | ~ l1_pre_topc(X1) ),
% 7.37/1.47      inference(renaming,[status(thm)],[c_201]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_28,negated_conjecture,
% 7.37/1.47      ( v1_tsep_1(sK3,sK2)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 7.37/1.47      inference(cnf_transformation,[],[f87]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_272,plain,
% 7.37/1.47      ( v1_tsep_1(sK3,sK2)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 7.37/1.47      inference(prop_impl,[status(thm)],[c_28]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_642,plain,
% 7.37/1.47      ( v3_pre_topc(u1_struct_0(X0),X1)
% 7.37/1.47      | ~ m1_pre_topc(X0,X1)
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 7.37/1.47      | sK3 != X0
% 7.37/1.47      | sK2 != X1 ),
% 7.37/1.47      inference(resolution_lifted,[status(thm)],[c_202,c_272]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_643,plain,
% 7.37/1.47      ( v3_pre_topc(u1_struct_0(sK3),sK2)
% 7.37/1.47      | ~ m1_pre_topc(sK3,sK2)
% 7.37/1.47      | ~ l1_pre_topc(sK2)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 7.37/1.47      inference(unflattening,[status(thm)],[c_642]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_645,plain,
% 7.37/1.47      ( v3_pre_topc(u1_struct_0(sK3),sK2)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_643,c_31,c_29]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3273,plain,
% 7.37/1.47      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 7.37/1.47      | v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3288,plain,
% 7.37/1.47      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.37/1.47      | m1_pre_topc(X0,X1) != iProver_top
% 7.37/1.47      | l1_pre_topc(X1) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_17,plain,
% 7.37/1.47      ( ~ v3_pre_topc(X0,X1)
% 7.37/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.37/1.47      | v2_struct_0(X1)
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | ~ v2_pre_topc(X1)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0) ),
% 7.37/1.47      inference(cnf_transformation,[],[f72]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1402,plain,
% 7.37/1.47      ( ~ v3_pre_topc(X0,X1)
% 7.37/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | ~ v2_pre_topc(X1)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X0)
% 7.37/1.47      | sK2 != X1 ),
% 7.37/1.47      inference(resolution_lifted,[status(thm)],[c_17,c_33]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1403,plain,
% 7.37/1.47      ( ~ v3_pre_topc(X0,sK2)
% 7.37/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.37/1.47      | ~ l1_pre_topc(sK2)
% 7.37/1.47      | ~ v2_pre_topc(sK2)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,X0) ),
% 7.37/1.47      inference(unflattening,[status(thm)],[c_1402]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1407,plain,
% 7.37/1.47      ( ~ v3_pre_topc(X0,sK2)
% 7.37/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,X0) ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_1403,c_32,c_31]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3258,plain,
% 7.37/1.47      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,X0)
% 7.37/1.47      | v3_pre_topc(X0,sK2) != iProver_top
% 7.37/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_1407]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_4213,plain,
% 7.37/1.47      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,u1_struct_0(X0))
% 7.37/1.47      | v3_pre_topc(u1_struct_0(X0),sK2) != iProver_top
% 7.37/1.47      | m1_pre_topc(X0,sK2) != iProver_top
% 7.37/1.47      | l1_pre_topc(sK2) != iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_3288,c_3258]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_5264,plain,
% 7.37/1.47      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.37/1.47      | v3_pre_topc(u1_struct_0(X0),sK2) != iProver_top
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,u1_struct_0(X0)) ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_4213,c_36]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_5265,plain,
% 7.37/1.47      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,u1_struct_0(X0))
% 7.37/1.47      | v3_pre_topc(u1_struct_0(X0),sK2) != iProver_top
% 7.37/1.47      | m1_pre_topc(X0,sK2) != iProver_top ),
% 7.37/1.47      inference(renaming,[status(thm)],[c_5264]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_5270,plain,
% 7.37/1.47      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,u1_struct_0(sK3))
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3)
% 7.37/1.47      | m1_pre_topc(sK3,sK2) != iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_3273,c_5265]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_27408,plain,
% 7.37/1.47      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k8_tmap_1(sK2,sK3) ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_27019,c_35,c_36,c_38,c_52,c_58,c_61,c_3599,c_3983,
% 7.37/1.47                 c_5270]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_27543,plain,
% 7.37/1.47      ( v1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
% 7.37/1.47      | l1_pre_topc(sK2) != iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_27408,c_4270]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2564,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3614,plain,
% 7.37/1.47      ( X0 != X1
% 7.37/1.47      | X0 = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
% 7.37/1.47      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_2564]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_4109,plain,
% 7.37/1.47      ( X0 != k8_tmap_1(sK2,sK3)
% 7.37/1.47      | X0 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_3614]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_5176,plain,
% 7.37/1.47      ( k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK3)
% 7.37/1.47      | k8_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_4109]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1,plain,
% 7.37/1.47      ( r1_tarski(X0,X0) ),
% 7.37/1.47      inference(cnf_transformation,[],[f90]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_6980,plain,
% 7.37/1.47      ( r1_tarski(k8_tmap_1(sK2,sK3),k8_tmap_1(sK2,sK3)) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_1]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_0,plain,
% 7.37/1.47      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.37/1.47      inference(cnf_transformation,[],[f58]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_4970,plain,
% 7.37/1.47      ( ~ r1_tarski(X0,k8_tmap_1(sK2,sK3))
% 7.37/1.47      | ~ r1_tarski(k8_tmap_1(sK2,sK3),X0)
% 7.37/1.47      | X0 = k8_tmap_1(sK2,sK3) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_0]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_6988,plain,
% 7.37/1.47      ( ~ r1_tarski(k8_tmap_1(sK2,sK3),k8_tmap_1(sK2,sK3))
% 7.37/1.47      | k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK3) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_4970]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2575,plain,
% 7.37/1.47      ( ~ v1_pre_topc(X0) | v1_pre_topc(X1) | X1 != X0 ),
% 7.37/1.47      theory(equality) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3402,plain,
% 7.37/1.47      ( ~ v1_pre_topc(X0)
% 7.37/1.47      | v1_pre_topc(k8_tmap_1(sK2,X1))
% 7.37/1.47      | k8_tmap_1(sK2,X1) != X0 ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_2575]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3487,plain,
% 7.37/1.47      ( v1_pre_topc(k8_tmap_1(sK2,X0))
% 7.37/1.47      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.37/1.47      | k8_tmap_1(sK2,X0) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_3402]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_8570,plain,
% 7.37/1.47      ( v1_pre_topc(k8_tmap_1(sK2,sK3))
% 7.37/1.47      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.37/1.47      | k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_3487]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_8571,plain,
% 7.37/1.47      ( k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 7.37/1.47      | v1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
% 7.37/1.47      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_8570]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_8573,plain,
% 7.37/1.47      ( k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 7.37/1.47      | v1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
% 7.37/1.47      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_8571]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_28058,plain,
% 7.37/1.47      ( v1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_27543,c_35,c_36,c_38,c_52,c_58,c_61,c_3599,c_3983,
% 7.37/1.47                 c_5176,c_5270,c_6980,c_6988,c_8573,c_27019]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_11,plain,
% 7.37/1.47      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.37/1.47      | ~ m1_pre_topc(X0,X1)
% 7.37/1.47      | v2_struct_0(X1)
% 7.37/1.47      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 7.37/1.47      | ~ v2_pre_topc(X1)
% 7.37/1.47      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 7.37/1.47      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 7.37/1.47      inference(cnf_transformation,[],[f93]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_211,plain,
% 7.37/1.47      ( ~ m1_pre_topc(X0,X1)
% 7.37/1.47      | v2_struct_0(X1)
% 7.37/1.47      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 7.37/1.47      | ~ v2_pre_topc(X1)
% 7.37/1.47      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 7.37/1.47      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_11,c_20]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1375,plain,
% 7.37/1.47      ( ~ m1_pre_topc(X0,X1)
% 7.37/1.47      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 7.37/1.47      | ~ v2_pre_topc(X1)
% 7.37/1.47      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 7.37/1.47      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0)
% 7.37/1.47      | sK2 != X1 ),
% 7.37/1.47      inference(resolution_lifted,[status(thm)],[c_211,c_33]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1376,plain,
% 7.37/1.47      ( ~ m1_pre_topc(X0,sK2)
% 7.37/1.47      | ~ v1_pre_topc(k8_tmap_1(sK2,X0))
% 7.37/1.47      | ~ l1_pre_topc(k8_tmap_1(sK2,X0))
% 7.37/1.47      | ~ l1_pre_topc(sK2)
% 7.37/1.47      | ~ v2_pre_topc(k8_tmap_1(sK2,X0))
% 7.37/1.47      | ~ v2_pre_topc(sK2)
% 7.37/1.47      | k6_tmap_1(sK2,u1_struct_0(X0)) = k8_tmap_1(sK2,X0) ),
% 7.37/1.47      inference(unflattening,[status(thm)],[c_1375]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1380,plain,
% 7.37/1.47      ( ~ v2_pre_topc(k8_tmap_1(sK2,X0))
% 7.37/1.47      | ~ m1_pre_topc(X0,sK2)
% 7.37/1.47      | ~ v1_pre_topc(k8_tmap_1(sK2,X0))
% 7.37/1.47      | ~ l1_pre_topc(k8_tmap_1(sK2,X0))
% 7.37/1.47      | k6_tmap_1(sK2,u1_struct_0(X0)) = k8_tmap_1(sK2,X0) ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_1376,c_32,c_31]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1381,plain,
% 7.37/1.47      ( ~ m1_pre_topc(X0,sK2)
% 7.37/1.47      | ~ v1_pre_topc(k8_tmap_1(sK2,X0))
% 7.37/1.47      | ~ l1_pre_topc(k8_tmap_1(sK2,X0))
% 7.37/1.47      | ~ v2_pre_topc(k8_tmap_1(sK2,X0))
% 7.37/1.47      | k6_tmap_1(sK2,u1_struct_0(X0)) = k8_tmap_1(sK2,X0) ),
% 7.37/1.47      inference(renaming,[status(thm)],[c_1380]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3259,plain,
% 7.37/1.47      ( k6_tmap_1(sK2,u1_struct_0(X0)) = k8_tmap_1(sK2,X0)
% 7.37/1.47      | m1_pre_topc(X0,sK2) != iProver_top
% 7.37/1.47      | v1_pre_topc(k8_tmap_1(sK2,X0)) != iProver_top
% 7.37/1.47      | l1_pre_topc(k8_tmap_1(sK2,X0)) != iProver_top
% 7.37/1.47      | v2_pre_topc(k8_tmap_1(sK2,X0)) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_1381]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_28072,plain,
% 7.37/1.47      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3)
% 7.37/1.47      | m1_pre_topc(sK3,sK2) != iProver_top
% 7.37/1.47      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 7.37/1.47      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_28058,c_3259]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_51,plain,
% 7.37/1.47      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_21]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_57,plain,
% 7.37/1.47      ( ~ m1_pre_topc(sK2,sK2)
% 7.37/1.47      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.37/1.47      | ~ l1_pre_topc(sK2) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_19]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_60,plain,
% 7.37/1.47      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
% 7.37/1.47      | ~ m1_pre_topc(sK2,sK2)
% 7.37/1.47      | ~ l1_pre_topc(sK2) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_18]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2,plain,
% 7.37/1.47      ( r1_tarski(X0,X0) ),
% 7.37/1.47      inference(cnf_transformation,[],[f91]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_100,plain,
% 7.37/1.47      ( r1_tarski(sK2,sK2) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_2]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_104,plain,
% 7.37/1.47      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_0]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3598,plain,
% 7.37/1.47      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
% 7.37/1.47      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.37/1.47      | ~ l1_pre_topc(sK2) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_3596]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2568,plain,
% 7.37/1.47      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 7.37/1.47      theory(equality) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_4332,plain,
% 7.37/1.47      ( ~ l1_pre_topc(X0)
% 7.37/1.47      | l1_pre_topc(k8_tmap_1(sK2,X1))
% 7.37/1.47      | k8_tmap_1(sK2,X1) != X0 ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_2568]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_5461,plain,
% 7.37/1.47      ( l1_pre_topc(k8_tmap_1(sK2,sK3))
% 7.37/1.47      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 7.37/1.47      | k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_4332]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_5463,plain,
% 7.37/1.47      ( l1_pre_topc(k8_tmap_1(sK2,sK3))
% 7.37/1.47      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.37/1.47      | k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_5461]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_7868,plain,
% 7.37/1.47      ( ~ m1_pre_topc(sK3,sK2)
% 7.37/1.47      | ~ v1_pre_topc(k8_tmap_1(sK2,sK3))
% 7.37/1.47      | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
% 7.37/1.47      | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
% 7.37/1.47      | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_1381]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_8572,plain,
% 7.37/1.47      ( v1_pre_topc(k8_tmap_1(sK2,sK3))
% 7.37/1.47      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.37/1.47      | k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_8570]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2567,plain,
% 7.37/1.47      ( ~ m1_pre_topc(X0,X1) | m1_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.37/1.47      theory(equality) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_5289,plain,
% 7.37/1.47      ( ~ m1_pre_topc(X0,X1)
% 7.37/1.47      | m1_pre_topc(k8_tmap_1(sK2,X2),X3)
% 7.37/1.47      | X3 != X1
% 7.37/1.47      | k8_tmap_1(sK2,X2) != X0 ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_2567]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_7809,plain,
% 7.37/1.47      ( m1_pre_topc(k8_tmap_1(sK2,X0),X1)
% 7.37/1.47      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
% 7.37/1.47      | X1 != X3
% 7.37/1.47      | k8_tmap_1(sK2,X0) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_5289]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_8778,plain,
% 7.37/1.47      ( m1_pre_topc(k8_tmap_1(sK2,sK3),X0)
% 7.37/1.47      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
% 7.37/1.47      | X0 != X2
% 7.37/1.47      | k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_7809]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_8780,plain,
% 7.37/1.47      ( m1_pre_topc(k8_tmap_1(sK2,sK3),sK2)
% 7.37/1.47      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2)
% 7.37/1.47      | k8_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 7.37/1.47      | sK2 != sK2 ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_8778]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_9075,plain,
% 7.37/1.47      ( ~ m1_pre_topc(k8_tmap_1(sK2,sK3),X0)
% 7.37/1.47      | ~ l1_pre_topc(X0)
% 7.37/1.47      | ~ v2_pre_topc(X0)
% 7.37/1.47      | v2_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_3]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_9077,plain,
% 7.37/1.47      ( ~ m1_pre_topc(k8_tmap_1(sK2,sK3),sK2)
% 7.37/1.47      | ~ l1_pre_topc(sK2)
% 7.37/1.47      | v2_pre_topc(k8_tmap_1(sK2,sK3))
% 7.37/1.47      | ~ v2_pre_topc(sK2) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_9075]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_28084,plain,
% 7.37/1.47      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_28072,c_32,c_35,c_31,c_36,c_29,c_38,c_51,c_52,c_57,
% 7.37/1.47                 c_58,c_60,c_61,c_100,c_104,c_3598,c_3599,c_3983,c_5176,
% 7.37/1.47                 c_5270,c_5463,c_6980,c_6988,c_7868,c_8572,c_8780,c_9077,
% 7.37/1.47                 c_27019]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_16,plain,
% 7.37/1.47      ( v3_pre_topc(X0,X1)
% 7.37/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.37/1.47      | v2_struct_0(X1)
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | ~ v2_pre_topc(X1)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k6_tmap_1(X1,X0) ),
% 7.37/1.47      inference(cnf_transformation,[],[f73]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1423,plain,
% 7.37/1.47      ( v3_pre_topc(X0,X1)
% 7.37/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | ~ v2_pre_topc(X1)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k6_tmap_1(X1,X0)
% 7.37/1.47      | sK2 != X1 ),
% 7.37/1.47      inference(resolution_lifted,[status(thm)],[c_16,c_33]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1424,plain,
% 7.37/1.47      ( v3_pre_topc(X0,sK2)
% 7.37/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.37/1.47      | ~ l1_pre_topc(sK2)
% 7.37/1.47      | ~ v2_pre_topc(sK2)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,X0) ),
% 7.37/1.47      inference(unflattening,[status(thm)],[c_1423]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1428,plain,
% 7.37/1.47      ( v3_pre_topc(X0,sK2)
% 7.37/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,X0) ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_1424,c_32,c_31]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3257,plain,
% 7.37/1.47      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,X0)
% 7.37/1.47      | v3_pre_topc(X0,sK2) = iProver_top
% 7.37/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_1428]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_27439,plain,
% 7.37/1.47      ( k6_tmap_1(sK2,X0) != k8_tmap_1(sK2,sK3)
% 7.37/1.47      | v3_pre_topc(X0,sK2) = iProver_top
% 7.37/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 7.37/1.47      inference(demodulation,[status(thm)],[c_27408,c_3257]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_28092,plain,
% 7.37/1.47      ( v3_pre_topc(u1_struct_0(sK3),sK2) = iProver_top
% 7.37/1.47      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_28084,c_27439]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_8010,plain,
% 7.37/1.47      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.37/1.47      | ~ m1_pre_topc(sK3,sK2)
% 7.37/1.47      | ~ l1_pre_topc(sK2) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_20]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_8011,plain,
% 7.37/1.47      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 7.37/1.47      | m1_pre_topc(sK3,sK2) != iProver_top
% 7.37/1.47      | l1_pre_topc(sK2) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_8010]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2579,plain,
% 7.37/1.47      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.37/1.47      theory(equality) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3384,plain,
% 7.37/1.47      ( ~ v3_pre_topc(X0,X1)
% 7.37/1.47      | v3_pre_topc(X2,sK2)
% 7.37/1.47      | X2 != X0
% 7.37/1.47      | sK2 != X1 ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_2579]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3573,plain,
% 7.37/1.47      ( v3_pre_topc(X0,sK2)
% 7.37/1.47      | ~ v3_pre_topc(u1_struct_0(X1),X2)
% 7.37/1.47      | X0 != u1_struct_0(X1)
% 7.37/1.47      | sK2 != X2 ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_3384]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_6104,plain,
% 7.37/1.47      ( v3_pre_topc(X0,sK2)
% 7.37/1.47      | ~ v3_pre_topc(u1_struct_0(sK3),sK2)
% 7.37/1.47      | X0 != u1_struct_0(sK3)
% 7.37/1.47      | sK2 != sK2 ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_3573]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_7715,plain,
% 7.37/1.47      ( v3_pre_topc(sK1(sK2,sK3),sK2)
% 7.37/1.47      | ~ v3_pre_topc(u1_struct_0(sK3),sK2)
% 7.37/1.47      | sK1(sK2,sK3) != u1_struct_0(sK3)
% 7.37/1.47      | sK2 != sK2 ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_6104]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_7716,plain,
% 7.37/1.47      ( sK1(sK2,sK3) != u1_struct_0(sK3)
% 7.37/1.47      | sK2 != sK2
% 7.37/1.47      | v3_pre_topc(sK1(sK2,sK3),sK2) = iProver_top
% 7.37/1.47      | v3_pre_topc(u1_struct_0(sK3),sK2) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_7715]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_13,plain,
% 7.37/1.47      ( v1_tsep_1(X0,X1)
% 7.37/1.47      | ~ m1_pre_topc(X0,X1)
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | sK1(X1,X0) = u1_struct_0(X0) ),
% 7.37/1.47      inference(cnf_transformation,[],[f70]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_26,negated_conjecture,
% 7.37/1.47      ( ~ v1_tsep_1(sK3,sK2)
% 7.37/1.47      | ~ m1_pre_topc(sK3,sK2)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 7.37/1.47      inference(cnf_transformation,[],[f89]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_270,plain,
% 7.37/1.47      ( ~ v1_tsep_1(sK3,sK2)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 7.37/1.47      inference(prop_impl,[status(thm)],[c_29,c_26]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_631,plain,
% 7.37/1.47      ( ~ m1_pre_topc(X0,X1)
% 7.37/1.47      | ~ l1_pre_topc(X1)
% 7.37/1.47      | sK1(X1,X0) = u1_struct_0(X0)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
% 7.37/1.47      | sK3 != X0
% 7.37/1.47      | sK2 != X1 ),
% 7.37/1.47      inference(resolution_lifted,[status(thm)],[c_13,c_270]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_632,plain,
% 7.37/1.47      ( ~ m1_pre_topc(sK3,sK2)
% 7.37/1.47      | ~ l1_pre_topc(sK2)
% 7.37/1.47      | sK1(sK2,sK3) = u1_struct_0(sK3)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 7.37/1.47      inference(unflattening,[status(thm)],[c_631]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_634,plain,
% 7.37/1.47      ( sK1(sK2,sK3) = u1_struct_0(sK3)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_632,c_31,c_29]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_12,plain,
% 7.37/1.47      ( ~ v3_pre_topc(sK1(X0,X1),X0)
% 7.37/1.47      | v1_tsep_1(X1,X0)
% 7.37/1.47      | ~ m1_pre_topc(X1,X0)
% 7.37/1.47      | ~ l1_pre_topc(X0) ),
% 7.37/1.47      inference(cnf_transformation,[],[f71]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_603,plain,
% 7.37/1.47      ( ~ v3_pre_topc(sK1(X0,X1),X0)
% 7.37/1.47      | ~ m1_pre_topc(X1,X0)
% 7.37/1.47      | ~ l1_pre_topc(X0)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
% 7.37/1.47      | sK3 != X1
% 7.37/1.47      | sK2 != X0 ),
% 7.37/1.47      inference(resolution_lifted,[status(thm)],[c_12,c_270]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_604,plain,
% 7.37/1.47      ( ~ v3_pre_topc(sK1(sK2,sK3),sK2)
% 7.37/1.47      | ~ m1_pre_topc(sK3,sK2)
% 7.37/1.47      | ~ l1_pre_topc(sK2)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 7.37/1.47      inference(unflattening,[status(thm)],[c_603]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_606,plain,
% 7.37/1.47      ( ~ v3_pre_topc(sK1(sK2,sK3),sK2)
% 7.37/1.47      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3) ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_604,c_31,c_29]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_608,plain,
% 7.37/1.47      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k8_tmap_1(sK2,sK3)
% 7.37/1.47      | v3_pre_topc(sK1(sK2,sK3),sK2) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(contradiction,plain,
% 7.37/1.47      ( $false ),
% 7.37/1.47      inference(minisat,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_28092,c_27408,c_8011,c_7716,c_634,c_608,c_104,c_100,
% 7.37/1.47                 c_38,c_36]) ).
% 7.37/1.47  
% 7.37/1.47  
% 7.37/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 7.37/1.47  
% 7.37/1.47  ------                               Statistics
% 7.37/1.47  
% 7.37/1.47  ------ General
% 7.37/1.47  
% 7.37/1.47  abstr_ref_over_cycles:                  0
% 7.37/1.47  abstr_ref_under_cycles:                 0
% 7.37/1.47  gc_basic_clause_elim:                   0
% 7.37/1.47  forced_gc_time:                         0
% 7.37/1.47  parsing_time:                           0.009
% 7.37/1.47  unif_index_cands_time:                  0.
% 7.37/1.47  unif_index_add_time:                    0.
% 7.37/1.47  orderings_time:                         0.
% 7.37/1.47  out_proof_time:                         0.016
% 7.37/1.47  total_time:                             0.917
% 7.37/1.47  num_of_symbols:                         56
% 7.37/1.47  num_of_terms:                           16144
% 7.37/1.47  
% 7.37/1.47  ------ Preprocessing
% 7.37/1.47  
% 7.37/1.47  num_of_splits:                          6
% 7.37/1.47  num_of_split_atoms:                     6
% 7.37/1.47  num_of_reused_defs:                     0
% 7.37/1.47  num_eq_ax_congr_red:                    9
% 7.37/1.47  num_of_sem_filtered_clauses:            1
% 7.37/1.47  num_of_subtypes:                        0
% 7.37/1.47  monotx_restored_types:                  0
% 7.37/1.47  sat_num_of_epr_types:                   0
% 7.37/1.47  sat_num_of_non_cyclic_types:            0
% 7.37/1.47  sat_guarded_non_collapsed_types:        0
% 7.37/1.47  num_pure_diseq_elim:                    0
% 7.37/1.47  simp_replaced_by:                       0
% 7.37/1.47  res_preprocessed:                       150
% 7.37/1.47  prep_upred:                             0
% 7.37/1.47  prep_unflattend:                        64
% 7.37/1.47  smt_new_axioms:                         0
% 7.37/1.47  pred_elim_cands:                        9
% 7.37/1.47  pred_elim:                              2
% 7.37/1.47  pred_elim_cl:                           -5
% 7.37/1.47  pred_elim_cycles:                       7
% 7.37/1.47  merged_defs:                            2
% 7.37/1.47  merged_defs_ncl:                        0
% 7.37/1.47  bin_hyper_res:                          2
% 7.37/1.47  prep_cycles:                            3
% 7.37/1.47  pred_elim_time:                         0.05
% 7.37/1.47  splitting_time:                         0.
% 7.37/1.47  sem_filter_time:                        0.
% 7.37/1.47  monotx_time:                            0.001
% 7.37/1.47  subtype_inf_time:                       0.
% 7.37/1.47  
% 7.37/1.47  ------ Problem properties
% 7.37/1.47  
% 7.37/1.47  clauses:                                42
% 7.37/1.47  conjectures:                            3
% 7.37/1.47  epr:                                    15
% 7.37/1.47  horn:                                   35
% 7.37/1.47  ground:                                 13
% 7.37/1.47  unary:                                  4
% 7.37/1.47  binary:                                 5
% 7.37/1.47  lits:                                   153
% 7.37/1.47  lits_eq:                                23
% 7.37/1.47  fd_pure:                                0
% 7.37/1.47  fd_pseudo:                              0
% 7.37/1.47  fd_cond:                                0
% 7.37/1.47  fd_pseudo_cond:                         7
% 7.37/1.47  ac_symbols:                             0
% 7.37/1.47  
% 7.37/1.47  ------ Propositional Solver
% 7.37/1.47  
% 7.37/1.47  prop_solver_calls:                      29
% 7.37/1.47  prop_fast_solver_calls:                 3466
% 7.37/1.47  smt_solver_calls:                       0
% 7.37/1.47  smt_fast_solver_calls:                  0
% 7.37/1.47  prop_num_of_clauses:                    10969
% 7.37/1.47  prop_preprocess_simplified:             16356
% 7.37/1.47  prop_fo_subsumed:                       438
% 7.37/1.47  prop_solver_time:                       0.
% 7.37/1.47  smt_solver_time:                        0.
% 7.37/1.47  smt_fast_solver_time:                   0.
% 7.37/1.47  prop_fast_solver_time:                  0.
% 7.37/1.47  prop_unsat_core_time:                   0.001
% 7.37/1.47  
% 7.37/1.47  ------ QBF
% 7.37/1.47  
% 7.37/1.47  qbf_q_res:                              0
% 7.37/1.47  qbf_num_tautologies:                    0
% 7.37/1.47  qbf_prep_cycles:                        0
% 7.37/1.47  
% 7.37/1.47  ------ BMC1
% 7.37/1.47  
% 7.37/1.47  bmc1_current_bound:                     -1
% 7.37/1.47  bmc1_last_solved_bound:                 -1
% 7.37/1.47  bmc1_unsat_core_size:                   -1
% 7.37/1.47  bmc1_unsat_core_parents_size:           -1
% 7.37/1.47  bmc1_merge_next_fun:                    0
% 7.37/1.47  bmc1_unsat_core_clauses_time:           0.
% 7.37/1.47  
% 7.37/1.47  ------ Instantiation
% 7.37/1.47  
% 7.37/1.47  inst_num_of_clauses:                    2675
% 7.37/1.47  inst_num_in_passive:                    228
% 7.37/1.47  inst_num_in_active:                     1256
% 7.37/1.47  inst_num_in_unprocessed:                1191
% 7.37/1.47  inst_num_of_loops:                      1510
% 7.37/1.47  inst_num_of_learning_restarts:          0
% 7.37/1.47  inst_num_moves_active_passive:          248
% 7.37/1.47  inst_lit_activity:                      0
% 7.37/1.47  inst_lit_activity_moves:                0
% 7.37/1.47  inst_num_tautologies:                   0
% 7.37/1.47  inst_num_prop_implied:                  0
% 7.37/1.47  inst_num_existing_simplified:           0
% 7.37/1.47  inst_num_eq_res_simplified:             0
% 7.37/1.47  inst_num_child_elim:                    0
% 7.37/1.47  inst_num_of_dismatching_blockings:      2773
% 7.37/1.47  inst_num_of_non_proper_insts:           5194
% 7.37/1.47  inst_num_of_duplicates:                 0
% 7.37/1.47  inst_inst_num_from_inst_to_res:         0
% 7.37/1.47  inst_dismatching_checking_time:         0.
% 7.37/1.47  
% 7.37/1.47  ------ Resolution
% 7.37/1.47  
% 7.37/1.47  res_num_of_clauses:                     0
% 7.37/1.47  res_num_in_passive:                     0
% 7.37/1.47  res_num_in_active:                      0
% 7.37/1.47  res_num_of_loops:                       153
% 7.37/1.47  res_forward_subset_subsumed:            466
% 7.37/1.47  res_backward_subset_subsumed:           0
% 7.37/1.47  res_forward_subsumed:                   1
% 7.37/1.47  res_backward_subsumed:                  0
% 7.37/1.47  res_forward_subsumption_resolution:     0
% 7.37/1.47  res_backward_subsumption_resolution:    0
% 7.37/1.47  res_clause_to_clause_subsumption:       5565
% 7.37/1.47  res_orphan_elimination:                 0
% 7.37/1.47  res_tautology_del:                      625
% 7.37/1.47  res_num_eq_res_simplified:              0
% 7.37/1.47  res_num_sel_changes:                    0
% 7.37/1.47  res_moves_from_active_to_pass:          0
% 7.37/1.47  
% 7.37/1.47  ------ Superposition
% 7.37/1.47  
% 7.37/1.47  sup_time_total:                         0.
% 7.37/1.47  sup_time_generating:                    0.
% 7.37/1.47  sup_time_sim_full:                      0.
% 7.37/1.47  sup_time_sim_immed:                     0.
% 7.37/1.47  
% 7.37/1.47  sup_num_of_clauses:                     1054
% 7.37/1.47  sup_num_in_active:                      248
% 7.37/1.47  sup_num_in_passive:                     806
% 7.37/1.47  sup_num_of_loops:                       301
% 7.37/1.47  sup_fw_superposition:                   855
% 7.37/1.47  sup_bw_superposition:                   1420
% 7.37/1.47  sup_immediate_simplified:               420
% 7.37/1.47  sup_given_eliminated:                   1
% 7.37/1.47  comparisons_done:                       0
% 7.37/1.47  comparisons_avoided:                    223
% 7.37/1.47  
% 7.37/1.47  ------ Simplifications
% 7.37/1.47  
% 7.37/1.47  
% 7.37/1.47  sim_fw_subset_subsumed:                 229
% 7.37/1.47  sim_bw_subset_subsumed:                 173
% 7.37/1.47  sim_fw_subsumed:                        156
% 7.37/1.47  sim_bw_subsumed:                        25
% 7.37/1.47  sim_fw_subsumption_res:                 0
% 7.37/1.47  sim_bw_subsumption_res:                 0
% 7.37/1.47  sim_tautology_del:                      53
% 7.37/1.47  sim_eq_tautology_del:                   54
% 7.37/1.47  sim_eq_res_simp:                        3
% 7.37/1.47  sim_fw_demodulated:                     1
% 7.37/1.47  sim_bw_demodulated:                     37
% 7.37/1.47  sim_light_normalised:                   12
% 7.37/1.47  sim_joinable_taut:                      0
% 7.37/1.47  sim_joinable_simp:                      0
% 7.37/1.47  sim_ac_normalised:                      0
% 7.37/1.47  sim_smt_subsumption:                    0
% 7.37/1.47  
%------------------------------------------------------------------------------
