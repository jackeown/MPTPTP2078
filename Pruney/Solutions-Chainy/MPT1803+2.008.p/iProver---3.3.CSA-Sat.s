%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:09 EST 2020

% Result     : CounterSatisfiable 3.51s
% Output     : Saturation 3.51s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_3628)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] : m1_pre_topc(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
     => m1_pre_topc(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( m1_pre_topc(sK0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f41])).

fof(f53,plain,(
    ! [X0] :
      ( m1_pre_topc(sK0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),sK4)
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r1_tmap_1(sK3,k8_tmap_1(X0,sK3),k2_tmap_1(X0,k8_tmap_1(X0,sK3),k9_tmap_1(X0,sK3),sK3),X2)
            & m1_subset_1(X2,u1_struct_0(sK3)) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2)
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tmap_1(X1,k8_tmap_1(sK2,X1),k2_tmap_1(sK2,k8_tmap_1(sK2,X1),k9_tmap_1(sK2,X1),X1),X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ~ r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4)
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f40,f50,f49,f48])).

fof(f80,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f76,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK1(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK1(X0,X1,X2)
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK1(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK1(X0,X1,X2)
                    & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k8_tmap_1(X0,X1) = X2
      | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k8_tmap_1(X0,X1) = X2
      | u1_struct_0(X1) = sK1(X0,X1,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f84,plain,(
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
    inference(equality_resolution,[],[f58])).

fof(f85,plain,(
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
    inference(equality_resolution,[],[f84])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X4 = X5
      | ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( u1_struct_0(X2) = X1
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    ! [X2,X0,X3] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f82,plain,(
    ~ r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f51])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k8_tmap_1(X0,X1) = X2
      | k6_tmap_1(X0,sK1(X0,X1,X2)) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2475,plain,
    ( k5_tmap_1(X0_58,X0_57) = k5_tmap_1(X1_58,X1_57)
    | X0_58 != X1_58
    | X0_57 != X1_57 ),
    theory(equality)).

cnf(c_2474,plain,
    ( u1_pre_topc(X0_58) = u1_pre_topc(X1_58)
    | X0_58 != X1_58 ),
    theory(equality)).

cnf(c_2455,plain,
    ( X0_60 != X1_60
    | X2_60 != X1_60
    | X2_60 = X0_60 ),
    theory(equality)).

cnf(c_2451,plain,
    ( X0_60 = X0_60 ),
    theory(equality)).

cnf(c_1,plain,
    ( m1_pre_topc(sK0(X0),X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_23,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_183,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_23])).

cnf(c_184,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(renaming,[status(thm)],[c_183])).

cnf(c_1000,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X0)
    | X0 != X2
    | k5_tmap_1(X0,u1_struct_0(X1)) = u1_pre_topc(k8_tmap_1(X0,X1))
    | sK0(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_184])).

cnf(c_1001,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0(X0))
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,u1_struct_0(sK0(X0))) = u1_pre_topc(k8_tmap_1(X0,sK0(X0))) ),
    inference(unflattening,[status(thm)],[c_1000])).

cnf(c_2431,plain,
    ( ~ v2_pre_topc(X0_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(sK0(X0_58))
    | ~ l1_pre_topc(X0_58)
    | k5_tmap_1(X0_58,u1_struct_0(sK0(X0_58))) = u1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) ),
    inference(subtyping,[status(esa)],[c_1001])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1290,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k5_tmap_1(X0,u1_struct_0(X1)) = u1_pre_topc(k8_tmap_1(X0,X1))
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_184,c_26])).

cnf(c_1291,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_1290])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1293,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1291,c_30,c_29,c_28,c_27])).

cnf(c_2417,plain,
    ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_1293])).

cnf(c_316,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1339,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(k8_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_1340,plain,
    ( v2_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1339])).

cnf(c_1342,plain,
    ( v2_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1340,c_30,c_29,c_28])).

cnf(c_2412,plain,
    ( v2_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_1342])).

cnf(c_3166,plain,
    ( v2_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2412])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1072,plain,
    ( v1_pre_topc(k8_tmap_1(X0,X1))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X0)
    | X0 != X2
    | sK0(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_15])).

cnf(c_1073,plain,
    ( v1_pre_topc(k8_tmap_1(X0,sK0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_1072])).

cnf(c_2427,plain,
    ( v1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58)))
    | ~ v2_pre_topc(X0_58)
    | v2_struct_0(X0_58)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_1073])).

cnf(c_3154,plain,
    ( v1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2427])).

cnf(c_1090,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(k8_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X0)
    | X0 != X2
    | sK0(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_14])).

cnf(c_1091,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(k8_tmap_1(X0,sK0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_1090])).

cnf(c_2426,plain,
    ( ~ v2_pre_topc(X0_58)
    | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58)))
    | v2_struct_0(X0_58)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_1091])).

cnf(c_3155,plain,
    ( v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2426])).

cnf(c_8,plain,
    ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | k8_tmap_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_952,plain,
    ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | X0 != X3
    | k8_tmap_1(X0,X1) = X2
    | sK0(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_953,plain,
    ( m1_subset_1(sK1(X0,sK0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | k8_tmap_1(X0,sK0(X0)) = X1 ),
    inference(unflattening,[status(thm)],[c_952])).

cnf(c_2433,plain,
    ( m1_subset_1(sK1(X0_58,sK0(X0_58),X1_58),k1_zfmisc_1(u1_struct_0(X0_58)))
    | ~ v1_pre_topc(X1_58)
    | ~ v2_pre_topc(X0_58)
    | ~ v2_pre_topc(X1_58)
    | v2_struct_0(X0_58)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(X1_58)
    | k8_tmap_1(X0_58,sK0(X0_58)) = X1_58 ),
    inference(subtyping,[status(esa)],[c_953])).

cnf(c_3148,plain,
    ( k8_tmap_1(X0_58,sK0(X0_58)) = X1_58
    | m1_subset_1(sK1(X0_58,sK0(X0_58),X1_58),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | v1_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2433])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2446,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_58)))
    | ~ v2_pre_topc(X0_58)
    | v2_struct_0(X0_58)
    | ~ l1_pre_topc(X0_58)
    | k7_tmap_1(X0_58,X0_57) = k6_partfun1(u1_struct_0(X0_58)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3135,plain,
    ( k7_tmap_1(X0_58,X0_57) = k6_partfun1(u1_struct_0(X0_58))
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2446])).

cnf(c_5966,plain,
    ( k8_tmap_1(X0_58,sK0(X0_58)) = X1_58
    | k7_tmap_1(X0_58,sK1(X0_58,sK0(X0_58),X1_58)) = k6_partfun1(u1_struct_0(X0_58))
    | v1_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(superposition,[status(thm)],[c_3148,c_3135])).

cnf(c_7563,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = X1_58
    | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),X1_58)) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v1_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_5966])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k8_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1108,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X2))
    | X0 != X1
    | sK0(X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_13])).

cnf(c_1109,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,sK0(X0))) ),
    inference(unflattening,[status(thm)],[c_1108])).

cnf(c_2425,plain,
    ( ~ v2_pre_topc(X0_58)
    | v2_struct_0(X0_58)
    | ~ l1_pre_topc(X0_58)
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) ),
    inference(subtyping,[status(esa)],[c_1109])).

cnf(c_2542,plain,
    ( v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2425])).

cnf(c_9701,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_pre_topc(X1_58) != iProver_top
    | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),X1_58)) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
    | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = X1_58 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7563,c_2542])).

cnf(c_9702,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = X1_58
    | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),X1_58)) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v1_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_9701])).

cnf(c_9717,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(X1_58,sK0(X1_58))
    | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(X1_58,sK0(X1_58)))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(k8_tmap_1(X1_58,sK0(X1_58))) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X1_58,sK0(X1_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3154,c_9702])).

cnf(c_3156,plain,
    ( v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2425])).

cnf(c_11351,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(X1_58,sK0(X1_58))
    | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(X1_58,sK0(X1_58)))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9717,c_3156,c_3155])).

cnf(c_11356,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_11351])).

cnf(c_31,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_32,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_33,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1350,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k8_tmap_1(X0,X1))
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_1351,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | l1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1350])).

cnf(c_1352,plain,
    ( v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1351])).

cnf(c_11715,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
    | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11356,c_31,c_32,c_33,c_1352])).

cnf(c_11716,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_11715])).

cnf(c_11357,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(X1_58,sK0(X1_58)),sK0(k8_tmap_1(X1_58,sK0(X1_58))))
    | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(k8_tmap_1(X1_58,sK0(X1_58)),sK0(k8_tmap_1(X1_58,sK0(X1_58)))))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X1_58,sK0(X1_58))) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X1_58,sK0(X1_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_11351])).

cnf(c_11707,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(X1_58,sK0(X1_58)),sK0(k8_tmap_1(X1_58,sK0(X1_58))))
    | k7_tmap_1(k8_tmap_1(X1_58,sK0(X1_58)),sK1(k8_tmap_1(X1_58,sK0(X1_58)),sK0(k8_tmap_1(X1_58,sK0(X1_58))),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(k8_tmap_1(X1_58,sK0(X1_58))))
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X1_58,sK0(X1_58))) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11357,c_3156])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK1(X1,X0,X2) = u1_struct_0(X0)
    | k8_tmap_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1126,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | X1 != X2
    | sK1(X1,X3,X0) = u1_struct_0(X3)
    | k8_tmap_1(X1,X3) = X0
    | sK0(X2) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_7])).

cnf(c_1127,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | sK1(X1,sK0(X1),X0) = u1_struct_0(sK0(X1))
    | k8_tmap_1(X1,sK0(X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_1126])).

cnf(c_2424,plain,
    ( ~ v1_pre_topc(X0_58)
    | ~ v2_pre_topc(X0_58)
    | ~ v2_pre_topc(X1_58)
    | v2_struct_0(X1_58)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(X1_58)
    | k8_tmap_1(X1_58,sK0(X1_58)) = X0_58
    | sK1(X1_58,sK0(X1_58),X0_58) = u1_struct_0(sK0(X1_58)) ),
    inference(subtyping,[status(esa)],[c_1127])).

cnf(c_3157,plain,
    ( k8_tmap_1(X0_58,sK0(X0_58)) = X1_58
    | sK1(X0_58,sK0(X0_58),X1_58) = u1_struct_0(sK0(X0_58))
    | v1_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2424])).

cnf(c_8379,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = X1_58
    | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),X1_58) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v1_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_3157])).

cnf(c_10993,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_pre_topc(X1_58) != iProver_top
    | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),X1_58) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
    | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = X1_58 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8379,c_2542])).

cnf(c_10994,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = X1_58
    | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),X1_58) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v1_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_10993])).

cnf(c_11009,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(X1_58,sK0(X1_58))
    | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(X1_58,sK0(X1_58))) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(k8_tmap_1(X1_58,sK0(X1_58))) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X1_58,sK0(X1_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3154,c_10994])).

cnf(c_11157,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(X1_58,sK0(X1_58))
    | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(X1_58,sK0(X1_58))) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11009,c_3156,c_3155])).

cnf(c_11163,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(X1_58,sK0(X1_58)),sK0(k8_tmap_1(X1_58,sK0(X1_58))))
    | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(k8_tmap_1(X1_58,sK0(X1_58)),sK0(k8_tmap_1(X1_58,sK0(X1_58))))) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X1_58,sK0(X1_58))) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X1_58,sK0(X1_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_11157])).

cnf(c_11647,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(X1_58,sK0(X1_58)),sK0(k8_tmap_1(X1_58,sK0(X1_58))))
    | sK1(k8_tmap_1(X1_58,sK0(X1_58)),sK0(k8_tmap_1(X1_58,sK0(X1_58))),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = u1_struct_0(sK0(k8_tmap_1(X1_58,sK0(X1_58))))
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X1_58) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X1_58,sK0(X1_58))) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11163,c_3156])).

cnf(c_2439,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_3142,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2439])).

cnf(c_11355,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
    | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3142,c_11351])).

cnf(c_11625,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
    | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11355,c_31,c_33])).

cnf(c_11626,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
    | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_11625])).

cnf(c_11162,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
    | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_11157])).

cnf(c_11326,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
    | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11162,c_31,c_32,c_33,c_1352])).

cnf(c_11327,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
    | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_11326])).

cnf(c_11161,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
    | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK0(sK2))) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3142,c_11157])).

cnf(c_11226,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
    | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK0(sK2))) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11161,c_31,c_33])).

cnf(c_11227,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
    | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK0(sK2))) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_11226])).

cnf(c_1328,plain,
    ( v1_pre_topc(k8_tmap_1(X0,X1))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_1329,plain,
    ( v1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1328])).

cnf(c_1331,plain,
    ( v1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1329,c_30,c_29,c_28])).

cnf(c_2413,plain,
    ( v1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_1331])).

cnf(c_3165,plain,
    ( v1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2413])).

cnf(c_11008,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
    | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK3)) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3165,c_10994])).

cnf(c_1341,plain,
    ( v2_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1340])).

cnf(c_11055,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
    | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK3)) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11008,c_31,c_32,c_33,c_1341,c_1352])).

cnf(c_11056,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
    | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK3)) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_11055])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1309,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(k8_tmap_1(X0,X1)) = u1_struct_0(X0)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_1310,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1309])).

cnf(c_1312,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1310,c_30,c_29,c_28,c_27])).

cnf(c_2415,plain,
    ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_1312])).

cnf(c_5964,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
    | m1_subset_1(sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2415,c_3148])).

cnf(c_6203,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
    | m1_subset_1(sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5964,c_31,c_32,c_33,c_1341,c_1352])).

cnf(c_6204,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
    | m1_subset_1(sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_6203])).

cnf(c_3664,plain,
    ( k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57) = k6_partfun1(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2415,c_3135])).

cnf(c_3665,plain,
    ( k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57) = k6_partfun1(u1_struct_0(sK2))
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3664,c_2415])).

cnf(c_5017,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57) = k6_partfun1(u1_struct_0(sK2))
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3665,c_31,c_32,c_33,c_1341,c_1352])).

cnf(c_5018,plain,
    ( k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57) = k6_partfun1(u1_struct_0(sK2))
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5017])).

cnf(c_6217,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58)) = k6_partfun1(u1_struct_0(sK2))
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(superposition,[status(thm)],[c_6204,c_5018])).

cnf(c_7431,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(X0_58,sK0(X0_58))
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3154,c_6217])).

cnf(c_2541,plain,
    ( v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2426])).

cnf(c_10472,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(X0_58,sK0(X0_58))
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7431,c_2541,c_2542])).

cnf(c_10473,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(X0_58,sK0(X0_58))
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_10472])).

cnf(c_10486,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_10473])).

cnf(c_10879,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
    | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10486,c_2542])).

cnf(c_10880,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_10879])).

cnf(c_8378,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
    | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_3157])).

cnf(c_8957,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_pre_topc(X0_58) != iProver_top
    | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
    | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8378,c_31,c_32,c_33,c_1352])).

cnf(c_8958,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
    | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_8957])).

cnf(c_8970,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(X0_58,sK0(X0_58))
    | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3154,c_8958])).

cnf(c_10323,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(X0_58,sK0(X0_58))
    | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
    | v2_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8970,c_2541,c_2542])).

cnf(c_10324,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(X0_58,sK0(X0_58))
    | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_10323])).

cnf(c_10337,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
    | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_10324])).

cnf(c_10865,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
    | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10337,c_2542])).

cnf(c_10866,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
    | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_10865])).

cnf(c_6216,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
    | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58)) = k6_partfun1(u1_struct_0(sK2))
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6204,c_3135])).

cnf(c_6597,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_pre_topc(X0_58) != iProver_top
    | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58)) = k6_partfun1(u1_struct_0(sK2))
    | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6216,c_31,c_32,c_33])).

cnf(c_6598,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
    | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58)) = k6_partfun1(u1_struct_0(sK2))
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_6597])).

cnf(c_7429,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(X0_58,sK0(X0_58))
    | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3154,c_6598])).

cnf(c_9339,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(X0_58,sK0(X0_58))
    | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7429,c_2541,c_2542])).

cnf(c_9340,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(X0_58,sK0(X0_58))
    | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_9339])).

cnf(c_9353,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_9340])).

cnf(c_10740,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
    | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9353,c_2542])).

cnf(c_10741,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
    | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_10740])).

cnf(c_5967,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = X0_58
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),X0_58)) = k6_partfun1(u1_struct_0(sK2))
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3148,c_5018])).

cnf(c_6464,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_pre_topc(X0_58) != iProver_top
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),X0_58)) = k6_partfun1(u1_struct_0(sK2))
    | k8_tmap_1(sK2,sK0(sK2)) = X0_58
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5967,c_31,c_32,c_33])).

cnf(c_6465,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = X0_58
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),X0_58)) = k6_partfun1(u1_struct_0(sK2))
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_6464])).

cnf(c_7430,plain,
    ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK0(sK2))
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3154,c_6465])).

cnf(c_10061,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK0(sK2))
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7430,c_2541,c_2542])).

cnf(c_10062,plain,
    ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK0(sK2))
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_10061])).

cnf(c_10073,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_10062])).

cnf(c_10726,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
    | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10073,c_2542])).

cnf(c_10727,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_10726])).

cnf(c_1255,plain,
    ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | k8_tmap_1(X0,X1) = X2
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_26])).

cnf(c_1256,plain,
    ( m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_1255])).

cnf(c_1260,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1256,c_30,c_29,c_28])).

cnf(c_1261,plain,
    ( m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_1260])).

cnf(c_2419,plain,
    ( m1_subset_1(sK1(sK2,sK3,X0_58),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_pre_topc(X0_58)
    | ~ v2_pre_topc(X0_58)
    | ~ l1_pre_topc(X0_58)
    | k8_tmap_1(sK2,sK3) = X0_58 ),
    inference(subtyping,[status(esa)],[c_1261])).

cnf(c_3162,plain,
    ( k8_tmap_1(sK2,sK3) = X0_58
    | m1_subset_1(sK1(sK2,sK3,X0_58),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2419])).

cnf(c_5027,plain,
    ( k8_tmap_1(sK2,sK3) = X0_58
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,X0_58)) = k6_partfun1(u1_struct_0(sK2))
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(superposition,[status(thm)],[c_3162,c_5018])).

cnf(c_7433,plain,
    ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3154,c_5027])).

cnf(c_9101,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7433,c_2541,c_2542])).

cnf(c_9102,plain,
    ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_9101])).

cnf(c_9115,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_9102])).

cnf(c_10607,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
    | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9115,c_2542])).

cnf(c_10608,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_10607])).

cnf(c_4547,plain,
    ( k8_tmap_1(sK2,sK3) = X0_58
    | k7_tmap_1(sK2,sK1(sK2,sK3,X0_58)) = k6_partfun1(u1_struct_0(sK2))
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3162,c_3135])).

cnf(c_6128,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_pre_topc(X0_58) != iProver_top
    | k7_tmap_1(sK2,sK1(sK2,sK3,X0_58)) = k6_partfun1(u1_struct_0(sK2))
    | k8_tmap_1(sK2,sK3) = X0_58 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4547,c_31,c_32,c_33])).

cnf(c_6129,plain,
    ( k8_tmap_1(sK2,sK3) = X0_58
    | k7_tmap_1(sK2,sK1(sK2,sK3,X0_58)) = k6_partfun1(u1_struct_0(sK2))
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_6128])).

cnf(c_7432,plain,
    ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3154,c_6129])).

cnf(c_1298,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_26])).

cnf(c_1299,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1298])).

cnf(c_2448,plain,
    ( X0_57 = X0_57 ),
    theory(equality)).

cnf(c_4173,plain,
    ( k1_zfmisc_1(u1_struct_0(X0_58)) = k1_zfmisc_1(u1_struct_0(X0_58)) ),
    inference(instantiation,[status(thm)],[c_2448])).

cnf(c_4178,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4173])).

cnf(c_6560,plain,
    ( ~ m1_subset_1(sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2446])).

cnf(c_2462,plain,
    ( ~ m1_subset_1(X0_57,X1_57)
    | m1_subset_1(X2_57,X3_57)
    | X2_57 != X0_57
    | X3_57 != X1_57 ),
    theory(equality)).

cnf(c_3593,plain,
    ( m1_subset_1(X0_57,X1_57)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | X1_57 != k1_zfmisc_1(u1_struct_0(sK2))
    | X0_57 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2462])).

cnf(c_6622,plain,
    ( m1_subset_1(sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58))),X0_57)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | X0_57 != k1_zfmisc_1(u1_struct_0(sK2))
    | sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58))) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3593])).

cnf(c_7379,plain,
    ( m1_subset_1(sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58))) != u1_struct_0(sK3)
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_6622])).

cnf(c_1361,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | sK1(X1,X2,X0) = u1_struct_0(X2)
    | k8_tmap_1(X1,X2) = X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_26])).

cnf(c_1362,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_1361])).

cnf(c_1366,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1362,c_30,c_29,c_28])).

cnf(c_1367,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_1366])).

cnf(c_2410,plain,
    ( ~ v1_pre_topc(X0_58)
    | ~ v2_pre_topc(X0_58)
    | ~ l1_pre_topc(X0_58)
    | k8_tmap_1(sK2,sK3) = X0_58
    | sK1(sK2,sK3,X0_58) = u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_1367])).

cnf(c_3168,plain,
    ( k8_tmap_1(sK2,sK3) = X0_58
    | sK1(sK2,sK3,X0_58) = u1_struct_0(sK3)
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2410])).

cnf(c_7434,plain,
    ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
    | sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(sK3)
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3154,c_3168])).

cnf(c_7781,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
    | sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(sK3)
    | v2_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7434,c_2541,c_2542])).

cnf(c_7782,plain,
    ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
    | sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(sK3)
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_7781])).

cnf(c_8101,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7432,c_30,c_29,c_28,c_1299,c_2541,c_2542,c_4178,c_6560,c_7379,c_7434])).

cnf(c_8102,plain,
    ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_8101])).

cnf(c_8114,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_8102])).

cnf(c_10594,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
    | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8114,c_2542])).

cnf(c_10595,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_10594])).

cnf(c_10484,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3142,c_10473])).

cnf(c_10518,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10484,c_31,c_33])).

cnf(c_10335,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
    | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK0(sK2))) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3142,c_10324])).

cnf(c_10369,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
    | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK0(sK2))) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10335,c_31,c_33])).

cnf(c_6935,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = X0_58
    | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),X0_58)) = k6_partfun1(u1_struct_0(sK2))
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3142,c_5966])).

cnf(c_6961,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | k8_tmap_1(sK2,sK0(sK2)) = X0_58
    | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),X0_58)) = k6_partfun1(u1_struct_0(sK2))
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6935,c_31,c_33])).

cnf(c_6962,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = X0_58
    | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),X0_58)) = k6_partfun1(u1_struct_0(sK2))
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_6961])).

cnf(c_7428,plain,
    ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK0(sK2))
    | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3154,c_6962])).

cnf(c_7997,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK0(sK2))
    | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7428,c_2541,c_2542])).

cnf(c_7998,plain,
    ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK0(sK2))
    | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_7997])).

cnf(c_8008,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
    | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_7998])).

cnf(c_10239,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
    | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8008,c_2542])).

cnf(c_10240,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
    | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_10239])).

cnf(c_8377,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = X0_58
    | sK1(sK2,sK0(sK2),X0_58) = u1_struct_0(sK0(sK2))
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3142,c_3157])).

cnf(c_8436,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | k8_tmap_1(sK2,sK0(sK2)) = X0_58
    | sK1(sK2,sK0(sK2),X0_58) = u1_struct_0(sK0(sK2))
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8377,c_31,c_33])).

cnf(c_8437,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = X0_58
    | sK1(sK2,sK0(sK2),X0_58) = u1_struct_0(sK0(sK2))
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_8436])).

cnf(c_8448,plain,
    ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK0(sK2))
    | sK1(sK2,sK0(sK2),k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(sK0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3154,c_8437])).

cnf(c_8792,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK0(sK2))
    | sK1(sK2,sK0(sK2),k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(sK0(sK2))
    | v2_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8448,c_2541,c_2542])).

cnf(c_8793,plain,
    ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK0(sK2))
    | sK1(sK2,sK0(sK2),k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(sK0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_8792])).

cnf(c_8803,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
    | sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = u1_struct_0(sK0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_8793])).

cnf(c_10226,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = u1_struct_0(sK0(sK2))
    | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8803,c_2542])).

cnf(c_10227,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
    | sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = u1_struct_0(sK0(sK2))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_10226])).

cnf(c_10072,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_10062])).

cnf(c_10103,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
    | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10072,c_31,c_32,c_33,c_1352])).

cnf(c_10104,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_10103])).

cnf(c_9716,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3165,c_9702])).

cnf(c_9933,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9716,c_31,c_32,c_33,c_1341,c_1352])).

cnf(c_9934,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_9933])).

cnf(c_9114,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_9102])).

cnf(c_9925,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
    | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9114,c_31,c_32,c_33,c_1352])).

cnf(c_9926,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_9925])).

cnf(c_9,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(k8_tmap_1(X1,X0))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(k8_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k8_tmap_1(X1,X0))
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_206,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_23,c_15,c_14,c_13])).

cnf(c_207,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_206])).

cnf(c_982,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | X0 != X1
    | k6_tmap_1(X0,u1_struct_0(X2)) = k8_tmap_1(X0,X2)
    | sK0(X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_207])).

cnf(c_983,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(sK0(X0))) = k8_tmap_1(X0,sK0(X0)) ),
    inference(unflattening,[status(thm)],[c_982])).

cnf(c_2432,plain,
    ( ~ v2_pre_topc(X0_58)
    | v2_struct_0(X0_58)
    | ~ l1_pre_topc(X0_58)
    | k6_tmap_1(X0_58,u1_struct_0(sK0(X0_58))) = k8_tmap_1(X0_58,sK0(X0_58)) ),
    inference(subtyping,[status(esa)],[c_983])).

cnf(c_3149,plain,
    ( k6_tmap_1(X0_58,u1_struct_0(sK0(X0_58))) = k8_tmap_1(X0_58,sK0(X0_58))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2432])).

cnf(c_7564,plain,
    ( k6_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_3149])).

cnf(c_9763,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | k6_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7564,c_2542])).

cnf(c_9764,plain,
    ( k6_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_9763])).

cnf(c_1021,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_23])).

cnf(c_1022,plain,
    ( m1_subset_1(u1_struct_0(sK0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_1021])).

cnf(c_2430,plain,
    ( m1_subset_1(u1_struct_0(sK0(X0_58)),k1_zfmisc_1(u1_struct_0(X0_58)))
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_1022])).

cnf(c_3151,plain,
    ( m1_subset_1(u1_struct_0(sK0(X0_58)),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2430])).

cnf(c_4301,plain,
    ( k7_tmap_1(X0_58,u1_struct_0(sK0(X0_58))) = k6_partfun1(u1_struct_0(X0_58))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(superposition,[status(thm)],[c_3151,c_3135])).

cnf(c_7565,plain,
    ( k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_4301])).

cnf(c_9615,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7565,c_2542])).

cnf(c_9616,plain,
    ( k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_9615])).

cnf(c_9351,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
    | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3142,c_9340])).

cnf(c_9607,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
    | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9351,c_31,c_33])).

cnf(c_9113,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3142,c_9102])).

cnf(c_9331,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9113,c_31,c_33])).

cnf(c_7794,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
    | sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = u1_struct_0(sK3)
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_7782])).

cnf(c_9088,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = u1_struct_0(sK3)
    | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7794,c_2542])).

cnf(c_9089,plain,
    ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
    | sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = u1_struct_0(sK3)
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_9088])).

cnf(c_8969,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
    | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK3)) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3165,c_8958])).

cnf(c_9002,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
    | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK3)) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8969,c_31,c_32,c_33,c_1341,c_1352])).

cnf(c_9003,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
    | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK3)) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_9002])).

cnf(c_8802,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
    | sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))) = u1_struct_0(sK0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_8793])).

cnf(c_8831,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))) = u1_struct_0(sK0(sK2))
    | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8802,c_31,c_32,c_33,c_1352])).

cnf(c_8832,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
    | sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))) = u1_struct_0(sK0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8831])).

cnf(c_8447,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3)) = u1_struct_0(sK0(sK2))
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3165,c_8437])).

cnf(c_8471,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3)) = u1_struct_0(sK0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8447])).

cnf(c_8680,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3)) = u1_struct_0(sK0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8447,c_30,c_29,c_28,c_1329,c_1340,c_1351,c_3628])).

cnf(c_8112,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3142,c_8102])).

cnf(c_8145,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8112])).

cnf(c_8240,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8112,c_31,c_32,c_33,c_1094,c_1112,c_7550])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2445,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_58)))
    | m1_subset_1(k7_tmap_1(X0_58,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(k6_tmap_1(X0_58,X0_57)))))
    | ~ v2_pre_topc(X0_58)
    | v2_struct_0(X0_58)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3136,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
    | m1_subset_1(k7_tmap_1(X0_58,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(k6_tmap_1(X0_58,X0_57))))) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2445])).

cnf(c_8245,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | m1_subset_1(sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2)))))))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8240,c_3136])).

cnf(c_1074,plain,
    ( v1_pre_topc(k8_tmap_1(X0,sK0(X0))) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1073])).

cnf(c_1076,plain,
    ( v1_pre_topc(k8_tmap_1(sK2,sK0(sK2))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1074])).

cnf(c_1092,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_pre_topc(k8_tmap_1(X0,sK0(X0))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1091])).

cnf(c_1094,plain,
    ( v2_pre_topc(k8_tmap_1(sK2,sK0(sK2))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1092])).

cnf(c_1110,plain,
    ( v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0,sK0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1109])).

cnf(c_1112,plain,
    ( v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1110])).

cnf(c_3548,plain,
    ( m1_subset_1(sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58)))
    | ~ v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58)))
    | ~ l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58)))
    | k8_tmap_1(sK2,sK3) = k8_tmap_1(X0_58,sK0(X0_58)) ),
    inference(instantiation,[status(thm)],[c_2419])).

cnf(c_3554,plain,
    ( k8_tmap_1(sK2,sK3) = k8_tmap_1(X0_58,sK0(X0_58))
    | m1_subset_1(sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
    | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
    | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3548])).

cnf(c_3556,plain,
    ( k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK0(sK2))
    | m1_subset_1(sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_pre_topc(k8_tmap_1(sK2,sK0(sK2))) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK0(sK2))) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK0(sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3554])).

cnf(c_2453,plain,
    ( X0_58 != X1_58
    | X2_58 != X1_58
    | X2_58 = X0_58 ),
    theory(equality)).

cnf(c_3833,plain,
    ( X0_58 != X1_58
    | X0_58 = k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK3) != X1_58 ),
    inference(instantiation,[status(thm)],[c_2453])).

cnf(c_4060,plain,
    ( X0_58 != k8_tmap_1(X1_58,X2_58)
    | X0_58 = k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK3) != k8_tmap_1(X1_58,X2_58) ),
    inference(instantiation,[status(thm)],[c_3833])).

cnf(c_4759,plain,
    ( X0_58 != k8_tmap_1(X1_58,sK0(X1_58))
    | X0_58 = k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK3) != k8_tmap_1(X1_58,sK0(X1_58)) ),
    inference(instantiation,[status(thm)],[c_4060])).

cnf(c_4983,plain,
    ( k8_tmap_1(X0_58,sK0(X0_58)) != k8_tmap_1(X0_58,sK0(X0_58))
    | k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK3) != k8_tmap_1(X0_58,sK0(X0_58)) ),
    inference(instantiation,[status(thm)],[c_4759])).

cnf(c_4985,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) != k8_tmap_1(sK2,sK0(sK2))
    | k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4983])).

cnf(c_2449,plain,
    ( X0_58 = X0_58 ),
    theory(equality)).

cnf(c_4984,plain,
    ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(X0_58,sK0(X0_58)) ),
    inference(instantiation,[status(thm)],[c_2449])).

cnf(c_4986,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4984])).

cnf(c_8554,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2)))))))) = iProver_top
    | k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8245,c_31,c_32,c_33,c_1076,c_1094,c_1112,c_3556,c_4985,c_4986])).

cnf(c_8555,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2)))))))) = iProver_top ),
    inference(renaming,[status(thm)],[c_8554])).

cnf(c_11,plain,
    ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2444,plain,
    ( v1_funct_2(k7_tmap_1(X0_58,X0_57),u1_struct_0(X0_58),u1_struct_0(k6_tmap_1(X0_58,X0_57)))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_58)))
    | ~ v2_pre_topc(X0_58)
    | v2_struct_0(X0_58)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_3137,plain,
    ( v1_funct_2(k7_tmap_1(X0_58,X0_57),u1_struct_0(X0_58),u1_struct_0(k6_tmap_1(X0_58,X0_57))) = iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2444])).

cnf(c_8246,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2)))))) = iProver_top
    | m1_subset_1(sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8240,c_3137])).

cnf(c_8545,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2)))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8246,c_31,c_32,c_33,c_1076,c_1094,c_1112,c_3556,c_4985,c_4986])).

cnf(c_8113,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_8102])).

cnf(c_8275,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
    | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8113,c_31,c_32,c_33,c_1352])).

cnf(c_8276,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8275])).

cnf(c_8007,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
    | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_7998])).

cnf(c_8093,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
    | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8007,c_31,c_32,c_33,c_1352])).

cnf(c_8094,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
    | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8093])).

cnf(c_7793,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
    | sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))) = u1_struct_0(sK3)
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_7782])).

cnf(c_7989,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))) = u1_struct_0(sK3)
    | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7793,c_31,c_32,c_33,c_1352])).

cnf(c_7990,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
    | sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))) = u1_struct_0(sK3)
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7989])).

cnf(c_7792,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2))) = u1_struct_0(sK3)
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3142,c_7782])).

cnf(c_7825,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2))) = u1_struct_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7792])).

cnf(c_7831,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2))) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7792,c_31,c_32,c_33,c_1094,c_1112,c_7556])).

cnf(c_6972,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3165,c_6962])).

cnf(c_6973,plain,
    ( ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6972])).

cnf(c_7185,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6972,c_31,c_32,c_33,c_1341,c_1352])).

cnf(c_7189,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | m1_subset_1(sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))))))) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7185,c_3136])).

cnf(c_1330,plain,
    ( v1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1329])).

cnf(c_3636,plain,
    ( m1_subset_1(sK1(X0_58,sK0(X0_58),k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(X0_58)))
    | ~ v1_pre_topc(k8_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(X0_58)
    | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
    | v2_struct_0(X0_58)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
    | k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2433])).

cnf(c_3637,plain,
    ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
    | m1_subset_1(sK1(X0_58,sK0(X0_58),k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
    | v1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3636])).

cnf(c_3639,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | m1_subset_1(sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3637])).

cnf(c_7360,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))))))) = iProver_top
    | k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7189,c_31,c_32,c_33,c_1330,c_1341,c_1352,c_3639])).

cnf(c_7361,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))))))) = iProver_top ),
    inference(renaming,[status(thm)],[c_7360])).

cnf(c_7190,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))))) = iProver_top
    | m1_subset_1(sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7185,c_3137])).

cnf(c_7262,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7190,c_31,c_32,c_33,c_1330,c_1341,c_1352,c_3639])).

cnf(c_6609,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3165,c_6598])).

cnf(c_7219,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6609,c_31,c_32,c_33,c_1341,c_1352])).

cnf(c_7220,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7219])).

cnf(c_6677,plain,
    ( k6_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_3149])).

cnf(c_7079,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | k6_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6677,c_31,c_32,c_33,c_1352])).

cnf(c_7080,plain,
    ( k6_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7079])).

cnf(c_6676,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK0(sK2))) = k8_tmap_1(sK2,sK0(sK2))
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3142,c_3149])).

cnf(c_2530,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,u1_struct_0(sK0(sK2))) = k8_tmap_1(sK2,sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2432])).

cnf(c_6693,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK0(sK2))) = k8_tmap_1(sK2,sK0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6676,c_30,c_29,c_28,c_2530])).

cnf(c_4772,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK0(sK2))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3142,c_4301])).

cnf(c_1024,plain,
    ( m1_subset_1(u1_struct_0(sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1022])).

cnf(c_3578,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0(X0_58)),k1_zfmisc_1(u1_struct_0(X0_58)))
    | ~ v2_pre_topc(X0_58)
    | v2_struct_0(X0_58)
    | ~ l1_pre_topc(X0_58)
    | k7_tmap_1(X0_58,u1_struct_0(sK0(X0_58))) = k6_partfun1(u1_struct_0(X0_58)) ),
    inference(instantiation,[status(thm)],[c_2446])).

cnf(c_3580,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k7_tmap_1(sK2,u1_struct_0(sK0(sK2))) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3578])).

cnf(c_4905,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK0(sK2))) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4772,c_30,c_29,c_28,c_1024,c_3580])).

cnf(c_4909,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK0(sK2))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4905,c_3137])).

cnf(c_1023,plain,
    ( m1_subset_1(u1_struct_0(sK0(X0)),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1022])).

cnf(c_1025,plain,
    ( m1_subset_1(u1_struct_0(sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1023])).

cnf(c_5408,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK0(sK2))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4909,c_31,c_32,c_33,c_1025])).

cnf(c_6697,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK0(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6693,c_5408])).

cnf(c_4908,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK0(sK2))))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4905,c_3136])).

cnf(c_5503,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK0(sK2))))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4908,c_31,c_32,c_33,c_1025])).

cnf(c_6696,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK0(sK2)))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6693,c_5503])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k7_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2443,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_58)))
    | ~ v2_pre_topc(X0_58)
    | v1_funct_1(k7_tmap_1(X0_58,X0_57))
    | v2_struct_0(X0_58)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3138,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(k7_tmap_1(X0_58,X0_57)) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2443])).

cnf(c_6215,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6204,c_3138])).

cnf(c_6584,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_pre_topc(X0_58) != iProver_top
    | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
    | v1_funct_1(k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6215,c_31,c_32,c_33])).

cnf(c_6585,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_6584])).

cnf(c_6476,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3165,c_6465])).

cnf(c_6479,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6476,c_31,c_32,c_33,c_1341,c_1352])).

cnf(c_6480,plain,
    ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6479])).

cnf(c_6367,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3165,c_6217])).

cnf(c_6370,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6367,c_31,c_32,c_33,c_1341,c_1352])).

cnf(c_6371,plain,
    ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
    | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6370])).

cnf(c_4546,plain,
    ( k8_tmap_1(sK2,sK3) = X0_58
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,sK1(sK2,sK3,X0_58))) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3162,c_3138])).

cnf(c_6116,plain,
    ( l1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_pre_topc(X0_58) != iProver_top
    | k8_tmap_1(sK2,sK3) = X0_58
    | v1_funct_1(k7_tmap_1(sK2,sK1(sK2,sK3,X0_58))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4546,c_31,c_32,c_33])).

cnf(c_6117,plain,
    ( k8_tmap_1(sK2,sK3) = X0_58
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,sK1(sK2,sK3,X0_58))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(renaming,[status(thm)],[c_6116])).

cnf(c_4299,plain,
    ( m1_subset_1(u1_struct_0(sK0(k8_tmap_1(sK2,sK3))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2415,c_3151])).

cnf(c_4377,plain,
    ( m1_subset_1(u1_struct_0(sK0(k8_tmap_1(sK2,sK3))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4299,c_31,c_32,c_33,c_1352])).

cnf(c_4383,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4377,c_3135])).

cnf(c_5379,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4383,c_31,c_32,c_33])).

cnf(c_5383,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK0(k8_tmap_1(sK2,sK3))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5379,c_3136])).

cnf(c_6047,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5383,c_31,c_32,c_33,c_1352,c_4299])).

cnf(c_5965,plain,
    ( k8_tmap_1(X0_58,sK0(X0_58)) = X1_58
    | v1_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v1_funct_1(k7_tmap_1(X0_58,sK1(X0_58,sK0(X0_58),X1_58))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X1_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(superposition,[status(thm)],[c_3148,c_3138])).

cnf(c_5028,plain,
    ( k7_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK0(sK2))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3151,c_5018])).

cnf(c_5836,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | k7_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK0(sK2))) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5028,c_33])).

cnf(c_5837,plain,
    ( k7_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK0(sK2))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5836])).

cnf(c_16,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_934,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X0)
    | X0 != X2
    | sK0(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_16])).

cnf(c_935,plain,
    ( m1_subset_1(k9_tmap_1(X0,sK0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK0(X0))))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_934])).

cnf(c_2434,plain,
    ( m1_subset_1(k9_tmap_1(X0_58,sK0(X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))))
    | ~ v2_pre_topc(X0_58)
    | v2_struct_0(X0_58)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_935])).

cnf(c_3147,plain,
    ( m1_subset_1(k9_tmap_1(X0_58,sK0(X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58)))))) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2434])).

cnf(c_5309,plain,
    ( m1_subset_1(k9_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))))) = iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2415,c_3147])).

cnf(c_5614,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | m1_subset_1(k9_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5309,c_31,c_32,c_33,c_1341,c_1352])).

cnf(c_5615,plain,
    ( m1_subset_1(k9_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5614])).

cnf(c_5384,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK0(k8_tmap_1(sK2,sK3))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5379,c_3137])).

cnf(c_5509,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5384,c_31,c_32,c_33,c_1352,c_4299])).

cnf(c_4,plain,
    ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | X4 = X5 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,plain,
    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_429,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_pre_topc(X6,X7)
    | ~ v2_pre_topc(X7)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_struct_0(X7)
    | v2_struct_0(X6)
    | v1_xboole_0(X2)
    | v1_xboole_0(X5)
    | ~ l1_pre_topc(X7)
    | X3 = X0
    | k9_tmap_1(X7,X6) != X0
    | k3_struct_0(X7) != X3
    | u1_struct_0(X7) != X5
    | u1_struct_0(X7) != X4
    | u1_struct_0(X7) != X1
    | u1_struct_0(k8_tmap_1(X7,X6)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_22])).

cnf(c_430,plain,
    ( ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_17,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_372,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_2])).

cnf(c_434,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_funct_1(k3_struct_0(X0))
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_430,c_17,c_16,c_372])).

cnf(c_435,plain,
    ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k9_tmap_1(X0,X1))
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(renaming,[status(thm)],[c_434])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v1_funct_1(k9_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_462,plain,
    ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_435,c_18])).

cnf(c_883,plain,
    ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X0)
    | X0 != X2
    | k9_tmap_1(X0,X1) = k3_struct_0(X0)
    | sK0(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_462])).

cnf(c_884,plain,
    ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK0(X0))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,sK0(X0))))
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,sK0(X0)) = k3_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_883])).

cnf(c_2436,plain,
    ( ~ v1_funct_2(k3_struct_0(X0_58),u1_struct_0(X0_58),u1_struct_0(X0_58))
    | ~ m1_subset_1(k3_struct_0(X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X0_58))))
    | ~ v2_pre_topc(X0_58)
    | ~ v1_funct_1(k3_struct_0(X0_58))
    | v2_struct_0(X0_58)
    | v2_struct_0(sK0(X0_58))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
    | ~ l1_pre_topc(X0_58)
    | k9_tmap_1(X0_58,sK0(X0_58)) = k3_struct_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_884])).

cnf(c_3145,plain,
    ( k9_tmap_1(X0_58,sK0(X0_58)) = k3_struct_0(X0_58)
    | v1_funct_2(k3_struct_0(X0_58),u1_struct_0(X0_58),u1_struct_0(X0_58)) != iProver_top
    | m1_subset_1(k3_struct_0(X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X0_58)))) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(k3_struct_0(X0_58)) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(sK0(X0_58)) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58)))) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2436])).

cnf(c_4107,plain,
    ( k9_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k3_struct_0(k8_tmap_1(sK2,sK3))
    | v1_funct_2(k3_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | m1_subset_1(k3_struct_0(k8_tmap_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(k3_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(sK0(k8_tmap_1(sK2,sK3))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2415,c_3145])).

cnf(c_4109,plain,
    ( k9_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k3_struct_0(k8_tmap_1(sK2,sK3))
    | v1_funct_2(k3_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k3_struct_0(k8_tmap_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(k3_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(sK0(k8_tmap_1(sK2,sK3))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4107,c_2415])).

cnf(c_5221,plain,
    ( v1_xboole_0(u1_struct_0(k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = iProver_top
    | v2_struct_0(sK0(k8_tmap_1(sK2,sK3))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k3_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | k9_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k3_struct_0(k8_tmap_1(sK2,sK3))
    | v1_funct_2(k3_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k3_struct_0(k8_tmap_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4109,c_31,c_32,c_33,c_1341,c_1352])).

cnf(c_5222,plain,
    ( k9_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k3_struct_0(k8_tmap_1(sK2,sK3))
    | v1_funct_2(k3_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k3_struct_0(k8_tmap_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k3_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v2_struct_0(sK0(k8_tmap_1(sK2,sK3))) = iProver_top
    | v1_xboole_0(u1_struct_0(k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = iProver_top ),
    inference(renaming,[status(thm)],[c_5221])).

cnf(c_3743,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK2,sK3)))) != iProver_top
    | m1_subset_1(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(k8_tmap_1(sK2,sK3),X0_57))))) = iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2415,c_3136])).

cnf(c_3761,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(k8_tmap_1(sK2,sK3),X0_57))))) = iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3743,c_2415])).

cnf(c_5211,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(k8_tmap_1(sK2,sK3),X0_57))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3761,c_31,c_32,c_33,c_1341,c_1352])).

cnf(c_5212,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(k8_tmap_1(sK2,sK3),X0_57))))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5211])).

cnf(c_3709,plain,
    ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(k8_tmap_1(sK2,sK3),X0_57))) = iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK2,sK3)))) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2415,c_3137])).

cnf(c_3727,plain,
    ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(k8_tmap_1(sK2,sK3),X0_57))) = iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3709,c_2415])).

cnf(c_5136,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_2(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(k8_tmap_1(sK2,sK3),X0_57))) = iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3727,c_31,c_32,c_33,c_1341,c_1352])).

cnf(c_5137,plain,
    ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(k8_tmap_1(sK2,sK3),X0_57))) = iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5136])).

cnf(c_916,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X0)
    | X0 != X2
    | sK0(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_17])).

cnf(c_917,plain,
    ( v1_funct_2(k9_tmap_1(X0,sK0(X0)),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK0(X0))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_916])).

cnf(c_2435,plain,
    ( v1_funct_2(k9_tmap_1(X0_58,sK0(X0_58)),u1_struct_0(X0_58),u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
    | ~ v2_pre_topc(X0_58)
    | v2_struct_0(X0_58)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_917])).

cnf(c_3146,plain,
    ( v1_funct_2(k9_tmap_1(X0_58,sK0(X0_58)),u1_struct_0(X0_58),u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58)))) = iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2435])).

cnf(c_4681,plain,
    ( v1_funct_2(k9_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2415,c_3146])).

cnf(c_5129,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_2(k9_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4681,c_31,c_32,c_33,c_1341,c_1352])).

cnf(c_5130,plain,
    ( v1_funct_2(k9_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5129])).

cnf(c_1301,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1299,c_28])).

cnf(c_2416,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_1301])).

cnf(c_3163,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2416])).

cnf(c_5026,plain,
    ( k7_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3163,c_5018])).

cnf(c_4773,plain,
    ( k7_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))) = k6_partfun1(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_4301])).

cnf(c_4777,plain,
    ( k7_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4773,c_2415])).

cnf(c_5004,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | k7_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4777,c_31,c_32,c_33,c_1352])).

cnf(c_5005,plain,
    ( k7_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))) = k6_partfun1(u1_struct_0(sK2))
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5004])).

cnf(c_3974,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK2))
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3163,c_3135])).

cnf(c_3575,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k7_tmap_1(sK2,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2446])).

cnf(c_4195,plain,
    ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3974,c_30,c_29,c_28,c_1299,c_3575])).

cnf(c_4205,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4195,c_3136])).

cnf(c_1282,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_207,c_26])).

cnf(c_1283,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_1282])).

cnf(c_1285,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1283,c_30,c_29,c_28])).

cnf(c_2418,plain,
    ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_1285])).

cnf(c_4223,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4205,c_2415,c_2418])).

cnf(c_1300,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1299])).

cnf(c_4671,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4223,c_31,c_32,c_33,c_1300])).

cnf(c_4206,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4195,c_3137])).

cnf(c_4212,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4206,c_2415,c_2418])).

cnf(c_4587,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4212,c_31,c_32,c_33,c_1300])).

cnf(c_2437,plain,
    ( v2_struct_0(X0_58)
    | ~ v1_xboole_0(u1_struct_0(X0_58))
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_372])).

cnf(c_3144,plain,
    ( v2_struct_0(X0_58) = iProver_top
    | v1_xboole_0(u1_struct_0(X0_58)) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2437])).

cnf(c_3803,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2415,c_3144])).

cnf(c_101,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_103,plain,
    ( v2_struct_0(sK2) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_107,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_109,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_107])).

cnf(c_4403,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3803,c_31,c_33,c_103,c_109])).

cnf(c_4300,plain,
    ( v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(k7_tmap_1(X0_58,u1_struct_0(sK0(X0_58)))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(superposition,[status(thm)],[c_3151,c_3138])).

cnf(c_3675,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
    | v1_funct_1(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57)) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2415,c_3138])).

cnf(c_4287,plain,
    ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
    | v1_funct_1(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57)) = iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3675,c_31,c_32,c_33,c_1341,c_1352])).

cnf(c_4288,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_funct_1(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57)) = iProver_top
    | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4287])).

cnf(c_19,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_190,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_23])).

cnf(c_191,plain,
    ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_190])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X2)
    | k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(X1)),k7_tmap_1(X2,u1_struct_0(X1)),X1) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X2,u1_struct_0(X1)) != k8_tmap_1(sK2,sK3)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_191,c_24])).

cnf(c_391,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_395,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ m1_pre_topc(sK3,X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_391,c_27,c_25])).

cnf(c_396,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_395])).

cnf(c_1415,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | sK2 != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_396])).

cnf(c_1416,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_1415])).

cnf(c_398,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_396])).

cnf(c_1418,plain,
    ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1416,c_30,c_29,c_28,c_26,c_398,c_1283])).

cnf(c_2408,plain,
    ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
    inference(subtyping,[status(esa)],[c_1418])).

cnf(c_3213,plain,
    ( k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
    inference(light_normalisation,[status(thm)],[c_2408,c_2418])).

cnf(c_4199,plain,
    ( k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k6_partfun1(u1_struct_0(sK2)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
    inference(demodulation,[status(thm)],[c_4195,c_3213])).

cnf(c_3973,plain,
    ( v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3163,c_3138])).

cnf(c_3567,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2443])).

cnf(c_3568,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3567])).

cnf(c_4189,plain,
    ( v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3973,c_31,c_32,c_33,c_1300,c_3568])).

cnf(c_4198,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4195,c_4189])).

cnf(c_1244,plain,
    ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_1245,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1244])).

cnf(c_1247,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1245,c_30,c_29,c_28])).

cnf(c_2420,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) ),
    inference(subtyping,[status(esa)],[c_1247])).

cnf(c_3161,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2420])).

cnf(c_3200,plain,
    ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3161,c_2415])).

cnf(c_1233,plain,
    ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_1234,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1233])).

cnf(c_1236,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1234,c_30,c_29,c_28])).

cnf(c_2421,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) ),
    inference(subtyping,[status(esa)],[c_1236])).

cnf(c_3160,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2421])).

cnf(c_3197,plain,
    ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3160,c_2415])).

cnf(c_1210,plain,
    ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
    | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ v1_funct_1(k3_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(X0,X1) = k3_struct_0(X0)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_462,c_26])).

cnf(c_1211,plain,
    ( ~ v1_funct_2(k3_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(k3_struct_0(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ v2_pre_topc(sK2)
    | ~ v1_funct_1(k3_struct_0(sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ l1_pre_topc(sK2)
    | k9_tmap_1(sK2,sK3) = k3_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_1210])).

cnf(c_1213,plain,
    ( v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | ~ v1_funct_1(k3_struct_0(sK2))
    | ~ v1_funct_2(k3_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(k3_struct_0(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | k9_tmap_1(sK2,sK3) = k3_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1211,c_30,c_29,c_28,c_27])).

cnf(c_1214,plain,
    ( ~ v1_funct_2(k3_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(k3_struct_0(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ v1_funct_1(k3_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
    | k9_tmap_1(sK2,sK3) = k3_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1213])).

cnf(c_1597,plain,
    ( ~ v1_funct_2(k3_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(k3_struct_0(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ v1_funct_1(k3_struct_0(sK2))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k9_tmap_1(sK2,sK3) = k3_struct_0(sK2)
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(X0) ),
    inference(resolution_lifted,[status(thm)],[c_372,c_1214])).

cnf(c_1599,plain,
    ( ~ v1_funct_2(k3_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(k3_struct_0(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ v1_funct_1(k3_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k9_tmap_1(sK2,sK3) = k3_struct_0(sK2)
    | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1597])).

cnf(c_1601,plain,
    ( k9_tmap_1(sK2,sK3) = k3_struct_0(sK2)
    | ~ v1_funct_1(k3_struct_0(sK2))
    | ~ m1_subset_1(k3_struct_0(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ v1_funct_2(k3_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1597,c_30,c_29,c_28,c_27,c_1310,c_1599])).

cnf(c_1602,plain,
    ( ~ v1_funct_2(k3_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(k3_struct_0(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ v1_funct_1(k3_struct_0(sK2))
    | k9_tmap_1(sK2,sK3) = k3_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1601])).

cnf(c_2407,plain,
    ( ~ v1_funct_2(k3_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(k3_struct_0(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ v1_funct_1(k3_struct_0(sK2))
    | k9_tmap_1(sK2,sK3) = k3_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_1602])).

cnf(c_3170,plain,
    ( k9_tmap_1(sK2,sK3) = k3_struct_0(sK2)
    | v1_funct_2(k3_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k3_struct_0(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k3_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2407])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | k6_tmap_1(X1,sK1(X1,X0,X2)) != X2
    | k8_tmap_1(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1388,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(X1,sK1(X1,X2,X0)) != X0
    | k8_tmap_1(X1,X2) = X0
    | sK2 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_26])).

cnf(c_1389,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | k6_tmap_1(sK2,sK1(sK2,sK3,X0)) != X0
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_1388])).

cnf(c_1393,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | k6_tmap_1(sK2,sK1(sK2,sK3,X0)) != X0
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1389,c_30,c_29,c_28])).

cnf(c_1394,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k6_tmap_1(sK2,sK1(sK2,sK3,X0)) != X0
    | k8_tmap_1(sK2,sK3) = X0 ),
    inference(renaming,[status(thm)],[c_1393])).

cnf(c_2409,plain,
    ( ~ v1_pre_topc(X0_58)
    | ~ v2_pre_topc(X0_58)
    | ~ l1_pre_topc(X0_58)
    | k6_tmap_1(sK2,sK1(sK2,sK3,X0_58)) != X0_58
    | k8_tmap_1(sK2,sK3) = X0_58 ),
    inference(subtyping,[status(esa)],[c_1394])).

cnf(c_3169,plain,
    ( k6_tmap_1(sK2,sK1(sK2,sK3,X0_58)) != X0_58
    | k8_tmap_1(sK2,sK3) = X0_58
    | v1_pre_topc(X0_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2409])).

cnf(c_1186,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | X0 != X1
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | sK0(X1) != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_396])).

cnf(c_1187,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | sK0(X0) != sK3 ),
    inference(unflattening,[status(thm)],[c_1186])).

cnf(c_2422,plain,
    ( ~ v2_pre_topc(X0_58)
    | v2_struct_0(X0_58)
    | ~ l1_pre_topc(X0_58)
    | k2_tmap_1(X0_58,k6_tmap_1(X0_58,u1_struct_0(sK3)),k7_tmap_1(X0_58,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X0_58,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | sK0(X0_58) != sK3 ),
    inference(subtyping,[status(esa)],[c_1187])).

cnf(c_3159,plain,
    ( k2_tmap_1(X0_58,k6_tmap_1(X0_58,u1_struct_0(sK3)),k7_tmap_1(X0_58,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
    | k6_tmap_1(X0_58,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
    | sK0(X0_58) != sK3
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2422])).

cnf(c_1156,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | X1 != X2
    | k6_tmap_1(X1,sK1(X1,X3,X0)) != X0
    | k8_tmap_1(X1,X3) = X0
    | sK0(X2) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_6])).

cnf(c_1157,plain,
    ( ~ v1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(X1,sK1(X1,sK0(X1),X0)) != X0
    | k8_tmap_1(X1,sK0(X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_1156])).

cnf(c_2423,plain,
    ( ~ v1_pre_topc(X0_58)
    | ~ v2_pre_topc(X0_58)
    | ~ v2_pre_topc(X1_58)
    | v2_struct_0(X1_58)
    | ~ l1_pre_topc(X0_58)
    | ~ l1_pre_topc(X1_58)
    | k6_tmap_1(X1_58,sK1(X1_58,sK0(X1_58),X0_58)) != X0_58
    | k8_tmap_1(X1_58,sK0(X1_58)) = X0_58 ),
    inference(subtyping,[status(esa)],[c_1157])).

cnf(c_3158,plain,
    ( k6_tmap_1(X0_58,sK1(X0_58,sK0(X0_58),X1_58)) != X1_58
    | k8_tmap_1(X0_58,sK0(X0_58)) = X1_58
    | v1_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X1_58) != iProver_top
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top
    | l1_pre_topc(X1_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2423])).

cnf(c_1054,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X0)
    | X0 != X2
    | sK0(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_18])).

cnf(c_1055,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,sK0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_1054])).

cnf(c_2428,plain,
    ( ~ v2_pre_topc(X0_58)
    | v1_funct_1(k9_tmap_1(X0_58,sK0(X0_58)))
    | v2_struct_0(X0_58)
    | ~ l1_pre_topc(X0_58) ),
    inference(subtyping,[status(esa)],[c_1055])).

cnf(c_3153,plain,
    ( v2_pre_topc(X0_58) != iProver_top
    | v1_funct_1(k9_tmap_1(X0_58,sK0(X0_58))) = iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2428])).

cnf(c_1033,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X0)
    | X0 != X2
    | u1_struct_0(k8_tmap_1(X0,X1)) = u1_struct_0(X0)
    | sK0(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_21])).

cnf(c_1034,plain,
    ( ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0(X0))
    | ~ l1_pre_topc(X0)
    | u1_struct_0(k8_tmap_1(X0,sK0(X0))) = u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_1033])).

cnf(c_2429,plain,
    ( ~ v2_pre_topc(X0_58)
    | v2_struct_0(X0_58)
    | v2_struct_0(sK0(X0_58))
    | ~ l1_pre_topc(X0_58)
    | u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_1034])).

cnf(c_3152,plain,
    ( u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(X0_58)
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(sK0(X0_58)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2429])).

cnf(c_3150,plain,
    ( k5_tmap_1(X0_58,u1_struct_0(sK0(X0_58))) = u1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58)))
    | v2_pre_topc(X0_58) != iProver_top
    | v2_struct_0(X0_58) = iProver_top
    | v2_struct_0(sK0(X0_58)) = iProver_top
    | l1_pre_topc(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2431])).

cnf(c_1353,plain,
    ( l1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1351,c_30,c_29,c_28])).

cnf(c_2411,plain,
    ( l1_pre_topc(k8_tmap_1(sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_1353])).

cnf(c_3167,plain,
    ( l1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2411])).

cnf(c_1317,plain,
    ( ~ v2_pre_topc(X0)
    | v1_funct_1(k9_tmap_1(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_1318,plain,
    ( ~ v2_pre_topc(sK2)
    | v1_funct_1(k9_tmap_1(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1317])).

cnf(c_1320,plain,
    ( v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1318,c_30,c_29,c_28])).

cnf(c_2414,plain,
    ( v1_funct_1(k9_tmap_1(sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_1320])).

cnf(c_3164,plain,
    ( v1_funct_1(k9_tmap_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2414])).

cnf(c_2442,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_3139,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2442])).

cnf(c_2441,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_3140,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2441])).

cnf(c_2440,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_3141,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2440])).

cnf(c_2438,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_3143,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2438])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:24:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.51/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/0.99  
% 3.51/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.51/0.99  
% 3.51/0.99  ------  iProver source info
% 3.51/0.99  
% 3.51/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.51/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.51/0.99  git: non_committed_changes: false
% 3.51/0.99  git: last_make_outside_of_git: false
% 3.51/0.99  
% 3.51/0.99  ------ 
% 3.51/0.99  
% 3.51/0.99  ------ Input Options
% 3.51/0.99  
% 3.51/0.99  --out_options                           all
% 3.51/0.99  --tptp_safe_out                         true
% 3.51/0.99  --problem_path                          ""
% 3.51/0.99  --include_path                          ""
% 3.51/0.99  --clausifier                            res/vclausify_rel
% 3.51/0.99  --clausifier_options                    --mode clausify
% 3.51/0.99  --stdin                                 false
% 3.51/0.99  --stats_out                             all
% 3.51/0.99  
% 3.51/0.99  ------ General Options
% 3.51/0.99  
% 3.51/0.99  --fof                                   false
% 3.51/0.99  --time_out_real                         305.
% 3.51/0.99  --time_out_virtual                      -1.
% 3.51/0.99  --symbol_type_check                     false
% 3.51/0.99  --clausify_out                          false
% 3.51/0.99  --sig_cnt_out                           false
% 3.51/0.99  --trig_cnt_out                          false
% 3.51/0.99  --trig_cnt_out_tolerance                1.
% 3.51/0.99  --trig_cnt_out_sk_spl                   false
% 3.51/0.99  --abstr_cl_out                          false
% 3.51/0.99  
% 3.51/0.99  ------ Global Options
% 3.51/0.99  
% 3.51/0.99  --schedule                              default
% 3.51/0.99  --add_important_lit                     false
% 3.51/0.99  --prop_solver_per_cl                    1000
% 3.51/0.99  --min_unsat_core                        false
% 3.51/0.99  --soft_assumptions                      false
% 3.51/0.99  --soft_lemma_size                       3
% 3.51/0.99  --prop_impl_unit_size                   0
% 3.51/0.99  --prop_impl_unit                        []
% 3.51/0.99  --share_sel_clauses                     true
% 3.51/0.99  --reset_solvers                         false
% 3.51/0.99  --bc_imp_inh                            [conj_cone]
% 3.51/0.99  --conj_cone_tolerance                   3.
% 3.51/0.99  --extra_neg_conj                        none
% 3.51/0.99  --large_theory_mode                     true
% 3.51/0.99  --prolific_symb_bound                   200
% 3.51/0.99  --lt_threshold                          2000
% 3.51/0.99  --clause_weak_htbl                      true
% 3.51/0.99  --gc_record_bc_elim                     false
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing Options
% 3.51/0.99  
% 3.51/0.99  --preprocessing_flag                    true
% 3.51/0.99  --time_out_prep_mult                    0.1
% 3.51/0.99  --splitting_mode                        input
% 3.51/0.99  --splitting_grd                         true
% 3.51/0.99  --splitting_cvd                         false
% 3.51/0.99  --splitting_cvd_svl                     false
% 3.51/0.99  --splitting_nvd                         32
% 3.51/0.99  --sub_typing                            true
% 3.51/0.99  --prep_gs_sim                           true
% 3.51/0.99  --prep_unflatten                        true
% 3.51/0.99  --prep_res_sim                          true
% 3.51/0.99  --prep_upred                            true
% 3.51/0.99  --prep_sem_filter                       exhaustive
% 3.51/0.99  --prep_sem_filter_out                   false
% 3.51/0.99  --pred_elim                             true
% 3.51/0.99  --res_sim_input                         true
% 3.51/0.99  --eq_ax_congr_red                       true
% 3.51/0.99  --pure_diseq_elim                       true
% 3.51/0.99  --brand_transform                       false
% 3.51/0.99  --non_eq_to_eq                          false
% 3.51/0.99  --prep_def_merge                        true
% 3.51/0.99  --prep_def_merge_prop_impl              false
% 3.51/0.99  --prep_def_merge_mbd                    true
% 3.51/0.99  --prep_def_merge_tr_red                 false
% 3.51/0.99  --prep_def_merge_tr_cl                  false
% 3.51/0.99  --smt_preprocessing                     true
% 3.51/0.99  --smt_ac_axioms                         fast
% 3.51/0.99  --preprocessed_out                      false
% 3.51/0.99  --preprocessed_stats                    false
% 3.51/0.99  
% 3.51/0.99  ------ Abstraction refinement Options
% 3.51/0.99  
% 3.51/0.99  --abstr_ref                             []
% 3.51/0.99  --abstr_ref_prep                        false
% 3.51/0.99  --abstr_ref_until_sat                   false
% 3.51/0.99  --abstr_ref_sig_restrict                funpre
% 3.51/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/0.99  --abstr_ref_under                       []
% 3.51/0.99  
% 3.51/0.99  ------ SAT Options
% 3.51/0.99  
% 3.51/0.99  --sat_mode                              false
% 3.51/0.99  --sat_fm_restart_options                ""
% 3.51/0.99  --sat_gr_def                            false
% 3.51/0.99  --sat_epr_types                         true
% 3.51/0.99  --sat_non_cyclic_types                  false
% 3.51/0.99  --sat_finite_models                     false
% 3.51/0.99  --sat_fm_lemmas                         false
% 3.51/0.99  --sat_fm_prep                           false
% 3.51/0.99  --sat_fm_uc_incr                        true
% 3.51/0.99  --sat_out_model                         small
% 3.51/0.99  --sat_out_clauses                       false
% 3.51/0.99  
% 3.51/0.99  ------ QBF Options
% 3.51/0.99  
% 3.51/0.99  --qbf_mode                              false
% 3.51/0.99  --qbf_elim_univ                         false
% 3.51/0.99  --qbf_dom_inst                          none
% 3.51/0.99  --qbf_dom_pre_inst                      false
% 3.51/0.99  --qbf_sk_in                             false
% 3.51/0.99  --qbf_pred_elim                         true
% 3.51/0.99  --qbf_split                             512
% 3.51/0.99  
% 3.51/0.99  ------ BMC1 Options
% 3.51/0.99  
% 3.51/0.99  --bmc1_incremental                      false
% 3.51/0.99  --bmc1_axioms                           reachable_all
% 3.51/0.99  --bmc1_min_bound                        0
% 3.51/0.99  --bmc1_max_bound                        -1
% 3.51/0.99  --bmc1_max_bound_default                -1
% 3.51/0.99  --bmc1_symbol_reachability              true
% 3.51/0.99  --bmc1_property_lemmas                  false
% 3.51/0.99  --bmc1_k_induction                      false
% 3.51/0.99  --bmc1_non_equiv_states                 false
% 3.51/0.99  --bmc1_deadlock                         false
% 3.51/0.99  --bmc1_ucm                              false
% 3.51/0.99  --bmc1_add_unsat_core                   none
% 3.51/0.99  --bmc1_unsat_core_children              false
% 3.51/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/0.99  --bmc1_out_stat                         full
% 3.51/0.99  --bmc1_ground_init                      false
% 3.51/0.99  --bmc1_pre_inst_next_state              false
% 3.51/0.99  --bmc1_pre_inst_state                   false
% 3.51/0.99  --bmc1_pre_inst_reach_state             false
% 3.51/0.99  --bmc1_out_unsat_core                   false
% 3.51/0.99  --bmc1_aig_witness_out                  false
% 3.51/0.99  --bmc1_verbose                          false
% 3.51/0.99  --bmc1_dump_clauses_tptp                false
% 3.51/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.51/0.99  --bmc1_dump_file                        -
% 3.51/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.51/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.51/0.99  --bmc1_ucm_extend_mode                  1
% 3.51/0.99  --bmc1_ucm_init_mode                    2
% 3.51/0.99  --bmc1_ucm_cone_mode                    none
% 3.51/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.51/0.99  --bmc1_ucm_relax_model                  4
% 3.51/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.51/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/0.99  --bmc1_ucm_layered_model                none
% 3.51/0.99  --bmc1_ucm_max_lemma_size               10
% 3.51/0.99  
% 3.51/0.99  ------ AIG Options
% 3.51/0.99  
% 3.51/0.99  --aig_mode                              false
% 3.51/0.99  
% 3.51/0.99  ------ Instantiation Options
% 3.51/0.99  
% 3.51/0.99  --instantiation_flag                    true
% 3.51/0.99  --inst_sos_flag                         false
% 3.51/0.99  --inst_sos_phase                        true
% 3.51/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/0.99  --inst_lit_sel_side                     num_symb
% 3.51/0.99  --inst_solver_per_active                1400
% 3.51/0.99  --inst_solver_calls_frac                1.
% 3.51/0.99  --inst_passive_queue_type               priority_queues
% 3.51/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/0.99  --inst_passive_queues_freq              [25;2]
% 3.51/0.99  --inst_dismatching                      true
% 3.51/0.99  --inst_eager_unprocessed_to_passive     true
% 3.51/0.99  --inst_prop_sim_given                   true
% 3.51/0.99  --inst_prop_sim_new                     false
% 3.51/0.99  --inst_subs_new                         false
% 3.51/0.99  --inst_eq_res_simp                      false
% 3.51/0.99  --inst_subs_given                       false
% 3.51/0.99  --inst_orphan_elimination               true
% 3.51/0.99  --inst_learning_loop_flag               true
% 3.51/0.99  --inst_learning_start                   3000
% 3.51/0.99  --inst_learning_factor                  2
% 3.51/0.99  --inst_start_prop_sim_after_learn       3
% 3.51/0.99  --inst_sel_renew                        solver
% 3.51/0.99  --inst_lit_activity_flag                true
% 3.51/0.99  --inst_restr_to_given                   false
% 3.51/0.99  --inst_activity_threshold               500
% 3.51/0.99  --inst_out_proof                        true
% 3.51/0.99  
% 3.51/0.99  ------ Resolution Options
% 3.51/0.99  
% 3.51/0.99  --resolution_flag                       true
% 3.51/0.99  --res_lit_sel                           adaptive
% 3.51/0.99  --res_lit_sel_side                      none
% 3.51/0.99  --res_ordering                          kbo
% 3.51/0.99  --res_to_prop_solver                    active
% 3.51/0.99  --res_prop_simpl_new                    false
% 3.51/0.99  --res_prop_simpl_given                  true
% 3.51/0.99  --res_passive_queue_type                priority_queues
% 3.51/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/0.99  --res_passive_queues_freq               [15;5]
% 3.51/0.99  --res_forward_subs                      full
% 3.51/0.99  --res_backward_subs                     full
% 3.51/0.99  --res_forward_subs_resolution           true
% 3.51/0.99  --res_backward_subs_resolution          true
% 3.51/0.99  --res_orphan_elimination                true
% 3.51/0.99  --res_time_limit                        2.
% 3.51/0.99  --res_out_proof                         true
% 3.51/0.99  
% 3.51/0.99  ------ Superposition Options
% 3.51/0.99  
% 3.51/0.99  --superposition_flag                    true
% 3.51/0.99  --sup_passive_queue_type                priority_queues
% 3.51/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.51/0.99  --demod_completeness_check              fast
% 3.51/0.99  --demod_use_ground                      true
% 3.51/0.99  --sup_to_prop_solver                    passive
% 3.51/0.99  --sup_prop_simpl_new                    true
% 3.51/0.99  --sup_prop_simpl_given                  true
% 3.51/0.99  --sup_fun_splitting                     false
% 3.51/0.99  --sup_smt_interval                      50000
% 3.51/0.99  
% 3.51/0.99  ------ Superposition Simplification Setup
% 3.51/0.99  
% 3.51/0.99  --sup_indices_passive                   []
% 3.51/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_full_bw                           [BwDemod]
% 3.51/0.99  --sup_immed_triv                        [TrivRules]
% 3.51/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_immed_bw_main                     []
% 3.51/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.99  
% 3.51/0.99  ------ Combination Options
% 3.51/0.99  
% 3.51/0.99  --comb_res_mult                         3
% 3.51/0.99  --comb_sup_mult                         2
% 3.51/0.99  --comb_inst_mult                        10
% 3.51/0.99  
% 3.51/0.99  ------ Debug Options
% 3.51/0.99  
% 3.51/0.99  --dbg_backtrace                         false
% 3.51/0.99  --dbg_dump_prop_clauses                 false
% 3.51/0.99  --dbg_dump_prop_clauses_file            -
% 3.51/0.99  --dbg_out_stat                          false
% 3.51/0.99  ------ Parsing...
% 3.51/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.51/0.99  ------ Proving...
% 3.51/0.99  ------ Problem Properties 
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  clauses                                 40
% 3.51/0.99  conjectures                             5
% 3.51/0.99  EPR                                     4
% 3.51/0.99  Horn                                    21
% 3.51/0.99  unary                                   16
% 3.51/0.99  binary                                  1
% 3.51/0.99  lits                                    137
% 3.51/0.99  lits eq                                 23
% 3.51/0.99  fd_pure                                 0
% 3.51/0.99  fd_pseudo                               0
% 3.51/0.99  fd_cond                                 3
% 3.51/0.99  fd_pseudo_cond                          3
% 3.51/0.99  AC symbols                              0
% 3.51/0.99  
% 3.51/0.99  ------ Schedule dynamic 5 is on 
% 3.51/0.99  
% 3.51/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  ------ 
% 3.51/0.99  Current options:
% 3.51/0.99  ------ 
% 3.51/0.99  
% 3.51/0.99  ------ Input Options
% 3.51/0.99  
% 3.51/0.99  --out_options                           all
% 3.51/0.99  --tptp_safe_out                         true
% 3.51/0.99  --problem_path                          ""
% 3.51/0.99  --include_path                          ""
% 3.51/0.99  --clausifier                            res/vclausify_rel
% 3.51/0.99  --clausifier_options                    --mode clausify
% 3.51/0.99  --stdin                                 false
% 3.51/0.99  --stats_out                             all
% 3.51/0.99  
% 3.51/0.99  ------ General Options
% 3.51/0.99  
% 3.51/0.99  --fof                                   false
% 3.51/0.99  --time_out_real                         305.
% 3.51/0.99  --time_out_virtual                      -1.
% 3.51/0.99  --symbol_type_check                     false
% 3.51/0.99  --clausify_out                          false
% 3.51/0.99  --sig_cnt_out                           false
% 3.51/0.99  --trig_cnt_out                          false
% 3.51/0.99  --trig_cnt_out_tolerance                1.
% 3.51/0.99  --trig_cnt_out_sk_spl                   false
% 3.51/0.99  --abstr_cl_out                          false
% 3.51/0.99  
% 3.51/0.99  ------ Global Options
% 3.51/0.99  
% 3.51/0.99  --schedule                              default
% 3.51/0.99  --add_important_lit                     false
% 3.51/0.99  --prop_solver_per_cl                    1000
% 3.51/0.99  --min_unsat_core                        false
% 3.51/0.99  --soft_assumptions                      false
% 3.51/0.99  --soft_lemma_size                       3
% 3.51/0.99  --prop_impl_unit_size                   0
% 3.51/0.99  --prop_impl_unit                        []
% 3.51/0.99  --share_sel_clauses                     true
% 3.51/0.99  --reset_solvers                         false
% 3.51/0.99  --bc_imp_inh                            [conj_cone]
% 3.51/0.99  --conj_cone_tolerance                   3.
% 3.51/0.99  --extra_neg_conj                        none
% 3.51/0.99  --large_theory_mode                     true
% 3.51/0.99  --prolific_symb_bound                   200
% 3.51/0.99  --lt_threshold                          2000
% 3.51/0.99  --clause_weak_htbl                      true
% 3.51/0.99  --gc_record_bc_elim                     false
% 3.51/0.99  
% 3.51/0.99  ------ Preprocessing Options
% 3.51/0.99  
% 3.51/0.99  --preprocessing_flag                    true
% 3.51/0.99  --time_out_prep_mult                    0.1
% 3.51/0.99  --splitting_mode                        input
% 3.51/0.99  --splitting_grd                         true
% 3.51/0.99  --splitting_cvd                         false
% 3.51/0.99  --splitting_cvd_svl                     false
% 3.51/0.99  --splitting_nvd                         32
% 3.51/0.99  --sub_typing                            true
% 3.51/0.99  --prep_gs_sim                           true
% 3.51/0.99  --prep_unflatten                        true
% 3.51/0.99  --prep_res_sim                          true
% 3.51/0.99  --prep_upred                            true
% 3.51/0.99  --prep_sem_filter                       exhaustive
% 3.51/0.99  --prep_sem_filter_out                   false
% 3.51/0.99  --pred_elim                             true
% 3.51/0.99  --res_sim_input                         true
% 3.51/0.99  --eq_ax_congr_red                       true
% 3.51/0.99  --pure_diseq_elim                       true
% 3.51/0.99  --brand_transform                       false
% 3.51/0.99  --non_eq_to_eq                          false
% 3.51/0.99  --prep_def_merge                        true
% 3.51/0.99  --prep_def_merge_prop_impl              false
% 3.51/0.99  --prep_def_merge_mbd                    true
% 3.51/0.99  --prep_def_merge_tr_red                 false
% 3.51/0.99  --prep_def_merge_tr_cl                  false
% 3.51/0.99  --smt_preprocessing                     true
% 3.51/0.99  --smt_ac_axioms                         fast
% 3.51/0.99  --preprocessed_out                      false
% 3.51/0.99  --preprocessed_stats                    false
% 3.51/0.99  
% 3.51/0.99  ------ Abstraction refinement Options
% 3.51/0.99  
% 3.51/0.99  --abstr_ref                             []
% 3.51/0.99  --abstr_ref_prep                        false
% 3.51/0.99  --abstr_ref_until_sat                   false
% 3.51/0.99  --abstr_ref_sig_restrict                funpre
% 3.51/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/0.99  --abstr_ref_under                       []
% 3.51/0.99  
% 3.51/0.99  ------ SAT Options
% 3.51/0.99  
% 3.51/0.99  --sat_mode                              false
% 3.51/0.99  --sat_fm_restart_options                ""
% 3.51/0.99  --sat_gr_def                            false
% 3.51/0.99  --sat_epr_types                         true
% 3.51/0.99  --sat_non_cyclic_types                  false
% 3.51/0.99  --sat_finite_models                     false
% 3.51/0.99  --sat_fm_lemmas                         false
% 3.51/0.99  --sat_fm_prep                           false
% 3.51/0.99  --sat_fm_uc_incr                        true
% 3.51/0.99  --sat_out_model                         small
% 3.51/0.99  --sat_out_clauses                       false
% 3.51/0.99  
% 3.51/0.99  ------ QBF Options
% 3.51/0.99  
% 3.51/0.99  --qbf_mode                              false
% 3.51/0.99  --qbf_elim_univ                         false
% 3.51/0.99  --qbf_dom_inst                          none
% 3.51/0.99  --qbf_dom_pre_inst                      false
% 3.51/0.99  --qbf_sk_in                             false
% 3.51/0.99  --qbf_pred_elim                         true
% 3.51/0.99  --qbf_split                             512
% 3.51/0.99  
% 3.51/0.99  ------ BMC1 Options
% 3.51/0.99  
% 3.51/0.99  --bmc1_incremental                      false
% 3.51/0.99  --bmc1_axioms                           reachable_all
% 3.51/0.99  --bmc1_min_bound                        0
% 3.51/0.99  --bmc1_max_bound                        -1
% 3.51/0.99  --bmc1_max_bound_default                -1
% 3.51/0.99  --bmc1_symbol_reachability              true
% 3.51/0.99  --bmc1_property_lemmas                  false
% 3.51/0.99  --bmc1_k_induction                      false
% 3.51/0.99  --bmc1_non_equiv_states                 false
% 3.51/0.99  --bmc1_deadlock                         false
% 3.51/0.99  --bmc1_ucm                              false
% 3.51/0.99  --bmc1_add_unsat_core                   none
% 3.51/0.99  --bmc1_unsat_core_children              false
% 3.51/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/0.99  --bmc1_out_stat                         full
% 3.51/0.99  --bmc1_ground_init                      false
% 3.51/0.99  --bmc1_pre_inst_next_state              false
% 3.51/0.99  --bmc1_pre_inst_state                   false
% 3.51/0.99  --bmc1_pre_inst_reach_state             false
% 3.51/0.99  --bmc1_out_unsat_core                   false
% 3.51/0.99  --bmc1_aig_witness_out                  false
% 3.51/0.99  --bmc1_verbose                          false
% 3.51/0.99  --bmc1_dump_clauses_tptp                false
% 3.51/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.51/0.99  --bmc1_dump_file                        -
% 3.51/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.51/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.51/0.99  --bmc1_ucm_extend_mode                  1
% 3.51/0.99  --bmc1_ucm_init_mode                    2
% 3.51/0.99  --bmc1_ucm_cone_mode                    none
% 3.51/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.51/0.99  --bmc1_ucm_relax_model                  4
% 3.51/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.51/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/0.99  --bmc1_ucm_layered_model                none
% 3.51/0.99  --bmc1_ucm_max_lemma_size               10
% 3.51/0.99  
% 3.51/0.99  ------ AIG Options
% 3.51/0.99  
% 3.51/0.99  --aig_mode                              false
% 3.51/0.99  
% 3.51/0.99  ------ Instantiation Options
% 3.51/0.99  
% 3.51/0.99  --instantiation_flag                    true
% 3.51/0.99  --inst_sos_flag                         false
% 3.51/0.99  --inst_sos_phase                        true
% 3.51/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/0.99  --inst_lit_sel_side                     none
% 3.51/0.99  --inst_solver_per_active                1400
% 3.51/0.99  --inst_solver_calls_frac                1.
% 3.51/0.99  --inst_passive_queue_type               priority_queues
% 3.51/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/0.99  --inst_passive_queues_freq              [25;2]
% 3.51/0.99  --inst_dismatching                      true
% 3.51/0.99  --inst_eager_unprocessed_to_passive     true
% 3.51/0.99  --inst_prop_sim_given                   true
% 3.51/0.99  --inst_prop_sim_new                     false
% 3.51/0.99  --inst_subs_new                         false
% 3.51/0.99  --inst_eq_res_simp                      false
% 3.51/0.99  --inst_subs_given                       false
% 3.51/0.99  --inst_orphan_elimination               true
% 3.51/0.99  --inst_learning_loop_flag               true
% 3.51/0.99  --inst_learning_start                   3000
% 3.51/0.99  --inst_learning_factor                  2
% 3.51/0.99  --inst_start_prop_sim_after_learn       3
% 3.51/0.99  --inst_sel_renew                        solver
% 3.51/0.99  --inst_lit_activity_flag                true
% 3.51/0.99  --inst_restr_to_given                   false
% 3.51/0.99  --inst_activity_threshold               500
% 3.51/0.99  --inst_out_proof                        true
% 3.51/0.99  
% 3.51/0.99  ------ Resolution Options
% 3.51/0.99  
% 3.51/0.99  --resolution_flag                       false
% 3.51/0.99  --res_lit_sel                           adaptive
% 3.51/0.99  --res_lit_sel_side                      none
% 3.51/0.99  --res_ordering                          kbo
% 3.51/0.99  --res_to_prop_solver                    active
% 3.51/0.99  --res_prop_simpl_new                    false
% 3.51/0.99  --res_prop_simpl_given                  true
% 3.51/0.99  --res_passive_queue_type                priority_queues
% 3.51/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/0.99  --res_passive_queues_freq               [15;5]
% 3.51/0.99  --res_forward_subs                      full
% 3.51/0.99  --res_backward_subs                     full
% 3.51/0.99  --res_forward_subs_resolution           true
% 3.51/0.99  --res_backward_subs_resolution          true
% 3.51/0.99  --res_orphan_elimination                true
% 3.51/0.99  --res_time_limit                        2.
% 3.51/0.99  --res_out_proof                         true
% 3.51/0.99  
% 3.51/0.99  ------ Superposition Options
% 3.51/0.99  
% 3.51/0.99  --superposition_flag                    true
% 3.51/0.99  --sup_passive_queue_type                priority_queues
% 3.51/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.51/0.99  --demod_completeness_check              fast
% 3.51/0.99  --demod_use_ground                      true
% 3.51/0.99  --sup_to_prop_solver                    passive
% 3.51/0.99  --sup_prop_simpl_new                    true
% 3.51/0.99  --sup_prop_simpl_given                  true
% 3.51/0.99  --sup_fun_splitting                     false
% 3.51/0.99  --sup_smt_interval                      50000
% 3.51/0.99  
% 3.51/0.99  ------ Superposition Simplification Setup
% 3.51/0.99  
% 3.51/0.99  --sup_indices_passive                   []
% 3.51/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_full_bw                           [BwDemod]
% 3.51/0.99  --sup_immed_triv                        [TrivRules]
% 3.51/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_immed_bw_main                     []
% 3.51/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.51/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.51/0.99  
% 3.51/0.99  ------ Combination Options
% 3.51/0.99  
% 3.51/0.99  --comb_res_mult                         3
% 3.51/0.99  --comb_sup_mult                         2
% 3.51/0.99  --comb_inst_mult                        10
% 3.51/0.99  
% 3.51/0.99  ------ Debug Options
% 3.51/0.99  
% 3.51/0.99  --dbg_backtrace                         false
% 3.51/0.99  --dbg_dump_prop_clauses                 false
% 3.51/0.99  --dbg_dump_prop_clauses_file            -
% 3.51/0.99  --dbg_out_stat                          false
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  ------ Proving...
% 3.51/0.99  
% 3.51/0.99  
% 3.51/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 3.51/0.99  
% 3.51/0.99  % SZS output start Saturation for theBenchmark.p
% 3.51/0.99  
% 3.51/0.99  fof(f2,axiom,(
% 3.51/0.99    ! [X0] : (l1_pre_topc(X0) => ? [X1] : m1_pre_topc(X1,X0))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f17,plain,(
% 3.51/0.99    ! [X0] : (? [X1] : m1_pre_topc(X1,X0) | ~l1_pre_topc(X0))),
% 3.51/0.99    inference(ennf_transformation,[],[f2])).
% 3.51/0.99  
% 3.51/0.99  fof(f41,plain,(
% 3.51/0.99    ! [X0] : (? [X1] : m1_pre_topc(X1,X0) => m1_pre_topc(sK0(X0),X0))),
% 3.51/0.99    introduced(choice_axiom,[])).
% 3.51/0.99  
% 3.51/0.99  fof(f42,plain,(
% 3.51/0.99    ! [X0] : (m1_pre_topc(sK0(X0),X0) | ~l1_pre_topc(X0))),
% 3.51/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f41])).
% 3.51/0.99  
% 3.51/0.99  fof(f53,plain,(
% 3.51/0.99    ( ! [X0] : (m1_pre_topc(sK0(X0),X0) | ~l1_pre_topc(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f42])).
% 3.51/0.99  
% 3.51/0.99  fof(f11,axiom,(
% 3.51/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)))))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f34,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : ((! [X2] : ((u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f11])).
% 3.51/0.99  
% 3.51/0.99  fof(f35,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : ((! [X2] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/0.99    inference(flattening,[],[f34])).
% 3.51/0.99  
% 3.51/0.99  fof(f73,plain,(
% 3.51/0.99    ( ! [X2,X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f35])).
% 3.51/0.99  
% 3.51/0.99  fof(f87,plain,(
% 3.51/0.99    ( ! [X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(equality_resolution,[],[f73])).
% 3.51/0.99  
% 3.51/0.99  fof(f13,axiom,(
% 3.51/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f38,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.51/0.99    inference(ennf_transformation,[],[f13])).
% 3.51/0.99  
% 3.51/0.99  fof(f75,plain,(
% 3.51/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f38])).
% 3.51/0.99  
% 3.51/0.99  fof(f14,conjecture,(
% 3.51/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f15,negated_conjecture,(
% 3.51/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2))))),
% 3.51/0.99    inference(negated_conjecture,[],[f14])).
% 3.51/0.99  
% 3.51/0.99  fof(f39,plain,(
% 3.51/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f15])).
% 3.51/0.99  
% 3.51/0.99  fof(f40,plain,(
% 3.51/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.51/0.99    inference(flattening,[],[f39])).
% 3.51/0.99  
% 3.51/0.99  fof(f50,plain,(
% 3.51/0.99    ( ! [X0,X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) => (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),sK4) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 3.51/0.99    introduced(choice_axiom,[])).
% 3.51/0.99  
% 3.51/0.99  fof(f49,plain,(
% 3.51/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (~r1_tmap_1(sK3,k8_tmap_1(X0,sK3),k2_tmap_1(X0,k8_tmap_1(X0,sK3),k9_tmap_1(X0,sK3),sK3),X2) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.51/0.99    introduced(choice_axiom,[])).
% 3.51/0.99  
% 3.51/0.99  fof(f48,plain,(
% 3.51/0.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tmap_1(X1,k8_tmap_1(sK2,X1),k2_tmap_1(sK2,k8_tmap_1(sK2,X1),k9_tmap_1(sK2,X1),X1),X2) & m1_subset_1(X2,u1_struct_0(X1))) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.51/0.99    introduced(choice_axiom,[])).
% 3.51/0.99  
% 3.51/0.99  fof(f51,plain,(
% 3.51/0.99    ((~r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4) & m1_subset_1(sK4,u1_struct_0(sK3))) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.51/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f40,f50,f49,f48])).
% 3.51/0.99  
% 3.51/0.99  fof(f80,plain,(
% 3.51/0.99    m1_pre_topc(sK3,sK2)),
% 3.51/0.99    inference(cnf_transformation,[],[f51])).
% 3.51/0.99  
% 3.51/0.99  fof(f76,plain,(
% 3.51/0.99    ~v2_struct_0(sK2)),
% 3.51/0.99    inference(cnf_transformation,[],[f51])).
% 3.51/0.99  
% 3.51/0.99  fof(f77,plain,(
% 3.51/0.99    v2_pre_topc(sK2)),
% 3.51/0.99    inference(cnf_transformation,[],[f51])).
% 3.51/0.99  
% 3.51/0.99  fof(f78,plain,(
% 3.51/0.99    l1_pre_topc(sK2)),
% 3.51/0.99    inference(cnf_transformation,[],[f51])).
% 3.51/0.99  
% 3.51/0.99  fof(f79,plain,(
% 3.51/0.99    ~v2_struct_0(sK3)),
% 3.51/0.99    inference(cnf_transformation,[],[f51])).
% 3.51/0.99  
% 3.51/0.99  fof(f8,axiom,(
% 3.51/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f28,plain,(
% 3.51/0.99    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f8])).
% 3.51/0.99  
% 3.51/0.99  fof(f29,plain,(
% 3.51/0.99    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/0.99    inference(flattening,[],[f28])).
% 3.51/0.99  
% 3.51/0.99  fof(f66,plain,(
% 3.51/0.99    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f29])).
% 3.51/0.99  
% 3.51/0.99  fof(f65,plain,(
% 3.51/0.99    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f29])).
% 3.51/0.99  
% 3.51/0.99  fof(f6,axiom,(
% 3.51/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f24,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f6])).
% 3.51/0.99  
% 3.51/0.99  fof(f25,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/0.99    inference(flattening,[],[f24])).
% 3.51/0.99  
% 3.51/0.99  fof(f44,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/0.99    inference(nnf_transformation,[],[f25])).
% 3.51/0.99  
% 3.51/0.99  fof(f45,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/0.99    inference(rectify,[],[f44])).
% 3.51/0.99  
% 3.51/0.99  fof(f46,plain,(
% 3.51/0.99    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK1(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.51/0.99    introduced(choice_axiom,[])).
% 3.51/0.99  
% 3.51/0.99  fof(f47,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK1(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK1(X0,X1,X2) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).
% 3.51/0.99  
% 3.51/0.99  fof(f59,plain,(
% 3.51/0.99    ( ! [X2,X0,X1] : (k8_tmap_1(X0,X1) = X2 | m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f47])).
% 3.51/0.99  
% 3.51/0.99  fof(f5,axiom,(
% 3.51/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f22,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f5])).
% 3.51/0.99  
% 3.51/0.99  fof(f23,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/0.99    inference(flattening,[],[f22])).
% 3.51/0.99  
% 3.51/0.99  fof(f57,plain,(
% 3.51/0.99    ( ! [X0,X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f23])).
% 3.51/0.99  
% 3.51/0.99  fof(f67,plain,(
% 3.51/0.99    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f29])).
% 3.51/0.99  
% 3.51/0.99  fof(f60,plain,(
% 3.51/0.99    ( ! [X2,X0,X1] : (k8_tmap_1(X0,X1) = X2 | u1_struct_0(X1) = sK1(X0,X1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f47])).
% 3.51/0.99  
% 3.51/0.99  fof(f72,plain,(
% 3.51/0.99    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f35])).
% 3.51/0.99  
% 3.51/0.99  fof(f58,plain,(
% 3.51/0.99    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f47])).
% 3.51/0.99  
% 3.51/0.99  fof(f84,plain,(
% 3.51/0.99    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(equality_resolution,[],[f58])).
% 3.51/0.99  
% 3.51/0.99  fof(f85,plain,(
% 3.51/0.99    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(equality_resolution,[],[f84])).
% 3.51/0.99  
% 3.51/0.99  fof(f7,axiom,(
% 3.51/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f26,plain,(
% 3.51/0.99    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f7])).
% 3.51/0.99  
% 3.51/0.99  fof(f27,plain,(
% 3.51/0.99    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/0.99    inference(flattening,[],[f26])).
% 3.51/0.99  
% 3.51/0.99  fof(f64,plain,(
% 3.51/0.99    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f27])).
% 3.51/0.99  
% 3.51/0.99  fof(f63,plain,(
% 3.51/0.99    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f27])).
% 3.51/0.99  
% 3.51/0.99  fof(f62,plain,(
% 3.51/0.99    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f27])).
% 3.51/0.99  
% 3.51/0.99  fof(f9,axiom,(
% 3.51/0.99    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f30,plain,(
% 3.51/0.99    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f9])).
% 3.51/0.99  
% 3.51/0.99  fof(f31,plain,(
% 3.51/0.99    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/0.99    inference(flattening,[],[f30])).
% 3.51/0.99  
% 3.51/0.99  fof(f70,plain,(
% 3.51/0.99    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f31])).
% 3.51/0.99  
% 3.51/0.99  fof(f4,axiom,(
% 3.51/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f20,plain,(
% 3.51/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.51/0.99    inference(ennf_transformation,[],[f4])).
% 3.51/0.99  
% 3.51/0.99  fof(f21,plain,(
% 3.51/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.51/0.99    inference(flattening,[],[f20])).
% 3.51/0.99  
% 3.51/0.99  fof(f43,plain,(
% 3.51/0.99    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.51/0.99    inference(nnf_transformation,[],[f21])).
% 3.51/0.99  
% 3.51/0.99  fof(f55,plain,(
% 3.51/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f43])).
% 3.51/0.99  
% 3.51/0.99  fof(f12,axiom,(
% 3.51/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f36,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f12])).
% 3.51/0.99  
% 3.51/0.99  fof(f37,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/0.99    inference(flattening,[],[f36])).
% 3.51/0.99  
% 3.51/0.99  fof(f74,plain,(
% 3.51/0.99    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f37])).
% 3.51/0.99  
% 3.51/0.99  fof(f69,plain,(
% 3.51/0.99    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f31])).
% 3.51/0.99  
% 3.51/0.99  fof(f1,axiom,(
% 3.51/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f16,plain,(
% 3.51/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.51/0.99    inference(ennf_transformation,[],[f1])).
% 3.51/0.99  
% 3.51/0.99  fof(f52,plain,(
% 3.51/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f16])).
% 3.51/0.99  
% 3.51/0.99  fof(f3,axiom,(
% 3.51/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f18,plain,(
% 3.51/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f3])).
% 3.51/0.99  
% 3.51/0.99  fof(f19,plain,(
% 3.51/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.51/0.99    inference(flattening,[],[f18])).
% 3.51/0.99  
% 3.51/0.99  fof(f54,plain,(
% 3.51/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f19])).
% 3.51/0.99  
% 3.51/0.99  fof(f68,plain,(
% 3.51/0.99    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f31])).
% 3.51/0.99  
% 3.51/0.99  fof(f10,axiom,(
% 3.51/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(X2) = X1 => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 3.51/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.99  
% 3.51/0.99  fof(f32,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | u1_struct_0(X2) != X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.51/0.99    inference(ennf_transformation,[],[f10])).
% 3.51/0.99  
% 3.51/0.99  fof(f33,plain,(
% 3.51/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.51/0.99    inference(flattening,[],[f32])).
% 3.51/0.99  
% 3.51/0.99  fof(f71,plain,(
% 3.51/0.99    ( ! [X2,X0,X3,X1] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f33])).
% 3.51/0.99  
% 3.51/0.99  fof(f86,plain,(
% 3.51/0.99    ( ! [X2,X0,X3] : (r1_tmap_1(X2,k6_tmap_1(X0,u1_struct_0(X2)),k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(equality_resolution,[],[f71])).
% 3.51/0.99  
% 3.51/0.99  fof(f82,plain,(
% 3.51/0.99    ~r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4)),
% 3.51/0.99    inference(cnf_transformation,[],[f51])).
% 3.51/0.99  
% 3.51/0.99  fof(f81,plain,(
% 3.51/0.99    m1_subset_1(sK4,u1_struct_0(sK3))),
% 3.51/0.99    inference(cnf_transformation,[],[f51])).
% 3.51/0.99  
% 3.51/0.99  fof(f61,plain,(
% 3.51/0.99    ( ! [X2,X0,X1] : (k8_tmap_1(X0,X1) = X2 | k6_tmap_1(X0,sK1(X0,X1,X2)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.51/0.99    inference(cnf_transformation,[],[f47])).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2475,plain,
% 3.51/0.99      ( k5_tmap_1(X0_58,X0_57) = k5_tmap_1(X1_58,X1_57)
% 3.51/0.99      | X0_58 != X1_58
% 3.51/0.99      | X0_57 != X1_57 ),
% 3.51/0.99      theory(equality) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2474,plain,
% 3.51/0.99      ( u1_pre_topc(X0_58) = u1_pre_topc(X1_58) | X0_58 != X1_58 ),
% 3.51/0.99      theory(equality) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2455,plain,
% 3.51/0.99      ( X0_60 != X1_60 | X2_60 != X1_60 | X2_60 = X0_60 ),
% 3.51/0.99      theory(equality) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2451,plain,( X0_60 = X0_60 ),theory(equality) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1,plain,
% 3.51/0.99      ( m1_pre_topc(sK0(X0),X0) | ~ l1_pre_topc(X0) ),
% 3.51/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_20,plain,
% 3.51/0.99      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.99      | ~ m1_pre_topc(X0,X1)
% 3.51/0.99      | ~ v2_pre_topc(X1)
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X1)
% 3.51/0.99      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.51/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_23,plain,
% 3.51/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.99      | ~ m1_pre_topc(X0,X1)
% 3.51/0.99      | ~ l1_pre_topc(X1) ),
% 3.51/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_183,plain,
% 3.51/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.51/0.99      | ~ v2_pre_topc(X1)
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X1)
% 3.51/0.99      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.51/0.99      inference(global_propositional_subsumption,[status(thm)],[c_20,c_23]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_184,plain,
% 3.51/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.51/0.99      | ~ v2_pre_topc(X1)
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | ~ l1_pre_topc(X1)
% 3.51/0.99      | k5_tmap_1(X1,u1_struct_0(X0)) = u1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.51/0.99      inference(renaming,[status(thm)],[c_183]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1000,plain,
% 3.51/0.99      ( ~ v2_pre_topc(X0)
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X2)
% 3.51/0.99      | ~ l1_pre_topc(X0)
% 3.51/0.99      | X0 != X2
% 3.51/0.99      | k5_tmap_1(X0,u1_struct_0(X1)) = u1_pre_topc(k8_tmap_1(X0,X1))
% 3.51/0.99      | sK0(X2) != X1 ),
% 3.51/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_184]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1001,plain,
% 3.51/0.99      ( ~ v2_pre_topc(X0)
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | v2_struct_0(sK0(X0))
% 3.51/0.99      | ~ l1_pre_topc(X0)
% 3.51/0.99      | k5_tmap_1(X0,u1_struct_0(sK0(X0))) = u1_pre_topc(k8_tmap_1(X0,sK0(X0))) ),
% 3.51/0.99      inference(unflattening,[status(thm)],[c_1000]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2431,plain,
% 3.51/0.99      ( ~ v2_pre_topc(X0_58)
% 3.51/0.99      | v2_struct_0(X0_58)
% 3.51/0.99      | v2_struct_0(sK0(X0_58))
% 3.51/0.99      | ~ l1_pre_topc(X0_58)
% 3.51/0.99      | k5_tmap_1(X0_58,u1_struct_0(sK0(X0_58))) = u1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) ),
% 3.51/0.99      inference(subtyping,[status(esa)],[c_1001]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_26,negated_conjecture,
% 3.51/0.99      ( m1_pre_topc(sK3,sK2) ),
% 3.51/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1290,plain,
% 3.51/0.99      ( ~ v2_pre_topc(X0)
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X0)
% 3.51/0.99      | k5_tmap_1(X0,u1_struct_0(X1)) = u1_pre_topc(k8_tmap_1(X0,X1))
% 3.51/0.99      | sK2 != X0
% 3.51/0.99      | sK3 != X1 ),
% 3.51/0.99      inference(resolution_lifted,[status(thm)],[c_184,c_26]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1291,plain,
% 3.51/0.99      ( ~ v2_pre_topc(sK2)
% 3.51/0.99      | v2_struct_0(sK2)
% 3.51/0.99      | v2_struct_0(sK3)
% 3.51/0.99      | ~ l1_pre_topc(sK2)
% 3.51/0.99      | k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.51/0.99      inference(unflattening,[status(thm)],[c_1290]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_30,negated_conjecture,
% 3.51/0.99      ( ~ v2_struct_0(sK2) ),
% 3.51/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_29,negated_conjecture,
% 3.51/0.99      ( v2_pre_topc(sK2) ),
% 3.51/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_28,negated_conjecture,
% 3.51/0.99      ( l1_pre_topc(sK2) ),
% 3.51/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_27,negated_conjecture,
% 3.51/0.99      ( ~ v2_struct_0(sK3) ),
% 3.51/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1293,plain,
% 3.51/0.99      ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_1291,c_30,c_29,c_28,c_27]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2417,plain,
% 3.51/0.99      ( k5_tmap_1(sK2,u1_struct_0(sK3)) = u1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.51/0.99      inference(subtyping,[status(esa)],[c_1293]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_316,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_14,plain,
% 3.51/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.51/0.99      | ~ v2_pre_topc(X1)
% 3.51/0.99      | v2_pre_topc(k8_tmap_1(X1,X0))
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | ~ l1_pre_topc(X1) ),
% 3.51/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1339,plain,
% 3.51/0.99      ( ~ v2_pre_topc(X0)
% 3.51/0.99      | v2_pre_topc(k8_tmap_1(X0,X1))
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X0)
% 3.51/0.99      | sK2 != X0
% 3.51/0.99      | sK3 != X1 ),
% 3.51/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1340,plain,
% 3.51/0.99      ( v2_pre_topc(k8_tmap_1(sK2,sK3))
% 3.51/0.99      | ~ v2_pre_topc(sK2)
% 3.51/0.99      | v2_struct_0(sK2)
% 3.51/0.99      | ~ l1_pre_topc(sK2) ),
% 3.51/0.99      inference(unflattening,[status(thm)],[c_1339]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1342,plain,
% 3.51/0.99      ( v2_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_1340,c_30,c_29,c_28]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2412,plain,
% 3.51/0.99      ( v2_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.51/0.99      inference(subtyping,[status(esa)],[c_1342]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_3166,plain,
% 3.51/0.99      ( v2_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_2412]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_15,plain,
% 3.51/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.51/0.99      | v1_pre_topc(k8_tmap_1(X1,X0))
% 3.51/0.99      | ~ v2_pre_topc(X1)
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | ~ l1_pre_topc(X1) ),
% 3.51/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1072,plain,
% 3.51/0.99      ( v1_pre_topc(k8_tmap_1(X0,X1))
% 3.51/0.99      | ~ v2_pre_topc(X0)
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X2)
% 3.51/0.99      | ~ l1_pre_topc(X0)
% 3.51/0.99      | X0 != X2
% 3.51/0.99      | sK0(X2) != X1 ),
% 3.51/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_15]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1073,plain,
% 3.51/0.99      ( v1_pre_topc(k8_tmap_1(X0,sK0(X0)))
% 3.51/0.99      | ~ v2_pre_topc(X0)
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X0) ),
% 3.51/0.99      inference(unflattening,[status(thm)],[c_1072]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2427,plain,
% 3.51/0.99      ( v1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58)))
% 3.51/0.99      | ~ v2_pre_topc(X0_58)
% 3.51/0.99      | v2_struct_0(X0_58)
% 3.51/0.99      | ~ l1_pre_topc(X0_58) ),
% 3.51/0.99      inference(subtyping,[status(esa)],[c_1073]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_3154,plain,
% 3.51/0.99      ( v1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_2427]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1090,plain,
% 3.51/0.99      ( ~ v2_pre_topc(X0)
% 3.51/0.99      | v2_pre_topc(k8_tmap_1(X0,X1))
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X2)
% 3.51/0.99      | ~ l1_pre_topc(X0)
% 3.51/0.99      | X0 != X2
% 3.51/0.99      | sK0(X2) != X1 ),
% 3.51/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_14]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1091,plain,
% 3.51/0.99      ( ~ v2_pre_topc(X0)
% 3.51/0.99      | v2_pre_topc(k8_tmap_1(X0,sK0(X0)))
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X0) ),
% 3.51/0.99      inference(unflattening,[status(thm)],[c_1090]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2426,plain,
% 3.51/0.99      ( ~ v2_pre_topc(X0_58)
% 3.51/0.99      | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58)))
% 3.51/0.99      | v2_struct_0(X0_58)
% 3.51/0.99      | ~ l1_pre_topc(X0_58) ),
% 3.51/0.99      inference(subtyping,[status(esa)],[c_1091]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_3155,plain,
% 3.51/0.99      ( v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_2426]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_8,plain,
% 3.51/0.99      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 3.51/0.99      | ~ m1_pre_topc(X1,X0)
% 3.51/0.99      | ~ v1_pre_topc(X2)
% 3.51/0.99      | ~ v2_pre_topc(X0)
% 3.51/0.99      | ~ v2_pre_topc(X2)
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X0)
% 3.51/0.99      | ~ l1_pre_topc(X2)
% 3.51/0.99      | k8_tmap_1(X0,X1) = X2 ),
% 3.51/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_952,plain,
% 3.51/0.99      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 3.51/0.99      | ~ v1_pre_topc(X2)
% 3.51/0.99      | ~ v2_pre_topc(X0)
% 3.51/0.99      | ~ v2_pre_topc(X2)
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X3)
% 3.51/0.99      | ~ l1_pre_topc(X0)
% 3.51/0.99      | ~ l1_pre_topc(X2)
% 3.51/0.99      | X0 != X3
% 3.51/0.99      | k8_tmap_1(X0,X1) = X2
% 3.51/0.99      | sK0(X3) != X1 ),
% 3.51/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_8]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_953,plain,
% 3.51/0.99      ( m1_subset_1(sK1(X0,sK0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.51/0.99      | ~ v1_pre_topc(X1)
% 3.51/0.99      | ~ v2_pre_topc(X1)
% 3.51/0.99      | ~ v2_pre_topc(X0)
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X1)
% 3.51/0.99      | ~ l1_pre_topc(X0)
% 3.51/0.99      | k8_tmap_1(X0,sK0(X0)) = X1 ),
% 3.51/0.99      inference(unflattening,[status(thm)],[c_952]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2433,plain,
% 3.51/0.99      ( m1_subset_1(sK1(X0_58,sK0(X0_58),X1_58),k1_zfmisc_1(u1_struct_0(X0_58)))
% 3.51/0.99      | ~ v1_pre_topc(X1_58)
% 3.51/0.99      | ~ v2_pre_topc(X0_58)
% 3.51/0.99      | ~ v2_pre_topc(X1_58)
% 3.51/0.99      | v2_struct_0(X0_58)
% 3.51/0.99      | ~ l1_pre_topc(X0_58)
% 3.51/0.99      | ~ l1_pre_topc(X1_58)
% 3.51/0.99      | k8_tmap_1(X0_58,sK0(X0_58)) = X1_58 ),
% 3.51/0.99      inference(subtyping,[status(esa)],[c_953]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_3148,plain,
% 3.51/0.99      ( k8_tmap_1(X0_58,sK0(X0_58)) = X1_58
% 3.51/0.99      | m1_subset_1(sK1(X0_58,sK0(X0_58),X1_58),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 3.51/0.99      | v1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | l1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_2433]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_5,plain,
% 3.51/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.99      | ~ v2_pre_topc(X1)
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | ~ l1_pre_topc(X1)
% 3.51/0.99      | k7_tmap_1(X1,X0) = k6_partfun1(u1_struct_0(X1)) ),
% 3.51/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2446,plain,
% 3.51/0.99      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_58)))
% 3.51/0.99      | ~ v2_pre_topc(X0_58)
% 3.51/0.99      | v2_struct_0(X0_58)
% 3.51/0.99      | ~ l1_pre_topc(X0_58)
% 3.51/0.99      | k7_tmap_1(X0_58,X0_57) = k6_partfun1(u1_struct_0(X0_58)) ),
% 3.51/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_3135,plain,
% 3.51/0.99      ( k7_tmap_1(X0_58,X0_57) = k6_partfun1(u1_struct_0(X0_58))
% 3.51/0.99      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_2446]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_5966,plain,
% 3.51/0.99      ( k8_tmap_1(X0_58,sK0(X0_58)) = X1_58
% 3.51/0.99      | k7_tmap_1(X0_58,sK1(X0_58,sK0(X0_58),X1_58)) = k6_partfun1(u1_struct_0(X0_58))
% 3.51/0.99      | v1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | l1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_3148,c_3135]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_7563,plain,
% 3.51/0.99      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = X1_58
% 3.51/0.99      | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),X1_58)) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/0.99      | v1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/0.99      | l1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_3155,c_5966]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_13,plain,
% 3.51/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.51/0.99      | ~ v2_pre_topc(X1)
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | ~ l1_pre_topc(X1)
% 3.51/0.99      | l1_pre_topc(k8_tmap_1(X1,X0)) ),
% 3.51/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1108,plain,
% 3.51/0.99      ( ~ v2_pre_topc(X0)
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X1)
% 3.51/0.99      | ~ l1_pre_topc(X0)
% 3.51/0.99      | l1_pre_topc(k8_tmap_1(X0,X2))
% 3.51/0.99      | X0 != X1
% 3.51/0.99      | sK0(X1) != X2 ),
% 3.51/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_13]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1109,plain,
% 3.51/0.99      ( ~ v2_pre_topc(X0)
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X0)
% 3.51/0.99      | l1_pre_topc(k8_tmap_1(X0,sK0(X0))) ),
% 3.51/0.99      inference(unflattening,[status(thm)],[c_1108]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2425,plain,
% 3.51/0.99      ( ~ v2_pre_topc(X0_58)
% 3.51/0.99      | v2_struct_0(X0_58)
% 3.51/0.99      | ~ l1_pre_topc(X0_58)
% 3.51/0.99      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) ),
% 3.51/0.99      inference(subtyping,[status(esa)],[c_1109]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2542,plain,
% 3.51/0.99      ( v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_2425]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_9701,plain,
% 3.51/0.99      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | v2_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),X1_58)) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/0.99      | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = X1_58 ),
% 3.51/0.99      inference(global_propositional_subsumption,[status(thm)],[c_7563,c_2542]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_9702,plain,
% 3.51/0.99      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = X1_58
% 3.51/0.99      | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),X1_58)) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/0.99      | v1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/0.99      | l1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/0.99      inference(renaming,[status(thm)],[c_9701]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_9717,plain,
% 3.51/0.99      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(X1_58,sK0(X1_58))
% 3.51/0.99      | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(X1_58,sK0(X1_58)))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/0.99      | v2_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(k8_tmap_1(X1_58,sK0(X1_58))) != iProver_top
% 3.51/0.99      | v2_struct_0(X1_58) = iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(k8_tmap_1(X1_58,sK0(X1_58))) != iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_3154,c_9702]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_3156,plain,
% 3.51/0.99      ( v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_2425]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11351,plain,
% 3.51/0.99      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(X1_58,sK0(X1_58))
% 3.51/0.99      | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(X1_58,sK0(X1_58)))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | v2_struct_0(X1_58) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/0.99      | l1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/0.99      inference(forward_subsumption_resolution,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_9717,c_3156,c_3155]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11356,plain,
% 3.51/0.99      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
% 3.51/0.99      | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_3166,c_11351]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_31,plain,
% 3.51/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_32,plain,
% 3.51/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_33,plain,
% 3.51/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1350,plain,
% 3.51/0.99      ( ~ v2_pre_topc(X0)
% 3.51/0.99      | v2_struct_0(X0)
% 3.51/0.99      | ~ l1_pre_topc(X0)
% 3.51/0.99      | l1_pre_topc(k8_tmap_1(X0,X1))
% 3.51/0.99      | sK2 != X0
% 3.51/0.99      | sK3 != X1 ),
% 3.51/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1351,plain,
% 3.51/0.99      ( ~ v2_pre_topc(sK2)
% 3.51/0.99      | v2_struct_0(sK2)
% 3.51/0.99      | l1_pre_topc(k8_tmap_1(sK2,sK3))
% 3.51/0.99      | ~ l1_pre_topc(sK2) ),
% 3.51/0.99      inference(unflattening,[status(thm)],[c_1350]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1352,plain,
% 3.51/0.99      ( v2_pre_topc(sK2) != iProver_top
% 3.51/0.99      | v2_struct_0(sK2) = iProver_top
% 3.51/0.99      | l1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_1351]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11715,plain,
% 3.51/0.99      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/0.99      | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) ),
% 3.51/0.99      inference(global_propositional_subsumption,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_11356,c_31,c_32,c_33,c_1352]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11716,plain,
% 3.51/0.99      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
% 3.51/0.99      | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/0.99      inference(renaming,[status(thm)],[c_11715]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11357,plain,
% 3.51/0.99      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(X1_58,sK0(X1_58)),sK0(k8_tmap_1(X1_58,sK0(X1_58))))
% 3.51/0.99      | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(k8_tmap_1(X1_58,sK0(X1_58)),sK0(k8_tmap_1(X1_58,sK0(X1_58)))))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/0.99      | v2_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_struct_0(X1_58) = iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X1_58,sK0(X1_58))) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(k8_tmap_1(X1_58,sK0(X1_58))) != iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_3155,c_11351]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11707,plain,
% 3.51/0.99      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(X1_58,sK0(X1_58)),sK0(k8_tmap_1(X1_58,sK0(X1_58))))
% 3.51/0.99      | k7_tmap_1(k8_tmap_1(X1_58,sK0(X1_58)),sK1(k8_tmap_1(X1_58,sK0(X1_58)),sK0(k8_tmap_1(X1_58,sK0(X1_58))),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(k8_tmap_1(X1_58,sK0(X1_58))))
% 3.51/0.99      | v2_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_struct_0(X1_58) = iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X1_58,sK0(X1_58))) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(X1_58) != iProver_top ),
% 3.51/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_11357,c_3156]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_7,plain,
% 3.51/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.51/0.99      | ~ v1_pre_topc(X2)
% 3.51/0.99      | ~ v2_pre_topc(X1)
% 3.51/0.99      | ~ v2_pre_topc(X2)
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | ~ l1_pre_topc(X1)
% 3.51/0.99      | ~ l1_pre_topc(X2)
% 3.51/0.99      | sK1(X1,X0,X2) = u1_struct_0(X0)
% 3.51/0.99      | k8_tmap_1(X1,X0) = X2 ),
% 3.51/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1126,plain,
% 3.51/0.99      ( ~ v1_pre_topc(X0)
% 3.51/0.99      | ~ v2_pre_topc(X1)
% 3.51/0.99      | ~ v2_pre_topc(X0)
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | ~ l1_pre_topc(X2)
% 3.51/0.99      | ~ l1_pre_topc(X1)
% 3.51/0.99      | ~ l1_pre_topc(X0)
% 3.51/0.99      | X1 != X2
% 3.51/0.99      | sK1(X1,X3,X0) = u1_struct_0(X3)
% 3.51/0.99      | k8_tmap_1(X1,X3) = X0
% 3.51/0.99      | sK0(X2) != X3 ),
% 3.51/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_7]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_1127,plain,
% 3.51/0.99      ( ~ v1_pre_topc(X0)
% 3.51/0.99      | ~ v2_pre_topc(X0)
% 3.51/0.99      | ~ v2_pre_topc(X1)
% 3.51/0.99      | v2_struct_0(X1)
% 3.51/0.99      | ~ l1_pre_topc(X0)
% 3.51/0.99      | ~ l1_pre_topc(X1)
% 3.51/0.99      | sK1(X1,sK0(X1),X0) = u1_struct_0(sK0(X1))
% 3.51/0.99      | k8_tmap_1(X1,sK0(X1)) = X0 ),
% 3.51/0.99      inference(unflattening,[status(thm)],[c_1126]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2424,plain,
% 3.51/0.99      ( ~ v1_pre_topc(X0_58)
% 3.51/0.99      | ~ v2_pre_topc(X0_58)
% 3.51/0.99      | ~ v2_pre_topc(X1_58)
% 3.51/0.99      | v2_struct_0(X1_58)
% 3.51/0.99      | ~ l1_pre_topc(X0_58)
% 3.51/0.99      | ~ l1_pre_topc(X1_58)
% 3.51/0.99      | k8_tmap_1(X1_58,sK0(X1_58)) = X0_58
% 3.51/0.99      | sK1(X1_58,sK0(X1_58),X0_58) = u1_struct_0(sK0(X1_58)) ),
% 3.51/0.99      inference(subtyping,[status(esa)],[c_1127]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_3157,plain,
% 3.51/0.99      ( k8_tmap_1(X0_58,sK0(X0_58)) = X1_58
% 3.51/0.99      | sK1(X0_58,sK0(X0_58),X1_58) = u1_struct_0(sK0(X0_58))
% 3.51/0.99      | v1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(X1_58) != iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_2424]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_8379,plain,
% 3.51/0.99      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = X1_58
% 3.51/0.99      | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),X1_58) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/0.99      | v1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/0.99      | l1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_3155,c_3157]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_10993,plain,
% 3.51/0.99      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | v2_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),X1_58) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/0.99      | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = X1_58 ),
% 3.51/0.99      inference(global_propositional_subsumption,[status(thm)],[c_8379,c_2542]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_10994,plain,
% 3.51/0.99      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = X1_58
% 3.51/0.99      | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),X1_58) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/0.99      | v1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/0.99      | l1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/0.99      inference(renaming,[status(thm)],[c_10993]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11009,plain,
% 3.51/0.99      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(X1_58,sK0(X1_58))
% 3.51/0.99      | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(X1_58,sK0(X1_58))) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/0.99      | v2_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(k8_tmap_1(X1_58,sK0(X1_58))) != iProver_top
% 3.51/0.99      | v2_struct_0(X1_58) = iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(k8_tmap_1(X1_58,sK0(X1_58))) != iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_3154,c_10994]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11157,plain,
% 3.51/0.99      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(X1_58,sK0(X1_58))
% 3.51/0.99      | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(X1_58,sK0(X1_58))) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | v2_struct_0(X1_58) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/0.99      | l1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/0.99      inference(forward_subsumption_resolution,
% 3.51/0.99                [status(thm)],
% 3.51/0.99                [c_11009,c_3156,c_3155]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11163,plain,
% 3.51/0.99      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(X1_58,sK0(X1_58)),sK0(k8_tmap_1(X1_58,sK0(X1_58))))
% 3.51/0.99      | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(k8_tmap_1(X1_58,sK0(X1_58)),sK0(k8_tmap_1(X1_58,sK0(X1_58))))) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/0.99      | v2_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_struct_0(X1_58) = iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X1_58,sK0(X1_58))) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(k8_tmap_1(X1_58,sK0(X1_58))) != iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_3155,c_11157]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11647,plain,
% 3.51/0.99      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(X1_58,sK0(X1_58)),sK0(k8_tmap_1(X1_58,sK0(X1_58))))
% 3.51/0.99      | sK1(k8_tmap_1(X1_58,sK0(X1_58)),sK0(k8_tmap_1(X1_58,sK0(X1_58))),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = u1_struct_0(sK0(k8_tmap_1(X1_58,sK0(X1_58))))
% 3.51/0.99      | v2_pre_topc(X1_58) != iProver_top
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_struct_0(X1_58) = iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X1_58,sK0(X1_58))) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(X1_58) != iProver_top ),
% 3.51/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_11163,c_3156]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_2439,negated_conjecture,
% 3.51/0.99      ( v2_pre_topc(sK2) ),
% 3.51/0.99      inference(subtyping,[status(esa)],[c_29]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_3142,plain,
% 3.51/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 3.51/0.99      inference(predicate_to_equality,[status(thm)],[c_2439]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11355,plain,
% 3.51/0.99      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/0.99      | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/0.99      | v2_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | v2_struct_0(X0_58) = iProver_top
% 3.51/0.99      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/0.99      | v2_struct_0(sK2) = iProver_top
% 3.51/0.99      | l1_pre_topc(X0_58) != iProver_top
% 3.51/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/0.99      inference(superposition,[status(thm)],[c_3142,c_11351]) ).
% 3.51/0.99  
% 3.51/0.99  cnf(c_11625,plain,
% 3.51/0.99      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_11355,c_31,c_33]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_11626,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_11625]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_11162,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3166,c_11157]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_11326,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_11162,c_31,c_32,c_33,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_11327,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_11326]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_11161,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK0(sK2))) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3142,c_11157]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_11226,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK0(sK2))) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_11161,c_31,c_33]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_11227,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK0(sK2))) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_11226]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1328,plain,
% 3.51/1.00      ( v1_pre_topc(k8_tmap_1(X0,X1))
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | sK2 != X0
% 3.51/1.00      | sK3 != X1 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1329,plain,
% 3.51/1.00      ( v1_pre_topc(k8_tmap_1(sK2,sK3))
% 3.51/1.00      | ~ v2_pre_topc(sK2)
% 3.51/1.00      | v2_struct_0(sK2)
% 3.51/1.00      | ~ l1_pre_topc(sK2) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_1328]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1331,plain,
% 3.51/1.00      ( v1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_1329,c_30,c_29,c_28]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2413,plain,
% 3.51/1.00      ( v1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_1331]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3165,plain,
% 3.51/1.00      ( v1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2413]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_11008,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK3)) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3165,c_10994]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1341,plain,
% 3.51/1.00      ( v2_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_1340]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_11055,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK3)) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_11008,c_31,c_32,c_33,c_1341,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_11056,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK3)) = u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_11055]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_21,plain,
% 3.51/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | u1_struct_0(k8_tmap_1(X1,X0)) = u1_struct_0(X1) ),
% 3.51/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1309,plain,
% 3.51/1.00      ( ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | u1_struct_0(k8_tmap_1(X0,X1)) = u1_struct_0(X0)
% 3.51/1.00      | sK2 != X0
% 3.51/1.00      | sK3 != X1 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1310,plain,
% 3.51/1.00      ( ~ v2_pre_topc(sK2)
% 3.51/1.00      | v2_struct_0(sK2)
% 3.51/1.00      | v2_struct_0(sK3)
% 3.51/1.00      | ~ l1_pre_topc(sK2)
% 3.51/1.00      | u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_1309]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1312,plain,
% 3.51/1.00      ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_1310,c_30,c_29,c_28,c_27]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2415,plain,
% 3.51/1.00      ( u1_struct_0(k8_tmap_1(sK2,sK3)) = u1_struct_0(sK2) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_1312]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5964,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
% 3.51/1.00      | m1_subset_1(sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2415,c_3148]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6203,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
% 3.51/1.00      | m1_subset_1(sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_5964,c_31,c_32,c_33,c_1341,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6204,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
% 3.51/1.00      | m1_subset_1(sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_6203]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3664,plain,
% 3.51/1.00      ( k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57) = k6_partfun1(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2415,c_3135]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3665,plain,
% 3.51/1.00      ( k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_3664,c_2415]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5017,plain,
% 3.51/1.00      ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_3665,c_31,c_32,c_33,c_1341,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5018,plain,
% 3.51/1.00      ( k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_5017]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6217,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58)) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_6204,c_5018]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7431,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(X0_58,sK0(X0_58))
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3154,c_6217]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2541,plain,
% 3.51/1.00      ( v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2426]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10472,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(X0_58,sK0(X0_58))
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_7431,c_2541,c_2542]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10473,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(X0_58,sK0(X0_58))
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_10472]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10486,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3155,c_10473]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10879,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_10486,c_2542]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10880,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_10879]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8378,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
% 3.51/1.00      | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3166,c_3157]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8957,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58 ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_8378,c_31,c_32,c_33,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8958,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
% 3.51/1.00      | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_8957]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8970,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(X0_58,sK0(X0_58))
% 3.51/1.00      | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3154,c_8958]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10323,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(X0_58,sK0(X0_58))
% 3.51/1.00      | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_8970,c_2541,c_2542]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10324,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(X0_58,sK0(X0_58))
% 3.51/1.00      | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_10323]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10337,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3155,c_10324]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10865,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_10337,c_2542]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10866,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_10865]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6216,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
% 3.51/1.00      | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58)) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_6204,c_3135]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6597,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58)) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_6216,c_31,c_32,c_33]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6598,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
% 3.51/1.00      | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58)) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_6597]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7429,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(X0_58,sK0(X0_58))
% 3.51/1.00      | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3154,c_6598]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9339,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(X0_58,sK0(X0_58))
% 3.51/1.00      | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_7429,c_2541,c_2542]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9340,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(X0_58,sK0(X0_58))
% 3.51/1.00      | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_9339]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9353,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3155,c_9340]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10740,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) ),
% 3.51/1.00      inference(global_propositional_subsumption,[status(thm)],[c_9353,c_2542]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10741,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_10740]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5967,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = X0_58
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),X0_58)) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3148,c_5018]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6464,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),X0_58)) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | k8_tmap_1(sK2,sK0(sK2)) = X0_58
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_5967,c_31,c_32,c_33]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6465,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = X0_58
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),X0_58)) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_6464]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7430,plain,
% 3.51/1.00      ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3154,c_6465]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10061,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_7430,c_2541,c_2542]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10062,plain,
% 3.51/1.00      ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_10061]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10073,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3155,c_10062]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10726,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2)) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_10073,c_2542]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10727,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_10726]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1255,plain,
% 3.51/1.00      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 3.51/1.00      | ~ v1_pre_topc(X2)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ v2_pre_topc(X2)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | k8_tmap_1(X0,X1) = X2
% 3.51/1.00      | sK2 != X0
% 3.51/1.00      | sK3 != X1 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_26]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1256,plain,
% 3.51/1.00      ( m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/1.00      | ~ v1_pre_topc(X0)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ v2_pre_topc(sK2)
% 3.51/1.00      | v2_struct_0(sK2)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | ~ l1_pre_topc(sK2)
% 3.51/1.00      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_1255]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1260,plain,
% 3.51/1.00      ( ~ l1_pre_topc(X0)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ v1_pre_topc(X0)
% 3.51/1.00      | m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/1.00      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_1256,c_30,c_29,c_28]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1261,plain,
% 3.51/1.00      ( m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/1.00      | ~ v1_pre_topc(X0)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_1260]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2419,plain,
% 3.51/1.00      ( m1_subset_1(sK1(sK2,sK3,X0_58),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/1.00      | ~ v1_pre_topc(X0_58)
% 3.51/1.00      | ~ v2_pre_topc(X0_58)
% 3.51/1.00      | ~ l1_pre_topc(X0_58)
% 3.51/1.00      | k8_tmap_1(sK2,sK3) = X0_58 ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_1261]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3162,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK3) = X0_58
% 3.51/1.00      | m1_subset_1(sK1(sK2,sK3,X0_58),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2419]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5027,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK3) = X0_58
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,X0_58)) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3162,c_5018]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7433,plain,
% 3.51/1.00      ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3154,c_5027]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9101,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_7433,c_2541,c_2542]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9102,plain,
% 3.51/1.00      ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_9101]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9115,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3155,c_9102]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10607,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3) ),
% 3.51/1.00      inference(global_propositional_subsumption,[status(thm)],[c_9115,c_2542]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10608,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_10607]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4547,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK3) = X0_58
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK3,X0_58)) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3162,c_3135]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6128,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK3,X0_58)) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | k8_tmap_1(sK2,sK3) = X0_58 ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_4547,c_31,c_32,c_33]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6129,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK3) = X0_58
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK3,X0_58)) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_6128]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7432,plain,
% 3.51/1.00      ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3154,c_6129]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1298,plain,
% 3.51/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | sK2 != X1
% 3.51/1.00      | sK3 != X0 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_26]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1299,plain,
% 3.51/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/1.00      | ~ l1_pre_topc(sK2) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_1298]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2448,plain,( X0_57 = X0_57 ),theory(equality) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4173,plain,
% 3.51/1.00      ( k1_zfmisc_1(u1_struct_0(X0_58)) = k1_zfmisc_1(u1_struct_0(X0_58)) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_2448]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4178,plain,
% 3.51/1.00      ( k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_4173]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6560,plain,
% 3.51/1.00      ( ~ m1_subset_1(sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58))),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/1.00      | ~ v2_pre_topc(sK2)
% 3.51/1.00      | v2_struct_0(sK2)
% 3.51/1.00      | ~ l1_pre_topc(sK2)
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_2446]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2462,plain,
% 3.51/1.00      ( ~ m1_subset_1(X0_57,X1_57)
% 3.51/1.00      | m1_subset_1(X2_57,X3_57)
% 3.51/1.00      | X2_57 != X0_57
% 3.51/1.00      | X3_57 != X1_57 ),
% 3.51/1.00      theory(equality) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3593,plain,
% 3.51/1.00      ( m1_subset_1(X0_57,X1_57)
% 3.51/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/1.00      | X1_57 != k1_zfmisc_1(u1_struct_0(sK2))
% 3.51/1.00      | X0_57 != u1_struct_0(sK3) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_2462]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6622,plain,
% 3.51/1.00      ( m1_subset_1(sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58))),X0_57)
% 3.51/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/1.00      | X0_57 != k1_zfmisc_1(u1_struct_0(sK2))
% 3.51/1.00      | sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58))) != u1_struct_0(sK3) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_3593]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7379,plain,
% 3.51/1.00      ( m1_subset_1(sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58))),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/1.00      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/1.00      | sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58))) != u1_struct_0(sK3)
% 3.51/1.00      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_6622]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1361,plain,
% 3.51/1.00      ( ~ v1_pre_topc(X0)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | sK1(X1,X2,X0) = u1_struct_0(X2)
% 3.51/1.00      | k8_tmap_1(X1,X2) = X0
% 3.51/1.00      | sK2 != X1
% 3.51/1.00      | sK3 != X2 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_26]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1362,plain,
% 3.51/1.00      ( ~ v1_pre_topc(X0)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ v2_pre_topc(sK2)
% 3.51/1.00      | v2_struct_0(sK2)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | ~ l1_pre_topc(sK2)
% 3.51/1.00      | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
% 3.51/1.00      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_1361]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1366,plain,
% 3.51/1.00      ( ~ l1_pre_topc(X0)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ v1_pre_topc(X0)
% 3.51/1.00      | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
% 3.51/1.00      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_1362,c_30,c_29,c_28]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1367,plain,
% 3.51/1.00      ( ~ v1_pre_topc(X0)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | sK1(sK2,sK3,X0) = u1_struct_0(sK3)
% 3.51/1.00      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_1366]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2410,plain,
% 3.51/1.00      ( ~ v1_pre_topc(X0_58)
% 3.51/1.00      | ~ v2_pre_topc(X0_58)
% 3.51/1.00      | ~ l1_pre_topc(X0_58)
% 3.51/1.00      | k8_tmap_1(sK2,sK3) = X0_58
% 3.51/1.00      | sK1(sK2,sK3,X0_58) = u1_struct_0(sK3) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_1367]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3168,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK3) = X0_58
% 3.51/1.00      | sK1(sK2,sK3,X0_58) = u1_struct_0(sK3)
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2410]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7434,plain,
% 3.51/1.00      ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(sK3)
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3154,c_3168]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7781,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(sK3)
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_7434,c_2541,c_2542]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7782,plain,
% 3.51/1.00      ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(sK3)
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_7781]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8101,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_7432,c_30,c_29,c_28,c_1299,c_2541,c_2542,c_4178,c_6560,
% 3.51/1.00                 c_7379,c_7434]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8102,plain,
% 3.51/1.00      ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_8101]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8114,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3155,c_8102]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10594,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3) ),
% 3.51/1.00      inference(global_propositional_subsumption,[status(thm)],[c_8114,c_2542]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10595,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_10594]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10484,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3142,c_10473]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10518,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_10484,c_31,c_33]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10335,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK0(sK2))) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3142,c_10324]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10369,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK0(sK2))) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_10335,c_31,c_33]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6935,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = X0_58
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),X0_58)) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3142,c_5966]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6961,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | k8_tmap_1(sK2,sK0(sK2)) = X0_58
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),X0_58)) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_6935,c_31,c_33]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6962,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = X0_58
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),X0_58)) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_6961]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7428,plain,
% 3.51/1.00      ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3154,c_6962]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7997,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_7428,c_2541,c_2542]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7998,plain,
% 3.51/1.00      ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(X0_58,sK0(X0_58)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_7997]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8008,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3155,c_7998]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10239,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2)) ),
% 3.51/1.00      inference(global_propositional_subsumption,[status(thm)],[c_8008,c_2542]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10240,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_10239]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8377,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = X0_58
% 3.51/1.00      | sK1(sK2,sK0(sK2),X0_58) = u1_struct_0(sK0(sK2))
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3142,c_3157]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8436,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | k8_tmap_1(sK2,sK0(sK2)) = X0_58
% 3.51/1.00      | sK1(sK2,sK0(sK2),X0_58) = u1_struct_0(sK0(sK2))
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_8377,c_31,c_33]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8437,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = X0_58
% 3.51/1.00      | sK1(sK2,sK0(sK2),X0_58) = u1_struct_0(sK0(sK2))
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_8436]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8448,plain,
% 3.51/1.00      ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | sK1(sK2,sK0(sK2),k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(sK0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3154,c_8437]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8792,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | sK1(sK2,sK0(sK2),k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(sK0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_8448,c_2541,c_2542]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8793,plain,
% 3.51/1.00      ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | sK1(sK2,sK0(sK2),k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(sK0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_8792]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8803,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = u1_struct_0(sK0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3155,c_8793]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10226,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = u1_struct_0(sK0(sK2))
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2)) ),
% 3.51/1.00      inference(global_propositional_subsumption,[status(thm)],[c_8803,c_2542]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10227,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = u1_struct_0(sK0(sK2))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_10226]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10072,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3166,c_10062]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10103,plain,
% 3.51/1.00      ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2)) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_10072,c_31,c_32,c_33,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10104,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_10103]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9716,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3165,c_9702]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9933,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_9716,c_31,c_32,c_33,c_1341,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9934,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_9933]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9114,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3166,c_9102]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9925,plain,
% 3.51/1.00      ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_9114,c_31,c_32,c_33,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9926,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_9925]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9,plain,
% 3.51/1.00      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/1.00      | ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ v1_pre_topc(k8_tmap_1(X1,X0))
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ v2_pre_topc(k8_tmap_1(X1,X0))
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(k8_tmap_1(X1,X0))
% 3.51/1.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_206,plain,
% 3.51/1.00      ( ~ l1_pre_topc(X1)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_9,c_23,c_15,c_14,c_13]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_207,plain,
% 3.51/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | k6_tmap_1(X1,u1_struct_0(X0)) = k8_tmap_1(X1,X0) ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_206]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_982,plain,
% 3.51/1.00      ( ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | X0 != X1
% 3.51/1.00      | k6_tmap_1(X0,u1_struct_0(X2)) = k8_tmap_1(X0,X2)
% 3.51/1.00      | sK0(X1) != X2 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_207]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_983,plain,
% 3.51/1.00      ( ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | k6_tmap_1(X0,u1_struct_0(sK0(X0))) = k8_tmap_1(X0,sK0(X0)) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_982]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2432,plain,
% 3.51/1.00      ( ~ v2_pre_topc(X0_58)
% 3.51/1.00      | v2_struct_0(X0_58)
% 3.51/1.00      | ~ l1_pre_topc(X0_58)
% 3.51/1.00      | k6_tmap_1(X0_58,u1_struct_0(sK0(X0_58))) = k8_tmap_1(X0_58,sK0(X0_58)) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_983]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3149,plain,
% 3.51/1.00      ( k6_tmap_1(X0_58,u1_struct_0(sK0(X0_58))) = k8_tmap_1(X0_58,sK0(X0_58))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2432]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7564,plain,
% 3.51/1.00      ( k6_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3155,c_3149]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9763,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | k6_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) ),
% 3.51/1.00      inference(global_propositional_subsumption,[status(thm)],[c_7564,c_2542]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9764,plain,
% 3.51/1.00      ( k6_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_9763]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1021,plain,
% 3.51/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | X1 != X2
% 3.51/1.00      | sK0(X2) != X0 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_23]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1022,plain,
% 3.51/1.00      ( m1_subset_1(u1_struct_0(sK0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
% 3.51/1.00      | ~ l1_pre_topc(X0) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_1021]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2430,plain,
% 3.51/1.00      ( m1_subset_1(u1_struct_0(sK0(X0_58)),k1_zfmisc_1(u1_struct_0(X0_58)))
% 3.51/1.00      | ~ l1_pre_topc(X0_58) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_1022]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3151,plain,
% 3.51/1.00      ( m1_subset_1(u1_struct_0(sK0(X0_58)),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2430]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4301,plain,
% 3.51/1.00      ( k7_tmap_1(X0_58,u1_struct_0(sK0(X0_58))) = k6_partfun1(u1_struct_0(X0_58))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3151,c_3135]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7565,plain,
% 3.51/1.00      ( k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3155,c_4301]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9615,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58)))) ),
% 3.51/1.00      inference(global_propositional_subsumption,[status(thm)],[c_7565,c_2542]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9616,plain,
% 3.51/1.00      ( k7_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),u1_struct_0(sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = k6_partfun1(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_9615]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9351,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3142,c_9340]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9607,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_9351,c_31,c_33]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9113,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3142,c_9102]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9331,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_9113,c_31,c_33]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7794,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = u1_struct_0(sK3)
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3155,c_7782]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9088,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = u1_struct_0(sK3)
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3) ),
% 3.51/1.00      inference(global_propositional_subsumption,[status(thm)],[c_7794,c_2542]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9089,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58)))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(X0_58,sK0(X0_58)),sK0(k8_tmap_1(X0_58,sK0(X0_58))))) = u1_struct_0(sK3)
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_9088]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8969,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK3)) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3165,c_8958]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9002,plain,
% 3.51/1.00      ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK3)) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3))) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_8969,c_31,c_32,c_33,c_1341,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_9003,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK3)) = u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_9002]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8802,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))) = u1_struct_0(sK0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3166,c_8793]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8831,plain,
% 3.51/1.00      ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))) = u1_struct_0(sK0(sK2))
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2)) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_8802,c_31,c_32,c_33,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8832,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))) = u1_struct_0(sK0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_8831]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8447,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3)) = u1_struct_0(sK0(sK2))
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3165,c_8437]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8471,plain,
% 3.51/1.00      ( ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
% 3.51/1.00      | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
% 3.51/1.00      | k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3)) = u1_struct_0(sK0(sK2)) ),
% 3.51/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_8447]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8680,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3)) = u1_struct_0(sK0(sK2)) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_8447,c_30,c_29,c_28,c_1329,c_1340,c_1351,c_3628]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8112,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3142,c_8102]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8145,plain,
% 3.51/1.00      ( v2_struct_0(sK2)
% 3.51/1.00      | ~ l1_pre_topc(sK2)
% 3.51/1.00      | k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.51/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_8112]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8240,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2)))) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_8112,c_31,c_32,c_33,c_1094,c_1112,c_7550]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_10,plain,
% 3.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/1.00      | m1_subset_1(k7_tmap_1(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X0)))))
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | ~ l1_pre_topc(X1) ),
% 3.51/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2445,plain,
% 3.51/1.00      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_58)))
% 3.51/1.00      | m1_subset_1(k7_tmap_1(X0_58,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(k6_tmap_1(X0_58,X0_57)))))
% 3.51/1.00      | ~ v2_pre_topc(X0_58)
% 3.51/1.00      | v2_struct_0(X0_58)
% 3.51/1.00      | ~ l1_pre_topc(X0_58) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3136,plain,
% 3.51/1.00      ( m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_tmap_1(X0_58,X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(k6_tmap_1(X0_58,X0_57))))) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2445]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8245,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | m1_subset_1(sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2)))))))) = iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_8240,c_3136]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1074,plain,
% 3.51/1.00      ( v1_pre_topc(k8_tmap_1(X0,sK0(X0))) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0) != iProver_top
% 3.51/1.00      | v2_struct_0(X0) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_1073]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1076,plain,
% 3.51/1.00      ( v1_pre_topc(k8_tmap_1(sK2,sK0(sK2))) = iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_1074]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1092,plain,
% 3.51/1.00      ( v2_pre_topc(X0) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(X0,sK0(X0))) = iProver_top
% 3.51/1.00      | v2_struct_0(X0) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_1091]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1094,plain,
% 3.51/1.00      ( v2_pre_topc(k8_tmap_1(sK2,sK0(sK2))) = iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_1092]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1110,plain,
% 3.51/1.00      ( v2_pre_topc(X0) != iProver_top
% 3.51/1.00      | v2_struct_0(X0) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0,sK0(X0))) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_1109]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1112,plain,
% 3.51/1.00      ( v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK0(sK2))) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_1110]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3548,plain,
% 3.51/1.00      ( m1_subset_1(sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58))),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/1.00      | ~ v1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58)))
% 3.51/1.00      | ~ v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58)))
% 3.51/1.00      | ~ l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58)))
% 3.51/1.00      | k8_tmap_1(sK2,sK3) = k8_tmap_1(X0_58,sK0(X0_58)) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_2419]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3554,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK3) = k8_tmap_1(X0_58,sK0(X0_58))
% 3.51/1.00      | m1_subset_1(sK1(sK2,sK3,k8_tmap_1(X0_58,sK0(X0_58))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.51/1.00      | v1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58))) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_3548]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3556,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK3) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | m1_subset_1(sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.51/1.00      | v1_pre_topc(k8_tmap_1(sK2,sK0(sK2))) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK0(sK2))) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK0(sK2))) != iProver_top ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_3554]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2453,plain,
% 3.51/1.00      ( X0_58 != X1_58 | X2_58 != X1_58 | X2_58 = X0_58 ),
% 3.51/1.00      theory(equality) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3833,plain,
% 3.51/1.00      ( X0_58 != X1_58
% 3.51/1.00      | X0_58 = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k8_tmap_1(sK2,sK3) != X1_58 ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_2453]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4060,plain,
% 3.51/1.00      ( X0_58 != k8_tmap_1(X1_58,X2_58)
% 3.51/1.00      | X0_58 = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k8_tmap_1(sK2,sK3) != k8_tmap_1(X1_58,X2_58) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_3833]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4759,plain,
% 3.51/1.00      ( X0_58 != k8_tmap_1(X1_58,sK0(X1_58))
% 3.51/1.00      | X0_58 = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k8_tmap_1(sK2,sK3) != k8_tmap_1(X1_58,sK0(X1_58)) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_4060]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4983,plain,
% 3.51/1.00      ( k8_tmap_1(X0_58,sK0(X0_58)) != k8_tmap_1(X0_58,sK0(X0_58))
% 3.51/1.00      | k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k8_tmap_1(sK2,sK3) != k8_tmap_1(X0_58,sK0(X0_58)) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_4759]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4985,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) != k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k8_tmap_1(sK2,sK3) != k8_tmap_1(sK2,sK0(sK2)) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_4983]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2449,plain,( X0_58 = X0_58 ),theory(equality) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4984,plain,
% 3.51/1.00      ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(X0_58,sK0(X0_58)) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_2449]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4986,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK0(sK2)) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_4984]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8554,plain,
% 3.51/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2)))))))) = iProver_top
% 3.51/1.00      | k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_8245,c_31,c_32,c_33,c_1076,c_1094,c_1112,c_3556,c_4985,
% 3.51/1.00                 c_4986]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8555,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2)))))))) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_8554]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_11,plain,
% 3.51/1.00      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
% 3.51/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2444,plain,
% 3.51/1.00      ( v1_funct_2(k7_tmap_1(X0_58,X0_57),u1_struct_0(X0_58),u1_struct_0(k6_tmap_1(X0_58,X0_57)))
% 3.51/1.00      | ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_58)))
% 3.51/1.00      | ~ v2_pre_topc(X0_58)
% 3.51/1.00      | v2_struct_0(X0_58)
% 3.51/1.00      | ~ l1_pre_topc(X0_58) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3137,plain,
% 3.51/1.00      ( v1_funct_2(k7_tmap_1(X0_58,X0_57),u1_struct_0(X0_58),u1_struct_0(k6_tmap_1(X0_58,X0_57))) = iProver_top
% 3.51/1.00      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2444]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8246,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2)))))) = iProver_top
% 3.51/1.00      | m1_subset_1(sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_8240,c_3137]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8545,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2)))))) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_8246,c_31,c_32,c_33,c_1076,c_1094,c_1112,c_3556,c_4985,
% 3.51/1.00                 c_4986]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8113,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3166,c_8102]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8275,plain,
% 3.51/1.00      ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_8113,c_31,c_32,c_33,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8276,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_8275]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8007,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3166,c_7998]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8093,plain,
% 3.51/1.00      ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2)) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_8007,c_31,c_32,c_33,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_8094,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_8093]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7793,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))) = u1_struct_0(sK3)
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3166,c_7782]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7989,plain,
% 3.51/1.00      ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))) = u1_struct_0(sK3)
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_7793,c_31,c_32,c_33,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7990,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK1(sK2,sK3,k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))) = u1_struct_0(sK3)
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_7989]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7792,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2))) = u1_struct_0(sK3)
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3142,c_7782]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7825,plain,
% 3.51/1.00      ( v2_struct_0(sK2)
% 3.51/1.00      | ~ l1_pre_topc(sK2)
% 3.51/1.00      | k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2))) = u1_struct_0(sK3) ),
% 3.51/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_7792]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7831,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK1(sK2,sK3,k8_tmap_1(sK2,sK0(sK2))) = u1_struct_0(sK3) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_7792,c_31,c_32,c_33,c_1094,c_1112,c_7556]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6972,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3165,c_6962]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6973,plain,
% 3.51/1.00      ( ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
% 3.51/1.00      | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
% 3.51/1.00      | k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.51/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6972]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7185,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_6972,c_31,c_32,c_33,c_1341,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7189,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | m1_subset_1(sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))))))) = iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_7185,c_3136]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1330,plain,
% 3.51/1.00      ( v1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_1329]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3636,plain,
% 3.51/1.00      ( m1_subset_1(sK1(X0_58,sK0(X0_58),k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(X0_58)))
% 3.51/1.00      | ~ v1_pre_topc(k8_tmap_1(sK2,sK3))
% 3.51/1.00      | ~ v2_pre_topc(X0_58)
% 3.51/1.00      | ~ v2_pre_topc(k8_tmap_1(sK2,sK3))
% 3.51/1.00      | v2_struct_0(X0_58)
% 3.51/1.00      | ~ l1_pre_topc(X0_58)
% 3.51/1.00      | ~ l1_pre_topc(k8_tmap_1(sK2,sK3))
% 3.51/1.00      | k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_2433]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3637,plain,
% 3.51/1.00      ( k8_tmap_1(X0_58,sK0(X0_58)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | m1_subset_1(sK1(X0_58,sK0(X0_58),k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(X0_58))) = iProver_top
% 3.51/1.00      | v1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_3636]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3639,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | m1_subset_1(sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.51/1.00      | v1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_3637]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7360,plain,
% 3.51/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))))))) = iProver_top
% 3.51/1.00      | k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_7189,c_31,c_32,c_33,c_1330,c_1341,c_1352,c_3639]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7361,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))))))) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_7360]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7190,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))))) = iProver_top
% 3.51/1.00      | m1_subset_1(sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_7185,c_3137]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7262,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))))) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_7190,c_31,c_32,c_33,c_1330,c_1341,c_1352,c_3639]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6609,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3165,c_6598]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7219,plain,
% 3.51/1.00      ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_6609,c_31,c_32,c_33,c_1341,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7220,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_7219]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6677,plain,
% 3.51/1.00      ( k6_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3166,c_3149]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7079,plain,
% 3.51/1.00      ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | k6_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_6677,c_31,c_32,c_33,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_7080,plain,
% 3.51/1.00      ( k6_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))) = k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_7079]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6676,plain,
% 3.51/1.00      ( k6_tmap_1(sK2,u1_struct_0(sK0(sK2))) = k8_tmap_1(sK2,sK0(sK2))
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3142,c_3149]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2530,plain,
% 3.51/1.00      ( ~ v2_pre_topc(sK2)
% 3.51/1.00      | v2_struct_0(sK2)
% 3.51/1.00      | ~ l1_pre_topc(sK2)
% 3.51/1.00      | k6_tmap_1(sK2,u1_struct_0(sK0(sK2))) = k8_tmap_1(sK2,sK0(sK2)) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_2432]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6693,plain,
% 3.51/1.00      ( k6_tmap_1(sK2,u1_struct_0(sK0(sK2))) = k8_tmap_1(sK2,sK0(sK2)) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_6676,c_30,c_29,c_28,c_2530]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4772,plain,
% 3.51/1.00      ( k7_tmap_1(sK2,u1_struct_0(sK0(sK2))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3142,c_4301]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1024,plain,
% 3.51/1.00      ( m1_subset_1(u1_struct_0(sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/1.00      | ~ l1_pre_topc(sK2) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_1022]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3578,plain,
% 3.51/1.00      ( ~ m1_subset_1(u1_struct_0(sK0(X0_58)),k1_zfmisc_1(u1_struct_0(X0_58)))
% 3.51/1.00      | ~ v2_pre_topc(X0_58)
% 3.51/1.00      | v2_struct_0(X0_58)
% 3.51/1.00      | ~ l1_pre_topc(X0_58)
% 3.51/1.00      | k7_tmap_1(X0_58,u1_struct_0(sK0(X0_58))) = k6_partfun1(u1_struct_0(X0_58)) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_2446]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3580,plain,
% 3.51/1.00      ( ~ m1_subset_1(u1_struct_0(sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/1.00      | ~ v2_pre_topc(sK2)
% 3.51/1.00      | v2_struct_0(sK2)
% 3.51/1.00      | ~ l1_pre_topc(sK2)
% 3.51/1.00      | k7_tmap_1(sK2,u1_struct_0(sK0(sK2))) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_3578]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4905,plain,
% 3.51/1.00      ( k7_tmap_1(sK2,u1_struct_0(sK0(sK2))) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_4772,c_30,c_29,c_28,c_1024,c_3580]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4909,plain,
% 3.51/1.00      ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK0(sK2))))) = iProver_top
% 3.51/1.00      | m1_subset_1(u1_struct_0(sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_4905,c_3137]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1023,plain,
% 3.51/1.00      ( m1_subset_1(u1_struct_0(sK0(X0)),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_1022]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1025,plain,
% 3.51/1.00      ( m1_subset_1(u1_struct_0(sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_1023]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5408,plain,
% 3.51/1.00      ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK0(sK2))))) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_4909,c_31,c_32,c_33,c_1025]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6697,plain,
% 3.51/1.00      ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK0(sK2)))) = iProver_top ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_6693,c_5408]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4908,plain,
% 3.51/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK0(sK2))))))) = iProver_top
% 3.51/1.00      | m1_subset_1(u1_struct_0(sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_4905,c_3136]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5503,plain,
% 3.51/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK0(sK2))))))) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_4908,c_31,c_32,c_33,c_1025]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6696,plain,
% 3.51/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK0(sK2)))))) = iProver_top ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_6693,c_5503]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_12,plain,
% 3.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | v1_funct_1(k7_tmap_1(X1,X0))
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | ~ l1_pre_topc(X1) ),
% 3.51/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2443,plain,
% 3.51/1.00      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_58)))
% 3.51/1.00      | ~ v2_pre_topc(X0_58)
% 3.51/1.00      | v1_funct_1(k7_tmap_1(X0_58,X0_57))
% 3.51/1.00      | v2_struct_0(X0_58)
% 3.51/1.00      | ~ l1_pre_topc(X0_58) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3138,plain,
% 3.51/1.00      ( m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(X0_58))) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v1_funct_1(k7_tmap_1(X0_58,X0_57)) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2443]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6215,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v1_funct_1(k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_6204,c_3138]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6584,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
% 3.51/1.00      | v1_funct_1(k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_6215,c_31,c_32,c_33]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6585,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = X0_58
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v1_funct_1(k7_tmap_1(sK2,sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_6584]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6476,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3165,c_6465]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6479,plain,
% 3.51/1.00      ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_6476,c_31,c_32,c_33,c_1341,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6480,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK0(sK2)) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(sK2,sK0(sK2),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_6479]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6367,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3165,c_6217]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6370,plain,
% 3.51/1.00      ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_6367,c_31,c_32,c_33,c_1341,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6371,plain,
% 3.51/1.00      ( k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k8_tmap_1(sK2,sK3)
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),sK1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3)),k8_tmap_1(sK2,sK3))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_6370]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4546,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK3) = X0_58
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v1_funct_1(k7_tmap_1(sK2,sK1(sK2,sK3,X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3162,c_3138]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6116,plain,
% 3.51/1.00      ( l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | k8_tmap_1(sK2,sK3) = X0_58
% 3.51/1.00      | v1_funct_1(k7_tmap_1(sK2,sK1(sK2,sK3,X0_58))) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_4546,c_31,c_32,c_33]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6117,plain,
% 3.51/1.00      ( k8_tmap_1(sK2,sK3) = X0_58
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v1_funct_1(k7_tmap_1(sK2,sK1(sK2,sK3,X0_58))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_6116]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4299,plain,
% 3.51/1.00      ( m1_subset_1(u1_struct_0(sK0(k8_tmap_1(sK2,sK3))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2415,c_3151]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4377,plain,
% 3.51/1.00      ( m1_subset_1(u1_struct_0(sK0(k8_tmap_1(sK2,sK3))),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_4299,c_31,c_32,c_33,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4383,plain,
% 3.51/1.00      ( k7_tmap_1(sK2,u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_4377,c_3135]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5379,plain,
% 3.51/1.00      ( k7_tmap_1(sK2,u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_4383,c_31,c_32,c_33]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5383,plain,
% 3.51/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))))))) = iProver_top
% 3.51/1.00      | m1_subset_1(u1_struct_0(sK0(k8_tmap_1(sK2,sK3))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_5379,c_3136]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6047,plain,
% 3.51/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))))))) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_5383,c_31,c_32,c_33,c_1352,c_4299]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5965,plain,
% 3.51/1.00      ( k8_tmap_1(X0_58,sK0(X0_58)) = X1_58
% 3.51/1.00      | v1_pre_topc(X1_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X1_58) != iProver_top
% 3.51/1.00      | v1_funct_1(k7_tmap_1(X0_58,sK1(X0_58,sK0(X0_58),X1_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X1_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3148,c_3138]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5028,plain,
% 3.51/1.00      ( k7_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK0(sK2))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3151,c_5018]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5836,plain,
% 3.51/1.00      ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK0(sK2))) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.51/1.00      inference(global_propositional_subsumption,[status(thm)],[c_5028,c_33]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5837,plain,
% 3.51/1.00      ( k7_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK0(sK2))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_5836]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_16,plain,
% 3.51/1.00      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.51/1.00      | ~ m1_pre_topc(X1,X0)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_934,plain,
% 3.51/1.00      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | X0 != X2
% 3.51/1.00      | sK0(X2) != X1 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_16]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_935,plain,
% 3.51/1.00      ( m1_subset_1(k9_tmap_1(X0,sK0(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK0(X0))))))
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_934]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2434,plain,
% 3.51/1.00      ( m1_subset_1(k9_tmap_1(X0_58,sK0(X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))))
% 3.51/1.00      | ~ v2_pre_topc(X0_58)
% 3.51/1.00      | v2_struct_0(X0_58)
% 3.51/1.00      | ~ l1_pre_topc(X0_58) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_935]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3147,plain,
% 3.51/1.00      ( m1_subset_1(k9_tmap_1(X0_58,sK0(X0_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58)))))) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2434]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5309,plain,
% 3.51/1.00      ( m1_subset_1(k9_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))))) = iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2415,c_3147]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5614,plain,
% 3.51/1.00      ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | m1_subset_1(k9_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))))) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_5309,c_31,c_32,c_33,c_1341,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5615,plain,
% 3.51/1.00      ( m1_subset_1(k9_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))))) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_5614]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5384,plain,
% 3.51/1.00      ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))))) = iProver_top
% 3.51/1.00      | m1_subset_1(u1_struct_0(sK0(k8_tmap_1(sK2,sK3))),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_5379,c_3137]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5509,plain,
% 3.51/1.00      ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))))) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_5384,c_31,c_32,c_33,c_1352,c_4299]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4,plain,
% 3.51/1.00      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
% 3.51/1.00      | ~ v1_funct_2(X5,X2,X3)
% 3.51/1.00      | ~ v1_funct_2(X4,X0,X1)
% 3.51/1.00      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.51/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.51/1.00      | ~ v1_funct_1(X5)
% 3.51/1.00      | ~ v1_funct_1(X4)
% 3.51/1.00      | v1_xboole_0(X1)
% 3.51/1.00      | v1_xboole_0(X3)
% 3.51/1.00      | X4 = X5 ),
% 3.51/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_22,plain,
% 3.51/1.00      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(X0),k9_tmap_1(X0,X1),k3_struct_0(X0))
% 3.51/1.00      | ~ m1_pre_topc(X1,X0)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | ~ l1_pre_topc(X0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_429,plain,
% 3.51/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.51/1.00      | ~ v1_funct_2(X3,X4,X5)
% 3.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.51/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.51/1.00      | ~ m1_pre_topc(X6,X7)
% 3.51/1.00      | ~ v2_pre_topc(X7)
% 3.51/1.00      | ~ v1_funct_1(X0)
% 3.51/1.00      | ~ v1_funct_1(X3)
% 3.51/1.00      | v2_struct_0(X7)
% 3.51/1.00      | v2_struct_0(X6)
% 3.51/1.00      | v1_xboole_0(X2)
% 3.51/1.00      | v1_xboole_0(X5)
% 3.51/1.00      | ~ l1_pre_topc(X7)
% 3.51/1.00      | X3 = X0
% 3.51/1.00      | k9_tmap_1(X7,X6) != X0
% 3.51/1.00      | k3_struct_0(X7) != X3
% 3.51/1.00      | u1_struct_0(X7) != X5
% 3.51/1.00      | u1_struct_0(X7) != X4
% 3.51/1.00      | u1_struct_0(X7) != X1
% 3.51/1.00      | u1_struct_0(k8_tmap_1(X7,X6)) != X2 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_22]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_430,plain,
% 3.51/1.00      ( ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.51/1.00      | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 3.51/1.00      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.51/1.00      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 3.51/1.00      | ~ m1_pre_topc(X1,X0)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.51/1.00      | ~ v1_funct_1(k3_struct_0(X0))
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | v1_xboole_0(u1_struct_0(X0))
% 3.51/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_429]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_17,plain,
% 3.51/1.00      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.51/1.00      | ~ m1_pre_topc(X1,X0)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_0,plain,
% 3.51/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2,plain,
% 3.51/1.00      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 3.51/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_372,plain,
% 3.51/1.00      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_pre_topc(X0) ),
% 3.51/1.00      inference(resolution,[status(thm)],[c_0,c_2]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_434,plain,
% 3.51/1.00      ( v2_struct_0(X0)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | ~ v1_funct_1(k3_struct_0(X0))
% 3.51/1.00      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ m1_pre_topc(X1,X0)
% 3.51/1.00      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 3.51/1.00      | ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 3.51/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_430,c_17,c_16,c_372]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_435,plain,
% 3.51/1.00      ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 3.51/1.00      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 3.51/1.00      | ~ m1_pre_topc(X1,X0)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ v1_funct_1(k9_tmap_1(X0,X1))
% 3.51/1.00      | ~ v1_funct_1(k3_struct_0(X0))
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_434]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_18,plain,
% 3.51/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | v1_funct_1(k9_tmap_1(X1,X0))
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | ~ l1_pre_topc(X1) ),
% 3.51/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_462,plain,
% 3.51/1.00      ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 3.51/1.00      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 3.51/1.00      | ~ m1_pre_topc(X1,X0)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ v1_funct_1(k3_struct_0(X0))
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | k3_struct_0(X0) = k9_tmap_1(X0,X1) ),
% 3.51/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_435,c_18]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_883,plain,
% 3.51/1.00      ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 3.51/1.00      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ v1_funct_1(k3_struct_0(X0))
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | X0 != X2
% 3.51/1.00      | k9_tmap_1(X0,X1) = k3_struct_0(X0)
% 3.51/1.00      | sK0(X2) != X1 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_462]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_884,plain,
% 3.51/1.00      ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 3.51/1.00      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ v1_funct_1(k3_struct_0(X0))
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | v2_struct_0(sK0(X0))
% 3.51/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,sK0(X0))))
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | k9_tmap_1(X0,sK0(X0)) = k3_struct_0(X0) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_883]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2436,plain,
% 3.51/1.00      ( ~ v1_funct_2(k3_struct_0(X0_58),u1_struct_0(X0_58),u1_struct_0(X0_58))
% 3.51/1.00      | ~ m1_subset_1(k3_struct_0(X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X0_58))))
% 3.51/1.00      | ~ v2_pre_topc(X0_58)
% 3.51/1.00      | ~ v1_funct_1(k3_struct_0(X0_58))
% 3.51/1.00      | v2_struct_0(X0_58)
% 3.51/1.00      | v2_struct_0(sK0(X0_58))
% 3.51/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/1.00      | ~ l1_pre_topc(X0_58)
% 3.51/1.00      | k9_tmap_1(X0_58,sK0(X0_58)) = k3_struct_0(X0_58) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_884]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3145,plain,
% 3.51/1.00      ( k9_tmap_1(X0_58,sK0(X0_58)) = k3_struct_0(X0_58)
% 3.51/1.00      | v1_funct_2(k3_struct_0(X0_58),u1_struct_0(X0_58),u1_struct_0(X0_58)) != iProver_top
% 3.51/1.00      | m1_subset_1(k3_struct_0(X0_58),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_58),u1_struct_0(X0_58)))) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v1_funct_1(k3_struct_0(X0_58)) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(sK0(X0_58)) = iProver_top
% 3.51/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58)))) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2436]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4107,plain,
% 3.51/1.00      ( k9_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k3_struct_0(k8_tmap_1(sK2,sK3))
% 3.51/1.00      | v1_funct_2(k3_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 3.51/1.00      | m1_subset_1(k3_struct_0(k8_tmap_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v1_funct_1(k3_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_struct_0(sK0(k8_tmap_1(sK2,sK3))) = iProver_top
% 3.51/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2415,c_3145]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4109,plain,
% 3.51/1.00      ( k9_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k3_struct_0(k8_tmap_1(sK2,sK3))
% 3.51/1.00      | v1_funct_2(k3_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.51/1.00      | m1_subset_1(k3_struct_0(k8_tmap_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v1_funct_1(k3_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_struct_0(sK0(k8_tmap_1(sK2,sK3))) = iProver_top
% 3.51/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_4107,c_2415]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5221,plain,
% 3.51/1.00      ( v1_xboole_0(u1_struct_0(k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = iProver_top
% 3.51/1.00      | v2_struct_0(sK0(k8_tmap_1(sK2,sK3))) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v1_funct_1(k3_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 3.51/1.00      | k9_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k3_struct_0(k8_tmap_1(sK2,sK3))
% 3.51/1.00      | v1_funct_2(k3_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.51/1.00      | m1_subset_1(k3_struct_0(k8_tmap_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_4109,c_31,c_32,c_33,c_1341,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5222,plain,
% 3.51/1.00      ( k9_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))) = k3_struct_0(k8_tmap_1(sK2,sK3))
% 3.51/1.00      | v1_funct_2(k3_struct_0(k8_tmap_1(sK2,sK3)),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.51/1.00      | m1_subset_1(k3_struct_0(k8_tmap_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.51/1.00      | v1_funct_1(k3_struct_0(k8_tmap_1(sK2,sK3))) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v2_struct_0(sK0(k8_tmap_1(sK2,sK3))) = iProver_top
% 3.51/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_5221]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3743,plain,
% 3.51/1.00      ( m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK2,sK3)))) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(k8_tmap_1(sK2,sK3),X0_57))))) = iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2415,c_3136]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3761,plain,
% 3.51/1.00      ( m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(k8_tmap_1(sK2,sK3),X0_57))))) = iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_3743,c_2415]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5211,plain,
% 3.51/1.00      ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(k8_tmap_1(sK2,sK3),X0_57))))) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_3761,c_31,c_32,c_33,c_1341,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5212,plain,
% 3.51/1.00      ( m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | m1_subset_1(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(k8_tmap_1(sK2,sK3),X0_57))))) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_5211]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3709,plain,
% 3.51/1.00      ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(k8_tmap_1(sK2,sK3),X0_57))) = iProver_top
% 3.51/1.00      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(k8_tmap_1(sK2,sK3)))) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2415,c_3137]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3727,plain,
% 3.51/1.00      ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(k8_tmap_1(sK2,sK3),X0_57))) = iProver_top
% 3.51/1.00      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_3709,c_2415]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5136,plain,
% 3.51/1.00      ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v1_funct_2(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(k8_tmap_1(sK2,sK3),X0_57))) = iProver_top
% 3.51/1.00      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_3727,c_31,c_32,c_33,c_1341,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5137,plain,
% 3.51/1.00      ( v1_funct_2(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(k8_tmap_1(sK2,sK3),X0_57))) = iProver_top
% 3.51/1.00      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_5136]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_916,plain,
% 3.51/1.00      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | X0 != X2
% 3.51/1.00      | sK0(X2) != X1 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_17]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_917,plain,
% 3.51/1.00      ( v1_funct_2(k9_tmap_1(X0,sK0(X0)),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,sK0(X0))))
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_916]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2435,plain,
% 3.51/1.00      ( v1_funct_2(k9_tmap_1(X0_58,sK0(X0_58)),u1_struct_0(X0_58),u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))))
% 3.51/1.00      | ~ v2_pre_topc(X0_58)
% 3.51/1.00      | v2_struct_0(X0_58)
% 3.51/1.00      | ~ l1_pre_topc(X0_58) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_917]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3146,plain,
% 3.51/1.00      ( v1_funct_2(k9_tmap_1(X0_58,sK0(X0_58)),u1_struct_0(X0_58),u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58)))) = iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2435]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4681,plain,
% 3.51/1.00      ( v1_funct_2(k9_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2415,c_3146]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5129,plain,
% 3.51/1.00      ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v1_funct_2(k9_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_4681,c_31,c_32,c_33,c_1341,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5130,plain,
% 3.51/1.00      ( v1_funct_2(k9_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(k8_tmap_1(sK2,sK3),sK0(k8_tmap_1(sK2,sK3))))) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_5129]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1301,plain,
% 3.51/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.51/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1299,c_28]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2416,plain,
% 3.51/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_1301]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3163,plain,
% 3.51/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2416]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5026,plain,
% 3.51/1.00      ( k7_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3163,c_5018]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4773,plain,
% 3.51/1.00      ( k7_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))) = k6_partfun1(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3166,c_4301]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4777,plain,
% 3.51/1.00      ( k7_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_4773,c_2415]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5004,plain,
% 3.51/1.00      ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | k7_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_4777,c_31,c_32,c_33,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_5005,plain,
% 3.51/1.00      ( k7_tmap_1(k8_tmap_1(sK2,sK3),u1_struct_0(sK0(k8_tmap_1(sK2,sK3)))) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_5004]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3974,plain,
% 3.51/1.00      ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK2))
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3163,c_3135]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3575,plain,
% 3.51/1.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/1.00      | ~ v2_pre_topc(sK2)
% 3.51/1.00      | v2_struct_0(sK2)
% 3.51/1.00      | ~ l1_pre_topc(sK2)
% 3.51/1.00      | k7_tmap_1(sK2,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_2446]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4195,plain,
% 3.51/1.00      ( k7_tmap_1(sK2,u1_struct_0(sK3)) = k6_partfun1(u1_struct_0(sK2)) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_3974,c_30,c_29,c_28,c_1299,c_3575]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4205,plain,
% 3.51/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))))) = iProver_top
% 3.51/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_4195,c_3136]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1282,plain,
% 3.51/1.00      ( ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | k6_tmap_1(X0,u1_struct_0(X1)) = k8_tmap_1(X0,X1)
% 3.51/1.00      | sK2 != X0
% 3.51/1.00      | sK3 != X1 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_207,c_26]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1283,plain,
% 3.51/1.00      ( ~ v2_pre_topc(sK2)
% 3.51/1.00      | v2_struct_0(sK2)
% 3.51/1.00      | ~ l1_pre_topc(sK2)
% 3.51/1.00      | k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_1282]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1285,plain,
% 3.51/1.00      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_1283,c_30,c_29,c_28]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2418,plain,
% 3.51/1.00      ( k6_tmap_1(sK2,u1_struct_0(sK3)) = k8_tmap_1(sK2,sK3) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_1285]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4223,plain,
% 3.51/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top
% 3.51/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_4205,c_2415,c_2418]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1300,plain,
% 3.51/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_1299]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4671,plain,
% 3.51/1.00      ( m1_subset_1(k6_partfun1(u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_4223,c_31,c_32,c_33,c_1300]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4206,plain,
% 3.51/1.00      ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(k6_tmap_1(sK2,u1_struct_0(sK3)))) = iProver_top
% 3.51/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_4195,c_3137]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4212,plain,
% 3.51/1.00      ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top
% 3.51/1.00      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_4206,c_2415,c_2418]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4587,plain,
% 3.51/1.00      ( v1_funct_2(k6_partfun1(u1_struct_0(sK2)),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_4212,c_31,c_32,c_33,c_1300]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2437,plain,
% 3.51/1.00      ( v2_struct_0(X0_58)
% 3.51/1.00      | ~ v1_xboole_0(u1_struct_0(X0_58))
% 3.51/1.00      | ~ l1_pre_topc(X0_58) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_372]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3144,plain,
% 3.51/1.00      ( v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v1_xboole_0(u1_struct_0(X0_58)) != iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2437]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3803,plain,
% 3.51/1.00      ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2415,c_3144]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_101,plain,
% 3.51/1.00      ( v2_struct_0(X0) = iProver_top
% 3.51/1.00      | v1_xboole_0(u1_struct_0(X0)) != iProver_top
% 3.51/1.00      | l1_struct_0(X0) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_103,plain,
% 3.51/1.00      ( v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
% 3.51/1.00      | l1_struct_0(sK2) != iProver_top ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_101]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_107,plain,
% 3.51/1.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_109,plain,
% 3.51/1.00      ( l1_pre_topc(sK2) != iProver_top | l1_struct_0(sK2) = iProver_top ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_107]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4403,plain,
% 3.51/1.00      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_3803,c_31,c_33,c_103,c_109]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4300,plain,
% 3.51/1.00      ( v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v1_funct_1(k7_tmap_1(X0_58,u1_struct_0(sK0(X0_58)))) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3151,c_3138]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3675,plain,
% 3.51/1.00      ( m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | v2_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top
% 3.51/1.00      | v1_funct_1(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57)) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | l1_pre_topc(k8_tmap_1(sK2,sK3)) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_2415,c_3138]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4287,plain,
% 3.51/1.00      ( v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top
% 3.51/1.00      | v1_funct_1(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57)) = iProver_top
% 3.51/1.00      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_3675,c_31,c_32,c_33,c_1341,c_1352]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4288,plain,
% 3.51/1.00      ( m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | v1_funct_1(k7_tmap_1(k8_tmap_1(sK2,sK3),X0_57)) = iProver_top
% 3.51/1.00      | v2_struct_0(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_4287]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_19,plain,
% 3.51/1.00      ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
% 3.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.51/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/1.00      | ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X1) ),
% 3.51/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_190,plain,
% 3.51/1.00      ( ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.51/1.00      | r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
% 3.51/1.00      | ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X1) ),
% 3.51/1.00      inference(global_propositional_subsumption,[status(thm)],[c_19,c_23]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_191,plain,
% 3.51/1.00      ( r1_tmap_1(X0,k6_tmap_1(X1,u1_struct_0(X0)),k2_tmap_1(X1,k6_tmap_1(X1,u1_struct_0(X0)),k7_tmap_1(X1,u1_struct_0(X0)),X0),X2)
% 3.51/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.51/1.00      | ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | ~ l1_pre_topc(X1) ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_190]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_24,negated_conjecture,
% 3.51/1.00      ( ~ r1_tmap_1(sK3,k8_tmap_1(sK2,sK3),k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3),sK4) ),
% 3.51/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_390,plain,
% 3.51/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.51/1.00      | ~ m1_pre_topc(X1,X2)
% 3.51/1.00      | ~ v2_pre_topc(X2)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X2)
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | k2_tmap_1(X2,k6_tmap_1(X2,u1_struct_0(X1)),k7_tmap_1(X2,u1_struct_0(X1)),X1) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.51/1.00      | k6_tmap_1(X2,u1_struct_0(X1)) != k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK4 != X0
% 3.51/1.00      | sK3 != X1 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_191,c_24]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_391,plain,
% 3.51/1.00      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 3.51/1.00      | ~ m1_pre_topc(sK3,X0)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | v2_struct_0(sK3)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.51/1.00      | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_390]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_25,negated_conjecture,
% 3.51/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.51/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_395,plain,
% 3.51/1.00      ( v2_struct_0(X0)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ m1_pre_topc(sK3,X0)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.51/1.00      | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_391,c_27,c_25]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_396,plain,
% 3.51/1.00      ( ~ m1_pre_topc(sK3,X0)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.51/1.00      | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_395]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1415,plain,
% 3.51/1.00      ( ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.51/1.00      | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK2 != X0
% 3.51/1.00      | sK3 != sK3 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_396]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1416,plain,
% 3.51/1.00      ( ~ v2_pre_topc(sK2)
% 3.51/1.00      | v2_struct_0(sK2)
% 3.51/1.00      | ~ l1_pre_topc(sK2)
% 3.51/1.00      | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.51/1.00      | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_1415]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_398,plain,
% 3.51/1.00      ( ~ m1_pre_topc(sK3,sK2)
% 3.51/1.00      | ~ v2_pre_topc(sK2)
% 3.51/1.00      | v2_struct_0(sK2)
% 3.51/1.00      | ~ l1_pre_topc(sK2)
% 3.51/1.00      | k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.51/1.00      | k6_tmap_1(sK2,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_396]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1418,plain,
% 3.51/1.00      ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_1416,c_30,c_29,c_28,c_26,c_398,c_1283]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2408,plain,
% 3.51/1.00      ( k2_tmap_1(sK2,k6_tmap_1(sK2,u1_struct_0(sK3)),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_1418]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3213,plain,
% 3.51/1.00      ( k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k7_tmap_1(sK2,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_2408,c_2418]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4199,plain,
% 3.51/1.00      ( k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k6_partfun1(u1_struct_0(sK2)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3) ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_4195,c_3213]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3973,plain,
% 3.51/1.00      ( v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) = iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(superposition,[status(thm)],[c_3163,c_3138]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3567,plain,
% 3.51/1.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.51/1.00      | ~ v2_pre_topc(sK2)
% 3.51/1.00      | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3)))
% 3.51/1.00      | v2_struct_0(sK2)
% 3.51/1.00      | ~ l1_pre_topc(sK2) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_2443]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3568,plain,
% 3.51/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.51/1.00      | v2_pre_topc(sK2) != iProver_top
% 3.51/1.00      | v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) = iProver_top
% 3.51/1.00      | v2_struct_0(sK2) = iProver_top
% 3.51/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_3567]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4189,plain,
% 3.51/1.00      ( v1_funct_1(k7_tmap_1(sK2,u1_struct_0(sK3))) = iProver_top ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_3973,c_31,c_32,c_33,c_1300,c_3568]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_4198,plain,
% 3.51/1.00      ( v1_funct_1(k6_partfun1(u1_struct_0(sK2))) = iProver_top ),
% 3.51/1.00      inference(demodulation,[status(thm)],[c_4195,c_4189]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1244,plain,
% 3.51/1.00      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | sK2 != X0
% 3.51/1.00      | sK3 != X1 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1245,plain,
% 3.51/1.00      ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))))
% 3.51/1.00      | ~ v2_pre_topc(sK2)
% 3.51/1.00      | v2_struct_0(sK2)
% 3.51/1.00      | ~ l1_pre_topc(sK2) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_1244]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1247,plain,
% 3.51/1.00      ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_1245,c_30,c_29,c_28]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2420,plain,
% 3.51/1.00      ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_1247]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3161,plain,
% 3.51/1.00      ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))))) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2420]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3200,plain,
% 3.51/1.00      ( m1_subset_1(k9_tmap_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) = iProver_top ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_3161,c_2415]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1233,plain,
% 3.51/1.00      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | sK2 != X0
% 3.51/1.00      | sK3 != X1 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1234,plain,
% 3.51/1.00      ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | ~ v2_pre_topc(sK2)
% 3.51/1.00      | v2_struct_0(sK2)
% 3.51/1.00      | ~ l1_pre_topc(sK2) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_1233]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1236,plain,
% 3.51/1.00      ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_1234,c_30,c_29,c_28]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2421,plain,
% 3.51/1.00      ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_1236]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3160,plain,
% 3.51/1.00      ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(k8_tmap_1(sK2,sK3))) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2421]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3197,plain,
% 3.51/1.00      ( v1_funct_2(k9_tmap_1(sK2,sK3),u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
% 3.51/1.00      inference(light_normalisation,[status(thm)],[c_3160,c_2415]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1210,plain,
% 3.51/1.00      ( ~ v1_funct_2(k3_struct_0(X0),u1_struct_0(X0),u1_struct_0(X0))
% 3.51/1.00      | ~ m1_subset_1(k3_struct_0(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ v1_funct_1(k3_struct_0(X0))
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(X0,X1)))
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | k9_tmap_1(X0,X1) = k3_struct_0(X0)
% 3.51/1.00      | sK2 != X0
% 3.51/1.00      | sK3 != X1 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_462,c_26]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1211,plain,
% 3.51/1.00      ( ~ v1_funct_2(k3_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2))
% 3.51/1.00      | ~ m1_subset_1(k3_struct_0(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
% 3.51/1.00      | ~ v2_pre_topc(sK2)
% 3.51/1.00      | ~ v1_funct_1(k3_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(sK2)
% 3.51/1.00      | v2_struct_0(sK3)
% 3.51/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | ~ l1_pre_topc(sK2)
% 3.51/1.00      | k9_tmap_1(sK2,sK3) = k3_struct_0(sK2) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_1210]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1213,plain,
% 3.51/1.00      ( v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | ~ v1_funct_1(k3_struct_0(sK2))
% 3.51/1.00      | ~ v1_funct_2(k3_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2))
% 3.51/1.00      | ~ m1_subset_1(k3_struct_0(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
% 3.51/1.00      | k9_tmap_1(sK2,sK3) = k3_struct_0(sK2) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_1211,c_30,c_29,c_28,c_27]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1214,plain,
% 3.51/1.00      ( ~ v1_funct_2(k3_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2))
% 3.51/1.00      | ~ m1_subset_1(k3_struct_0(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
% 3.51/1.00      | ~ v1_funct_1(k3_struct_0(sK2))
% 3.51/1.00      | v1_xboole_0(u1_struct_0(k8_tmap_1(sK2,sK3)))
% 3.51/1.00      | k9_tmap_1(sK2,sK3) = k3_struct_0(sK2) ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_1213]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1597,plain,
% 3.51/1.00      ( ~ v1_funct_2(k3_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2))
% 3.51/1.00      | ~ m1_subset_1(k3_struct_0(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
% 3.51/1.00      | ~ v1_funct_1(k3_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | k9_tmap_1(sK2,sK3) = k3_struct_0(sK2)
% 3.51/1.00      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(X0) ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_372,c_1214]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1599,plain,
% 3.51/1.00      ( ~ v1_funct_2(k3_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2))
% 3.51/1.00      | ~ m1_subset_1(k3_struct_0(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
% 3.51/1.00      | ~ v1_funct_1(k3_struct_0(sK2))
% 3.51/1.00      | v2_struct_0(sK2)
% 3.51/1.00      | ~ l1_pre_topc(sK2)
% 3.51/1.00      | k9_tmap_1(sK2,sK3) = k3_struct_0(sK2)
% 3.51/1.00      | u1_struct_0(k8_tmap_1(sK2,sK3)) != u1_struct_0(sK2) ),
% 3.51/1.00      inference(instantiation,[status(thm)],[c_1597]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1601,plain,
% 3.51/1.00      ( k9_tmap_1(sK2,sK3) = k3_struct_0(sK2)
% 3.51/1.00      | ~ v1_funct_1(k3_struct_0(sK2))
% 3.51/1.00      | ~ m1_subset_1(k3_struct_0(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
% 3.51/1.00      | ~ v1_funct_2(k3_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2)) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_1597,c_30,c_29,c_28,c_27,c_1310,c_1599]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1602,plain,
% 3.51/1.00      ( ~ v1_funct_2(k3_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2))
% 3.51/1.00      | ~ m1_subset_1(k3_struct_0(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
% 3.51/1.00      | ~ v1_funct_1(k3_struct_0(sK2))
% 3.51/1.00      | k9_tmap_1(sK2,sK3) = k3_struct_0(sK2) ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_1601]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2407,plain,
% 3.51/1.00      ( ~ v1_funct_2(k3_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2))
% 3.51/1.00      | ~ m1_subset_1(k3_struct_0(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
% 3.51/1.00      | ~ v1_funct_1(k3_struct_0(sK2))
% 3.51/1.00      | k9_tmap_1(sK2,sK3) = k3_struct_0(sK2) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_1602]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3170,plain,
% 3.51/1.00      ( k9_tmap_1(sK2,sK3) = k3_struct_0(sK2)
% 3.51/1.00      | v1_funct_2(k3_struct_0(sK2),u1_struct_0(sK2),u1_struct_0(sK2)) != iProver_top
% 3.51/1.00      | m1_subset_1(k3_struct_0(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top
% 3.51/1.00      | v1_funct_1(k3_struct_0(sK2)) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2407]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_6,plain,
% 3.51/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.51/1.00      | ~ v1_pre_topc(X2)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ v2_pre_topc(X2)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | k6_tmap_1(X1,sK1(X1,X0,X2)) != X2
% 3.51/1.00      | k8_tmap_1(X1,X0) = X2 ),
% 3.51/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1388,plain,
% 3.51/1.00      ( ~ v1_pre_topc(X0)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | k6_tmap_1(X1,sK1(X1,X2,X0)) != X0
% 3.51/1.00      | k8_tmap_1(X1,X2) = X0
% 3.51/1.00      | sK2 != X1
% 3.51/1.00      | sK3 != X2 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_26]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1389,plain,
% 3.51/1.00      ( ~ v1_pre_topc(X0)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ v2_pre_topc(sK2)
% 3.51/1.00      | v2_struct_0(sK2)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | ~ l1_pre_topc(sK2)
% 3.51/1.00      | k6_tmap_1(sK2,sK1(sK2,sK3,X0)) != X0
% 3.51/1.00      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_1388]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1393,plain,
% 3.51/1.00      ( ~ l1_pre_topc(X0)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ v1_pre_topc(X0)
% 3.51/1.00      | k6_tmap_1(sK2,sK1(sK2,sK3,X0)) != X0
% 3.51/1.00      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_1389,c_30,c_29,c_28]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1394,plain,
% 3.51/1.00      ( ~ v1_pre_topc(X0)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | k6_tmap_1(sK2,sK1(sK2,sK3,X0)) != X0
% 3.51/1.00      | k8_tmap_1(sK2,sK3) = X0 ),
% 3.51/1.00      inference(renaming,[status(thm)],[c_1393]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2409,plain,
% 3.51/1.00      ( ~ v1_pre_topc(X0_58)
% 3.51/1.00      | ~ v2_pre_topc(X0_58)
% 3.51/1.00      | ~ l1_pre_topc(X0_58)
% 3.51/1.00      | k6_tmap_1(sK2,sK1(sK2,sK3,X0_58)) != X0_58
% 3.51/1.00      | k8_tmap_1(sK2,sK3) = X0_58 ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_1394]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3169,plain,
% 3.51/1.00      ( k6_tmap_1(sK2,sK1(sK2,sK3,X0_58)) != X0_58
% 3.51/1.00      | k8_tmap_1(sK2,sK3) = X0_58
% 3.51/1.00      | v1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2409]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1186,plain,
% 3.51/1.00      ( ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | X0 != X1
% 3.51/1.00      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.51/1.00      | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK0(X1) != sK3 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_396]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1187,plain,
% 3.51/1.00      ( ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(sK3)),k7_tmap_1(X0,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.51/1.00      | k6_tmap_1(X0,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK0(X0) != sK3 ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_1186]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2422,plain,
% 3.51/1.00      ( ~ v2_pre_topc(X0_58)
% 3.51/1.00      | v2_struct_0(X0_58)
% 3.51/1.00      | ~ l1_pre_topc(X0_58)
% 3.51/1.00      | k2_tmap_1(X0_58,k6_tmap_1(X0_58,u1_struct_0(sK3)),k7_tmap_1(X0_58,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.51/1.00      | k6_tmap_1(X0_58,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK0(X0_58) != sK3 ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_1187]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3159,plain,
% 3.51/1.00      ( k2_tmap_1(X0_58,k6_tmap_1(X0_58,u1_struct_0(sK3)),k7_tmap_1(X0_58,u1_struct_0(sK3)),sK3) != k2_tmap_1(sK2,k8_tmap_1(sK2,sK3),k9_tmap_1(sK2,sK3),sK3)
% 3.51/1.00      | k6_tmap_1(X0_58,u1_struct_0(sK3)) != k8_tmap_1(sK2,sK3)
% 3.51/1.00      | sK0(X0_58) != sK3
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2422]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1156,plain,
% 3.51/1.00      ( ~ v1_pre_topc(X0)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | X1 != X2
% 3.51/1.00      | k6_tmap_1(X1,sK1(X1,X3,X0)) != X0
% 3.51/1.00      | k8_tmap_1(X1,X3) = X0
% 3.51/1.00      | sK0(X2) != X3 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_6]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1157,plain,
% 3.51/1.00      ( ~ v1_pre_topc(X0)
% 3.51/1.00      | ~ v2_pre_topc(X0)
% 3.51/1.00      | ~ v2_pre_topc(X1)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | ~ l1_pre_topc(X1)
% 3.51/1.00      | k6_tmap_1(X1,sK1(X1,sK0(X1),X0)) != X0
% 3.51/1.00      | k8_tmap_1(X1,sK0(X1)) = X0 ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_1156]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2423,plain,
% 3.51/1.00      ( ~ v1_pre_topc(X0_58)
% 3.51/1.00      | ~ v2_pre_topc(X0_58)
% 3.51/1.00      | ~ v2_pre_topc(X1_58)
% 3.51/1.00      | v2_struct_0(X1_58)
% 3.51/1.00      | ~ l1_pre_topc(X0_58)
% 3.51/1.00      | ~ l1_pre_topc(X1_58)
% 3.51/1.00      | k6_tmap_1(X1_58,sK1(X1_58,sK0(X1_58),X0_58)) != X0_58
% 3.51/1.00      | k8_tmap_1(X1_58,sK0(X1_58)) = X0_58 ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_1157]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3158,plain,
% 3.51/1.00      ( k6_tmap_1(X0_58,sK1(X0_58,sK0(X0_58),X1_58)) != X1_58
% 3.51/1.00      | k8_tmap_1(X0_58,sK0(X0_58)) = X1_58
% 3.51/1.00      | v1_pre_topc(X1_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X1_58) != iProver_top
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | l1_pre_topc(X1_58) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2423]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1054,plain,
% 3.51/1.00      ( ~ v2_pre_topc(X0)
% 3.51/1.00      | v1_funct_1(k9_tmap_1(X0,X1))
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | X0 != X2
% 3.51/1.00      | sK0(X2) != X1 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_18]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1055,plain,
% 3.51/1.00      ( ~ v2_pre_topc(X0)
% 3.51/1.00      | v1_funct_1(k9_tmap_1(X0,sK0(X0)))
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_1054]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2428,plain,
% 3.51/1.00      ( ~ v2_pre_topc(X0_58)
% 3.51/1.00      | v1_funct_1(k9_tmap_1(X0_58,sK0(X0_58)))
% 3.51/1.00      | v2_struct_0(X0_58)
% 3.51/1.00      | ~ l1_pre_topc(X0_58) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_1055]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3153,plain,
% 3.51/1.00      ( v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v1_funct_1(k9_tmap_1(X0_58,sK0(X0_58))) = iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2428]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1033,plain,
% 3.51/1.00      ( ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X1)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X2)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | X0 != X2
% 3.51/1.00      | u1_struct_0(k8_tmap_1(X0,X1)) = u1_struct_0(X0)
% 3.51/1.00      | sK0(X2) != X1 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_21]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1034,plain,
% 3.51/1.00      ( ~ v2_pre_topc(X0)
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | v2_struct_0(sK0(X0))
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | u1_struct_0(k8_tmap_1(X0,sK0(X0))) = u1_struct_0(X0) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_1033]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2429,plain,
% 3.51/1.00      ( ~ v2_pre_topc(X0_58)
% 3.51/1.00      | v2_struct_0(X0_58)
% 3.51/1.00      | v2_struct_0(sK0(X0_58))
% 3.51/1.00      | ~ l1_pre_topc(X0_58)
% 3.51/1.00      | u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(X0_58) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_1034]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3152,plain,
% 3.51/1.00      ( u1_struct_0(k8_tmap_1(X0_58,sK0(X0_58))) = u1_struct_0(X0_58)
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(sK0(X0_58)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2429]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3150,plain,
% 3.51/1.00      ( k5_tmap_1(X0_58,u1_struct_0(sK0(X0_58))) = u1_pre_topc(k8_tmap_1(X0_58,sK0(X0_58)))
% 3.51/1.00      | v2_pre_topc(X0_58) != iProver_top
% 3.51/1.00      | v2_struct_0(X0_58) = iProver_top
% 3.51/1.00      | v2_struct_0(sK0(X0_58)) = iProver_top
% 3.51/1.00      | l1_pre_topc(X0_58) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2431]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1353,plain,
% 3.51/1.00      ( l1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_1351,c_30,c_29,c_28]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2411,plain,
% 3.51/1.00      ( l1_pre_topc(k8_tmap_1(sK2,sK3)) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_1353]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3167,plain,
% 3.51/1.00      ( l1_pre_topc(k8_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2411]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1317,plain,
% 3.51/1.00      ( ~ v2_pre_topc(X0)
% 3.51/1.00      | v1_funct_1(k9_tmap_1(X0,X1))
% 3.51/1.00      | v2_struct_0(X0)
% 3.51/1.00      | ~ l1_pre_topc(X0)
% 3.51/1.00      | sK2 != X0
% 3.51/1.00      | sK3 != X1 ),
% 3.51/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1318,plain,
% 3.51/1.00      ( ~ v2_pre_topc(sK2)
% 3.51/1.00      | v1_funct_1(k9_tmap_1(sK2,sK3))
% 3.51/1.00      | v2_struct_0(sK2)
% 3.51/1.00      | ~ l1_pre_topc(sK2) ),
% 3.51/1.00      inference(unflattening,[status(thm)],[c_1317]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_1320,plain,
% 3.51/1.00      ( v1_funct_1(k9_tmap_1(sK2,sK3)) ),
% 3.51/1.00      inference(global_propositional_subsumption,
% 3.51/1.00                [status(thm)],
% 3.51/1.00                [c_1318,c_30,c_29,c_28]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2414,plain,
% 3.51/1.00      ( v1_funct_1(k9_tmap_1(sK2,sK3)) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_1320]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3164,plain,
% 3.51/1.00      ( v1_funct_1(k9_tmap_1(sK2,sK3)) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2414]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2442,negated_conjecture,
% 3.51/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_25]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3139,plain,
% 3.51/1.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2442]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2441,negated_conjecture,
% 3.51/1.00      ( ~ v2_struct_0(sK3) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_27]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3140,plain,
% 3.51/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2441]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2440,negated_conjecture,
% 3.51/1.00      ( l1_pre_topc(sK2) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_28]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3141,plain,
% 3.51/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2440]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_2438,negated_conjecture,
% 3.51/1.00      ( ~ v2_struct_0(sK2) ),
% 3.51/1.00      inference(subtyping,[status(esa)],[c_30]) ).
% 3.51/1.00  
% 3.51/1.00  cnf(c_3143,plain,
% 3.51/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 3.51/1.00      inference(predicate_to_equality,[status(thm)],[c_2438]) ).
% 3.51/1.00  
% 3.51/1.00  
% 3.51/1.00  % SZS output end Saturation for theBenchmark.p
% 3.51/1.00  
% 3.51/1.00  ------                               Statistics
% 3.51/1.00  
% 3.51/1.00  ------ General
% 3.51/1.00  
% 3.51/1.00  abstr_ref_over_cycles:                  0
% 3.51/1.00  abstr_ref_under_cycles:                 0
% 3.51/1.00  gc_basic_clause_elim:                   0
% 3.51/1.00  forced_gc_time:                         0
% 3.51/1.00  parsing_time:                           0.012
% 3.51/1.00  unif_index_cands_time:                  0.
% 3.51/1.00  unif_index_add_time:                    0.
% 3.51/1.00  orderings_time:                         0.
% 3.51/1.00  out_proof_time:                         0.
% 3.51/1.00  total_time:                             0.402
% 3.51/1.00  num_of_symbols:                         67
% 3.51/1.00  num_of_terms:                           7935
% 3.51/1.00  
% 3.51/1.00  ------ Preprocessing
% 3.51/1.00  
% 3.51/1.00  num_of_splits:                          0
% 3.51/1.00  num_of_split_atoms:                     0
% 3.51/1.00  num_of_reused_defs:                     0
% 3.51/1.00  num_eq_ax_congr_red:                    11
% 3.51/1.00  num_of_sem_filtered_clauses:            7
% 3.51/1.00  num_of_subtypes:                        4
% 3.51/1.00  monotx_restored_types:                  0
% 3.51/1.00  sat_num_of_epr_types:                   0
% 3.51/1.00  sat_num_of_non_cyclic_types:            0
% 3.51/1.00  sat_guarded_non_collapsed_types:        1
% 3.51/1.00  num_pure_diseq_elim:                    0
% 3.51/1.00  simp_replaced_by:                       0
% 3.51/1.00  res_preprocessed:                       164
% 3.51/1.00  prep_upred:                             0
% 3.51/1.00  prep_unflattend:                        87
% 3.51/1.00  smt_new_axioms:                         0
% 3.51/1.00  pred_elim_cands:                        12
% 3.51/1.00  pred_elim:                              4
% 3.51/1.00  pred_elim_cl:                           -9
% 3.51/1.00  pred_elim_cycles:                       13
% 3.51/1.00  merged_defs:                            0
% 3.51/1.00  merged_defs_ncl:                        0
% 3.51/1.00  bin_hyper_res:                          0
% 3.51/1.00  prep_cycles:                            3
% 3.51/1.00  pred_elim_time:                         0.052
% 3.51/1.00  splitting_time:                         0.
% 3.51/1.00  sem_filter_time:                        0.
% 3.51/1.00  monotx_time:                            0.
% 3.51/1.00  subtype_inf_time:                       0.
% 3.51/1.00  
% 3.51/1.00  ------ Problem properties
% 3.51/1.00  
% 3.51/1.00  clauses:                                40
% 3.51/1.00  conjectures:                            5
% 3.51/1.00  epr:                                    4
% 3.51/1.00  horn:                                   21
% 3.51/1.00  ground:                                 17
% 3.51/1.00  unary:                                  16
% 3.51/1.00  binary:                                 1
% 3.51/1.00  lits:                                   137
% 3.51/1.00  lits_eq:                                23
% 3.51/1.00  fd_pure:                                0
% 3.51/1.00  fd_pseudo:                              0
% 3.51/1.00  fd_cond:                                3
% 3.51/1.00  fd_pseudo_cond:                         3
% 3.51/1.00  ac_symbols:                             0
% 3.51/1.00  
% 3.51/1.00  ------ Propositional Solver
% 3.51/1.00  
% 3.51/1.00  prop_solver_calls:                      26
% 3.51/1.00  prop_fast_solver_calls:                 2819
% 3.51/1.00  smt_solver_calls:                       0
% 3.51/1.00  smt_fast_solver_calls:                  0
% 3.51/1.00  prop_num_of_clauses:                    3291
% 3.51/1.00  prop_preprocess_simplified:             9323
% 3.51/1.00  prop_fo_subsumed:                       250
% 3.51/1.00  prop_solver_time:                       0.
% 3.51/1.00  smt_solver_time:                        0.
% 3.51/1.00  smt_fast_solver_time:                   0.
% 3.51/1.00  prop_fast_solver_time:                  0.
% 3.51/1.00  prop_unsat_core_time:                   0.
% 3.51/1.00  
% 3.51/1.00  ------ QBF
% 3.51/1.00  
% 3.51/1.00  qbf_q_res:                              0
% 3.51/1.00  qbf_num_tautologies:                    0
% 3.51/1.00  qbf_prep_cycles:                        0
% 3.51/1.00  
% 3.51/1.00  ------ BMC1
% 3.51/1.00  
% 3.51/1.00  bmc1_current_bound:                     -1
% 3.51/1.00  bmc1_last_solved_bound:                 -1
% 3.51/1.00  bmc1_unsat_core_size:                   -1
% 3.51/1.00  bmc1_unsat_core_parents_size:           -1
% 3.51/1.00  bmc1_merge_next_fun:                    0
% 3.51/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.51/1.00  
% 3.51/1.00  ------ Instantiation
% 3.51/1.00  
% 3.51/1.00  inst_num_of_clauses:                    1101
% 3.51/1.00  inst_num_in_passive:                    433
% 3.51/1.00  inst_num_in_active:                     631
% 3.51/1.00  inst_num_in_unprocessed:                37
% 3.51/1.00  inst_num_of_loops:                      700
% 3.51/1.00  inst_num_of_learning_restarts:          0
% 3.51/1.00  inst_num_moves_active_passive:          65
% 3.51/1.00  inst_lit_activity:                      0
% 3.51/1.00  inst_lit_activity_moves:                0
% 3.51/1.00  inst_num_tautologies:                   0
% 3.51/1.00  inst_num_prop_implied:                  0
% 3.51/1.00  inst_num_existing_simplified:           0
% 3.51/1.00  inst_num_eq_res_simplified:             0
% 3.51/1.00  inst_num_child_elim:                    0
% 3.51/1.00  inst_num_of_dismatching_blockings:      692
% 3.51/1.00  inst_num_of_non_proper_insts:           1375
% 3.51/1.00  inst_num_of_duplicates:                 0
% 3.51/1.00  inst_inst_num_from_inst_to_res:         0
% 3.51/1.00  inst_dismatching_checking_time:         0.
% 3.51/1.00  
% 3.51/1.00  ------ Resolution
% 3.51/1.00  
% 3.51/1.00  res_num_of_clauses:                     0
% 3.51/1.00  res_num_in_passive:                     0
% 3.51/1.00  res_num_in_active:                      0
% 3.51/1.00  res_num_of_loops:                       167
% 3.51/1.00  res_forward_subset_subsumed:            246
% 3.51/1.00  res_backward_subset_subsumed:           2
% 3.51/1.00  res_forward_subsumed:                   0
% 3.51/1.00  res_backward_subsumed:                  1
% 3.51/1.00  res_forward_subsumption_resolution:     13
% 3.51/1.00  res_backward_subsumption_resolution:    0
% 3.51/1.00  res_clause_to_clause_subsumption:       581
% 3.51/1.00  res_orphan_elimination:                 0
% 3.51/1.00  res_tautology_del:                      254
% 3.51/1.00  res_num_eq_res_simplified:              0
% 3.51/1.00  res_num_sel_changes:                    0
% 3.51/1.00  res_moves_from_active_to_pass:          0
% 3.51/1.00  
% 3.51/1.00  ------ Superposition
% 3.51/1.00  
% 3.51/1.00  sup_time_total:                         0.
% 3.51/1.00  sup_time_generating:                    0.
% 3.51/1.00  sup_time_sim_full:                      0.
% 3.51/1.00  sup_time_sim_immed:                     0.
% 3.51/1.00  
% 3.51/1.00  sup_num_of_clauses:                     138
% 3.51/1.00  sup_num_in_active:                      133
% 3.51/1.00  sup_num_in_passive:                     5
% 3.51/1.00  sup_num_of_loops:                       138
% 3.51/1.00  sup_fw_superposition:                   79
% 3.51/1.00  sup_bw_superposition:                   48
% 3.51/1.00  sup_immediate_simplified:               31
% 3.51/1.00  sup_given_eliminated:                   0
% 3.51/1.00  comparisons_done:                       0
% 3.51/1.00  comparisons_avoided:                    131
% 3.51/1.00  
% 3.51/1.00  ------ Simplifications
% 3.51/1.00  
% 3.51/1.00  
% 3.51/1.00  sim_fw_subset_subsumed:                 8
% 3.51/1.00  sim_bw_subset_subsumed:                 0
% 3.51/1.00  sim_fw_subsumed:                        9
% 3.51/1.00  sim_bw_subsumed:                        0
% 3.51/1.00  sim_fw_subsumption_res:                 6
% 3.51/1.00  sim_bw_subsumption_res:                 0
% 3.51/1.00  sim_tautology_del:                      2
% 3.51/1.00  sim_eq_tautology_del:                   11
% 3.51/1.00  sim_eq_res_simp:                        2
% 3.51/1.00  sim_fw_demodulated:                     0
% 3.51/1.00  sim_bw_demodulated:                     5
% 3.51/1.00  sim_light_normalised:                   27
% 3.51/1.00  sim_joinable_taut:                      0
% 3.51/1.00  sim_joinable_simp:                      0
% 3.51/1.00  sim_ac_normalised:                      0
% 3.51/1.00  sim_smt_subsumption:                    0
% 3.51/1.00  
%------------------------------------------------------------------------------
