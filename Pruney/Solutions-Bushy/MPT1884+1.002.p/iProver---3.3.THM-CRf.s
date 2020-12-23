%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1884+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:47 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_7031)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( v4_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & ~ v2_struct_0(X2) )
                 => ( m1_pre_topc(X1,X2)
                   => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) )
              & v1_tdlat_3(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( v4_tex_2(X1,X0)
            <=> ( ! [X2] :
                    ( ( m1_pre_topc(X2,X0)
                      & v1_tdlat_3(X2)
                      & ~ v2_struct_0(X2) )
                   => ( m1_pre_topc(X1,X2)
                     => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) )
                & v1_tdlat_3(X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_tex_2(X1,X0)
          <~> ( ! [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tdlat_3(X2)
                  | v2_struct_0(X2) )
              & v1_tdlat_3(X1) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_tex_2(X1,X0)
          <~> ( ! [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tdlat_3(X2)
                  | v2_struct_0(X2) )
              & v1_tdlat_3(X1) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,X0) )
          & ( ( ! [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tdlat_3(X2)
                  | v2_struct_0(X2) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,X0) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,X0) )
          & ( ( ! [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tdlat_3(X2)
                  | v2_struct_0(X2) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,X0) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,X0) )
          & ( ( ! [X3] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | ~ m1_pre_topc(X1,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_tdlat_3(X3)
                  | v2_struct_0(X3) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,X0) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f56])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
          & m1_pre_topc(X1,X2)
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
     => ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        & m1_pre_topc(X1,sK4)
        & m1_pre_topc(sK4,X0)
        & v1_tdlat_3(sK4)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,X0) )
          & ( ( ! [X3] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | ~ m1_pre_topc(X1,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_tdlat_3(X3)
                  | v2_struct_0(X3) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,X0) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ( ? [X2] :
              ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(sK3,X2)
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v1_tdlat_3(sK3)
          | ~ v4_tex_2(sK3,X0) )
        & ( ( ! [X3] :
                ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                | ~ m1_pre_topc(sK3,X3)
                | ~ m1_pre_topc(X3,X0)
                | ~ v1_tdlat_3(X3)
                | v2_struct_0(X3) )
            & v1_tdlat_3(sK3) )
          | v4_tex_2(sK3,X0) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X2,X0)
                  & v1_tdlat_3(X2)
                  & ~ v2_struct_0(X2) )
              | ~ v1_tdlat_3(X1)
              | ~ v4_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                    | ~ m1_pre_topc(X1,X3)
                    | ~ m1_pre_topc(X3,X0)
                    | ~ v1_tdlat_3(X3)
                    | v2_struct_0(X3) )
                & v1_tdlat_3(X1) )
              | v4_tex_2(X1,X0) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,sK2)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,sK2) )
          & ( ( ! [X3] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | ~ m1_pre_topc(X1,X3)
                  | ~ m1_pre_topc(X3,sK2)
                  | ~ v1_tdlat_3(X3)
                  | v2_struct_0(X3) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,sK2) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ( ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
        & m1_pre_topc(sK3,sK4)
        & m1_pre_topc(sK4,sK2)
        & v1_tdlat_3(sK4)
        & ~ v2_struct_0(sK4) )
      | ~ v1_tdlat_3(sK3)
      | ~ v4_tex_2(sK3,sK2) )
    & ( ( ! [X3] :
            ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
            | ~ m1_pre_topc(sK3,X3)
            | ~ m1_pre_topc(X3,sK2)
            | ~ v1_tdlat_3(X3)
            | v2_struct_0(X3) )
        & v1_tdlat_3(sK3) )
      | v4_tex_2(sK3,sK2) )
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f57,f60,f59,f58])).

fof(f97,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f73,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f95,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f74,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f71,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f62,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK1(X0,X1)) = X1
        & m1_pre_topc(sK1(X0,X1),X0)
        & v1_tdlat_3(sK1(X0,X1))
        & v1_pre_topc(sK1(X0,X1))
        & ~ v2_struct_0(sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK1(X0,X1)) = X1
            & m1_pre_topc(sK1(X0,X1),X0)
            & v1_tdlat_3(sK1(X0,X1))
            & v1_pre_topc(sK1(X0,X1))
            & ~ v2_struct_0(sK1(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f50])).

fof(f85,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK1(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f94,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f93,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f96,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f72,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v3_tex_2(X2,X0)
                <=> v4_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tex_2(X2,X0)
              <=> v4_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tex_2(X2,X0)
              <=> v4_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tex_2(X2,X0)
                  | ~ v4_tex_2(X1,X0) )
                & ( v4_tex_2(X1,X0)
                  | ~ v3_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v3_tex_2(X2,X0)
      | ~ v4_tex_2(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v3_tex_2(u1_struct_0(X1),X0)
      | ~ v4_tex_2(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f98,plain,
    ( v1_tdlat_3(sK3)
    | v4_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK0(X0,X1) != X1
        & r1_tarski(X1,sK0(X0,X1))
        & v2_tex_2(sK0(X0,X1),X0)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK0(X0,X1) != X1
                & r1_tarski(X1,sK0(X0,X1))
                & v2_tex_2(sK0(X0,X1),X0)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f46,f47])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK0(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK0(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f100,plain,
    ( ~ v2_struct_0(sK4)
    | ~ v1_tdlat_3(sK3)
    | ~ v4_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f101,plain,
    ( v1_tdlat_3(sK4)
    | ~ v1_tdlat_3(sK3)
    | ~ v4_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f102,plain,
    ( m1_pre_topc(sK4,sK2)
    | ~ v1_tdlat_3(sK3)
    | ~ v4_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f103,plain,
    ( m1_pre_topc(sK3,sK4)
    | ~ v1_tdlat_3(sK3)
    | ~ v4_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f104,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ v1_tdlat_3(sK3)
    | ~ v4_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v4_tex_2(X1,X0)
      | ~ v3_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v4_tex_2(X1,X0)
      | ~ v3_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | u1_struct_0(X1) != u1_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK1(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f99,plain,(
    ! [X3] :
      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | ~ m1_pre_topc(sK3,X3)
      | ~ m1_pre_topc(X3,sK2)
      | ~ v1_tdlat_3(X3)
      | v2_struct_0(X3)
      | v4_tex_2(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(sK1(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK1(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK1(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK0(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_38,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_4201,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4216,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5361,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4201,c_4216])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_45,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_47,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4423,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_4757,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_4423])).

cnf(c_4758,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4757])).

cnf(c_5409,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5361,c_45,c_47,c_4758])).

cnf(c_12,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4215,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_4218,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5314,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4215,c_4218])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4225,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7746,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5314,c_4225])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4217,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5305,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4215,c_4217])).

cnf(c_9430,plain,
    ( l1_pre_topc(X0) != iProver_top
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7746,c_5305])).

cnf(c_9431,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9430])).

cnf(c_9437,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(superposition,[status(thm)],[c_5409,c_9431])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_4213,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9859,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9437,c_4213])).

cnf(c_10203,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3)
    | m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_9859])).

cnf(c_108,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_5310,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5305])).

cnf(c_7748,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | l1_pre_topc(sK3) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7746])).

cnf(c_5907,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | X2 = u1_struct_0(X1)
    | g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(X1),X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_6583,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | X1 = u1_struct_0(X0)
    | g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_5907])).

cnf(c_8358,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_6583])).

cnf(c_8360,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_8358])).

cnf(c_21571,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10203,c_40,c_45,c_38,c_47,c_108,c_4757,c_4758,c_5310,c_7748,c_8360])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_272,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_16])).

cnf(c_273,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_tex_2(u1_struct_0(X0),X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_272])).

cnf(c_4194,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v2_tex_2(u1_struct_0(X0),X1) = iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_273])).

cnf(c_4212,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_19,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_803,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_41])).

cnf(c_804,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(sK1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_803])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_808,plain,
    ( v1_xboole_0(X0)
    | ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_804,c_42,c_40])).

cnf(c_809,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(sK2,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_808])).

cnf(c_4185,plain,
    ( u1_struct_0(sK1(sK2,X0)) = X0
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_809])).

cnf(c_5727,plain,
    ( u1_struct_0(sK1(sK2,u1_struct_0(X0))) = u1_struct_0(X0)
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4212,c_4185])).

cnf(c_6422,plain,
    ( v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | v2_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | u1_struct_0(sK1(sK2,u1_struct_0(X0))) = u1_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5727,c_45])).

cnf(c_6423,plain,
    ( u1_struct_0(sK1(sK2,u1_struct_0(X0))) = u1_struct_0(X0)
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6422])).

cnf(c_6428,plain,
    ( u1_struct_0(sK1(sK2,u1_struct_0(X0))) = u1_struct_0(X0)
    | m1_pre_topc(X0,sK2) != iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4194,c_6423])).

cnf(c_43,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_7141,plain,
    ( v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | u1_struct_0(sK1(sK2,u1_struct_0(X0))) = u1_struct_0(X0)
    | m1_pre_topc(X0,sK2) != iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6428,c_43,c_45])).

cnf(c_7142,plain,
    ( u1_struct_0(sK1(sK2,u1_struct_0(X0))) = u1_struct_0(X0)
    | m1_pre_topc(X0,sK2) != iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7141])).

cnf(c_7147,plain,
    ( u1_struct_0(sK1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK3)
    | v1_tdlat_3(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4201,c_7142])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_10,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_13,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_583,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_10,c_13])).

cnf(c_585,plain,
    ( v2_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_28,plain,
    ( ~ v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v3_tex_2(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_249,plain,
    ( v3_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v4_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_16])).

cnf(c_250,plain,
    ( ~ v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v3_tex_2(u1_struct_0(X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_249])).

cnf(c_37,negated_conjecture,
    ( v4_tex_2(sK3,sK2)
    | v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1423,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v3_tex_2(u1_struct_0(X0),X1)
    | v1_tdlat_3(sK3)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_250,c_37])).

cnf(c_1424,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | v3_tex_2(u1_struct_0(sK3),sK2)
    | v1_tdlat_3(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1423])).

cnf(c_1426,plain,
    ( v3_tex_2(u1_struct_0(sK3),sK2)
    | v1_tdlat_3(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1424,c_42,c_40,c_38])).

cnf(c_7,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4607,plain,
    ( v2_tex_2(X0,sK2)
    | ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5194,plain,
    ( v2_tex_2(u1_struct_0(X0),sK2)
    | ~ v3_tex_2(u1_struct_0(X0),sK2)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_4607])).

cnf(c_5196,plain,
    ( v2_tex_2(u1_struct_0(sK3),sK2)
    | ~ v3_tex_2(u1_struct_0(sK3),sK2)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5194])).

cnf(c_6020,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_6424,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ v2_tex_2(u1_struct_0(X0),sK2)
    | v1_xboole_0(u1_struct_0(X0))
    | u1_struct_0(sK1(sK2,u1_struct_0(X0))) = u1_struct_0(X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6423])).

cnf(c_6426,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v2_tex_2(u1_struct_0(sK3),sK2)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(sK1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_6424])).

cnf(c_7151,plain,
    ( ~ v1_tdlat_3(sK3)
    | v2_struct_0(sK3)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(sK1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7147])).

cnf(c_7365,plain,
    ( u1_struct_0(sK1(sK2,u1_struct_0(sK3))) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7147,c_40,c_39,c_38,c_585,c_1426,c_4757,c_5196,c_6020,c_6426,c_7151])).

cnf(c_26,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_707,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_41])).

cnf(c_708,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_707])).

cnf(c_712,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_708,c_40])).

cnf(c_713,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_712])).

cnf(c_4189,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_24,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4211,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4221,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | v3_tex_2(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6296,plain,
    ( u1_struct_0(sK1(sK2,sK0(sK2,X0))) = sK0(sK2,X0)
    | v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(sK0(sK2,X0),sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK0(sK2,X0)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4221,c_4185])).

cnf(c_4,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_4937,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(sK0(sK2,X0),sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4938,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(sK0(sK2,X0),sK2) = iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4937])).

cnf(c_6769,plain,
    ( v1_xboole_0(sK0(sK2,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | u1_struct_0(sK1(sK2,sK0(sK2,X0))) = sK0(sK2,X0)
    | v2_tex_2(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6296,c_45,c_4938])).

cnf(c_6770,plain,
    ( u1_struct_0(sK1(sK2,sK0(sK2,X0))) = sK0(sK2,X0)
    | v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK0(sK2,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6769])).

cnf(c_6775,plain,
    ( u1_struct_0(sK1(sK2,sK0(sK2,X0))) = sK0(sK2,X0)
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | v1_xboole_0(sK0(sK2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4211,c_6770])).

cnf(c_7023,plain,
    ( u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(X0)))) = sK0(sK2,u1_struct_0(X0))
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK2) = iProver_top
    | v1_xboole_0(sK0(sK2,u1_struct_0(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4189,c_6775])).

cnf(c_6777,plain,
    ( u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(X0)))) = sK0(sK2,u1_struct_0(X0))
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK2) = iProver_top
    | v1_xboole_0(sK0(sK2,u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4212,c_6770])).

cnf(c_7028,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(X0)))) = sK0(sK2,u1_struct_0(X0))
    | v2_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK2) = iProver_top
    | v1_xboole_0(sK0(sK2,u1_struct_0(X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7023,c_45,c_6777])).

cnf(c_7029,plain,
    ( u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(X0)))) = sK0(sK2,u1_struct_0(X0))
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK2) = iProver_top
    | v1_xboole_0(sK0(sK2,u1_struct_0(X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_7028])).

cnf(c_7370,plain,
    ( u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK1(sK2,u1_struct_0(sK3)))))) = sK0(sK2,u1_struct_0(sK1(sK2,u1_struct_0(sK3))))
    | m1_pre_topc(sK1(sK2,u1_struct_0(sK3)),sK2) != iProver_top
    | v2_tex_2(u1_struct_0(sK1(sK2,u1_struct_0(sK3))),sK2) != iProver_top
    | v3_tex_2(u1_struct_0(sK1(sK2,u1_struct_0(sK3))),sK2) = iProver_top
    | v1_xboole_0(sK0(sK2,u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7365,c_7029])).

cnf(c_7405,plain,
    ( u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK3)))) = sK0(sK2,u1_struct_0(sK3))
    | m1_pre_topc(sK1(sK2,u1_struct_0(sK3)),sK2) != iProver_top
    | v2_tex_2(u1_struct_0(sK3),sK2) != iProver_top
    | v3_tex_2(u1_struct_0(sK3),sK2) = iProver_top
    | v1_xboole_0(sK0(sK2,u1_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7370,c_7365])).

cnf(c_46,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_584,plain,
    ( v2_struct_0(X0) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_586,plain,
    ( v2_struct_0(sK3) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_584])).

cnf(c_1428,plain,
    ( v3_tex_2(u1_struct_0(sK3),sK2) = iProver_top
    | v1_tdlat_3(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1426])).

cnf(c_4529,plain,
    ( v2_tex_2(sK0(sK2,u1_struct_0(X0)),sK2)
    | ~ v2_tex_2(u1_struct_0(X0),sK2)
    | v3_tex_2(u1_struct_0(X0),sK2)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4530,plain,
    ( v2_tex_2(sK0(sK2,u1_struct_0(X0)),sK2) = iProver_top
    | v2_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK2) = iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4529])).

cnf(c_4532,plain,
    ( v2_tex_2(sK0(sK2,u1_struct_0(sK3)),sK2) = iProver_top
    | v2_tex_2(u1_struct_0(sK3),sK2) != iProver_top
    | v3_tex_2(u1_struct_0(sK3),sK2) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4530])).

cnf(c_3,plain,
    ( r1_tarski(X0,sK0(X1,X0))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4528,plain,
    ( r1_tarski(u1_struct_0(X0),sK0(sK2,u1_struct_0(X0)))
    | ~ v2_tex_2(u1_struct_0(X0),sK2)
    | v3_tex_2(u1_struct_0(X0),sK2)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4534,plain,
    ( r1_tarski(u1_struct_0(X0),sK0(sK2,u1_struct_0(X0))) = iProver_top
    | v2_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK2) = iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4528])).

cnf(c_4536,plain,
    ( r1_tarski(u1_struct_0(sK3),sK0(sK2,u1_struct_0(sK3))) = iProver_top
    | v2_tex_2(u1_struct_0(sK3),sK2) != iProver_top
    | v3_tex_2(u1_struct_0(sK3),sK2) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4534])).

cnf(c_4329,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | v2_tex_2(u1_struct_0(sK3),X0)
    | ~ v1_tdlat_3(sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_273])).

cnf(c_4626,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | v2_tex_2(u1_struct_0(sK3),sK2)
    | ~ v1_tdlat_3(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_4329])).

cnf(c_4627,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | v2_tex_2(u1_struct_0(sK3),sK2) = iProver_top
    | v1_tdlat_3(sK3) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4626])).

cnf(c_6021,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6020])).

cnf(c_6349,plain,
    ( ~ v2_tex_2(sK0(sK2,u1_struct_0(X0)),sK2)
    | ~ m1_subset_1(sK0(sK2,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK0(sK2,u1_struct_0(X0)))
    | u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(X0)))) = sK0(sK2,u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_809])).

cnf(c_6370,plain,
    ( u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(X0)))) = sK0(sK2,u1_struct_0(X0))
    | v2_tex_2(sK0(sK2,u1_struct_0(X0)),sK2) != iProver_top
    | m1_subset_1(sK0(sK2,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK0(sK2,u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6349])).

cnf(c_6372,plain,
    ( u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK3)))) = sK0(sK2,u1_struct_0(sK3))
    | v2_tex_2(sK0(sK2,u1_struct_0(sK3)),sK2) != iProver_top
    | m1_subset_1(sK0(sK2,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK0(sK2,u1_struct_0(sK3))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6370])).

cnf(c_7778,plain,
    ( ~ v2_tex_2(u1_struct_0(X0),sK2)
    | v3_tex_2(u1_struct_0(X0),sK2)
    | m1_subset_1(sK0(sK2,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_7779,plain,
    ( v2_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK2) = iProver_top
    | m1_subset_1(sK0(sK2,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7778])).

cnf(c_7781,plain,
    ( v2_tex_2(u1_struct_0(sK3),sK2) != iProver_top
    | v3_tex_2(u1_struct_0(sK3),sK2) = iProver_top
    | m1_subset_1(sK0(sK2,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7779])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_347,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_432,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_1,c_347])).

cnf(c_7674,plain,
    ( ~ r1_tarski(X0,sK0(sK2,u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(sK0(sK2,u1_struct_0(X1))) ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_9113,plain,
    ( ~ r1_tarski(u1_struct_0(X0),sK0(sK2,u1_struct_0(X0)))
    | ~ v1_xboole_0(sK0(sK2,u1_struct_0(X0)))
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_7674])).

cnf(c_9114,plain,
    ( r1_tarski(u1_struct_0(X0),sK0(sK2,u1_struct_0(X0))) != iProver_top
    | v1_xboole_0(sK0(sK2,u1_struct_0(X0))) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9113])).

cnf(c_9116,plain,
    ( r1_tarski(u1_struct_0(sK3),sK0(sK2,u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(sK0(sK2,u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_9114])).

cnf(c_10481,plain,
    ( v3_tex_2(u1_struct_0(sK3),sK2) = iProver_top
    | u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK3)))) = sK0(sK2,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7405,c_43,c_45,c_46,c_47,c_586,c_1428,c_4536,c_4627,c_4758,c_6021,c_7031,c_9116])).

cnf(c_10482,plain,
    ( u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK3)))) = sK0(sK2,u1_struct_0(sK3))
    | v3_tex_2(u1_struct_0(sK3),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_10481])).

cnf(c_4199,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_9436,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(superposition,[status(thm)],[c_4199,c_9431])).

cnf(c_9586,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9436,c_4213])).

cnf(c_9606,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2)
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_9586])).

cnf(c_8137,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_8138,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8137])).

cnf(c_15094,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9606,c_45,c_8138])).

cnf(c_15162,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15094,c_4189])).

cnf(c_6255,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_6266,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6255])).

cnf(c_25,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_4644,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_7847,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_4644])).

cnf(c_7848,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7847])).

cnf(c_16565,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15162,c_45,c_6266,c_7848])).

cnf(c_16571,plain,
    ( m1_pre_topc(sK1(sK2,u1_struct_0(sK3)),sK2) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7365,c_16565])).

cnf(c_6155,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_4644])).

cnf(c_6156,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6155])).

cnf(c_16629,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16571,c_45,c_47,c_6021,c_6156])).

cnf(c_4219,plain,
    ( v2_tex_2(X0,X1) = iProver_top
    | v3_tex_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5856,plain,
    ( r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | v2_tex_2(X0,X1) = iProver_top
    | v3_tex_2(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4211,c_4219])).

cnf(c_16634,plain,
    ( v2_tex_2(u1_struct_0(sK3),sK2) = iProver_top
    | v3_tex_2(u1_struct_0(sK3),sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_16629,c_5856])).

cnf(c_35,negated_conjecture,
    ( ~ v4_tex_2(sK3,sK2)
    | ~ v1_tdlat_3(sK3)
    | ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_52,plain,
    ( v4_tex_2(sK3,sK2) != iProver_top
    | v1_tdlat_3(sK3) != iProver_top
    | v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( ~ v4_tex_2(sK3,sK2)
    | v1_tdlat_3(sK4)
    | ~ v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_53,plain,
    ( v4_tex_2(sK3,sK2) != iProver_top
    | v1_tdlat_3(sK4) = iProver_top
    | v1_tdlat_3(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( ~ v4_tex_2(sK3,sK2)
    | m1_pre_topc(sK4,sK2)
    | ~ v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_54,plain,
    ( v4_tex_2(sK3,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) = iProver_top
    | v1_tdlat_3(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( ~ v4_tex_2(sK3,sK2)
    | m1_pre_topc(sK3,sK4)
    | ~ v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_55,plain,
    ( v4_tex_2(sK3,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) = iProver_top
    | v1_tdlat_3(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( ~ v4_tex_2(sK3,sK2)
    | ~ v1_tdlat_3(sK3)
    | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_56,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | v4_tex_2(sK3,sK2) != iProver_top
    | v1_tdlat_3(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3237,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_3253,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3237])).

cnf(c_3235,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3270,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_3235])).

cnf(c_29,plain,
    ( v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v3_tex_2(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_242,plain,
    ( ~ v3_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | v4_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29,c_16])).

cnf(c_243,plain,
    ( v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v3_tex_2(u1_struct_0(X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_242])).

cnf(c_4352,plain,
    ( v4_tex_2(X0,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ v3_tex_2(u1_struct_0(X0),sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_243])).

cnf(c_4361,plain,
    ( v4_tex_2(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4352])).

cnf(c_4363,plain,
    ( v4_tex_2(sK3,sK2) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v3_tex_2(u1_struct_0(sK3),sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4361])).

cnf(c_4654,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK3,sK4)
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_4655,plain,
    ( m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4654])).

cnf(c_3236,plain,
    ( X0 != X1
    | X2 != X1
    | X0 = X2 ),
    theory(equality)).

cnf(c_4509,plain,
    ( u1_struct_0(sK4) != X0
    | u1_struct_0(sK3) != X0
    | u1_struct_0(sK3) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3236])).

cnf(c_4821,plain,
    ( u1_struct_0(sK4) != u1_struct_0(X0)
    | u1_struct_0(sK3) != u1_struct_0(X0)
    | u1_struct_0(sK3) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_4509])).

cnf(c_4822,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK3)
    | u1_struct_0(sK3) = u1_struct_0(sK4)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4821])).

cnf(c_5195,plain,
    ( v2_tex_2(u1_struct_0(X0),sK2) = iProver_top
    | v3_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5194])).

cnf(c_5197,plain,
    ( v2_tex_2(u1_struct_0(sK3),sK2) = iProver_top
    | v3_tex_2(u1_struct_0(sK3),sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5195])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_265,plain,
    ( ~ v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_16])).

cnf(c_266,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_tex_2(u1_struct_0(X0),X1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_265])).

cnf(c_5063,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | ~ v2_tex_2(u1_struct_0(sK3),X0)
    | v1_tdlat_3(sK3)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_5874,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ v2_tex_2(u1_struct_0(sK3),sK2)
    | v1_tdlat_3(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_5063])).

cnf(c_5875,plain,
    ( m1_pre_topc(sK3,sK2) != iProver_top
    | v2_tex_2(u1_struct_0(sK3),sK2) != iProver_top
    | v1_tdlat_3(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5874])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ v3_tex_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_5912,plain,
    ( ~ r1_tarski(u1_struct_0(X0),X1)
    | ~ v2_tex_2(X1,X2)
    | ~ v3_tex_2(u1_struct_0(X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | X1 = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_6588,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ v2_tex_2(u1_struct_0(X1),sK2)
    | ~ v3_tex_2(u1_struct_0(X0),sK2)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(X1) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_5912])).

cnf(c_8080,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK4))
    | ~ v2_tex_2(u1_struct_0(sK4),sK2)
    | ~ v3_tex_2(u1_struct_0(X0),sK2)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | u1_struct_0(sK4) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_6588])).

cnf(c_8081,plain,
    ( u1_struct_0(sK4) = u1_struct_0(X0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK4)) != iProver_top
    | v2_tex_2(u1_struct_0(sK4),sK2) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8080])).

cnf(c_8083,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK3)
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK4)) != iProver_top
    | v2_tex_2(u1_struct_0(sK4),sK2) != iProver_top
    | v3_tex_2(u1_struct_0(sK3),sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8081])).

cnf(c_7468,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | v2_tex_2(u1_struct_0(X0),sK2)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_273])).

cnf(c_8878,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_tex_2(u1_struct_0(sK4),sK2)
    | ~ v1_tdlat_3(sK4)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_7468])).

cnf(c_8882,plain,
    ( m1_pre_topc(sK4,sK2) != iProver_top
    | v2_tex_2(u1_struct_0(sK4),sK2) = iProver_top
    | v1_tdlat_3(sK4) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8878])).

cnf(c_10020,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_6255])).

cnf(c_10025,plain,
    ( m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10020])).

cnf(c_30,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | u1_struct_0(X2) != u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_10272,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK3,X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | u1_struct_0(sK3) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_13031,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | u1_struct_0(sK3) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_10272])).

cnf(c_13603,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | u1_struct_0(sK3) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_13031])).

cnf(c_13604,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | u1_struct_0(sK3) != u1_struct_0(sK4)
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13603])).

cnf(c_17511,plain,
    ( v3_tex_2(u1_struct_0(sK3),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16634,c_43,c_45,c_46,c_47,c_52,c_53,c_54,c_55,c_56,c_3253,c_3270,c_4363,c_4655,c_4822,c_5197,c_5875,c_6021,c_8083,c_8882,c_10025,c_13604])).

cnf(c_17517,plain,
    ( u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK3)))) = sK0(sK2,u1_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_10482,c_17511])).

cnf(c_27,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_683,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_41])).

cnf(c_684,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_683])).

cnf(c_688,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_684,c_40])).

cnf(c_689,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_688])).

cnf(c_4190,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_689])).

cnf(c_17622,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(sK3))),X0) = iProver_top
    | m1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(sK3))),sK2) != iProver_top
    | r1_tarski(sK0(sK2,u1_struct_0(sK3)),u1_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17517,c_4190])).

cnf(c_20,plain,
    ( m1_pre_topc(sK1(X0,X1),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v1_xboole_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_659,plain,
    ( m1_pre_topc(sK1(X0,X1),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v1_xboole_0(X1)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_41])).

cnf(c_660,plain,
    ( m1_pre_topc(sK1(sK2,X0),sK2)
    | ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_659])).

cnf(c_664,plain,
    ( v1_xboole_0(X0)
    | m1_pre_topc(sK1(sK2,X0),sK2)
    | ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_660,c_42,c_40])).

cnf(c_665,plain,
    ( m1_pre_topc(sK1(sK2,X0),sK2)
    | ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_664])).

cnf(c_6353,plain,
    ( m1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(X0))),sK2)
    | ~ v2_tex_2(sK0(sK2,u1_struct_0(X0)),sK2)
    | ~ m1_subset_1(sK0(sK2,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK0(sK2,u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_665])).

cnf(c_6354,plain,
    ( m1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(X0))),sK2) = iProver_top
    | v2_tex_2(sK0(sK2,u1_struct_0(X0)),sK2) != iProver_top
    | m1_subset_1(sK0(sK2,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK0(sK2,u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6353])).

cnf(c_6356,plain,
    ( m1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(sK3))),sK2) = iProver_top
    | v2_tex_2(sK0(sK2,u1_struct_0(sK3)),sK2) != iProver_top
    | m1_subset_1(sK0(sK2,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK0(sK2,u1_struct_0(sK3))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6354])).

cnf(c_17814,plain,
    ( m1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(sK3))),X0) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(sK0(sK2,u1_struct_0(sK3)),u1_struct_0(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17622,c_43,c_45,c_46,c_47,c_52,c_53,c_54,c_55,c_56,c_586,c_1428,c_3253,c_3270,c_4363,c_4532,c_4536,c_4627,c_4655,c_4758,c_4822,c_5197,c_5875,c_6021,c_6356,c_7781,c_8083,c_8882,c_9116,c_10025,c_13604])).

cnf(c_17815,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(sK3))),X0) = iProver_top
    | r1_tarski(sK0(sK2,u1_struct_0(sK3)),u1_struct_0(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_17814])).

cnf(c_36,negated_conjecture,
    ( v4_tex_2(sK3,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(sK3,X0)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_4203,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | v4_tex_2(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_17825,plain,
    ( g1_pre_topc(u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK3)))),u1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(sK3))))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | v4_tex_2(sK3,sK2) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK3,sK1(sK2,sK0(sK2,u1_struct_0(sK3)))) != iProver_top
    | r1_tarski(sK0(sK2,u1_struct_0(sK3)),u1_struct_0(sK2)) != iProver_top
    | v1_tdlat_3(sK1(sK2,sK0(sK2,u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_17815,c_4203])).

cnf(c_4191,plain,
    ( m1_pre_topc(sK1(sK2,X0),sK2) = iProver_top
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_6292,plain,
    ( m1_pre_topc(sK1(sK2,sK0(sK2,X0)),sK2) = iProver_top
    | v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(sK0(sK2,X0),sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK0(sK2,X0)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4221,c_4191])).

cnf(c_6550,plain,
    ( v1_xboole_0(sK0(sK2,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_pre_topc(sK1(sK2,sK0(sK2,X0)),sK2) = iProver_top
    | v2_tex_2(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6292,c_45,c_4938])).

cnf(c_6551,plain,
    ( m1_pre_topc(sK1(sK2,sK0(sK2,X0)),sK2) = iProver_top
    | v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK0(sK2,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6550])).

cnf(c_6556,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK0(sK2,X0)) = iProver_top
    | l1_pre_topc(sK1(sK2,sK0(sK2,X0))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6551,c_4216])).

cnf(c_10831,plain,
    ( l1_pre_topc(sK1(sK2,sK0(sK2,X0))) = iProver_top
    | v1_xboole_0(sK0(sK2,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6556,c_45])).

cnf(c_10832,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK0(sK2,X0)) = iProver_top
    | l1_pre_topc(sK1(sK2,sK0(sK2,X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_10831])).

cnf(c_10838,plain,
    ( g1_pre_topc(u1_struct_0(sK1(sK2,sK0(sK2,X0))),u1_pre_topc(sK1(sK2,sK0(sK2,X0)))) = sK1(sK2,sK0(sK2,X0))
    | v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK0(sK2,X0)) = iProver_top
    | v1_pre_topc(sK1(sK2,sK0(sK2,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10832,c_4225])).

cnf(c_22,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(sK1(X1,X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_755,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(sK1(X1,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_41])).

cnf(c_756,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(sK2)
    | v1_pre_topc(sK1(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_755])).

cnf(c_760,plain,
    ( v1_xboole_0(X0)
    | ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_pre_topc(sK1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_756,c_42,c_40])).

cnf(c_761,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | v1_pre_topc(sK1(sK2,X0)) ),
    inference(renaming,[status(thm)],[c_760])).

cnf(c_4187,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_pre_topc(sK1(sK2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_761])).

cnf(c_6293,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(sK0(sK2,X0),sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK0(sK2,X0)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_pre_topc(sK1(sK2,sK0(sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4221,c_4187])).

cnf(c_6443,plain,
    ( v1_xboole_0(sK0(sK2,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(X0,sK2) != iProver_top
    | v1_pre_topc(sK1(sK2,sK0(sK2,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6293,c_45,c_4938])).

cnf(c_6444,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK0(sK2,X0)) = iProver_top
    | v1_pre_topc(sK1(sK2,sK0(sK2,X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_6443])).

cnf(c_12091,plain,
    ( v1_xboole_0(sK0(sK2,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(X0,sK2) != iProver_top
    | g1_pre_topc(u1_struct_0(sK1(sK2,sK0(sK2,X0))),u1_pre_topc(sK1(sK2,sK0(sK2,X0)))) = sK1(sK2,sK0(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10838,c_6444])).

cnf(c_12092,plain,
    ( g1_pre_topc(u1_struct_0(sK1(sK2,sK0(sK2,X0))),u1_pre_topc(sK1(sK2,sK0(sK2,X0)))) = sK1(sK2,sK0(sK2,X0))
    | v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(sK0(sK2,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_12091])).

cnf(c_12099,plain,
    ( g1_pre_topc(u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(X0)))),u1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(X0))))) = sK1(sK2,sK0(sK2,u1_struct_0(X0)))
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK2) = iProver_top
    | v1_xboole_0(sK0(sK2,u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4212,c_12092])).

cnf(c_12560,plain,
    ( v1_xboole_0(sK0(sK2,u1_struct_0(X0))) = iProver_top
    | v3_tex_2(u1_struct_0(X0),sK2) = iProver_top
    | v2_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | g1_pre_topc(u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(X0)))),u1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(X0))))) = sK1(sK2,sK0(sK2,u1_struct_0(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12099,c_45])).

cnf(c_12561,plain,
    ( g1_pre_topc(u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(X0)))),u1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(X0))))) = sK1(sK2,sK0(sK2,u1_struct_0(X0)))
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK2) = iProver_top
    | v1_xboole_0(sK0(sK2,u1_struct_0(X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_12560])).

cnf(c_12566,plain,
    ( g1_pre_topc(u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK1(sK2,u1_struct_0(sK3)))))),u1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(sK1(sK2,u1_struct_0(sK3))))))) = sK1(sK2,sK0(sK2,u1_struct_0(sK1(sK2,u1_struct_0(sK3)))))
    | m1_pre_topc(sK1(sK2,u1_struct_0(sK3)),sK2) != iProver_top
    | v2_tex_2(u1_struct_0(sK1(sK2,u1_struct_0(sK3))),sK2) != iProver_top
    | v3_tex_2(u1_struct_0(sK1(sK2,u1_struct_0(sK3))),sK2) = iProver_top
    | v1_xboole_0(sK0(sK2,u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7365,c_12561])).

cnf(c_12567,plain,
    ( g1_pre_topc(u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK3)))),u1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(sK3))))) = sK1(sK2,sK0(sK2,u1_struct_0(sK3)))
    | m1_pre_topc(sK1(sK2,u1_struct_0(sK3)),sK2) != iProver_top
    | v2_tex_2(u1_struct_0(sK3),sK2) != iProver_top
    | v3_tex_2(u1_struct_0(sK3),sK2) = iProver_top
    | v1_xboole_0(sK0(sK2,u1_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12566,c_7365])).

cnf(c_12107,plain,
    ( g1_pre_topc(u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK3)))),u1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(sK3))))) = sK1(sK2,sK0(sK2,u1_struct_0(sK3)))
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_tex_2(u1_struct_0(sK3),sK2) != iProver_top
    | v3_tex_2(u1_struct_0(sK3),sK2) = iProver_top
    | v1_xboole_0(sK0(sK2,u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12099])).

cnf(c_12775,plain,
    ( v3_tex_2(u1_struct_0(sK3),sK2) = iProver_top
    | g1_pre_topc(u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK3)))),u1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(sK3))))) = sK1(sK2,sK0(sK2,u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12567,c_43,c_45,c_46,c_47,c_586,c_1428,c_4536,c_4627,c_4758,c_6021,c_9116,c_12107])).

cnf(c_12776,plain,
    ( g1_pre_topc(u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK3)))),u1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(sK3))))) = sK1(sK2,sK0(sK2,u1_struct_0(sK3)))
    | v3_tex_2(u1_struct_0(sK3),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_12775])).

cnf(c_17516,plain,
    ( g1_pre_topc(u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK3)))),u1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(sK3))))) = sK1(sK2,sK0(sK2,u1_struct_0(sK3))) ),
    inference(superposition,[status(thm)],[c_12776,c_17511])).

cnf(c_17518,plain,
    ( g1_pre_topc(sK0(sK2,u1_struct_0(sK3)),u1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(sK3))))) = sK1(sK2,sK0(sK2,u1_struct_0(sK3))) ),
    inference(demodulation,[status(thm)],[c_17516,c_17517])).

cnf(c_17832,plain,
    ( sK1(sK2,sK0(sK2,u1_struct_0(sK3))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | v4_tex_2(sK3,sK2) = iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | m1_pre_topc(sK3,sK1(sK2,sK0(sK2,u1_struct_0(sK3)))) != iProver_top
    | r1_tarski(sK0(sK2,u1_struct_0(sK3)),u1_struct_0(sK2)) != iProver_top
    | v1_tdlat_3(sK1(sK2,sK0(sK2,u1_struct_0(sK3)))) != iProver_top
    | v2_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK3)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17825,c_17517,c_17518])).

cnf(c_4353,plain,
    ( ~ v4_tex_2(X0,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | v3_tex_2(u1_struct_0(X0),sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_250])).

cnf(c_4357,plain,
    ( v4_tex_2(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK2) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4353])).

cnf(c_4359,plain,
    ( v4_tex_2(sK3,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v3_tex_2(u1_struct_0(sK3),sK2) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4357])).

cnf(c_3247,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4649,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
    | u1_struct_0(X2) != X0
    | u1_struct_0(X3) != X1 ),
    inference(instantiation,[status(thm)],[c_3247])).

cnf(c_6399,plain,
    ( ~ r1_tarski(u1_struct_0(X0),sK0(sK2,u1_struct_0(X0)))
    | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | u1_struct_0(X2) != sK0(sK2,u1_struct_0(X0))
    | u1_struct_0(X1) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_4649])).

cnf(c_11178,plain,
    ( ~ r1_tarski(u1_struct_0(X0),sK0(sK2,u1_struct_0(X0)))
    | r1_tarski(u1_struct_0(X1),u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(X0)))))
    | u1_struct_0(X1) != u1_struct_0(X0)
    | u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(X0)))) != sK0(sK2,u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_6399])).

cnf(c_11179,plain,
    ( u1_struct_0(X0) != u1_struct_0(X1)
    | u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(X1)))) != sK0(sK2,u1_struct_0(X1))
    | r1_tarski(u1_struct_0(X1),sK0(sK2,u1_struct_0(X1))) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(X1))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11178])).

cnf(c_11181,plain,
    ( u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK3)))) != sK0(sK2,u1_struct_0(sK3))
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | r1_tarski(u1_struct_0(sK3),sK0(sK2,u1_struct_0(sK3))) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK3))))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_11179])).

cnf(c_13999,plain,
    ( m1_pre_topc(X0,sK1(sK2,sK0(sK2,u1_struct_0(X1))))
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(X1))),sK2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(X1))))) ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_14000,plain,
    ( m1_pre_topc(X0,sK1(sK2,sK0(sK2,u1_struct_0(X1)))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(X1))),sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(X1))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13999])).

cnf(c_14002,plain,
    ( m1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(sK3))),sK2) != iProver_top
    | m1_pre_topc(sK3,sK1(sK2,sK0(sK2,u1_struct_0(sK3)))) = iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK3))))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14000])).

cnf(c_5723,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK1(sK2,u1_struct_0(X0)),sK2) = iProver_top
    | v2_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4212,c_4191])).

cnf(c_6065,plain,
    ( v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | v2_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | m1_pre_topc(sK1(sK2,u1_struct_0(X0)),sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5723,c_45])).

cnf(c_6066,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK1(sK2,u1_struct_0(X0)),sK2) = iProver_top
    | v2_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_6065])).

cnf(c_6072,plain,
    ( g1_pre_topc(u1_struct_0(sK1(sK2,u1_struct_0(X0))),u1_pre_topc(sK1(sK2,u1_struct_0(X0)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | v4_tex_2(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK3,sK1(sK2,u1_struct_0(X0))) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | v1_tdlat_3(sK1(sK2,u1_struct_0(X0))) != iProver_top
    | v2_struct_0(sK1(sK2,u1_struct_0(X0))) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6066,c_4203])).

cnf(c_21,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v1_tdlat_3(sK1(X1,X0))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_779,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tdlat_3(sK1(X1,X0))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_41])).

cnf(c_780,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_tdlat_3(sK1(sK2,X0))
    | v2_struct_0(sK2)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_779])).

cnf(c_784,plain,
    ( v1_xboole_0(X0)
    | ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_tdlat_3(sK1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_780,c_42,c_40])).

cnf(c_785,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_tdlat_3(sK1(sK2,X0))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_784])).

cnf(c_4186,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_tdlat_3(sK1(sK2,X0)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_5725,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | v1_tdlat_3(sK1(sK2,u1_struct_0(X0))) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4212,c_4186])).

cnf(c_23,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0))
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_731,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0))
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_41])).

cnf(c_732,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_struct_0(sK1(sK2,X0))
    | v2_struct_0(sK2)
    | v1_xboole_0(X0)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_731])).

cnf(c_736,plain,
    ( v1_xboole_0(X0)
    | ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_struct_0(sK1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_732,c_42,c_40])).

cnf(c_737,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_struct_0(sK1(sK2,X0))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_736])).

cnf(c_4188,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_struct_0(sK1(sK2,X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_5726,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | v2_struct_0(sK1(sK2,u1_struct_0(X0))) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4212,c_4188])).

cnf(c_6322,plain,
    ( g1_pre_topc(u1_struct_0(sK1(sK2,u1_struct_0(X0))),u1_pre_topc(sK1(sK2,u1_struct_0(X0)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | v4_tex_2(sK3,sK2) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK3,sK1(sK2,u1_struct_0(X0))) != iProver_top
    | v2_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6072,c_45,c_5725,c_5726])).

cnf(c_17613,plain,
    ( g1_pre_topc(u1_struct_0(sK1(sK2,u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK3)))))),u1_pre_topc(sK1(sK2,u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK3))))))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | v4_tex_2(sK3,sK2) = iProver_top
    | m1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(sK3))),sK2) != iProver_top
    | m1_pre_topc(sK3,sK1(sK2,sK0(sK2,u1_struct_0(sK3)))) != iProver_top
    | v2_tex_2(u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK3)))),sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1(sK2,sK0(sK2,u1_struct_0(sK3))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_17517,c_6322])).

cnf(c_17661,plain,
    ( sK1(sK2,sK0(sK2,u1_struct_0(sK3))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | v4_tex_2(sK3,sK2) = iProver_top
    | m1_pre_topc(sK1(sK2,sK0(sK2,u1_struct_0(sK3))),sK2) != iProver_top
    | m1_pre_topc(sK3,sK1(sK2,sK0(sK2,u1_struct_0(sK3)))) != iProver_top
    | v2_tex_2(sK0(sK2,u1_struct_0(sK3)),sK2) != iProver_top
    | v1_xboole_0(sK0(sK2,u1_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17613,c_17517,c_17518])).

cnf(c_19646,plain,
    ( sK1(sK2,sK0(sK2,u1_struct_0(sK3))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17832,c_43,c_45,c_46,c_47,c_52,c_53,c_54,c_55,c_56,c_586,c_1428,c_3253,c_3270,c_4359,c_4363,c_4532,c_4536,c_4627,c_4655,c_4758,c_4822,c_5197,c_5875,c_6021,c_6356,c_7781,c_8083,c_8882,c_9116,c_10025,c_10482,c_11181,c_13604,c_14002,c_17661])).

cnf(c_19666,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = sK0(sK2,u1_struct_0(sK3)) ),
    inference(demodulation,[status(thm)],[c_19646,c_17517])).

cnf(c_21573,plain,
    ( sK0(sK2,u1_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(demodulation,[status(thm)],[c_21571,c_19666])).

cnf(c_2,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4527,plain,
    ( ~ v2_tex_2(u1_struct_0(X0),sK2)
    | v3_tex_2(u1_struct_0(X0),sK2)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | sK0(sK2,u1_struct_0(X0)) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4538,plain,
    ( sK0(sK2,u1_struct_0(X0)) != u1_struct_0(X0)
    | v2_tex_2(u1_struct_0(X0),sK2) != iProver_top
    | v3_tex_2(u1_struct_0(X0),sK2) = iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4527])).

cnf(c_4540,plain,
    ( sK0(sK2,u1_struct_0(sK3)) != u1_struct_0(sK3)
    | v2_tex_2(u1_struct_0(sK3),sK2) != iProver_top
    | v3_tex_2(u1_struct_0(sK3),sK2) = iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4538])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21573,c_17511,c_6021,c_4627,c_4540,c_1428,c_47,c_46,c_45,c_43])).


%------------------------------------------------------------------------------
