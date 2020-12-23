%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:10 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :  291 (2400 expanded)
%              Number of clauses        :  138 ( 544 expanded)
%              Number of leaves         :   35 ( 566 expanded)
%              Depth                    :   25
%              Number of atoms          : 1182 (13236 expanded)
%              Number of equality atoms :  229 ( 913 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f31,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f73,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f74,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f73])).

fof(f88,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f74])).

fof(f89,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f88])).

fof(f91,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( v1_subset_1(sK4,u1_struct_0(X0))
          | ~ v3_tex_2(sK4,X0) )
        & ( ~ v1_subset_1(sK4,u1_struct_0(X0))
          | v3_tex_2(sK4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK3))
            | ~ v3_tex_2(X1,sK3) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK3))
            | v3_tex_2(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3)
      & v1_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f92,plain,
    ( ( v1_subset_1(sK4,u1_struct_0(sK3))
      | ~ v3_tex_2(sK4,sK3) )
    & ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
      | v3_tex_2(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v1_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f89,f91,f90])).

fof(f140,plain,(
    v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f92])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
      <=> k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f79,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | k9_setfam_1(u1_struct_0(X0)) != u1_pre_topc(X0) )
        & ( k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0)
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f120,plain,(
    ! [X0] :
      ( k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f141,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f92])).

fof(f142,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f92])).

fof(f12,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f104,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f175,plain,(
    m1_subset_1(sK4,k9_setfam_1(u1_struct_0(sK3))) ),
    inference(definition_unfolding,[],[f142,f104])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f82,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK1(X0,X1)) = X1
        & m1_pre_topc(sK1(X0,X1),X0)
        & v1_pre_topc(sK1(X0,X1))
        & ~ v2_struct_0(sK1(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK1(X0,X1)) = X1
            & m1_pre_topc(sK1(X0,X1),X0)
            & v1_pre_topc(sK1(X0,X1))
            & ~ v2_struct_0(sK1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f62,f82])).

fof(f129,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f166,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK1(X0,X1),X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f129,f104])).

fof(f138,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f92])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f154,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f107,f104])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f118,plain,(
    ! [X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f77])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f113,f104])).

fof(f178,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f158])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f116,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f159,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f116,f104])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f117,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f130,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f165,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f130,f104])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f149,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k9_setfam_1(X0)) ) ),
    inference(definition_unfolding,[],[f99,f104])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( v1_xboole_0(X1)
           => v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f150,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k9_setfam_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f101,f104])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & v1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k9_setfam_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f126,f104])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f102,f104])).

fof(f139,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f92])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v4_pre_topc(sK0(X0),X0)
        & v3_pre_topc(sK0(X0),X0)
        & ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0] :
      ( ( v4_pre_topc(sK0(X0),X0)
        & v3_pre_topc(sK0(X0),X0)
        & ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f75])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f109,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f155,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f109,f104])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f152,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k9_setfam_1(X1)) ) ),
    inference(definition_unfolding,[],[f103,f104])).

fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f35])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f97,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f147,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f97,f95,f104])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f125,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f162,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k9_setfam_1(X0)) ) ),
    inference(definition_unfolding,[],[f125,f104])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f135,f104])).

fof(f143,plain,
    ( ~ v1_subset_1(sK4,u1_struct_0(sK3))
    | v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f92])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f123,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f160,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f123,f104])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f134,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f171,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f134,f104])).

fof(f30,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f137,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f174,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f137,f104])).

fof(f124,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f163,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(X0)) ) ),
    inference(definition_unfolding,[],[f124,f104])).

fof(f179,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k9_setfam_1(X1)) ) ),
    inference(equality_resolution,[],[f163])).

fof(f144,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    | ~ v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f92])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f98,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f100,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f145,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f100,f95])).

fof(f148,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f98,f145,f104])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f96,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f146,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f96,f145])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f63])).

fof(f84,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f64])).

fof(f85,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f84])).

fof(f86,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK2(X0),X0)
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f85,f86])).

fof(f131,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f170,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f131,f104])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f136,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f173,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f136,f104])).

fof(f122,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f161,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f122,f104])).

cnf(c_46,negated_conjecture,
    ( v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_6001,plain,
    ( v1_tdlat_3(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_25,plain,
    ( ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_6008,plain,
    ( k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0)
    | v1_tdlat_3(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7195,plain,
    ( k9_setfam_1(u1_struct_0(sK3)) = u1_pre_topc(sK3)
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6001,c_6008])).

cnf(c_45,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_101,plain,
    ( ~ v1_tdlat_3(sK3)
    | ~ l1_pre_topc(sK3)
    | k9_setfam_1(u1_struct_0(sK3)) = u1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_7339,plain,
    ( k9_setfam_1(u1_struct_0(sK3)) = u1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7195,c_46,c_45,c_101])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK4,k9_setfam_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f175])).

cnf(c_6003,plain,
    ( m1_subset_1(sK4,k9_setfam_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_7344,plain,
    ( m1_subset_1(sK4,u1_pre_topc(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7339,c_6003])).

cnf(c_32,plain,
    ( m1_pre_topc(sK1(X0,X1),X0)
    | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f166])).

cnf(c_6006,plain,
    ( m1_pre_topc(sK1(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_8588,plain,
    ( m1_pre_topc(sK1(sK3,X0),sK3) = iProver_top
    | m1_subset_1(X0,u1_pre_topc(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7339,c_6006])).

cnf(c_48,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_49,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_52,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_9186,plain,
    ( m1_pre_topc(sK1(sK3,X0),sK3) = iProver_top
    | m1_subset_1(X0,u1_pre_topc(sK3)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8588,c_49,c_52])).

cnf(c_12,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f154])).

cnf(c_23,plain,
    ( v1_borsuk_1(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_19,plain,
    ( ~ v1_borsuk_1(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k9_setfam_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f178])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k9_setfam_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f159])).

cnf(c_292,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_borsuk_1(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_20])).

cnf(c_293,plain,
    ( ~ v1_borsuk_1(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_292])).

cnf(c_711,plain,
    ( v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_23,c_293])).

cnf(c_21,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_727,plain,
    ( v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_711,c_21])).

cnf(c_767,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X3)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | X1 != X3
    | k2_pre_topc(X3,X2) = X2
    | u1_struct_0(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_727])).

cnf(c_768,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k9_setfam_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,u1_struct_0(X0)) = u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_767])).

cnf(c_772,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,u1_struct_0(X0)) = u1_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_768,c_20])).

cnf(c_5998,plain,
    ( k2_pre_topc(X0,u1_struct_0(X1)) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | v1_tdlat_3(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_772])).

cnf(c_13719,plain,
    ( k2_pre_topc(sK3,u1_struct_0(sK1(sK3,X0))) = u1_struct_0(sK1(sK3,X0))
    | m1_subset_1(X0,u1_pre_topc(sK3)) != iProver_top
    | v1_tdlat_3(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9186,c_5998])).

cnf(c_51,plain,
    ( v1_tdlat_3(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_14080,plain,
    ( m1_subset_1(X0,u1_pre_topc(sK3)) != iProver_top
    | k2_pre_topc(sK3,u1_struct_0(sK1(sK3,X0))) = u1_struct_0(sK1(sK3,X0))
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13719,c_49,c_51,c_52])).

cnf(c_14081,plain,
    ( k2_pre_topc(sK3,u1_struct_0(sK1(sK3,X0))) = u1_struct_0(sK1(sK3,X0))
    | m1_subset_1(X0,u1_pre_topc(sK3)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_14080])).

cnf(c_14090,plain,
    ( k2_pre_topc(sK3,u1_struct_0(sK1(sK3,sK4))) = u1_struct_0(sK1(sK3,sK4))
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7344,c_14081])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(sK1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f165])).

cnf(c_6007,plain,
    ( u1_struct_0(sK1(X0,X1)) = X1
    | m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_7805,plain,
    ( u1_struct_0(sK1(sK3,X0)) = X0
    | m1_subset_1(X0,u1_pre_topc(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7339,c_6007])).

cnf(c_8061,plain,
    ( u1_struct_0(sK1(sK3,X0)) = X0
    | m1_subset_1(X0,u1_pre_topc(sK3)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7805,c_49,c_52])).

cnf(c_8071,plain,
    ( u1_struct_0(sK1(sK3,sK4)) = sK4
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7344,c_8061])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f149])).

cnf(c_6013,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k9_setfam_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6591,plain,
    ( k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_6003,c_6013])).

cnf(c_6,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(X1))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_30,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(X1))
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f164])).

cnf(c_7,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_277,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30,c_7])).

cnf(c_278,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(X1))
    | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
    inference(renaming,[status(thm)],[c_277])).

cnf(c_1045,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(X1))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
    inference(resolution,[status(thm)],[c_6,c_278])).

cnf(c_5995,plain,
    ( m1_subset_1(X0,k9_setfam_1(X1)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k3_subset_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1045])).

cnf(c_12280,plain,
    ( m1_subset_1(X0,u1_pre_topc(sK3)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k3_subset_1(u1_struct_0(sK3),X0)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7339,c_5995])).

cnf(c_47,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_15,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_123,plain,
    ( v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(sK0(sK3)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_16,plain,
    ( m1_subset_1(sK0(X0),k9_setfam_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f155])).

cnf(c_1304,plain,
    ( m1_subset_1(sK0(X0),k9_setfam_1(u1_struct_0(X0)))
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_21,c_16])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_615,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_616,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_615])).

cnf(c_630,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(X1))
    | v1_xboole_0(X2)
    | X2 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_616])).

cnf(c_631,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(k1_xboole_0))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_630])).

cnf(c_3055,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(X1)
    | sK0(X0) != X1
    | k9_setfam_1(u1_struct_0(X0)) != k9_setfam_1(k1_xboole_0) ),
    inference(resolution_lifted,[status(thm)],[c_1304,c_631])).

cnf(c_3056,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(sK0(X0))
    | k9_setfam_1(u1_struct_0(X0)) != k9_setfam_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_3055])).

cnf(c_3058,plain,
    ( ~ v1_tdlat_3(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK0(sK3))
    | k9_setfam_1(u1_struct_0(sK3)) != k9_setfam_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3056])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_6353,plain,
    ( m1_subset_1(k1_xboole_0,k9_setfam_1(u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6358,plain,
    ( m1_subset_1(k1_xboole_0,k9_setfam_1(u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6353])).

cnf(c_6360,plain,
    ( m1_subset_1(k1_xboole_0,k9_setfam_1(u1_struct_0(sK3))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6358])).

cnf(c_28,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f162])).

cnf(c_1031,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(X1))
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_28,c_7])).

cnf(c_6622,plain,
    ( ~ m1_subset_1(k1_xboole_0,k9_setfam_1(X0))
    | ~ v1_xboole_0(X0)
    | X0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_6949,plain,
    ( ~ m1_subset_1(k1_xboole_0,k9_setfam_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6622])).

cnf(c_6950,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k9_setfam_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6949])).

cnf(c_5326,plain,
    ( X0 != X1
    | k9_setfam_1(X0) = k9_setfam_1(X1) ),
    theory(equality)).

cnf(c_7496,plain,
    ( u1_struct_0(sK3) != X0
    | k9_setfam_1(u1_struct_0(sK3)) = k9_setfam_1(X0) ),
    inference(instantiation,[status(thm)],[c_5326])).

cnf(c_11227,plain,
    ( u1_struct_0(sK3) != k1_xboole_0
    | k9_setfam_1(u1_struct_0(sK3)) = k9_setfam_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7496])).

cnf(c_12832,plain,
    ( v1_xboole_0(k3_subset_1(u1_struct_0(sK3),X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | m1_subset_1(X0,u1_pre_topc(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12280,c_48,c_47,c_46,c_45,c_123,c_3058,c_6360,c_6950,c_11227])).

cnf(c_12833,plain,
    ( m1_subset_1(X0,u1_pre_topc(sK3)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k3_subset_1(u1_struct_0(sK3),X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12832])).

cnf(c_12843,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK4),u1_pre_topc(sK3)) != iProver_top
    | v1_xboole_0(k3_subset_1(u1_struct_0(sK3),sK4)) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6591,c_12833])).

cnf(c_39,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f172])).

cnf(c_1338,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_39])).

cnf(c_1339,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_1338])).

cnf(c_43,negated_conjecture,
    ( v3_tex_2(sK4,sK3)
    | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_373,plain,
    ( v3_tex_2(sK4,sK3)
    | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(prop_impl,[status(thm)],[c_43])).

cnf(c_1080,plain,
    ( v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(X0,k9_setfam_1(X1))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_373])).

cnf(c_1081,plain,
    ( v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(sK4,k9_setfam_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1080])).

cnf(c_1083,plain,
    ( v3_tex_2(sK4,sK3)
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_xboole_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1081,c_44])).

cnf(c_1757,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_xboole_0(sK4)
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1339,c_1083])).

cnf(c_1758,plain,
    ( ~ m1_subset_1(sK4,k9_setfam_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1757])).

cnf(c_1760,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_xboole_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1758,c_48,c_46,c_45,c_44])).

cnf(c_5981,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1760])).

cnf(c_6015,plain,
    ( m1_subset_1(k1_xboole_0,k9_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5996,plain,
    ( X0 = X1
    | m1_subset_1(X1,k9_setfam_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1031])).

cnf(c_8850,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6015,c_5996])).

cnf(c_9008,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5981,c_8850])).

cnf(c_12867,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12843,c_48,c_47,c_46,c_45,c_123,c_3058,c_9008,c_11227])).

cnf(c_12873,plain,
    ( u1_struct_0(sK1(sK3,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_8071,c_12867])).

cnf(c_14106,plain,
    ( k2_pre_topc(sK3,sK4) = sK4
    | v1_xboole_0(sK4) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14090,c_12873])).

cnf(c_14145,plain,
    ( k2_pre_topc(sK3,sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14106,c_48,c_47,c_46,c_45,c_123,c_3058,c_9008,c_11227])).

cnf(c_26,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f160])).

cnf(c_38,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f171])).

cnf(c_41,plain,
    ( v3_tex_2(X0,X1)
    | ~ v2_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f174])).

cnf(c_675,plain,
    ( v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_38,c_41])).

cnf(c_693,plain,
    ( v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_675,c_21])).

cnf(c_1192,plain,
    ( v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_26,c_693])).

cnf(c_29,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f179])).

cnf(c_42,negated_conjecture,
    ( ~ v3_tex_2(sK4,sK3)
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_375,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(prop_impl,[status(thm)],[c_42])).

cnf(c_1125,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(X0,k9_setfam_1(X0))
    | u1_struct_0(sK3) != X0
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_375])).

cnf(c_1126,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(u1_struct_0(sK3),k9_setfam_1(u1_struct_0(sK3)))
    | sK4 != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1125])).

cnf(c_1712,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ m1_subset_1(u1_struct_0(sK3),k9_setfam_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != u1_struct_0(X1)
    | u1_struct_0(sK3) != sK4
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1192,c_1126])).

cnf(c_1713,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k9_setfam_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k9_setfam_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
    | u1_struct_0(sK3) != sK4 ),
    inference(unflattening,[status(thm)],[c_1712])).

cnf(c_1715,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k9_setfam_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
    | u1_struct_0(sK3) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1713,c_48,c_46,c_45,c_44])).

cnf(c_5984,plain,
    ( k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
    | u1_struct_0(sK3) != sK4
    | m1_subset_1(u1_struct_0(sK3),k9_setfam_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1715])).

cnf(c_4,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_6014,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k9_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f146])).

cnf(c_6034,plain,
    ( m1_subset_1(X0,k9_setfam_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6014,c_2])).

cnf(c_6135,plain,
    ( k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
    | u1_struct_0(sK3) != sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5984,c_6034])).

cnf(c_14148,plain,
    ( u1_struct_0(sK3) != sK4 ),
    inference(demodulation,[status(thm)],[c_14145,c_6135])).

cnf(c_37,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f170])).

cnf(c_40,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f173])).

cnf(c_922,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_37,c_40])).

cnf(c_940,plain,
    ( ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_922,c_21])).

cnf(c_27,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f161])).

cnf(c_1169,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_940,c_27])).

cnf(c_1066,plain,
    ( v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(X0,k9_setfam_1(X1))
    | X1 = X0
    | u1_struct_0(sK3) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_373])).

cnf(c_1067,plain,
    ( v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(sK4,k9_setfam_1(u1_struct_0(sK3)))
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_1066])).

cnf(c_1069,plain,
    ( v3_tex_2(sK4,sK3)
    | u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1067,c_44])).

cnf(c_1787,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | u1_struct_0(sK3) = sK4
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1169,c_1069])).

cnf(c_1788,plain,
    ( ~ m1_subset_1(sK4,k9_setfam_1(u1_struct_0(sK3)))
    | ~ v1_tdlat_3(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k2_pre_topc(sK3,sK4) = u1_struct_0(sK3)
    | u1_struct_0(sK3) = sK4 ),
    inference(unflattening,[status(thm)],[c_1787])).

cnf(c_1790,plain,
    ( k2_pre_topc(sK3,sK4) = u1_struct_0(sK3)
    | u1_struct_0(sK3) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1788,c_48,c_46,c_45,c_44])).

cnf(c_14151,plain,
    ( u1_struct_0(sK3) = sK4 ),
    inference(demodulation,[status(thm)],[c_14145,c_1790])).

cnf(c_14159,plain,
    ( sK4 != sK4 ),
    inference(light_normalisation,[status(thm)],[c_14148,c_14151])).

cnf(c_14160,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_14159])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:23:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.58/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/0.99  
% 3.58/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.58/0.99  
% 3.58/0.99  ------  iProver source info
% 3.58/0.99  
% 3.58/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.58/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.58/0.99  git: non_committed_changes: false
% 3.58/0.99  git: last_make_outside_of_git: false
% 3.58/0.99  
% 3.58/0.99  ------ 
% 3.58/0.99  
% 3.58/0.99  ------ Input Options
% 3.58/0.99  
% 3.58/0.99  --out_options                           all
% 3.58/0.99  --tptp_safe_out                         true
% 3.58/0.99  --problem_path                          ""
% 3.58/0.99  --include_path                          ""
% 3.58/0.99  --clausifier                            res/vclausify_rel
% 3.58/0.99  --clausifier_options                    --mode clausify
% 3.58/0.99  --stdin                                 false
% 3.58/0.99  --stats_out                             all
% 3.58/0.99  
% 3.58/0.99  ------ General Options
% 3.58/0.99  
% 3.58/0.99  --fof                                   false
% 3.58/0.99  --time_out_real                         305.
% 3.58/0.99  --time_out_virtual                      -1.
% 3.58/0.99  --symbol_type_check                     false
% 3.58/0.99  --clausify_out                          false
% 3.58/0.99  --sig_cnt_out                           false
% 3.58/0.99  --trig_cnt_out                          false
% 3.58/0.99  --trig_cnt_out_tolerance                1.
% 3.58/0.99  --trig_cnt_out_sk_spl                   false
% 3.58/0.99  --abstr_cl_out                          false
% 3.58/0.99  
% 3.58/0.99  ------ Global Options
% 3.58/0.99  
% 3.58/0.99  --schedule                              default
% 3.58/0.99  --add_important_lit                     false
% 3.58/0.99  --prop_solver_per_cl                    1000
% 3.58/0.99  --min_unsat_core                        false
% 3.58/0.99  --soft_assumptions                      false
% 3.58/0.99  --soft_lemma_size                       3
% 3.58/0.99  --prop_impl_unit_size                   0
% 3.58/0.99  --prop_impl_unit                        []
% 3.58/0.99  --share_sel_clauses                     true
% 3.58/0.99  --reset_solvers                         false
% 3.58/0.99  --bc_imp_inh                            [conj_cone]
% 3.58/0.99  --conj_cone_tolerance                   3.
% 3.58/0.99  --extra_neg_conj                        none
% 3.58/0.99  --large_theory_mode                     true
% 3.58/0.99  --prolific_symb_bound                   200
% 3.58/0.99  --lt_threshold                          2000
% 3.58/0.99  --clause_weak_htbl                      true
% 3.58/0.99  --gc_record_bc_elim                     false
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing Options
% 3.58/0.99  
% 3.58/0.99  --preprocessing_flag                    true
% 3.58/0.99  --time_out_prep_mult                    0.1
% 3.58/0.99  --splitting_mode                        input
% 3.58/0.99  --splitting_grd                         true
% 3.58/0.99  --splitting_cvd                         false
% 3.58/0.99  --splitting_cvd_svl                     false
% 3.58/0.99  --splitting_nvd                         32
% 3.58/0.99  --sub_typing                            true
% 3.58/0.99  --prep_gs_sim                           true
% 3.58/0.99  --prep_unflatten                        true
% 3.58/0.99  --prep_res_sim                          true
% 3.58/0.99  --prep_upred                            true
% 3.58/0.99  --prep_sem_filter                       exhaustive
% 3.58/0.99  --prep_sem_filter_out                   false
% 3.58/0.99  --pred_elim                             true
% 3.58/0.99  --res_sim_input                         true
% 3.58/0.99  --eq_ax_congr_red                       true
% 3.58/0.99  --pure_diseq_elim                       true
% 3.58/0.99  --brand_transform                       false
% 3.58/0.99  --non_eq_to_eq                          false
% 3.58/0.99  --prep_def_merge                        true
% 3.58/0.99  --prep_def_merge_prop_impl              false
% 3.58/0.99  --prep_def_merge_mbd                    true
% 3.58/0.99  --prep_def_merge_tr_red                 false
% 3.58/0.99  --prep_def_merge_tr_cl                  false
% 3.58/0.99  --smt_preprocessing                     true
% 3.58/0.99  --smt_ac_axioms                         fast
% 3.58/0.99  --preprocessed_out                      false
% 3.58/0.99  --preprocessed_stats                    false
% 3.58/0.99  
% 3.58/0.99  ------ Abstraction refinement Options
% 3.58/0.99  
% 3.58/0.99  --abstr_ref                             []
% 3.58/0.99  --abstr_ref_prep                        false
% 3.58/0.99  --abstr_ref_until_sat                   false
% 3.58/0.99  --abstr_ref_sig_restrict                funpre
% 3.58/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.58/0.99  --abstr_ref_under                       []
% 3.58/0.99  
% 3.58/0.99  ------ SAT Options
% 3.58/0.99  
% 3.58/0.99  --sat_mode                              false
% 3.58/0.99  --sat_fm_restart_options                ""
% 3.58/0.99  --sat_gr_def                            false
% 3.58/0.99  --sat_epr_types                         true
% 3.58/0.99  --sat_non_cyclic_types                  false
% 3.58/0.99  --sat_finite_models                     false
% 3.58/0.99  --sat_fm_lemmas                         false
% 3.58/0.99  --sat_fm_prep                           false
% 3.58/0.99  --sat_fm_uc_incr                        true
% 3.58/0.99  --sat_out_model                         small
% 3.58/0.99  --sat_out_clauses                       false
% 3.58/0.99  
% 3.58/0.99  ------ QBF Options
% 3.58/0.99  
% 3.58/0.99  --qbf_mode                              false
% 3.58/0.99  --qbf_elim_univ                         false
% 3.58/0.99  --qbf_dom_inst                          none
% 3.58/0.99  --qbf_dom_pre_inst                      false
% 3.58/0.99  --qbf_sk_in                             false
% 3.58/0.99  --qbf_pred_elim                         true
% 3.58/0.99  --qbf_split                             512
% 3.58/0.99  
% 3.58/0.99  ------ BMC1 Options
% 3.58/0.99  
% 3.58/0.99  --bmc1_incremental                      false
% 3.58/0.99  --bmc1_axioms                           reachable_all
% 3.58/0.99  --bmc1_min_bound                        0
% 3.58/0.99  --bmc1_max_bound                        -1
% 3.58/0.99  --bmc1_max_bound_default                -1
% 3.58/0.99  --bmc1_symbol_reachability              true
% 3.58/0.99  --bmc1_property_lemmas                  false
% 3.58/0.99  --bmc1_k_induction                      false
% 3.58/0.99  --bmc1_non_equiv_states                 false
% 3.58/0.99  --bmc1_deadlock                         false
% 3.58/0.99  --bmc1_ucm                              false
% 3.58/0.99  --bmc1_add_unsat_core                   none
% 3.58/0.99  --bmc1_unsat_core_children              false
% 3.58/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.58/0.99  --bmc1_out_stat                         full
% 3.58/0.99  --bmc1_ground_init                      false
% 3.58/0.99  --bmc1_pre_inst_next_state              false
% 3.58/0.99  --bmc1_pre_inst_state                   false
% 3.58/0.99  --bmc1_pre_inst_reach_state             false
% 3.58/0.99  --bmc1_out_unsat_core                   false
% 3.58/0.99  --bmc1_aig_witness_out                  false
% 3.58/0.99  --bmc1_verbose                          false
% 3.58/0.99  --bmc1_dump_clauses_tptp                false
% 3.58/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.58/0.99  --bmc1_dump_file                        -
% 3.58/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.58/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.58/0.99  --bmc1_ucm_extend_mode                  1
% 3.58/0.99  --bmc1_ucm_init_mode                    2
% 3.58/0.99  --bmc1_ucm_cone_mode                    none
% 3.58/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.58/0.99  --bmc1_ucm_relax_model                  4
% 3.58/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.58/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.58/0.99  --bmc1_ucm_layered_model                none
% 3.58/0.99  --bmc1_ucm_max_lemma_size               10
% 3.58/0.99  
% 3.58/0.99  ------ AIG Options
% 3.58/0.99  
% 3.58/0.99  --aig_mode                              false
% 3.58/0.99  
% 3.58/0.99  ------ Instantiation Options
% 3.58/0.99  
% 3.58/0.99  --instantiation_flag                    true
% 3.58/0.99  --inst_sos_flag                         false
% 3.58/0.99  --inst_sos_phase                        true
% 3.58/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.58/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.58/0.99  --inst_lit_sel_side                     num_symb
% 3.58/0.99  --inst_solver_per_active                1400
% 3.58/0.99  --inst_solver_calls_frac                1.
% 3.58/0.99  --inst_passive_queue_type               priority_queues
% 3.58/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.58/0.99  --inst_passive_queues_freq              [25;2]
% 3.58/0.99  --inst_dismatching                      true
% 3.58/0.99  --inst_eager_unprocessed_to_passive     true
% 3.58/0.99  --inst_prop_sim_given                   true
% 3.58/0.99  --inst_prop_sim_new                     false
% 3.58/0.99  --inst_subs_new                         false
% 3.58/0.99  --inst_eq_res_simp                      false
% 3.58/0.99  --inst_subs_given                       false
% 3.58/0.99  --inst_orphan_elimination               true
% 3.58/0.99  --inst_learning_loop_flag               true
% 3.58/0.99  --inst_learning_start                   3000
% 3.58/0.99  --inst_learning_factor                  2
% 3.58/0.99  --inst_start_prop_sim_after_learn       3
% 3.58/0.99  --inst_sel_renew                        solver
% 3.58/0.99  --inst_lit_activity_flag                true
% 3.58/0.99  --inst_restr_to_given                   false
% 3.58/0.99  --inst_activity_threshold               500
% 3.58/0.99  --inst_out_proof                        true
% 3.58/0.99  
% 3.58/0.99  ------ Resolution Options
% 3.58/0.99  
% 3.58/0.99  --resolution_flag                       true
% 3.58/0.99  --res_lit_sel                           adaptive
% 3.58/0.99  --res_lit_sel_side                      none
% 3.58/0.99  --res_ordering                          kbo
% 3.58/0.99  --res_to_prop_solver                    active
% 3.58/0.99  --res_prop_simpl_new                    false
% 3.58/0.99  --res_prop_simpl_given                  true
% 3.58/0.99  --res_passive_queue_type                priority_queues
% 3.58/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.58/0.99  --res_passive_queues_freq               [15;5]
% 3.58/0.99  --res_forward_subs                      full
% 3.58/0.99  --res_backward_subs                     full
% 3.58/0.99  --res_forward_subs_resolution           true
% 3.58/0.99  --res_backward_subs_resolution          true
% 3.58/0.99  --res_orphan_elimination                true
% 3.58/0.99  --res_time_limit                        2.
% 3.58/0.99  --res_out_proof                         true
% 3.58/0.99  
% 3.58/0.99  ------ Superposition Options
% 3.58/0.99  
% 3.58/0.99  --superposition_flag                    true
% 3.58/0.99  --sup_passive_queue_type                priority_queues
% 3.58/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.58/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.58/0.99  --demod_completeness_check              fast
% 3.58/0.99  --demod_use_ground                      true
% 3.58/0.99  --sup_to_prop_solver                    passive
% 3.58/0.99  --sup_prop_simpl_new                    true
% 3.58/0.99  --sup_prop_simpl_given                  true
% 3.58/0.99  --sup_fun_splitting                     false
% 3.58/0.99  --sup_smt_interval                      50000
% 3.58/0.99  
% 3.58/0.99  ------ Superposition Simplification Setup
% 3.58/0.99  
% 3.58/0.99  --sup_indices_passive                   []
% 3.58/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.58/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.58/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.58/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.58/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.58/0.99  --sup_full_bw                           [BwDemod]
% 3.58/0.99  --sup_immed_triv                        [TrivRules]
% 3.58/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.58/0.99  --sup_immed_bw_main                     []
% 3.58/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.58/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.58/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.58/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.58/0.99  
% 3.58/0.99  ------ Combination Options
% 3.58/0.99  
% 3.58/0.99  --comb_res_mult                         3
% 3.58/0.99  --comb_sup_mult                         2
% 3.58/0.99  --comb_inst_mult                        10
% 3.58/0.99  
% 3.58/0.99  ------ Debug Options
% 3.58/0.99  
% 3.58/0.99  --dbg_backtrace                         false
% 3.58/0.99  --dbg_dump_prop_clauses                 false
% 3.58/0.99  --dbg_dump_prop_clauses_file            -
% 3.58/0.99  --dbg_out_stat                          false
% 3.58/0.99  ------ Parsing...
% 3.58/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.58/0.99  ------ Proving...
% 3.58/0.99  ------ Problem Properties 
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  clauses                                 41
% 3.58/0.99  conjectures                             4
% 3.58/0.99  EPR                                     6
% 3.58/0.99  Horn                                    31
% 3.58/0.99  unary                                   10
% 3.58/0.99  binary                                  10
% 3.58/0.99  lits                                    112
% 3.58/0.99  lits eq                                 25
% 3.58/0.99  fd_pure                                 0
% 3.58/0.99  fd_pseudo                               0
% 3.58/0.99  fd_cond                                 0
% 3.58/0.99  fd_pseudo_cond                          2
% 3.58/0.99  AC symbols                              0
% 3.58/0.99  
% 3.58/0.99  ------ Schedule dynamic 5 is on 
% 3.58/0.99  
% 3.58/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ 
% 3.58/0.99  Current options:
% 3.58/0.99  ------ 
% 3.58/0.99  
% 3.58/0.99  ------ Input Options
% 3.58/0.99  
% 3.58/0.99  --out_options                           all
% 3.58/0.99  --tptp_safe_out                         true
% 3.58/0.99  --problem_path                          ""
% 3.58/0.99  --include_path                          ""
% 3.58/0.99  --clausifier                            res/vclausify_rel
% 3.58/0.99  --clausifier_options                    --mode clausify
% 3.58/0.99  --stdin                                 false
% 3.58/0.99  --stats_out                             all
% 3.58/0.99  
% 3.58/0.99  ------ General Options
% 3.58/0.99  
% 3.58/0.99  --fof                                   false
% 3.58/0.99  --time_out_real                         305.
% 3.58/0.99  --time_out_virtual                      -1.
% 3.58/0.99  --symbol_type_check                     false
% 3.58/0.99  --clausify_out                          false
% 3.58/0.99  --sig_cnt_out                           false
% 3.58/0.99  --trig_cnt_out                          false
% 3.58/0.99  --trig_cnt_out_tolerance                1.
% 3.58/0.99  --trig_cnt_out_sk_spl                   false
% 3.58/0.99  --abstr_cl_out                          false
% 3.58/0.99  
% 3.58/0.99  ------ Global Options
% 3.58/0.99  
% 3.58/0.99  --schedule                              default
% 3.58/0.99  --add_important_lit                     false
% 3.58/0.99  --prop_solver_per_cl                    1000
% 3.58/0.99  --min_unsat_core                        false
% 3.58/0.99  --soft_assumptions                      false
% 3.58/0.99  --soft_lemma_size                       3
% 3.58/0.99  --prop_impl_unit_size                   0
% 3.58/0.99  --prop_impl_unit                        []
% 3.58/0.99  --share_sel_clauses                     true
% 3.58/0.99  --reset_solvers                         false
% 3.58/0.99  --bc_imp_inh                            [conj_cone]
% 3.58/0.99  --conj_cone_tolerance                   3.
% 3.58/0.99  --extra_neg_conj                        none
% 3.58/0.99  --large_theory_mode                     true
% 3.58/0.99  --prolific_symb_bound                   200
% 3.58/0.99  --lt_threshold                          2000
% 3.58/0.99  --clause_weak_htbl                      true
% 3.58/0.99  --gc_record_bc_elim                     false
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing Options
% 3.58/0.99  
% 3.58/0.99  --preprocessing_flag                    true
% 3.58/0.99  --time_out_prep_mult                    0.1
% 3.58/0.99  --splitting_mode                        input
% 3.58/0.99  --splitting_grd                         true
% 3.58/0.99  --splitting_cvd                         false
% 3.58/0.99  --splitting_cvd_svl                     false
% 3.58/0.99  --splitting_nvd                         32
% 3.58/0.99  --sub_typing                            true
% 3.58/0.99  --prep_gs_sim                           true
% 3.58/0.99  --prep_unflatten                        true
% 3.58/0.99  --prep_res_sim                          true
% 3.58/0.99  --prep_upred                            true
% 3.58/0.99  --prep_sem_filter                       exhaustive
% 3.58/0.99  --prep_sem_filter_out                   false
% 3.58/0.99  --pred_elim                             true
% 3.58/0.99  --res_sim_input                         true
% 3.58/0.99  --eq_ax_congr_red                       true
% 3.58/0.99  --pure_diseq_elim                       true
% 3.58/0.99  --brand_transform                       false
% 3.58/0.99  --non_eq_to_eq                          false
% 3.58/0.99  --prep_def_merge                        true
% 3.58/0.99  --prep_def_merge_prop_impl              false
% 3.58/0.99  --prep_def_merge_mbd                    true
% 3.58/0.99  --prep_def_merge_tr_red                 false
% 3.58/0.99  --prep_def_merge_tr_cl                  false
% 3.58/0.99  --smt_preprocessing                     true
% 3.58/0.99  --smt_ac_axioms                         fast
% 3.58/0.99  --preprocessed_out                      false
% 3.58/0.99  --preprocessed_stats                    false
% 3.58/0.99  
% 3.58/0.99  ------ Abstraction refinement Options
% 3.58/0.99  
% 3.58/0.99  --abstr_ref                             []
% 3.58/0.99  --abstr_ref_prep                        false
% 3.58/0.99  --abstr_ref_until_sat                   false
% 3.58/0.99  --abstr_ref_sig_restrict                funpre
% 3.58/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.58/0.99  --abstr_ref_under                       []
% 3.58/0.99  
% 3.58/0.99  ------ SAT Options
% 3.58/0.99  
% 3.58/0.99  --sat_mode                              false
% 3.58/0.99  --sat_fm_restart_options                ""
% 3.58/0.99  --sat_gr_def                            false
% 3.58/0.99  --sat_epr_types                         true
% 3.58/0.99  --sat_non_cyclic_types                  false
% 3.58/0.99  --sat_finite_models                     false
% 3.58/0.99  --sat_fm_lemmas                         false
% 3.58/0.99  --sat_fm_prep                           false
% 3.58/0.99  --sat_fm_uc_incr                        true
% 3.58/0.99  --sat_out_model                         small
% 3.58/0.99  --sat_out_clauses                       false
% 3.58/0.99  
% 3.58/0.99  ------ QBF Options
% 3.58/0.99  
% 3.58/0.99  --qbf_mode                              false
% 3.58/0.99  --qbf_elim_univ                         false
% 3.58/0.99  --qbf_dom_inst                          none
% 3.58/0.99  --qbf_dom_pre_inst                      false
% 3.58/0.99  --qbf_sk_in                             false
% 3.58/0.99  --qbf_pred_elim                         true
% 3.58/0.99  --qbf_split                             512
% 3.58/0.99  
% 3.58/0.99  ------ BMC1 Options
% 3.58/0.99  
% 3.58/0.99  --bmc1_incremental                      false
% 3.58/0.99  --bmc1_axioms                           reachable_all
% 3.58/0.99  --bmc1_min_bound                        0
% 3.58/0.99  --bmc1_max_bound                        -1
% 3.58/0.99  --bmc1_max_bound_default                -1
% 3.58/0.99  --bmc1_symbol_reachability              true
% 3.58/0.99  --bmc1_property_lemmas                  false
% 3.58/0.99  --bmc1_k_induction                      false
% 3.58/0.99  --bmc1_non_equiv_states                 false
% 3.58/0.99  --bmc1_deadlock                         false
% 3.58/0.99  --bmc1_ucm                              false
% 3.58/0.99  --bmc1_add_unsat_core                   none
% 3.58/0.99  --bmc1_unsat_core_children              false
% 3.58/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.58/0.99  --bmc1_out_stat                         full
% 3.58/0.99  --bmc1_ground_init                      false
% 3.58/0.99  --bmc1_pre_inst_next_state              false
% 3.58/0.99  --bmc1_pre_inst_state                   false
% 3.58/0.99  --bmc1_pre_inst_reach_state             false
% 3.58/0.99  --bmc1_out_unsat_core                   false
% 3.58/0.99  --bmc1_aig_witness_out                  false
% 3.58/0.99  --bmc1_verbose                          false
% 3.58/0.99  --bmc1_dump_clauses_tptp                false
% 3.58/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.58/0.99  --bmc1_dump_file                        -
% 3.58/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.58/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.58/0.99  --bmc1_ucm_extend_mode                  1
% 3.58/0.99  --bmc1_ucm_init_mode                    2
% 3.58/0.99  --bmc1_ucm_cone_mode                    none
% 3.58/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.58/0.99  --bmc1_ucm_relax_model                  4
% 3.58/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.58/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.58/0.99  --bmc1_ucm_layered_model                none
% 3.58/0.99  --bmc1_ucm_max_lemma_size               10
% 3.58/0.99  
% 3.58/0.99  ------ AIG Options
% 3.58/0.99  
% 3.58/0.99  --aig_mode                              false
% 3.58/0.99  
% 3.58/0.99  ------ Instantiation Options
% 3.58/0.99  
% 3.58/0.99  --instantiation_flag                    true
% 3.58/0.99  --inst_sos_flag                         false
% 3.58/0.99  --inst_sos_phase                        true
% 3.58/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.58/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.58/0.99  --inst_lit_sel_side                     none
% 3.58/0.99  --inst_solver_per_active                1400
% 3.58/0.99  --inst_solver_calls_frac                1.
% 3.58/0.99  --inst_passive_queue_type               priority_queues
% 3.58/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.58/0.99  --inst_passive_queues_freq              [25;2]
% 3.58/0.99  --inst_dismatching                      true
% 3.58/0.99  --inst_eager_unprocessed_to_passive     true
% 3.58/0.99  --inst_prop_sim_given                   true
% 3.58/0.99  --inst_prop_sim_new                     false
% 3.58/0.99  --inst_subs_new                         false
% 3.58/0.99  --inst_eq_res_simp                      false
% 3.58/0.99  --inst_subs_given                       false
% 3.58/0.99  --inst_orphan_elimination               true
% 3.58/0.99  --inst_learning_loop_flag               true
% 3.58/0.99  --inst_learning_start                   3000
% 3.58/0.99  --inst_learning_factor                  2
% 3.58/0.99  --inst_start_prop_sim_after_learn       3
% 3.58/0.99  --inst_sel_renew                        solver
% 3.58/0.99  --inst_lit_activity_flag                true
% 3.58/0.99  --inst_restr_to_given                   false
% 3.58/0.99  --inst_activity_threshold               500
% 3.58/0.99  --inst_out_proof                        true
% 3.58/0.99  
% 3.58/0.99  ------ Resolution Options
% 3.58/0.99  
% 3.58/0.99  --resolution_flag                       false
% 3.58/0.99  --res_lit_sel                           adaptive
% 3.58/0.99  --res_lit_sel_side                      none
% 3.58/0.99  --res_ordering                          kbo
% 3.58/0.99  --res_to_prop_solver                    active
% 3.58/0.99  --res_prop_simpl_new                    false
% 3.58/0.99  --res_prop_simpl_given                  true
% 3.58/0.99  --res_passive_queue_type                priority_queues
% 3.58/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.58/0.99  --res_passive_queues_freq               [15;5]
% 3.58/0.99  --res_forward_subs                      full
% 3.58/0.99  --res_backward_subs                     full
% 3.58/0.99  --res_forward_subs_resolution           true
% 3.58/0.99  --res_backward_subs_resolution          true
% 3.58/0.99  --res_orphan_elimination                true
% 3.58/0.99  --res_time_limit                        2.
% 3.58/0.99  --res_out_proof                         true
% 3.58/0.99  
% 3.58/0.99  ------ Superposition Options
% 3.58/0.99  
% 3.58/0.99  --superposition_flag                    true
% 3.58/0.99  --sup_passive_queue_type                priority_queues
% 3.58/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.58/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.58/0.99  --demod_completeness_check              fast
% 3.58/0.99  --demod_use_ground                      true
% 3.58/0.99  --sup_to_prop_solver                    passive
% 3.58/0.99  --sup_prop_simpl_new                    true
% 3.58/0.99  --sup_prop_simpl_given                  true
% 3.58/0.99  --sup_fun_splitting                     false
% 3.58/0.99  --sup_smt_interval                      50000
% 3.58/0.99  
% 3.58/0.99  ------ Superposition Simplification Setup
% 3.58/0.99  
% 3.58/0.99  --sup_indices_passive                   []
% 3.58/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.58/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.58/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.58/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.58/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.58/0.99  --sup_full_bw                           [BwDemod]
% 3.58/0.99  --sup_immed_triv                        [TrivRules]
% 3.58/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.58/0.99  --sup_immed_bw_main                     []
% 3.58/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.58/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.58/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.58/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.58/0.99  
% 3.58/0.99  ------ Combination Options
% 3.58/0.99  
% 3.58/0.99  --comb_res_mult                         3
% 3.58/0.99  --comb_sup_mult                         2
% 3.58/0.99  --comb_inst_mult                        10
% 3.58/0.99  
% 3.58/0.99  ------ Debug Options
% 3.58/0.99  
% 3.58/0.99  --dbg_backtrace                         false
% 3.58/0.99  --dbg_dump_prop_clauses                 false
% 3.58/0.99  --dbg_dump_prop_clauses_file            -
% 3.58/0.99  --dbg_out_stat                          false
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ Proving...
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  % SZS status Theorem for theBenchmark.p
% 3.58/0.99  
% 3.58/0.99   Resolution empty clause
% 3.58/0.99  
% 3.58/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.58/0.99  
% 3.58/0.99  fof(f31,conjecture,(
% 3.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f32,negated_conjecture,(
% 3.58/0.99    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 3.58/0.99    inference(negated_conjecture,[],[f31])).
% 3.58/0.99  
% 3.58/0.99  fof(f73,plain,(
% 3.58/0.99    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f32])).
% 3.58/0.99  
% 3.58/0.99  fof(f74,plain,(
% 3.58/0.99    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.58/0.99    inference(flattening,[],[f73])).
% 3.58/0.99  
% 3.58/0.99  fof(f88,plain,(
% 3.58/0.99    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.58/0.99    inference(nnf_transformation,[],[f74])).
% 3.58/0.99  
% 3.58/0.99  fof(f89,plain,(
% 3.58/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.58/0.99    inference(flattening,[],[f88])).
% 3.58/0.99  
% 3.58/0.99  fof(f91,plain,(
% 3.58/0.99    ( ! [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_subset_1(sK4,u1_struct_0(X0)) | ~v3_tex_2(sK4,X0)) & (~v1_subset_1(sK4,u1_struct_0(X0)) | v3_tex_2(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f90,plain,(
% 3.58/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK3)) | ~v3_tex_2(X1,sK3)) & (~v1_subset_1(X1,u1_struct_0(sK3)) | v3_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v1_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f92,plain,(
% 3.58/0.99    ((v1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_tex_2(sK4,sK3)) & (~v1_subset_1(sK4,u1_struct_0(sK3)) | v3_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v1_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 3.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f89,f91,f90])).
% 3.58/0.99  
% 3.58/0.99  fof(f140,plain,(
% 3.58/0.99    v1_tdlat_3(sK3)),
% 3.58/0.99    inference(cnf_transformation,[],[f92])).
% 3.58/0.99  
% 3.58/0.99  fof(f21,axiom,(
% 3.58/0.99    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) <=> k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0)))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f56,plain,(
% 3.58/0.99    ! [X0] : ((v1_tdlat_3(X0) <=> k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.58/0.99    inference(ennf_transformation,[],[f21])).
% 3.58/0.99  
% 3.58/0.99  fof(f79,plain,(
% 3.58/0.99    ! [X0] : (((v1_tdlat_3(X0) | k9_setfam_1(u1_struct_0(X0)) != u1_pre_topc(X0)) & (k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 3.58/0.99    inference(nnf_transformation,[],[f56])).
% 3.58/0.99  
% 3.58/0.99  fof(f120,plain,(
% 3.58/0.99    ( ! [X0] : (k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f79])).
% 3.58/0.99  
% 3.58/0.99  fof(f141,plain,(
% 3.58/0.99    l1_pre_topc(sK3)),
% 3.58/0.99    inference(cnf_transformation,[],[f92])).
% 3.58/0.99  
% 3.58/0.99  fof(f142,plain,(
% 3.58/0.99    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 3.58/0.99    inference(cnf_transformation,[],[f92])).
% 3.58/0.99  
% 3.58/0.99  fof(f12,axiom,(
% 3.58/0.99    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f104,plain,(
% 3.58/0.99    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f12])).
% 3.58/0.99  
% 3.58/0.99  fof(f175,plain,(
% 3.58/0.99    m1_subset_1(sK4,k9_setfam_1(u1_struct_0(sK3)))),
% 3.58/0.99    inference(definition_unfolding,[],[f142,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f25,axiom,(
% 3.58/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f61,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f25])).
% 3.58/0.99  
% 3.58/0.99  fof(f62,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.58/0.99    inference(flattening,[],[f61])).
% 3.58/0.99  
% 3.58/0.99  fof(f82,plain,(
% 3.58/0.99    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & v1_pre_topc(sK1(X0,X1)) & ~v2_struct_0(sK1(X0,X1))))),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f83,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : ((u1_struct_0(sK1(X0,X1)) = X1 & m1_pre_topc(sK1(X0,X1),X0) & v1_pre_topc(sK1(X0,X1)) & ~v2_struct_0(sK1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f62,f82])).
% 3.58/0.99  
% 3.58/0.99  fof(f129,plain,(
% 3.58/0.99    ( ! [X0,X1] : (m1_pre_topc(sK1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f83])).
% 3.58/0.99  
% 3.58/0.99  fof(f166,plain,(
% 3.58/0.99    ( ! [X0,X1] : (m1_pre_topc(sK1(X0,X1),X0) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f129,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f138,plain,(
% 3.58/0.99    ~v2_struct_0(sK3)),
% 3.58/0.99    inference(cnf_transformation,[],[f92])).
% 3.58/0.99  
% 3.58/0.99  fof(f15,axiom,(
% 3.58/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f45,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.58/0.99    inference(ennf_transformation,[],[f15])).
% 3.58/0.99  
% 3.58/0.99  fof(f46,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.58/0.99    inference(flattening,[],[f45])).
% 3.58/0.99  
% 3.58/0.99  fof(f107,plain,(
% 3.58/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f46])).
% 3.58/0.99  
% 3.58/0.99  fof(f154,plain,(
% 3.58/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f107,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f20,axiom,(
% 3.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f34,plain,(
% 3.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_borsuk_1(X1,X0))))),
% 3.58/0.99    inference(pure_predicate_removal,[],[f20])).
% 3.58/0.99  
% 3.58/0.99  fof(f54,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f34])).
% 3.58/0.99  
% 3.58/0.99  fof(f55,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.58/0.99    inference(flattening,[],[f54])).
% 3.58/0.99  
% 3.58/0.99  fof(f118,plain,(
% 3.58/0.99    ( ! [X0,X1] : (v1_borsuk_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f55])).
% 3.58/0.99  
% 3.58/0.99  fof(f17,axiom,(
% 3.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0))))))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f49,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f17])).
% 3.58/0.99  
% 3.58/0.99  fof(f50,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.58/0.99    inference(flattening,[],[f49])).
% 3.58/0.99  
% 3.58/0.99  fof(f77,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.58/0.99    inference(nnf_transformation,[],[f50])).
% 3.58/0.99  
% 3.58/0.99  fof(f78,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.58/0.99    inference(flattening,[],[f77])).
% 3.58/0.99  
% 3.58/0.99  fof(f113,plain,(
% 3.58/0.99    ( ! [X2,X0,X1] : (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f78])).
% 3.58/0.99  
% 3.58/0.99  fof(f158,plain,(
% 3.58/0.99    ( ! [X2,X0,X1] : (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f113,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f178,plain,(
% 3.58/0.99    ( ! [X0,X1] : (v4_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k9_setfam_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.58/0.99    inference(equality_resolution,[],[f158])).
% 3.58/0.99  
% 3.58/0.99  fof(f18,axiom,(
% 3.58/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f51,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.58/0.99    inference(ennf_transformation,[],[f18])).
% 3.58/0.99  
% 3.58/0.99  fof(f116,plain,(
% 3.58/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f51])).
% 3.58/0.99  
% 3.58/0.99  fof(f159,plain,(
% 3.58/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k9_setfam_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f116,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f19,axiom,(
% 3.58/0.99    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f52,plain,(
% 3.58/0.99    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 3.58/0.99    inference(ennf_transformation,[],[f19])).
% 3.58/0.99  
% 3.58/0.99  fof(f53,plain,(
% 3.58/0.99    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 3.58/0.99    inference(flattening,[],[f52])).
% 3.58/0.99  
% 3.58/0.99  fof(f117,plain,(
% 3.58/0.99    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f53])).
% 3.58/0.99  
% 3.58/0.99  fof(f130,plain,(
% 3.58/0.99    ( ! [X0,X1] : (u1_struct_0(sK1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f83])).
% 3.58/0.99  
% 3.58/0.99  fof(f165,plain,(
% 3.58/0.99    ( ! [X0,X1] : (u1_struct_0(sK1(X0,X1)) = X1 | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f130,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f7,axiom,(
% 3.58/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f37,plain,(
% 3.58/0.99    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f7])).
% 3.58/0.99  
% 3.58/0.99  fof(f99,plain,(
% 3.58/0.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.58/0.99    inference(cnf_transformation,[],[f37])).
% 3.58/0.99  
% 3.58/0.99  fof(f149,plain,(
% 3.58/0.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k9_setfam_1(X0))) )),
% 3.58/0.99    inference(definition_unfolding,[],[f99,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f9,axiom,(
% 3.58/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_xboole_0(X1) => v1_subset_1(X1,X0))))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f38,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : ((v1_subset_1(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.58/0.99    inference(ennf_transformation,[],[f9])).
% 3.58/0.99  
% 3.58/0.99  fof(f39,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (v1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 3.58/0.99    inference(flattening,[],[f38])).
% 3.58/0.99  
% 3.58/0.99  fof(f101,plain,(
% 3.58/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f39])).
% 3.58/0.99  
% 3.58/0.99  fof(f150,plain,(
% 3.58/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k9_setfam_1(X0)) | v1_xboole_0(X0)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f101,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f24,axiom,(
% 3.58/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(X0)) & v1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k3_subset_1(X0,X1)))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f59,plain,(
% 3.58/0.99    ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f24])).
% 3.58/0.99  
% 3.58/0.99  fof(f60,plain,(
% 3.58/0.99    ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.58/0.99    inference(flattening,[],[f59])).
% 3.58/0.99  
% 3.58/0.99  fof(f126,plain,(
% 3.58/0.99    ( ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f60])).
% 3.58/0.99  
% 3.58/0.99  fof(f164,plain,(
% 3.58/0.99    ( ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k9_setfam_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f126,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f10,axiom,(
% 3.58/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f40,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.58/0.99    inference(ennf_transformation,[],[f10])).
% 3.58/0.99  
% 3.58/0.99  fof(f102,plain,(
% 3.58/0.99    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f40])).
% 3.58/0.99  
% 3.58/0.99  fof(f151,plain,(
% 3.58/0.99    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k9_setfam_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f102,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f139,plain,(
% 3.58/0.99    v2_pre_topc(sK3)),
% 3.58/0.99    inference(cnf_transformation,[],[f92])).
% 3.58/0.99  
% 3.58/0.99  fof(f16,axiom,(
% 3.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f47,plain,(
% 3.58/0.99    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f16])).
% 3.58/0.99  
% 3.58/0.99  fof(f48,plain,(
% 3.58/0.99    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.58/0.99    inference(flattening,[],[f47])).
% 3.58/0.99  
% 3.58/0.99  fof(f75,plain,(
% 3.58/0.99    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v4_pre_topc(sK0(X0),X0) & v3_pre_topc(sK0(X0),X0) & ~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f76,plain,(
% 3.58/0.99    ! [X0] : ((v4_pre_topc(sK0(X0),X0) & v3_pre_topc(sK0(X0),X0) & ~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f75])).
% 3.58/0.99  
% 3.58/0.99  fof(f110,plain,(
% 3.58/0.99    ( ! [X0] : (~v1_xboole_0(sK0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f76])).
% 3.58/0.99  
% 3.58/0.99  fof(f109,plain,(
% 3.58/0.99    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f76])).
% 3.58/0.99  
% 3.58/0.99  fof(f155,plain,(
% 3.58/0.99    ( ! [X0] : (m1_subset_1(sK0(X0),k9_setfam_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f109,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f11,axiom,(
% 3.58/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f33,plain,(
% 3.58/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 3.58/0.99    inference(unused_predicate_definition_removal,[],[f11])).
% 3.58/0.99  
% 3.58/0.99  fof(f41,plain,(
% 3.58/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.58/0.99    inference(ennf_transformation,[],[f33])).
% 3.58/0.99  
% 3.58/0.99  fof(f103,plain,(
% 3.58/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.58/0.99    inference(cnf_transformation,[],[f41])).
% 3.58/0.99  
% 3.58/0.99  fof(f152,plain,(
% 3.58/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k9_setfam_1(X1))) )),
% 3.58/0.99    inference(definition_unfolding,[],[f103,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f1,axiom,(
% 3.58/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f93,plain,(
% 3.58/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f1])).
% 3.58/0.99  
% 3.58/0.99  fof(f2,axiom,(
% 3.58/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f35,plain,(
% 3.58/0.99    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 3.58/0.99    inference(ennf_transformation,[],[f2])).
% 3.58/0.99  
% 3.58/0.99  fof(f36,plain,(
% 3.58/0.99    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 3.58/0.99    inference(flattening,[],[f35])).
% 3.58/0.99  
% 3.58/0.99  fof(f94,plain,(
% 3.58/0.99    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f36])).
% 3.58/0.99  
% 3.58/0.99  fof(f5,axiom,(
% 3.58/0.99    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f97,plain,(
% 3.58/0.99    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.58/0.99    inference(cnf_transformation,[],[f5])).
% 3.58/0.99  
% 3.58/0.99  fof(f3,axiom,(
% 3.58/0.99    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f95,plain,(
% 3.58/0.99    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f3])).
% 3.58/0.99  
% 3.58/0.99  fof(f147,plain,(
% 3.58/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k9_setfam_1(X0))) )),
% 3.58/0.99    inference(definition_unfolding,[],[f97,f95,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f23,axiom,(
% 3.58/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f58,plain,(
% 3.58/0.99    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f23])).
% 3.58/0.99  
% 3.58/0.99  fof(f81,plain,(
% 3.58/0.99    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.58/0.99    inference(nnf_transformation,[],[f58])).
% 3.58/0.99  
% 3.58/0.99  fof(f125,plain,(
% 3.58/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.58/0.99    inference(cnf_transformation,[],[f81])).
% 3.58/0.99  
% 3.58/0.99  fof(f162,plain,(
% 3.58/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k9_setfam_1(X0))) )),
% 3.58/0.99    inference(definition_unfolding,[],[f125,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f28,axiom,(
% 3.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f67,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f28])).
% 3.58/0.99  
% 3.58/0.99  fof(f68,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.58/0.99    inference(flattening,[],[f67])).
% 3.58/0.99  
% 3.58/0.99  fof(f135,plain,(
% 3.58/0.99    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f68])).
% 3.58/0.99  
% 3.58/0.99  fof(f172,plain,(
% 3.58/0.99    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f135,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f143,plain,(
% 3.58/0.99    ~v1_subset_1(sK4,u1_struct_0(sK3)) | v3_tex_2(sK4,sK3)),
% 3.58/0.99    inference(cnf_transformation,[],[f92])).
% 3.58/0.99  
% 3.58/0.99  fof(f22,axiom,(
% 3.58/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f57,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.58/0.99    inference(ennf_transformation,[],[f22])).
% 3.58/0.99  
% 3.58/0.99  fof(f80,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.58/0.99    inference(nnf_transformation,[],[f57])).
% 3.58/0.99  
% 3.58/0.99  fof(f123,plain,(
% 3.58/0.99    ( ! [X0,X1] : (v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f80])).
% 3.58/0.99  
% 3.58/0.99  fof(f160,plain,(
% 3.58/0.99    ( ! [X0,X1] : (v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f123,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f27,axiom,(
% 3.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f65,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f27])).
% 3.58/0.99  
% 3.58/0.99  fof(f66,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.58/0.99    inference(flattening,[],[f65])).
% 3.58/0.99  
% 3.58/0.99  fof(f134,plain,(
% 3.58/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f66])).
% 3.58/0.99  
% 3.58/0.99  fof(f171,plain,(
% 3.58/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f134,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f30,axiom,(
% 3.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f71,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f30])).
% 3.58/0.99  
% 3.58/0.99  fof(f72,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.58/0.99    inference(flattening,[],[f71])).
% 3.58/0.99  
% 3.58/0.99  fof(f137,plain,(
% 3.58/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f72])).
% 3.58/0.99  
% 3.58/0.99  fof(f174,plain,(
% 3.58/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f137,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f124,plain,(
% 3.58/0.99    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.58/0.99    inference(cnf_transformation,[],[f81])).
% 3.58/0.99  
% 3.58/0.99  fof(f163,plain,(
% 3.58/0.99    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k9_setfam_1(X0))) )),
% 3.58/0.99    inference(definition_unfolding,[],[f124,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f179,plain,(
% 3.58/0.99    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k9_setfam_1(X1))) )),
% 3.58/0.99    inference(equality_resolution,[],[f163])).
% 3.58/0.99  
% 3.58/0.99  fof(f144,plain,(
% 3.58/0.99    v1_subset_1(sK4,u1_struct_0(sK3)) | ~v3_tex_2(sK4,sK3)),
% 3.58/0.99    inference(cnf_transformation,[],[f92])).
% 3.58/0.99  
% 3.58/0.99  fof(f6,axiom,(
% 3.58/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f98,plain,(
% 3.58/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.58/0.99    inference(cnf_transformation,[],[f6])).
% 3.58/0.99  
% 3.58/0.99  fof(f8,axiom,(
% 3.58/0.99    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f100,plain,(
% 3.58/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 3.58/0.99    inference(cnf_transformation,[],[f8])).
% 3.58/0.99  
% 3.58/0.99  fof(f145,plain,(
% 3.58/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f100,f95])).
% 3.58/0.99  
% 3.58/0.99  fof(f148,plain,(
% 3.58/0.99    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k9_setfam_1(X0))) )),
% 3.58/0.99    inference(definition_unfolding,[],[f98,f145,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f4,axiom,(
% 3.58/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f96,plain,(
% 3.58/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.58/0.99    inference(cnf_transformation,[],[f4])).
% 3.58/0.99  
% 3.58/0.99  fof(f146,plain,(
% 3.58/0.99    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 3.58/0.99    inference(definition_unfolding,[],[f96,f145])).
% 3.58/0.99  
% 3.58/0.99  fof(f26,axiom,(
% 3.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f63,plain,(
% 3.58/0.99    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f26])).
% 3.58/0.99  
% 3.58/0.99  fof(f64,plain,(
% 3.58/0.99    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.58/0.99    inference(flattening,[],[f63])).
% 3.58/0.99  
% 3.58/0.99  fof(f84,plain,(
% 3.58/0.99    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.58/0.99    inference(nnf_transformation,[],[f64])).
% 3.58/0.99  
% 3.58/0.99  fof(f85,plain,(
% 3.58/0.99    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.58/0.99    inference(rectify,[],[f84])).
% 3.58/0.99  
% 3.58/0.99  fof(f86,plain,(
% 3.58/0.99    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f87,plain,(
% 3.58/0.99    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f85,f86])).
% 3.58/0.99  
% 3.58/0.99  fof(f131,plain,(
% 3.58/0.99    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f87])).
% 3.58/0.99  
% 3.58/0.99  fof(f170,plain,(
% 3.58/0.99    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f131,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f29,axiom,(
% 3.58/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 3.58/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f69,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.58/0.99    inference(ennf_transformation,[],[f29])).
% 3.58/0.99  
% 3.58/0.99  fof(f70,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.58/0.99    inference(flattening,[],[f69])).
% 3.58/0.99  
% 3.58/0.99  fof(f136,plain,(
% 3.58/0.99    ( ! [X0,X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f70])).
% 3.58/0.99  
% 3.58/0.99  fof(f173,plain,(
% 3.58/0.99    ( ! [X0,X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f136,f104])).
% 3.58/0.99  
% 3.58/0.99  fof(f122,plain,(
% 3.58/0.99    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f80])).
% 3.58/0.99  
% 3.58/0.99  fof(f161,plain,(
% 3.58/0.99    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f122,f104])).
% 3.58/0.99  
% 3.58/0.99  cnf(c_46,negated_conjecture,
% 3.58/0.99      ( v1_tdlat_3(sK3) ),
% 3.58/0.99      inference(cnf_transformation,[],[f140]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6001,plain,
% 3.58/0.99      ( v1_tdlat_3(sK3) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_25,plain,
% 3.58/0.99      ( ~ v1_tdlat_3(X0)
% 3.58/0.99      | ~ l1_pre_topc(X0)
% 3.58/0.99      | k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0) ),
% 3.58/0.99      inference(cnf_transformation,[],[f120]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6008,plain,
% 3.58/0.99      ( k9_setfam_1(u1_struct_0(X0)) = u1_pre_topc(X0)
% 3.58/0.99      | v1_tdlat_3(X0) != iProver_top
% 3.58/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_7195,plain,
% 3.58/0.99      ( k9_setfam_1(u1_struct_0(sK3)) = u1_pre_topc(sK3)
% 3.58/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_6001,c_6008]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_45,negated_conjecture,
% 3.58/0.99      ( l1_pre_topc(sK3) ),
% 3.58/0.99      inference(cnf_transformation,[],[f141]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_101,plain,
% 3.58/0.99      ( ~ v1_tdlat_3(sK3)
% 3.58/0.99      | ~ l1_pre_topc(sK3)
% 3.58/0.99      | k9_setfam_1(u1_struct_0(sK3)) = u1_pre_topc(sK3) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_25]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_7339,plain,
% 3.58/0.99      ( k9_setfam_1(u1_struct_0(sK3)) = u1_pre_topc(sK3) ),
% 3.58/0.99      inference(global_propositional_subsumption,
% 3.58/0.99                [status(thm)],
% 3.58/0.99                [c_7195,c_46,c_45,c_101]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_44,negated_conjecture,
% 3.58/0.99      ( m1_subset_1(sK4,k9_setfam_1(u1_struct_0(sK3))) ),
% 3.58/0.99      inference(cnf_transformation,[],[f175]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6003,plain,
% 3.58/0.99      ( m1_subset_1(sK4,k9_setfam_1(u1_struct_0(sK3))) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_7344,plain,
% 3.58/0.99      ( m1_subset_1(sK4,u1_pre_topc(sK3)) = iProver_top ),
% 3.58/0.99      inference(demodulation,[status(thm)],[c_7339,c_6003]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_32,plain,
% 3.58/0.99      ( m1_pre_topc(sK1(X0,X1),X0)
% 3.58/0.99      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
% 3.58/0.99      | v2_struct_0(X0)
% 3.58/0.99      | ~ l1_pre_topc(X0)
% 3.58/0.99      | v1_xboole_0(X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f166]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6006,plain,
% 3.58/0.99      ( m1_pre_topc(sK1(X0,X1),X0) = iProver_top
% 3.58/0.99      | m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) != iProver_top
% 3.58/0.99      | v2_struct_0(X0) = iProver_top
% 3.58/0.99      | l1_pre_topc(X0) != iProver_top
% 3.58/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_8588,plain,
% 3.58/0.99      ( m1_pre_topc(sK1(sK3,X0),sK3) = iProver_top
% 3.58/0.99      | m1_subset_1(X0,u1_pre_topc(sK3)) != iProver_top
% 3.58/0.99      | v2_struct_0(sK3) = iProver_top
% 3.58/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.58/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_7339,c_6006]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_48,negated_conjecture,
% 3.58/0.99      ( ~ v2_struct_0(sK3) ),
% 3.58/0.99      inference(cnf_transformation,[],[f138]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_49,plain,
% 3.58/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_52,plain,
% 3.58/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_9186,plain,
% 3.58/0.99      ( m1_pre_topc(sK1(sK3,X0),sK3) = iProver_top
% 3.58/0.99      | m1_subset_1(X0,u1_pre_topc(sK3)) != iProver_top
% 3.58/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.58/0.99      inference(global_propositional_subsumption,
% 3.58/0.99                [status(thm)],
% 3.58/0.99                [c_8588,c_49,c_52]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_12,plain,
% 3.58/0.99      ( ~ v4_pre_topc(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ l1_pre_topc(X1)
% 3.58/0.99      | k2_pre_topc(X1,X0) = X0 ),
% 3.58/0.99      inference(cnf_transformation,[],[f154]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_23,plain,
% 3.58/0.99      ( v1_borsuk_1(X0,X1)
% 3.58/0.99      | ~ m1_pre_topc(X0,X1)
% 3.58/0.99      | ~ v1_tdlat_3(X1)
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ v2_pre_topc(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f118]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_19,plain,
% 3.58/0.99      ( ~ v1_borsuk_1(X0,X1)
% 3.58/0.99      | v4_pre_topc(u1_struct_0(X0),X1)
% 3.58/0.99      | ~ m1_pre_topc(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(u1_struct_0(X0),k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ v2_pre_topc(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f178]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_20,plain,
% 3.58/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.58/0.99      | m1_subset_1(u1_struct_0(X0),k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ l1_pre_topc(X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f159]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_292,plain,
% 3.58/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.58/0.99      | v4_pre_topc(u1_struct_0(X0),X1)
% 3.58/0.99      | ~ v1_borsuk_1(X0,X1)
% 3.58/0.99      | ~ v2_pre_topc(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1) ),
% 3.58/0.99      inference(global_propositional_subsumption,[status(thm)],[c_19,c_20]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_293,plain,
% 3.58/0.99      ( ~ v1_borsuk_1(X0,X1)
% 3.58/0.99      | v4_pre_topc(u1_struct_0(X0),X1)
% 3.58/0.99      | ~ m1_pre_topc(X0,X1)
% 3.58/0.99      | ~ v2_pre_topc(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1) ),
% 3.58/0.99      inference(renaming,[status(thm)],[c_292]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_711,plain,
% 3.58/0.99      ( v4_pre_topc(u1_struct_0(X0),X1)
% 3.58/0.99      | ~ m1_pre_topc(X0,X1)
% 3.58/0.99      | ~ v1_tdlat_3(X1)
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ v2_pre_topc(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1) ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_23,c_293]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_21,plain,
% 3.58/0.99      ( ~ v1_tdlat_3(X0) | v2_pre_topc(X0) | ~ l1_pre_topc(X0) ),
% 3.58/0.99      inference(cnf_transformation,[],[f117]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_727,plain,
% 3.58/0.99      ( v4_pre_topc(u1_struct_0(X0),X1)
% 3.58/0.99      | ~ m1_pre_topc(X0,X1)
% 3.58/0.99      | ~ v1_tdlat_3(X1)
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1) ),
% 3.58/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_711,c_21]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_767,plain,
% 3.58/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X3)))
% 3.58/0.99      | ~ v1_tdlat_3(X1)
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ l1_pre_topc(X3)
% 3.58/0.99      | ~ l1_pre_topc(X1)
% 3.58/0.99      | X1 != X3
% 3.58/0.99      | k2_pre_topc(X3,X2) = X2
% 3.58/0.99      | u1_struct_0(X0) != X2 ),
% 3.58/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_727]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_768,plain,
% 3.58/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(u1_struct_0(X0),k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ v1_tdlat_3(X1)
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1)
% 3.58/0.99      | k2_pre_topc(X1,u1_struct_0(X0)) = u1_struct_0(X0) ),
% 3.58/0.99      inference(unflattening,[status(thm)],[c_767]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_772,plain,
% 3.58/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.58/0.99      | ~ v1_tdlat_3(X1)
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1)
% 3.58/0.99      | k2_pre_topc(X1,u1_struct_0(X0)) = u1_struct_0(X0) ),
% 3.58/0.99      inference(global_propositional_subsumption,[status(thm)],[c_768,c_20]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_5998,plain,
% 3.58/0.99      ( k2_pre_topc(X0,u1_struct_0(X1)) = u1_struct_0(X1)
% 3.58/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.58/0.99      | v1_tdlat_3(X0) != iProver_top
% 3.58/0.99      | v2_struct_0(X0) = iProver_top
% 3.58/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_772]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_13719,plain,
% 3.58/0.99      ( k2_pre_topc(sK3,u1_struct_0(sK1(sK3,X0))) = u1_struct_0(sK1(sK3,X0))
% 3.58/0.99      | m1_subset_1(X0,u1_pre_topc(sK3)) != iProver_top
% 3.58/0.99      | v1_tdlat_3(sK3) != iProver_top
% 3.58/0.99      | v2_struct_0(sK3) = iProver_top
% 3.58/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.58/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_9186,c_5998]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_51,plain,
% 3.58/0.99      ( v1_tdlat_3(sK3) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_14080,plain,
% 3.58/0.99      ( m1_subset_1(X0,u1_pre_topc(sK3)) != iProver_top
% 3.58/0.99      | k2_pre_topc(sK3,u1_struct_0(sK1(sK3,X0))) = u1_struct_0(sK1(sK3,X0))
% 3.58/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.58/0.99      inference(global_propositional_subsumption,
% 3.58/0.99                [status(thm)],
% 3.58/0.99                [c_13719,c_49,c_51,c_52]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_14081,plain,
% 3.58/0.99      ( k2_pre_topc(sK3,u1_struct_0(sK1(sK3,X0))) = u1_struct_0(sK1(sK3,X0))
% 3.58/0.99      | m1_subset_1(X0,u1_pre_topc(sK3)) != iProver_top
% 3.58/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.58/0.99      inference(renaming,[status(thm)],[c_14080]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_14090,plain,
% 3.58/0.99      ( k2_pre_topc(sK3,u1_struct_0(sK1(sK3,sK4))) = u1_struct_0(sK1(sK3,sK4))
% 3.58/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_7344,c_14081]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_31,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1)
% 3.58/0.99      | v1_xboole_0(X0)
% 3.58/0.99      | u1_struct_0(sK1(X1,X0)) = X0 ),
% 3.58/0.99      inference(cnf_transformation,[],[f165]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6007,plain,
% 3.58/0.99      ( u1_struct_0(sK1(X0,X1)) = X1
% 3.58/0.99      | m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) != iProver_top
% 3.58/0.99      | v2_struct_0(X0) = iProver_top
% 3.58/0.99      | l1_pre_topc(X0) != iProver_top
% 3.58/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_7805,plain,
% 3.58/0.99      ( u1_struct_0(sK1(sK3,X0)) = X0
% 3.58/0.99      | m1_subset_1(X0,u1_pre_topc(sK3)) != iProver_top
% 3.58/0.99      | v2_struct_0(sK3) = iProver_top
% 3.58/0.99      | l1_pre_topc(sK3) != iProver_top
% 3.58/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_7339,c_6007]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_8061,plain,
% 3.58/0.99      ( u1_struct_0(sK1(sK3,X0)) = X0
% 3.58/0.99      | m1_subset_1(X0,u1_pre_topc(sK3)) != iProver_top
% 3.58/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.58/0.99      inference(global_propositional_subsumption,
% 3.58/0.99                [status(thm)],
% 3.58/0.99                [c_7805,c_49,c_52]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_8071,plain,
% 3.58/0.99      ( u1_struct_0(sK1(sK3,sK4)) = sK4 | v1_xboole_0(sK4) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_7344,c_8061]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_5,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0,k9_setfam_1(X1))
% 3.58/0.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.58/0.99      inference(cnf_transformation,[],[f149]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6013,plain,
% 3.58/0.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.58/0.99      | m1_subset_1(X1,k9_setfam_1(X0)) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6591,plain,
% 3.58/0.99      ( k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK4)) = sK4 ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_6003,c_6013]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6,plain,
% 3.58/0.99      ( v1_subset_1(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(X1))
% 3.58/0.99      | ~ v1_xboole_0(X0)
% 3.58/0.99      | v1_xboole_0(X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f150]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_30,plain,
% 3.58/0.99      ( ~ v1_subset_1(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(X1))
% 3.58/0.99      | v1_xboole_0(X1)
% 3.58/0.99      | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
% 3.58/0.99      inference(cnf_transformation,[],[f164]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_7,plain,
% 3.58/0.99      ( ~ v1_subset_1(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(X1))
% 3.58/0.99      | ~ v1_xboole_0(X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f151]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_277,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0,k9_setfam_1(X1))
% 3.58/0.99      | ~ v1_subset_1(X0,X1)
% 3.58/0.99      | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
% 3.58/0.99      inference(global_propositional_subsumption,[status(thm)],[c_30,c_7]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_278,plain,
% 3.58/0.99      ( ~ v1_subset_1(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(X1))
% 3.58/0.99      | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
% 3.58/0.99      inference(renaming,[status(thm)],[c_277]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1045,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0,k9_setfam_1(X1))
% 3.58/0.99      | ~ v1_xboole_0(X0)
% 3.58/0.99      | v1_xboole_0(X1)
% 3.58/0.99      | ~ v1_xboole_0(k3_subset_1(X1,X0)) ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_6,c_278]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_5995,plain,
% 3.58/0.99      ( m1_subset_1(X0,k9_setfam_1(X1)) != iProver_top
% 3.58/0.99      | v1_xboole_0(X0) != iProver_top
% 3.58/0.99      | v1_xboole_0(X1) = iProver_top
% 3.58/0.99      | v1_xboole_0(k3_subset_1(X1,X0)) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_1045]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_12280,plain,
% 3.58/0.99      ( m1_subset_1(X0,u1_pre_topc(sK3)) != iProver_top
% 3.58/0.99      | v1_xboole_0(X0) != iProver_top
% 3.58/0.99      | v1_xboole_0(k3_subset_1(u1_struct_0(sK3),X0)) != iProver_top
% 3.58/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_7339,c_5995]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_47,negated_conjecture,
% 3.58/0.99      ( v2_pre_topc(sK3) ),
% 3.58/0.99      inference(cnf_transformation,[],[f139]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_15,plain,
% 3.58/0.99      ( v2_struct_0(X0)
% 3.58/0.99      | ~ v2_pre_topc(X0)
% 3.58/0.99      | ~ l1_pre_topc(X0)
% 3.58/0.99      | ~ v1_xboole_0(sK0(X0)) ),
% 3.58/0.99      inference(cnf_transformation,[],[f110]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_123,plain,
% 3.58/0.99      ( v2_struct_0(sK3)
% 3.58/0.99      | ~ v2_pre_topc(sK3)
% 3.58/0.99      | ~ l1_pre_topc(sK3)
% 3.58/0.99      | ~ v1_xboole_0(sK0(sK3)) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_16,plain,
% 3.58/0.99      ( m1_subset_1(sK0(X0),k9_setfam_1(u1_struct_0(X0)))
% 3.58/0.99      | v2_struct_0(X0)
% 3.58/0.99      | ~ v2_pre_topc(X0)
% 3.58/0.99      | ~ l1_pre_topc(X0) ),
% 3.58/0.99      inference(cnf_transformation,[],[f155]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1304,plain,
% 3.58/0.99      ( m1_subset_1(sK0(X0),k9_setfam_1(u1_struct_0(X0)))
% 3.58/0.99      | ~ v1_tdlat_3(X0)
% 3.58/0.99      | v2_struct_0(X0)
% 3.58/0.99      | ~ l1_pre_topc(X0) ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_21,c_16]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_8,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0,k9_setfam_1(X1)) | r1_tarski(X0,X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f152]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_0,plain,
% 3.58/0.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.58/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1,plain,
% 3.58/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 3.58/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_615,plain,
% 3.58/0.99      ( ~ r1_tarski(X0,X1) | v1_xboole_0(X0) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.58/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_616,plain,
% 3.58/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0) ),
% 3.58/0.99      inference(unflattening,[status(thm)],[c_615]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_630,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0,k9_setfam_1(X1))
% 3.58/0.99      | v1_xboole_0(X2)
% 3.58/0.99      | X2 != X0
% 3.58/0.99      | k1_xboole_0 != X1 ),
% 3.58/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_616]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_631,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0,k9_setfam_1(k1_xboole_0)) | v1_xboole_0(X0) ),
% 3.58/0.99      inference(unflattening,[status(thm)],[c_630]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_3055,plain,
% 3.58/0.99      ( ~ v1_tdlat_3(X0)
% 3.58/0.99      | v2_struct_0(X0)
% 3.58/0.99      | ~ l1_pre_topc(X0)
% 3.58/0.99      | v1_xboole_0(X1)
% 3.58/0.99      | sK0(X0) != X1
% 3.58/0.99      | k9_setfam_1(u1_struct_0(X0)) != k9_setfam_1(k1_xboole_0) ),
% 3.58/0.99      inference(resolution_lifted,[status(thm)],[c_1304,c_631]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_3056,plain,
% 3.58/0.99      ( ~ v1_tdlat_3(X0)
% 3.58/0.99      | v2_struct_0(X0)
% 3.58/0.99      | ~ l1_pre_topc(X0)
% 3.58/0.99      | v1_xboole_0(sK0(X0))
% 3.58/0.99      | k9_setfam_1(u1_struct_0(X0)) != k9_setfam_1(k1_xboole_0) ),
% 3.58/0.99      inference(unflattening,[status(thm)],[c_3055]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_3058,plain,
% 3.58/0.99      ( ~ v1_tdlat_3(sK3)
% 3.58/0.99      | v2_struct_0(sK3)
% 3.58/0.99      | ~ l1_pre_topc(sK3)
% 3.58/0.99      | v1_xboole_0(sK0(sK3))
% 3.58/0.99      | k9_setfam_1(u1_struct_0(sK3)) != k9_setfam_1(k1_xboole_0) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_3056]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_3,plain,
% 3.58/0.99      ( m1_subset_1(k1_xboole_0,k9_setfam_1(X0)) ),
% 3.58/0.99      inference(cnf_transformation,[],[f147]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6353,plain,
% 3.58/0.99      ( m1_subset_1(k1_xboole_0,k9_setfam_1(u1_struct_0(X0))) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6358,plain,
% 3.58/0.99      ( m1_subset_1(k1_xboole_0,k9_setfam_1(u1_struct_0(X0))) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_6353]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6360,plain,
% 3.58/0.99      ( m1_subset_1(k1_xboole_0,k9_setfam_1(u1_struct_0(sK3))) = iProver_top ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_6358]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_28,plain,
% 3.58/0.99      ( v1_subset_1(X0,X1) | ~ m1_subset_1(X0,k9_setfam_1(X1)) | X0 = X1 ),
% 3.58/0.99      inference(cnf_transformation,[],[f162]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1031,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0,k9_setfam_1(X1)) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_28,c_7]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6622,plain,
% 3.58/0.99      ( ~ m1_subset_1(k1_xboole_0,k9_setfam_1(X0))
% 3.58/0.99      | ~ v1_xboole_0(X0)
% 3.58/0.99      | X0 = k1_xboole_0 ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_1031]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6949,plain,
% 3.58/0.99      ( ~ m1_subset_1(k1_xboole_0,k9_setfam_1(u1_struct_0(sK3)))
% 3.58/0.99      | ~ v1_xboole_0(u1_struct_0(sK3))
% 3.58/0.99      | u1_struct_0(sK3) = k1_xboole_0 ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_6622]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6950,plain,
% 3.58/0.99      ( u1_struct_0(sK3) = k1_xboole_0
% 3.58/0.99      | m1_subset_1(k1_xboole_0,k9_setfam_1(u1_struct_0(sK3))) != iProver_top
% 3.58/0.99      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_6949]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_5326,plain,
% 3.58/0.99      ( X0 != X1 | k9_setfam_1(X0) = k9_setfam_1(X1) ),
% 3.58/0.99      theory(equality) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_7496,plain,
% 3.58/0.99      ( u1_struct_0(sK3) != X0
% 3.58/0.99      | k9_setfam_1(u1_struct_0(sK3)) = k9_setfam_1(X0) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_5326]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_11227,plain,
% 3.58/0.99      ( u1_struct_0(sK3) != k1_xboole_0
% 3.58/0.99      | k9_setfam_1(u1_struct_0(sK3)) = k9_setfam_1(k1_xboole_0) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_7496]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_12832,plain,
% 3.58/0.99      ( v1_xboole_0(k3_subset_1(u1_struct_0(sK3),X0)) != iProver_top
% 3.58/0.99      | v1_xboole_0(X0) != iProver_top
% 3.58/0.99      | m1_subset_1(X0,u1_pre_topc(sK3)) != iProver_top ),
% 3.58/0.99      inference(global_propositional_subsumption,
% 3.58/0.99                [status(thm)],
% 3.58/0.99                [c_12280,c_48,c_47,c_46,c_45,c_123,c_3058,c_6360,c_6950,
% 3.58/0.99                 c_11227]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_12833,plain,
% 3.58/0.99      ( m1_subset_1(X0,u1_pre_topc(sK3)) != iProver_top
% 3.58/0.99      | v1_xboole_0(X0) != iProver_top
% 3.58/0.99      | v1_xboole_0(k3_subset_1(u1_struct_0(sK3),X0)) != iProver_top ),
% 3.58/0.99      inference(renaming,[status(thm)],[c_12832]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_12843,plain,
% 3.58/0.99      ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK4),u1_pre_topc(sK3)) != iProver_top
% 3.58/0.99      | v1_xboole_0(k3_subset_1(u1_struct_0(sK3),sK4)) != iProver_top
% 3.58/0.99      | v1_xboole_0(sK4) != iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_6591,c_12833]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_39,plain,
% 3.58/0.99      ( ~ v3_tex_2(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ v2_pre_topc(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1)
% 3.58/0.99      | ~ v1_xboole_0(X0) ),
% 3.58/0.99      inference(cnf_transformation,[],[f172]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1338,plain,
% 3.58/0.99      ( ~ v3_tex_2(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ v1_tdlat_3(X2)
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ l1_pre_topc(X2)
% 3.58/0.99      | ~ l1_pre_topc(X1)
% 3.58/0.99      | ~ v1_xboole_0(X0)
% 3.58/0.99      | X1 != X2 ),
% 3.58/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_39]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1339,plain,
% 3.58/0.99      ( ~ v3_tex_2(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ v1_tdlat_3(X1)
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1)
% 3.58/0.99      | ~ v1_xboole_0(X0) ),
% 3.58/0.99      inference(unflattening,[status(thm)],[c_1338]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_43,negated_conjecture,
% 3.58/0.99      ( v3_tex_2(sK4,sK3) | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.58/0.99      inference(cnf_transformation,[],[f143]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_373,plain,
% 3.58/0.99      ( v3_tex_2(sK4,sK3) | ~ v1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.58/0.99      inference(prop_impl,[status(thm)],[c_43]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1080,plain,
% 3.58/0.99      ( v3_tex_2(sK4,sK3)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(X1))
% 3.58/0.99      | ~ v1_xboole_0(X0)
% 3.58/0.99      | v1_xboole_0(X1)
% 3.58/0.99      | u1_struct_0(sK3) != X1
% 3.58/0.99      | sK4 != X0 ),
% 3.58/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_373]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1081,plain,
% 3.58/0.99      ( v3_tex_2(sK4,sK3)
% 3.58/0.99      | ~ m1_subset_1(sK4,k9_setfam_1(u1_struct_0(sK3)))
% 3.58/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 3.58/0.99      | ~ v1_xboole_0(sK4) ),
% 3.58/0.99      inference(unflattening,[status(thm)],[c_1080]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1083,plain,
% 3.58/0.99      ( v3_tex_2(sK4,sK3)
% 3.58/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 3.58/0.99      | ~ v1_xboole_0(sK4) ),
% 3.58/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1081,c_44]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1757,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ v1_tdlat_3(X1)
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1)
% 3.58/0.99      | ~ v1_xboole_0(X0)
% 3.58/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 3.58/0.99      | ~ v1_xboole_0(sK4)
% 3.58/0.99      | sK3 != X1
% 3.58/0.99      | sK4 != X0 ),
% 3.58/0.99      inference(resolution_lifted,[status(thm)],[c_1339,c_1083]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1758,plain,
% 3.58/0.99      ( ~ m1_subset_1(sK4,k9_setfam_1(u1_struct_0(sK3)))
% 3.58/0.99      | ~ v1_tdlat_3(sK3)
% 3.58/0.99      | v2_struct_0(sK3)
% 3.58/0.99      | ~ l1_pre_topc(sK3)
% 3.58/0.99      | v1_xboole_0(u1_struct_0(sK3))
% 3.58/0.99      | ~ v1_xboole_0(sK4) ),
% 3.58/0.99      inference(unflattening,[status(thm)],[c_1757]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1760,plain,
% 3.58/0.99      ( v1_xboole_0(u1_struct_0(sK3)) | ~ v1_xboole_0(sK4) ),
% 3.58/0.99      inference(global_propositional_subsumption,
% 3.58/0.99                [status(thm)],
% 3.58/0.99                [c_1758,c_48,c_46,c_45,c_44]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_5981,plain,
% 3.58/0.99      ( v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 3.58/0.99      | v1_xboole_0(sK4) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_1760]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6015,plain,
% 3.58/0.99      ( m1_subset_1(k1_xboole_0,k9_setfam_1(X0)) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_5996,plain,
% 3.58/0.99      ( X0 = X1
% 3.58/0.99      | m1_subset_1(X1,k9_setfam_1(X0)) != iProver_top
% 3.58/0.99      | v1_xboole_0(X0) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_1031]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_8850,plain,
% 3.58/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_6015,c_5996]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_9008,plain,
% 3.58/0.99      ( u1_struct_0(sK3) = k1_xboole_0 | v1_xboole_0(sK4) != iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_5981,c_8850]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_12867,plain,
% 3.58/0.99      ( v1_xboole_0(sK4) != iProver_top ),
% 3.58/0.99      inference(global_propositional_subsumption,
% 3.58/0.99                [status(thm)],
% 3.58/0.99                [c_12843,c_48,c_47,c_46,c_45,c_123,c_3058,c_9008,c_11227]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_12873,plain,
% 3.58/0.99      ( u1_struct_0(sK1(sK3,sK4)) = sK4 ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_8071,c_12867]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_14106,plain,
% 3.58/0.99      ( k2_pre_topc(sK3,sK4) = sK4 | v1_xboole_0(sK4) = iProver_top ),
% 3.58/0.99      inference(light_normalisation,[status(thm)],[c_14090,c_12873]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_14145,plain,
% 3.58/0.99      ( k2_pre_topc(sK3,sK4) = sK4 ),
% 3.58/0.99      inference(global_propositional_subsumption,
% 3.58/0.99                [status(thm)],
% 3.58/0.99                [c_14106,c_48,c_47,c_46,c_45,c_123,c_3058,c_9008,c_11227]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_26,plain,
% 3.58/0.99      ( v1_tops_1(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ l1_pre_topc(X1)
% 3.58/0.99      | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f160]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_38,plain,
% 3.58/0.99      ( v2_tex_2(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ v1_tdlat_3(X1)
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ v2_pre_topc(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f171]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_41,plain,
% 3.58/0.99      ( v3_tex_2(X0,X1)
% 3.58/0.99      | ~ v2_tex_2(X0,X1)
% 3.58/0.99      | ~ v1_tops_1(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ v2_pre_topc(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f174]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_675,plain,
% 3.58/0.99      ( v3_tex_2(X0,X1)
% 3.58/0.99      | ~ v1_tops_1(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ v1_tdlat_3(X1)
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ v2_pre_topc(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1) ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_38,c_41]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_693,plain,
% 3.58/0.99      ( v3_tex_2(X0,X1)
% 3.58/0.99      | ~ v1_tops_1(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ v1_tdlat_3(X1)
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1) ),
% 3.58/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_675,c_21]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1192,plain,
% 3.58/0.99      ( v3_tex_2(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ v1_tdlat_3(X1)
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1)
% 3.58/0.99      | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_26,c_693]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_29,plain,
% 3.58/0.99      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k9_setfam_1(X0)) ),
% 3.58/0.99      inference(cnf_transformation,[],[f179]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_42,negated_conjecture,
% 3.58/0.99      ( ~ v3_tex_2(sK4,sK3) | v1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.58/0.99      inference(cnf_transformation,[],[f144]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_375,plain,
% 3.58/0.99      ( ~ v3_tex_2(sK4,sK3) | v1_subset_1(sK4,u1_struct_0(sK3)) ),
% 3.58/0.99      inference(prop_impl,[status(thm)],[c_42]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1125,plain,
% 3.58/0.99      ( ~ v3_tex_2(sK4,sK3)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(X0))
% 3.58/0.99      | u1_struct_0(sK3) != X0
% 3.58/0.99      | sK4 != X0 ),
% 3.58/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_375]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1126,plain,
% 3.58/0.99      ( ~ v3_tex_2(sK4,sK3)
% 3.58/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k9_setfam_1(u1_struct_0(sK3)))
% 3.58/0.99      | sK4 != u1_struct_0(sK3) ),
% 3.58/0.99      inference(unflattening,[status(thm)],[c_1125]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1712,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ m1_subset_1(u1_struct_0(sK3),k9_setfam_1(u1_struct_0(sK3)))
% 3.58/0.99      | ~ v1_tdlat_3(X1)
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1)
% 3.58/0.99      | k2_pre_topc(X1,X0) != u1_struct_0(X1)
% 3.58/0.99      | u1_struct_0(sK3) != sK4
% 3.58/0.99      | sK3 != X1
% 3.58/0.99      | sK4 != X0 ),
% 3.58/0.99      inference(resolution_lifted,[status(thm)],[c_1192,c_1126]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1713,plain,
% 3.58/0.99      ( ~ m1_subset_1(u1_struct_0(sK3),k9_setfam_1(u1_struct_0(sK3)))
% 3.58/0.99      | ~ m1_subset_1(sK4,k9_setfam_1(u1_struct_0(sK3)))
% 3.58/0.99      | ~ v1_tdlat_3(sK3)
% 3.58/0.99      | v2_struct_0(sK3)
% 3.58/0.99      | ~ l1_pre_topc(sK3)
% 3.58/0.99      | k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
% 3.58/0.99      | u1_struct_0(sK3) != sK4 ),
% 3.58/0.99      inference(unflattening,[status(thm)],[c_1712]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1715,plain,
% 3.58/0.99      ( ~ m1_subset_1(u1_struct_0(sK3),k9_setfam_1(u1_struct_0(sK3)))
% 3.58/0.99      | k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
% 3.58/0.99      | u1_struct_0(sK3) != sK4 ),
% 3.58/0.99      inference(global_propositional_subsumption,
% 3.58/0.99                [status(thm)],
% 3.58/0.99                [c_1713,c_48,c_46,c_45,c_44]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_5984,plain,
% 3.58/0.99      ( k2_pre_topc(sK3,sK4) != u1_struct_0(sK3)
% 3.58/0.99      | u1_struct_0(sK3) != sK4
% 3.58/0.99      | m1_subset_1(u1_struct_0(sK3),k9_setfam_1(u1_struct_0(sK3))) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_1715]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_4,plain,
% 3.58/0.99      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k9_setfam_1(X0)) ),
% 3.58/0.99      inference(cnf_transformation,[],[f148]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6014,plain,
% 3.58/0.99      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k9_setfam_1(X0)) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2,plain,
% 3.58/0.99      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.58/0.99      inference(cnf_transformation,[],[f146]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6034,plain,
% 3.58/0.99      ( m1_subset_1(X0,k9_setfam_1(X0)) = iProver_top ),
% 3.58/0.99      inference(light_normalisation,[status(thm)],[c_6014,c_2]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6135,plain,
% 3.58/0.99      ( k2_pre_topc(sK3,sK4) != u1_struct_0(sK3) | u1_struct_0(sK3) != sK4 ),
% 3.58/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5984,c_6034]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_14148,plain,
% 3.58/0.99      ( u1_struct_0(sK3) != sK4 ),
% 3.58/0.99      inference(demodulation,[status(thm)],[c_14145,c_6135]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_37,plain,
% 3.58/0.99      ( v3_pre_topc(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ v1_tdlat_3(X1)
% 3.58/0.99      | ~ v2_pre_topc(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f170]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_40,plain,
% 3.58/0.99      ( ~ v3_tex_2(X0,X1)
% 3.58/0.99      | v1_tops_1(X0,X1)
% 3.58/0.99      | ~ v3_pre_topc(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ v2_pre_topc(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f173]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_922,plain,
% 3.58/0.99      ( ~ v3_tex_2(X0,X1)
% 3.58/0.99      | v1_tops_1(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ v1_tdlat_3(X1)
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ v2_pre_topc(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1) ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_37,c_40]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_940,plain,
% 3.58/0.99      ( ~ v3_tex_2(X0,X1)
% 3.58/0.99      | v1_tops_1(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ v1_tdlat_3(X1)
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1) ),
% 3.58/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_922,c_21]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_27,plain,
% 3.58/0.99      ( ~ v1_tops_1(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ l1_pre_topc(X1)
% 3.58/0.99      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f161]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1169,plain,
% 3.58/0.99      ( ~ v3_tex_2(X0,X1)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ v1_tdlat_3(X1)
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1)
% 3.58/0.99      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_940,c_27]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1066,plain,
% 3.58/0.99      ( v3_tex_2(sK4,sK3)
% 3.58/0.99      | ~ m1_subset_1(X0,k9_setfam_1(X1))
% 3.58/0.99      | X1 = X0
% 3.58/0.99      | u1_struct_0(sK3) != X1
% 3.58/0.99      | sK4 != X0 ),
% 3.58/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_373]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1067,plain,
% 3.58/0.99      ( v3_tex_2(sK4,sK3)
% 3.58/0.99      | ~ m1_subset_1(sK4,k9_setfam_1(u1_struct_0(sK3)))
% 3.58/0.99      | u1_struct_0(sK3) = sK4 ),
% 3.58/0.99      inference(unflattening,[status(thm)],[c_1066]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1069,plain,
% 3.58/0.99      ( v3_tex_2(sK4,sK3) | u1_struct_0(sK3) = sK4 ),
% 3.58/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1067,c_44]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1787,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
% 3.58/0.99      | ~ v1_tdlat_3(X1)
% 3.58/0.99      | v2_struct_0(X1)
% 3.58/0.99      | ~ l1_pre_topc(X1)
% 3.58/0.99      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 3.58/0.99      | u1_struct_0(sK3) = sK4
% 3.58/0.99      | sK3 != X1
% 3.58/0.99      | sK4 != X0 ),
% 3.58/0.99      inference(resolution_lifted,[status(thm)],[c_1169,c_1069]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1788,plain,
% 3.58/0.99      ( ~ m1_subset_1(sK4,k9_setfam_1(u1_struct_0(sK3)))
% 3.58/0.99      | ~ v1_tdlat_3(sK3)
% 3.58/0.99      | v2_struct_0(sK3)
% 3.58/0.99      | ~ l1_pre_topc(sK3)
% 3.58/0.99      | k2_pre_topc(sK3,sK4) = u1_struct_0(sK3)
% 3.58/0.99      | u1_struct_0(sK3) = sK4 ),
% 3.58/0.99      inference(unflattening,[status(thm)],[c_1787]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1790,plain,
% 3.58/0.99      ( k2_pre_topc(sK3,sK4) = u1_struct_0(sK3) | u1_struct_0(sK3) = sK4 ),
% 3.58/0.99      inference(global_propositional_subsumption,
% 3.58/0.99                [status(thm)],
% 3.58/0.99                [c_1788,c_48,c_46,c_45,c_44]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_14151,plain,
% 3.58/0.99      ( u1_struct_0(sK3) = sK4 ),
% 3.58/0.99      inference(demodulation,[status(thm)],[c_14145,c_1790]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_14159,plain,
% 3.58/0.99      ( sK4 != sK4 ),
% 3.58/0.99      inference(light_normalisation,[status(thm)],[c_14148,c_14151]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_14160,plain,
% 3.58/0.99      ( $false ),
% 3.58/0.99      inference(equality_resolution_simp,[status(thm)],[c_14159]) ).
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.58/0.99  
% 3.58/0.99  ------                               Statistics
% 3.58/0.99  
% 3.58/0.99  ------ General
% 3.58/0.99  
% 3.58/0.99  abstr_ref_over_cycles:                  0
% 3.58/0.99  abstr_ref_under_cycles:                 0
% 3.58/0.99  gc_basic_clause_elim:                   0
% 3.58/0.99  forced_gc_time:                         0
% 3.58/0.99  parsing_time:                           0.012
% 3.58/0.99  unif_index_cands_time:                  0.
% 3.58/0.99  unif_index_add_time:                    0.
% 3.58/0.99  orderings_time:                         0.
% 3.58/0.99  out_proof_time:                         0.014
% 3.58/0.99  total_time:                             0.321
% 3.58/0.99  num_of_symbols:                         60
% 3.58/0.99  num_of_terms:                           7883
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing
% 3.58/0.99  
% 3.58/0.99  num_of_splits:                          0
% 3.58/0.99  num_of_split_atoms:                     0
% 3.58/0.99  num_of_reused_defs:                     0
% 3.58/0.99  num_eq_ax_congr_red:                    26
% 3.58/0.99  num_of_sem_filtered_clauses:            1
% 3.58/0.99  num_of_subtypes:                        0
% 3.58/0.99  monotx_restored_types:                  0
% 3.58/0.99  sat_num_of_epr_types:                   0
% 3.58/0.99  sat_num_of_non_cyclic_types:            0
% 3.58/0.99  sat_guarded_non_collapsed_types:        0
% 3.58/0.99  num_pure_diseq_elim:                    0
% 3.58/0.99  simp_replaced_by:                       0
% 3.58/0.99  res_preprocessed:                       202
% 3.58/0.99  prep_upred:                             0
% 3.58/0.99  prep_unflattend:                        226
% 3.58/0.99  smt_new_axioms:                         0
% 3.58/0.99  pred_elim_cands:                        7
% 3.58/0.99  pred_elim:                              10
% 3.58/0.99  pred_elim_cl:                           7
% 3.58/0.99  pred_elim_cycles:                       17
% 3.58/0.99  merged_defs:                            2
% 3.58/0.99  merged_defs_ncl:                        0
% 3.58/0.99  bin_hyper_res:                          2
% 3.58/0.99  prep_cycles:                            4
% 3.58/0.99  pred_elim_time:                         0.074
% 3.58/0.99  splitting_time:                         0.
% 3.58/0.99  sem_filter_time:                        0.
% 3.58/0.99  monotx_time:                            0.
% 3.58/0.99  subtype_inf_time:                       0.
% 3.58/0.99  
% 3.58/0.99  ------ Problem properties
% 3.58/0.99  
% 3.58/0.99  clauses:                                41
% 3.58/0.99  conjectures:                            4
% 3.58/0.99  epr:                                    6
% 3.58/0.99  horn:                                   31
% 3.58/0.99  ground:                                 16
% 3.58/0.99  unary:                                  10
% 3.58/0.99  binary:                                 10
% 3.58/0.99  lits:                                   112
% 3.58/0.99  lits_eq:                                25
% 3.58/0.99  fd_pure:                                0
% 3.58/0.99  fd_pseudo:                              0
% 3.58/0.99  fd_cond:                                0
% 3.58/0.99  fd_pseudo_cond:                         2
% 3.58/0.99  ac_symbols:                             0
% 3.58/0.99  
% 3.58/0.99  ------ Propositional Solver
% 3.58/0.99  
% 3.58/0.99  prop_solver_calls:                      28
% 3.58/0.99  prop_fast_solver_calls:                 2694
% 3.58/0.99  smt_solver_calls:                       0
% 3.58/0.99  smt_fast_solver_calls:                  0
% 3.58/0.99  prop_num_of_clauses:                    3714
% 3.58/0.99  prop_preprocess_simplified:             11524
% 3.58/0.99  prop_fo_subsumed:                       139
% 3.58/0.99  prop_solver_time:                       0.
% 3.58/0.99  smt_solver_time:                        0.
% 3.58/0.99  smt_fast_solver_time:                   0.
% 3.58/0.99  prop_fast_solver_time:                  0.
% 3.58/0.99  prop_unsat_core_time:                   0.
% 3.58/0.99  
% 3.58/0.99  ------ QBF
% 3.58/0.99  
% 3.58/0.99  qbf_q_res:                              0
% 3.58/0.99  qbf_num_tautologies:                    0
% 3.58/0.99  qbf_prep_cycles:                        0
% 3.58/0.99  
% 3.58/0.99  ------ BMC1
% 3.58/0.99  
% 3.58/0.99  bmc1_current_bound:                     -1
% 3.58/0.99  bmc1_last_solved_bound:                 -1
% 3.58/0.99  bmc1_unsat_core_size:                   -1
% 3.58/0.99  bmc1_unsat_core_parents_size:           -1
% 3.58/0.99  bmc1_merge_next_fun:                    0
% 3.58/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.58/0.99  
% 3.58/0.99  ------ Instantiation
% 3.58/0.99  
% 3.58/0.99  inst_num_of_clauses:                    996
% 3.58/0.99  inst_num_in_passive:                    464
% 3.58/0.99  inst_num_in_active:                     485
% 3.58/0.99  inst_num_in_unprocessed:                48
% 3.58/0.99  inst_num_of_loops:                      580
% 3.58/0.99  inst_num_of_learning_restarts:          0
% 3.58/0.99  inst_num_moves_active_passive:          92
% 3.58/0.99  inst_lit_activity:                      0
% 3.58/0.99  inst_lit_activity_moves:                0
% 3.58/0.99  inst_num_tautologies:                   0
% 3.58/0.99  inst_num_prop_implied:                  0
% 3.58/0.99  inst_num_existing_simplified:           0
% 3.58/0.99  inst_num_eq_res_simplified:             0
% 3.58/0.99  inst_num_child_elim:                    0
% 3.58/0.99  inst_num_of_dismatching_blockings:      513
% 3.58/0.99  inst_num_of_non_proper_insts:           1044
% 3.58/0.99  inst_num_of_duplicates:                 0
% 3.58/0.99  inst_inst_num_from_inst_to_res:         0
% 3.58/0.99  inst_dismatching_checking_time:         0.
% 3.58/0.99  
% 3.58/0.99  ------ Resolution
% 3.58/0.99  
% 3.58/0.99  res_num_of_clauses:                     0
% 3.58/0.99  res_num_in_passive:                     0
% 3.58/0.99  res_num_in_active:                      0
% 3.58/0.99  res_num_of_loops:                       206
% 3.58/0.99  res_forward_subset_subsumed:            142
% 3.58/0.99  res_backward_subset_subsumed:           2
% 3.58/0.99  res_forward_subsumed:                   6
% 3.58/0.99  res_backward_subsumed:                  2
% 3.58/0.99  res_forward_subsumption_resolution:     5
% 3.58/0.99  res_backward_subsumption_resolution:    0
% 3.58/0.99  res_clause_to_clause_subsumption:       535
% 3.58/0.99  res_orphan_elimination:                 0
% 3.58/0.99  res_tautology_del:                      94
% 3.58/0.99  res_num_eq_res_simplified:              0
% 3.58/0.99  res_num_sel_changes:                    0
% 3.58/0.99  res_moves_from_active_to_pass:          0
% 3.58/0.99  
% 3.58/0.99  ------ Superposition
% 3.58/0.99  
% 3.58/0.99  sup_time_total:                         0.
% 3.58/0.99  sup_time_generating:                    0.
% 3.58/0.99  sup_time_sim_full:                      0.
% 3.58/0.99  sup_time_sim_immed:                     0.
% 3.58/0.99  
% 3.58/0.99  sup_num_of_clauses:                     196
% 3.58/0.99  sup_num_in_active:                      100
% 3.58/0.99  sup_num_in_passive:                     96
% 3.58/0.99  sup_num_of_loops:                       114
% 3.58/0.99  sup_fw_superposition:                   156
% 3.58/0.99  sup_bw_superposition:                   95
% 3.58/0.99  sup_immediate_simplified:               72
% 3.58/0.99  sup_given_eliminated:                   0
% 3.58/0.99  comparisons_done:                       0
% 3.58/0.99  comparisons_avoided:                    0
% 3.58/0.99  
% 3.58/0.99  ------ Simplifications
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  sim_fw_subset_subsumed:                 32
% 3.58/0.99  sim_bw_subset_subsumed:                 11
% 3.58/0.99  sim_fw_subsumed:                        11
% 3.58/0.99  sim_bw_subsumed:                        1
% 3.58/0.99  sim_fw_subsumption_res:                 1
% 3.58/0.99  sim_bw_subsumption_res:                 0
% 3.58/0.99  sim_tautology_del:                      6
% 3.58/0.99  sim_eq_tautology_del:                   12
% 3.58/0.99  sim_eq_res_simp:                        1
% 3.58/0.99  sim_fw_demodulated:                     4
% 3.58/0.99  sim_bw_demodulated:                     10
% 3.58/0.99  sim_light_normalised:                   33
% 3.58/0.99  sim_joinable_taut:                      0
% 3.58/0.99  sim_joinable_simp:                      0
% 3.58/0.99  sim_ac_normalised:                      0
% 3.58/0.99  sim_smt_subsumption:                    0
% 3.58/0.99  
%------------------------------------------------------------------------------
