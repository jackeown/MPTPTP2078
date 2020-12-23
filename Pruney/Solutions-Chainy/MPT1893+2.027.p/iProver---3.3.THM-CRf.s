%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:42 EST 2020

% Result     : Theorem 0.96s
% Output     : CNFRefutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 672 expanded)
%              Number of clauses        :   62 ( 153 expanded)
%              Number of leaves         :   14 ( 180 expanded)
%              Depth                    :   21
%              Number of atoms          :  657 (5062 expanded)
%              Number of equality atoms :   78 ( 130 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_struct_0(X0) = X1
           => ( v2_tex_2(X1,X0)
            <=> v1_tdlat_3(X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_tdlat_3(X0) )
            & ( v1_tdlat_3(X0)
              | ~ v2_tex_2(X1,X0) ) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X0)
      | ~ v2_tex_2(X1,X0)
      | u1_struct_0(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ~ v2_tex_2(u1_struct_0(X0),X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f8,axiom,(
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

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( v1_subset_1(X1,u1_struct_0(X0))
              & v3_tex_2(X1,X0)
              & ( v4_pre_topc(X1,X0)
                | v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( v1_subset_1(X1,u1_struct_0(X0))
                & v3_tex_2(X1,X0)
                & ( v4_pre_topc(X1,X0)
                  | v3_pre_topc(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v1_subset_1(sK4,u1_struct_0(X0))
        & v3_tex_2(sK4,X0)
        & ( v4_pre_topc(sK4,X0)
          | v3_pre_topc(sK4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_subset_1(X1,u1_struct_0(X0))
            & v3_tex_2(X1,X0)
            & ( v4_pre_topc(X1,X0)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(sK3))
          & v3_tex_2(X1,sK3)
          & ( v4_pre_topc(X1,sK3)
            | v3_pre_topc(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3)
      & v3_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK3))
    & v3_tex_2(sK4,sK3)
    & ( v4_pre_topc(sK4,sK3)
      | v3_pre_topc(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v3_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f27,f45,f44])).

fof(f77,plain,(
    v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,
    ( v4_pre_topc(sK4,sK3)
    | v3_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
             => v4_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK1(X0),X0)
        & v3_pre_topc(sK1(X0),X0)
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v4_pre_topc(sK1(X0),X0)
            & v3_pre_topc(sK1(X0),X0)
            & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f57,plain,(
    ! [X2,X0] :
      ( v4_pre_topc(X2,X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    v3_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0),X0)
        & v4_pre_topc(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK2(X0),X0)
            & v4_pre_topc(sK2(X0),X0)
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f61,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
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

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
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

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

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

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_19,plain,
    ( ~ v2_tex_2(u1_struct_0(X0),X0)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_22,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(X1))
    | ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_23,negated_conjecture,
    ( v1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_410,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_struct_0(X1) != u1_struct_0(sK3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_23])).

cnf(c_411,plain,
    ( ~ v3_tex_2(sK4,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_445,plain,
    ( ~ v2_tex_2(u1_struct_0(X0),X0)
    | ~ v3_tex_2(sK4,X0)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_19,c_411])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_508,plain,
    ( ~ v2_tex_2(u1_struct_0(X0),X0)
    | ~ v3_tex_2(sK4,X0)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_445,c_30])).

cnf(c_509,plain,
    ( ~ v2_tex_2(u1_struct_0(sK3),sK3)
    | ~ v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_24,negated_conjecture,
    ( v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_447,plain,
    ( ~ v2_tex_2(u1_struct_0(sK3),sK3)
    | ~ v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_445])).

cnf(c_511,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(u1_struct_0(sK3),sK3)
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_509,c_30,c_29,c_27,c_26,c_24,c_447])).

cnf(c_512,plain,
    ( ~ v2_tex_2(u1_struct_0(sK3),sK3)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(renaming,[status(thm)],[c_511])).

cnf(c_950,plain,
    ( ~ v2_tex_2(u1_struct_0(sK3),sK3)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(equality_resolution_simp,[status(thm)],[c_512])).

cnf(c_1083,plain,
    ( ~ v2_tex_2(u1_struct_0(sK3),sK3)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_950])).

cnf(c_1272,plain,
    ( v2_tex_2(u1_struct_0(sK3),sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1083])).

cnf(c_25,negated_conjecture,
    ( v3_pre_topc(sK4,sK3)
    | v4_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_13,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v4_pre_topc(X0,X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_555,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v4_pre_topc(X0,X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_556,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v4_pre_topc(X0,sK3)
    | ~ v3_tdlat_3(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_28,negated_conjecture,
    ( v3_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_560,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v4_pre_topc(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_556,c_28,c_27])).

cnf(c_639,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v4_pre_topc(X0,sK3)
    | v4_pre_topc(sK4,sK3)
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_560])).

cnf(c_640,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v4_pre_topc(sK4,sK3) ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_642,plain,
    ( v4_pre_topc(sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_640,c_26])).

cnf(c_17,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_534,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_29])).

cnf(c_535,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v4_pre_topc(X0,sK3)
    | ~ v3_tdlat_3(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_539,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v4_pre_topc(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_28,c_27])).

cnf(c_20,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_374,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_20,c_3])).

cnf(c_484,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_374,c_30])).

cnf(c_485,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v3_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | k2_pre_topc(sK3,X0) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_489,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v3_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_485,c_29,c_27])).

cnf(c_622,plain,
    ( ~ v3_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v4_pre_topc(X0,sK3)
    | k2_pre_topc(sK3,X0) = u1_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_539,c_489])).

cnf(c_686,plain,
    ( ~ v3_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,X0) = u1_struct_0(sK3)
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_642,c_622])).

cnf(c_687,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_pre_topc(sK3,sK4) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_686])).

cnf(c_689,plain,
    ( k2_pre_topc(sK3,sK4) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_687,c_26,c_24])).

cnf(c_1088,plain,
    ( k2_pre_topc(sK3,sK4) = u1_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_689])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_676,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_642])).

cnf(c_677,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | k2_pre_topc(sK3,sK4) = sK4 ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_679,plain,
    ( k2_pre_topc(sK3,sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_677,c_27,c_26])).

cnf(c_1089,plain,
    ( k2_pre_topc(sK3,sK4) = sK4 ),
    inference(subtyping,[status(esa)],[c_679])).

cnf(c_1277,plain,
    ( u1_struct_0(sK3) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_1088,c_1089])).

cnf(c_1283,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1272,c_1277])).

cnf(c_1091,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1266,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1091])).

cnf(c_1280,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1266,c_1277])).

cnf(c_1286,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1283,c_1280])).

cnf(c_9,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_701,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_27])).

cnf(c_702,plain,
    ( v2_tex_2(X0,sK3)
    | ~ v3_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_701])).

cnf(c_908,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_702])).

cnf(c_909,plain,
    ( v2_tex_2(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_908])).

cnf(c_910,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_909])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1286,c_910,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n020.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 11:34:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 0.96/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.96/0.92  
% 0.96/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.96/0.92  
% 0.96/0.92  ------  iProver source info
% 0.96/0.92  
% 0.96/0.92  git: date: 2020-06-30 10:37:57 +0100
% 0.96/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.96/0.92  git: non_committed_changes: false
% 0.96/0.92  git: last_make_outside_of_git: false
% 0.96/0.92  
% 0.96/0.92  ------ 
% 0.96/0.92  
% 0.96/0.92  ------ Input Options
% 0.96/0.92  
% 0.96/0.92  --out_options                           all
% 0.96/0.92  --tptp_safe_out                         true
% 0.96/0.92  --problem_path                          ""
% 0.96/0.92  --include_path                          ""
% 0.96/0.92  --clausifier                            res/vclausify_rel
% 0.96/0.92  --clausifier_options                    --mode clausify
% 0.96/0.92  --stdin                                 false
% 0.96/0.92  --stats_out                             all
% 0.96/0.92  
% 0.96/0.92  ------ General Options
% 0.96/0.92  
% 0.96/0.92  --fof                                   false
% 0.96/0.92  --time_out_real                         305.
% 0.96/0.92  --time_out_virtual                      -1.
% 0.96/0.92  --symbol_type_check                     false
% 0.96/0.92  --clausify_out                          false
% 0.96/0.92  --sig_cnt_out                           false
% 0.96/0.92  --trig_cnt_out                          false
% 0.96/0.92  --trig_cnt_out_tolerance                1.
% 0.96/0.92  --trig_cnt_out_sk_spl                   false
% 0.96/0.92  --abstr_cl_out                          false
% 0.96/0.92  
% 0.96/0.92  ------ Global Options
% 0.96/0.92  
% 0.96/0.92  --schedule                              default
% 0.96/0.92  --add_important_lit                     false
% 0.96/0.92  --prop_solver_per_cl                    1000
% 0.96/0.92  --min_unsat_core                        false
% 0.96/0.92  --soft_assumptions                      false
% 0.96/0.92  --soft_lemma_size                       3
% 0.96/0.92  --prop_impl_unit_size                   0
% 0.96/0.92  --prop_impl_unit                        []
% 0.96/0.92  --share_sel_clauses                     true
% 0.96/0.92  --reset_solvers                         false
% 0.96/0.92  --bc_imp_inh                            [conj_cone]
% 0.96/0.92  --conj_cone_tolerance                   3.
% 0.96/0.92  --extra_neg_conj                        none
% 0.96/0.92  --large_theory_mode                     true
% 0.96/0.92  --prolific_symb_bound                   200
% 0.96/0.92  --lt_threshold                          2000
% 0.96/0.92  --clause_weak_htbl                      true
% 0.96/0.92  --gc_record_bc_elim                     false
% 0.96/0.92  
% 0.96/0.92  ------ Preprocessing Options
% 0.96/0.92  
% 0.96/0.92  --preprocessing_flag                    true
% 0.96/0.92  --time_out_prep_mult                    0.1
% 0.96/0.92  --splitting_mode                        input
% 0.96/0.92  --splitting_grd                         true
% 0.96/0.92  --splitting_cvd                         false
% 0.96/0.92  --splitting_cvd_svl                     false
% 0.96/0.92  --splitting_nvd                         32
% 0.96/0.92  --sub_typing                            true
% 0.96/0.92  --prep_gs_sim                           true
% 0.96/0.92  --prep_unflatten                        true
% 0.96/0.92  --prep_res_sim                          true
% 0.96/0.92  --prep_upred                            true
% 0.96/0.92  --prep_sem_filter                       exhaustive
% 0.96/0.92  --prep_sem_filter_out                   false
% 0.96/0.92  --pred_elim                             true
% 0.96/0.92  --res_sim_input                         true
% 0.96/0.92  --eq_ax_congr_red                       true
% 0.96/0.92  --pure_diseq_elim                       true
% 0.96/0.92  --brand_transform                       false
% 0.96/0.92  --non_eq_to_eq                          false
% 0.96/0.92  --prep_def_merge                        true
% 0.96/0.92  --prep_def_merge_prop_impl              false
% 0.96/0.92  --prep_def_merge_mbd                    true
% 0.96/0.92  --prep_def_merge_tr_red                 false
% 0.96/0.92  --prep_def_merge_tr_cl                  false
% 0.96/0.92  --smt_preprocessing                     true
% 0.96/0.92  --smt_ac_axioms                         fast
% 0.96/0.92  --preprocessed_out                      false
% 0.96/0.92  --preprocessed_stats                    false
% 0.96/0.92  
% 0.96/0.92  ------ Abstraction refinement Options
% 0.96/0.92  
% 0.96/0.92  --abstr_ref                             []
% 0.96/0.92  --abstr_ref_prep                        false
% 0.96/0.92  --abstr_ref_until_sat                   false
% 0.96/0.92  --abstr_ref_sig_restrict                funpre
% 0.96/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 0.96/0.92  --abstr_ref_under                       []
% 0.96/0.92  
% 0.96/0.92  ------ SAT Options
% 0.96/0.92  
% 0.96/0.92  --sat_mode                              false
% 0.96/0.92  --sat_fm_restart_options                ""
% 0.96/0.92  --sat_gr_def                            false
% 0.96/0.92  --sat_epr_types                         true
% 0.96/0.92  --sat_non_cyclic_types                  false
% 0.96/0.92  --sat_finite_models                     false
% 0.96/0.92  --sat_fm_lemmas                         false
% 0.96/0.92  --sat_fm_prep                           false
% 0.96/0.92  --sat_fm_uc_incr                        true
% 0.96/0.92  --sat_out_model                         small
% 0.96/0.92  --sat_out_clauses                       false
% 0.96/0.92  
% 0.96/0.92  ------ QBF Options
% 0.96/0.92  
% 0.96/0.92  --qbf_mode                              false
% 0.96/0.92  --qbf_elim_univ                         false
% 0.96/0.92  --qbf_dom_inst                          none
% 0.96/0.92  --qbf_dom_pre_inst                      false
% 0.96/0.92  --qbf_sk_in                             false
% 0.96/0.92  --qbf_pred_elim                         true
% 0.96/0.92  --qbf_split                             512
% 0.96/0.92  
% 0.96/0.92  ------ BMC1 Options
% 0.96/0.92  
% 0.96/0.92  --bmc1_incremental                      false
% 0.96/0.92  --bmc1_axioms                           reachable_all
% 0.96/0.92  --bmc1_min_bound                        0
% 0.96/0.92  --bmc1_max_bound                        -1
% 0.96/0.92  --bmc1_max_bound_default                -1
% 0.96/0.92  --bmc1_symbol_reachability              true
% 0.96/0.92  --bmc1_property_lemmas                  false
% 0.96/0.92  --bmc1_k_induction                      false
% 0.96/0.92  --bmc1_non_equiv_states                 false
% 0.96/0.92  --bmc1_deadlock                         false
% 0.96/0.92  --bmc1_ucm                              false
% 0.96/0.92  --bmc1_add_unsat_core                   none
% 0.96/0.92  --bmc1_unsat_core_children              false
% 0.96/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 0.96/0.92  --bmc1_out_stat                         full
% 0.96/0.92  --bmc1_ground_init                      false
% 0.96/0.92  --bmc1_pre_inst_next_state              false
% 0.96/0.92  --bmc1_pre_inst_state                   false
% 0.96/0.92  --bmc1_pre_inst_reach_state             false
% 0.96/0.92  --bmc1_out_unsat_core                   false
% 0.96/0.92  --bmc1_aig_witness_out                  false
% 0.96/0.92  --bmc1_verbose                          false
% 0.96/0.92  --bmc1_dump_clauses_tptp                false
% 0.96/0.92  --bmc1_dump_unsat_core_tptp             false
% 0.96/0.92  --bmc1_dump_file                        -
% 0.96/0.92  --bmc1_ucm_expand_uc_limit              128
% 0.96/0.92  --bmc1_ucm_n_expand_iterations          6
% 0.96/0.92  --bmc1_ucm_extend_mode                  1
% 0.96/0.92  --bmc1_ucm_init_mode                    2
% 0.96/0.92  --bmc1_ucm_cone_mode                    none
% 0.96/0.92  --bmc1_ucm_reduced_relation_type        0
% 0.96/0.92  --bmc1_ucm_relax_model                  4
% 0.96/0.92  --bmc1_ucm_full_tr_after_sat            true
% 0.96/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 0.96/0.92  --bmc1_ucm_layered_model                none
% 0.96/0.92  --bmc1_ucm_max_lemma_size               10
% 0.96/0.92  
% 0.96/0.92  ------ AIG Options
% 0.96/0.92  
% 0.96/0.92  --aig_mode                              false
% 0.96/0.92  
% 0.96/0.92  ------ Instantiation Options
% 0.96/0.92  
% 0.96/0.92  --instantiation_flag                    true
% 0.96/0.92  --inst_sos_flag                         false
% 0.96/0.92  --inst_sos_phase                        true
% 0.96/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.96/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.96/0.92  --inst_lit_sel_side                     num_symb
% 0.96/0.92  --inst_solver_per_active                1400
% 0.96/0.92  --inst_solver_calls_frac                1.
% 0.96/0.92  --inst_passive_queue_type               priority_queues
% 0.96/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.96/0.92  --inst_passive_queues_freq              [25;2]
% 0.96/0.92  --inst_dismatching                      true
% 0.96/0.92  --inst_eager_unprocessed_to_passive     true
% 0.96/0.92  --inst_prop_sim_given                   true
% 0.96/0.92  --inst_prop_sim_new                     false
% 0.96/0.92  --inst_subs_new                         false
% 0.96/0.92  --inst_eq_res_simp                      false
% 0.96/0.92  --inst_subs_given                       false
% 0.96/0.92  --inst_orphan_elimination               true
% 0.96/0.92  --inst_learning_loop_flag               true
% 0.96/0.92  --inst_learning_start                   3000
% 0.96/0.92  --inst_learning_factor                  2
% 0.96/0.92  --inst_start_prop_sim_after_learn       3
% 0.96/0.92  --inst_sel_renew                        solver
% 0.96/0.92  --inst_lit_activity_flag                true
% 0.96/0.92  --inst_restr_to_given                   false
% 0.96/0.92  --inst_activity_threshold               500
% 0.96/0.92  --inst_out_proof                        true
% 0.96/0.92  
% 0.96/0.92  ------ Resolution Options
% 0.96/0.92  
% 0.96/0.92  --resolution_flag                       true
% 0.96/0.92  --res_lit_sel                           adaptive
% 0.96/0.92  --res_lit_sel_side                      none
% 0.96/0.92  --res_ordering                          kbo
% 0.96/0.92  --res_to_prop_solver                    active
% 0.96/0.92  --res_prop_simpl_new                    false
% 0.96/0.92  --res_prop_simpl_given                  true
% 0.96/0.92  --res_passive_queue_type                priority_queues
% 0.96/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.96/0.92  --res_passive_queues_freq               [15;5]
% 0.96/0.92  --res_forward_subs                      full
% 0.96/0.92  --res_backward_subs                     full
% 0.96/0.92  --res_forward_subs_resolution           true
% 0.96/0.92  --res_backward_subs_resolution          true
% 0.96/0.92  --res_orphan_elimination                true
% 0.96/0.92  --res_time_limit                        2.
% 0.96/0.92  --res_out_proof                         true
% 0.96/0.92  
% 0.96/0.92  ------ Superposition Options
% 0.96/0.92  
% 0.96/0.92  --superposition_flag                    true
% 0.96/0.92  --sup_passive_queue_type                priority_queues
% 0.96/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.96/0.92  --sup_passive_queues_freq               [8;1;4]
% 0.96/0.92  --demod_completeness_check              fast
% 0.96/0.92  --demod_use_ground                      true
% 0.96/0.92  --sup_to_prop_solver                    passive
% 0.96/0.92  --sup_prop_simpl_new                    true
% 0.96/0.92  --sup_prop_simpl_given                  true
% 0.96/0.92  --sup_fun_splitting                     false
% 0.96/0.92  --sup_smt_interval                      50000
% 0.96/0.92  
% 0.96/0.92  ------ Superposition Simplification Setup
% 0.96/0.92  
% 0.96/0.92  --sup_indices_passive                   []
% 0.96/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 0.96/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.92  --sup_full_bw                           [BwDemod]
% 0.96/0.92  --sup_immed_triv                        [TrivRules]
% 0.96/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.96/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.92  --sup_immed_bw_main                     []
% 0.96/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 0.96/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/0.92  
% 0.96/0.92  ------ Combination Options
% 0.96/0.92  
% 0.96/0.92  --comb_res_mult                         3
% 0.96/0.92  --comb_sup_mult                         2
% 0.96/0.92  --comb_inst_mult                        10
% 0.96/0.92  
% 0.96/0.92  ------ Debug Options
% 0.96/0.92  
% 0.96/0.92  --dbg_backtrace                         false
% 0.96/0.92  --dbg_dump_prop_clauses                 false
% 0.96/0.92  --dbg_dump_prop_clauses_file            -
% 0.96/0.92  --dbg_out_stat                          false
% 0.96/0.92  ------ Parsing...
% 0.96/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.96/0.92  
% 0.96/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 0.96/0.92  
% 0.96/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.96/0.92  
% 0.96/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.96/0.92  ------ Proving...
% 0.96/0.92  ------ Problem Properties 
% 0.96/0.92  
% 0.96/0.92  
% 0.96/0.92  clauses                                 10
% 0.96/0.92  conjectures                             2
% 0.96/0.92  EPR                                     1
% 0.96/0.92  Horn                                    8
% 0.96/0.92  unary                                   4
% 0.96/0.92  binary                                  1
% 0.96/0.92  lits                                    25
% 0.96/0.92  lits eq                                 5
% 0.96/0.92  fd_pure                                 0
% 0.96/0.92  fd_pseudo                               0
% 0.96/0.92  fd_cond                                 0
% 0.96/0.92  fd_pseudo_cond                          0
% 0.96/0.92  AC symbols                              0
% 0.96/0.92  
% 0.96/0.92  ------ Schedule dynamic 5 is on 
% 0.96/0.92  
% 0.96/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.96/0.92  
% 0.96/0.92  
% 0.96/0.92  ------ 
% 0.96/0.92  Current options:
% 0.96/0.92  ------ 
% 0.96/0.92  
% 0.96/0.92  ------ Input Options
% 0.96/0.92  
% 0.96/0.92  --out_options                           all
% 0.96/0.92  --tptp_safe_out                         true
% 0.96/0.92  --problem_path                          ""
% 0.96/0.92  --include_path                          ""
% 0.96/0.92  --clausifier                            res/vclausify_rel
% 0.96/0.92  --clausifier_options                    --mode clausify
% 0.96/0.92  --stdin                                 false
% 0.96/0.92  --stats_out                             all
% 0.96/0.92  
% 0.96/0.92  ------ General Options
% 0.96/0.92  
% 0.96/0.92  --fof                                   false
% 0.96/0.92  --time_out_real                         305.
% 0.96/0.92  --time_out_virtual                      -1.
% 0.96/0.92  --symbol_type_check                     false
% 0.96/0.92  --clausify_out                          false
% 0.96/0.92  --sig_cnt_out                           false
% 0.96/0.92  --trig_cnt_out                          false
% 0.96/0.92  --trig_cnt_out_tolerance                1.
% 0.96/0.92  --trig_cnt_out_sk_spl                   false
% 0.96/0.92  --abstr_cl_out                          false
% 0.96/0.92  
% 0.96/0.92  ------ Global Options
% 0.96/0.92  
% 0.96/0.92  --schedule                              default
% 0.96/0.92  --add_important_lit                     false
% 0.96/0.92  --prop_solver_per_cl                    1000
% 0.96/0.92  --min_unsat_core                        false
% 0.96/0.92  --soft_assumptions                      false
% 0.96/0.92  --soft_lemma_size                       3
% 0.96/0.92  --prop_impl_unit_size                   0
% 0.96/0.92  --prop_impl_unit                        []
% 0.96/0.92  --share_sel_clauses                     true
% 0.96/0.92  --reset_solvers                         false
% 0.96/0.92  --bc_imp_inh                            [conj_cone]
% 0.96/0.92  --conj_cone_tolerance                   3.
% 0.96/0.92  --extra_neg_conj                        none
% 0.96/0.92  --large_theory_mode                     true
% 0.96/0.92  --prolific_symb_bound                   200
% 0.96/0.92  --lt_threshold                          2000
% 0.96/0.92  --clause_weak_htbl                      true
% 0.96/0.92  --gc_record_bc_elim                     false
% 0.96/0.92  
% 0.96/0.92  ------ Preprocessing Options
% 0.96/0.92  
% 0.96/0.92  --preprocessing_flag                    true
% 0.96/0.92  --time_out_prep_mult                    0.1
% 0.96/0.92  --splitting_mode                        input
% 0.96/0.92  --splitting_grd                         true
% 0.96/0.92  --splitting_cvd                         false
% 0.96/0.92  --splitting_cvd_svl                     false
% 0.96/0.92  --splitting_nvd                         32
% 0.96/0.92  --sub_typing                            true
% 0.96/0.92  --prep_gs_sim                           true
% 0.96/0.92  --prep_unflatten                        true
% 0.96/0.92  --prep_res_sim                          true
% 0.96/0.92  --prep_upred                            true
% 0.96/0.92  --prep_sem_filter                       exhaustive
% 0.96/0.92  --prep_sem_filter_out                   false
% 0.96/0.92  --pred_elim                             true
% 0.96/0.92  --res_sim_input                         true
% 0.96/0.92  --eq_ax_congr_red                       true
% 0.96/0.92  --pure_diseq_elim                       true
% 0.96/0.92  --brand_transform                       false
% 0.96/0.92  --non_eq_to_eq                          false
% 0.96/0.92  --prep_def_merge                        true
% 0.96/0.92  --prep_def_merge_prop_impl              false
% 0.96/0.92  --prep_def_merge_mbd                    true
% 0.96/0.92  --prep_def_merge_tr_red                 false
% 0.96/0.92  --prep_def_merge_tr_cl                  false
% 0.96/0.92  --smt_preprocessing                     true
% 0.96/0.92  --smt_ac_axioms                         fast
% 0.96/0.92  --preprocessed_out                      false
% 0.96/0.92  --preprocessed_stats                    false
% 0.96/0.92  
% 0.96/0.92  ------ Abstraction refinement Options
% 0.96/0.92  
% 0.96/0.92  --abstr_ref                             []
% 0.96/0.92  --abstr_ref_prep                        false
% 0.96/0.92  --abstr_ref_until_sat                   false
% 0.96/0.92  --abstr_ref_sig_restrict                funpre
% 0.96/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 0.96/0.92  --abstr_ref_under                       []
% 0.96/0.92  
% 0.96/0.92  ------ SAT Options
% 0.96/0.92  
% 0.96/0.92  --sat_mode                              false
% 0.96/0.92  --sat_fm_restart_options                ""
% 0.96/0.92  --sat_gr_def                            false
% 0.96/0.92  --sat_epr_types                         true
% 0.96/0.92  --sat_non_cyclic_types                  false
% 0.96/0.92  --sat_finite_models                     false
% 0.96/0.92  --sat_fm_lemmas                         false
% 0.96/0.92  --sat_fm_prep                           false
% 0.96/0.92  --sat_fm_uc_incr                        true
% 0.96/0.92  --sat_out_model                         small
% 0.96/0.92  --sat_out_clauses                       false
% 0.96/0.92  
% 0.96/0.92  ------ QBF Options
% 0.96/0.92  
% 0.96/0.92  --qbf_mode                              false
% 0.96/0.92  --qbf_elim_univ                         false
% 0.96/0.92  --qbf_dom_inst                          none
% 0.96/0.92  --qbf_dom_pre_inst                      false
% 0.96/0.92  --qbf_sk_in                             false
% 0.96/0.92  --qbf_pred_elim                         true
% 0.96/0.92  --qbf_split                             512
% 0.96/0.92  
% 0.96/0.92  ------ BMC1 Options
% 0.96/0.92  
% 0.96/0.92  --bmc1_incremental                      false
% 0.96/0.92  --bmc1_axioms                           reachable_all
% 0.96/0.92  --bmc1_min_bound                        0
% 0.96/0.92  --bmc1_max_bound                        -1
% 0.96/0.92  --bmc1_max_bound_default                -1
% 0.96/0.92  --bmc1_symbol_reachability              true
% 0.96/0.92  --bmc1_property_lemmas                  false
% 0.96/0.92  --bmc1_k_induction                      false
% 0.96/0.92  --bmc1_non_equiv_states                 false
% 0.96/0.92  --bmc1_deadlock                         false
% 0.96/0.92  --bmc1_ucm                              false
% 0.96/0.92  --bmc1_add_unsat_core                   none
% 0.96/0.92  --bmc1_unsat_core_children              false
% 0.96/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 0.96/0.92  --bmc1_out_stat                         full
% 0.96/0.92  --bmc1_ground_init                      false
% 0.96/0.92  --bmc1_pre_inst_next_state              false
% 0.96/0.92  --bmc1_pre_inst_state                   false
% 0.96/0.92  --bmc1_pre_inst_reach_state             false
% 0.96/0.92  --bmc1_out_unsat_core                   false
% 0.96/0.92  --bmc1_aig_witness_out                  false
% 0.96/0.92  --bmc1_verbose                          false
% 0.96/0.92  --bmc1_dump_clauses_tptp                false
% 0.96/0.92  --bmc1_dump_unsat_core_tptp             false
% 0.96/0.92  --bmc1_dump_file                        -
% 0.96/0.92  --bmc1_ucm_expand_uc_limit              128
% 0.96/0.92  --bmc1_ucm_n_expand_iterations          6
% 0.96/0.92  --bmc1_ucm_extend_mode                  1
% 0.96/0.92  --bmc1_ucm_init_mode                    2
% 0.96/0.92  --bmc1_ucm_cone_mode                    none
% 0.96/0.92  --bmc1_ucm_reduced_relation_type        0
% 0.96/0.92  --bmc1_ucm_relax_model                  4
% 0.96/0.92  --bmc1_ucm_full_tr_after_sat            true
% 0.96/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 0.96/0.92  --bmc1_ucm_layered_model                none
% 0.96/0.92  --bmc1_ucm_max_lemma_size               10
% 0.96/0.92  
% 0.96/0.92  ------ AIG Options
% 0.96/0.92  
% 0.96/0.92  --aig_mode                              false
% 0.96/0.92  
% 0.96/0.92  ------ Instantiation Options
% 0.96/0.92  
% 0.96/0.92  --instantiation_flag                    true
% 0.96/0.92  --inst_sos_flag                         false
% 0.96/0.92  --inst_sos_phase                        true
% 0.96/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.96/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.96/0.92  --inst_lit_sel_side                     none
% 0.96/0.92  --inst_solver_per_active                1400
% 0.96/0.92  --inst_solver_calls_frac                1.
% 0.96/0.92  --inst_passive_queue_type               priority_queues
% 0.96/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.96/0.92  --inst_passive_queues_freq              [25;2]
% 0.96/0.92  --inst_dismatching                      true
% 0.96/0.92  --inst_eager_unprocessed_to_passive     true
% 0.96/0.92  --inst_prop_sim_given                   true
% 0.96/0.92  --inst_prop_sim_new                     false
% 0.96/0.92  --inst_subs_new                         false
% 0.96/0.92  --inst_eq_res_simp                      false
% 0.96/0.92  --inst_subs_given                       false
% 0.96/0.92  --inst_orphan_elimination               true
% 0.96/0.92  --inst_learning_loop_flag               true
% 0.96/0.92  --inst_learning_start                   3000
% 0.96/0.92  --inst_learning_factor                  2
% 0.96/0.92  --inst_start_prop_sim_after_learn       3
% 0.96/0.92  --inst_sel_renew                        solver
% 0.96/0.92  --inst_lit_activity_flag                true
% 0.96/0.92  --inst_restr_to_given                   false
% 0.96/0.92  --inst_activity_threshold               500
% 0.96/0.92  --inst_out_proof                        true
% 0.96/0.92  
% 0.96/0.92  ------ Resolution Options
% 0.96/0.92  
% 0.96/0.92  --resolution_flag                       false
% 0.96/0.92  --res_lit_sel                           adaptive
% 0.96/0.92  --res_lit_sel_side                      none
% 0.96/0.92  --res_ordering                          kbo
% 0.96/0.92  --res_to_prop_solver                    active
% 0.96/0.92  --res_prop_simpl_new                    false
% 0.96/0.92  --res_prop_simpl_given                  true
% 0.96/0.92  --res_passive_queue_type                priority_queues
% 0.96/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.96/0.92  --res_passive_queues_freq               [15;5]
% 0.96/0.92  --res_forward_subs                      full
% 0.96/0.92  --res_backward_subs                     full
% 0.96/0.92  --res_forward_subs_resolution           true
% 0.96/0.92  --res_backward_subs_resolution          true
% 0.96/0.92  --res_orphan_elimination                true
% 0.96/0.92  --res_time_limit                        2.
% 0.96/0.92  --res_out_proof                         true
% 0.96/0.92  
% 0.96/0.92  ------ Superposition Options
% 0.96/0.92  
% 0.96/0.92  --superposition_flag                    true
% 0.96/0.92  --sup_passive_queue_type                priority_queues
% 0.96/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.96/0.92  --sup_passive_queues_freq               [8;1;4]
% 0.96/0.92  --demod_completeness_check              fast
% 0.96/0.92  --demod_use_ground                      true
% 0.96/0.92  --sup_to_prop_solver                    passive
% 0.96/0.92  --sup_prop_simpl_new                    true
% 0.96/0.92  --sup_prop_simpl_given                  true
% 0.96/0.92  --sup_fun_splitting                     false
% 0.96/0.92  --sup_smt_interval                      50000
% 0.96/0.92  
% 0.96/0.92  ------ Superposition Simplification Setup
% 0.96/0.92  
% 0.96/0.92  --sup_indices_passive                   []
% 0.96/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 0.96/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.92  --sup_full_bw                           [BwDemod]
% 0.96/0.92  --sup_immed_triv                        [TrivRules]
% 0.96/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.96/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.92  --sup_immed_bw_main                     []
% 0.96/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 0.96/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/0.92  
% 0.96/0.92  ------ Combination Options
% 0.96/0.92  
% 0.96/0.92  --comb_res_mult                         3
% 0.96/0.92  --comb_sup_mult                         2
% 0.96/0.92  --comb_inst_mult                        10
% 0.96/0.92  
% 0.96/0.92  ------ Debug Options
% 0.96/0.92  
% 0.96/0.92  --dbg_backtrace                         false
% 0.96/0.92  --dbg_dump_prop_clauses                 false
% 0.96/0.92  --dbg_dump_prop_clauses_file            -
% 0.96/0.92  --dbg_out_stat                          false
% 0.96/0.92  
% 0.96/0.92  
% 0.96/0.92  
% 0.96/0.92  
% 0.96/0.92  ------ Proving...
% 0.96/0.92  
% 0.96/0.92  
% 0.96/0.92  % SZS status Theorem for theBenchmark.p
% 0.96/0.92  
% 0.96/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 0.96/0.92  
% 0.96/0.92  fof(f6,axiom,(
% 0.96/0.92    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X0) = X1 => (v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)))))),
% 0.96/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.92  
% 0.96/0.92  fof(f20,plain,(
% 0.96/0.92    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.96/0.92    inference(ennf_transformation,[],[f6])).
% 0.96/0.92  
% 0.96/0.92  fof(f21,plain,(
% 0.96/0.92    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.96/0.92    inference(flattening,[],[f20])).
% 0.96/0.92  
% 0.96/0.92  fof(f42,plain,(
% 0.96/0.92    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_tdlat_3(X0)) & (v1_tdlat_3(X0) | ~v2_tex_2(X1,X0))) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.96/0.92    inference(nnf_transformation,[],[f21])).
% 0.96/0.92  
% 0.96/0.92  fof(f65,plain,(
% 0.96/0.92    ( ! [X0,X1] : (v1_tdlat_3(X0) | ~v2_tex_2(X1,X0) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.96/0.92    inference(cnf_transformation,[],[f42])).
% 0.96/0.92  
% 0.96/0.92  fof(f79,plain,(
% 0.96/0.92    ( ! [X0] : (v1_tdlat_3(X0) | ~v2_tex_2(u1_struct_0(X0),X0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.96/0.92    inference(equality_resolution,[],[f65])).
% 0.96/0.92  
% 0.96/0.92  fof(f8,axiom,(
% 0.96/0.92    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.96/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.92  
% 0.96/0.92  fof(f24,plain,(
% 0.96/0.92    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.96/0.92    inference(ennf_transformation,[],[f8])).
% 0.96/0.92  
% 0.96/0.92  fof(f25,plain,(
% 0.96/0.92    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.96/0.92    inference(flattening,[],[f24])).
% 0.96/0.92  
% 0.96/0.92  fof(f43,plain,(
% 0.96/0.92    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | v1_subset_1(X1,u1_struct_0(X0))) & (~v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.96/0.92    inference(nnf_transformation,[],[f25])).
% 0.96/0.92  
% 0.96/0.92  fof(f68,plain,(
% 0.96/0.92    ( ! [X0,X1] : (~v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.96/0.92    inference(cnf_transformation,[],[f43])).
% 0.96/0.92  
% 0.96/0.92  fof(f9,conjecture,(
% 0.96/0.92    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.96/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.92  
% 0.96/0.92  fof(f10,negated_conjecture,(
% 0.96/0.92    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.96/0.92    inference(negated_conjecture,[],[f9])).
% 0.96/0.92  
% 0.96/0.92  fof(f26,plain,(
% 0.96/0.92    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.96/0.92    inference(ennf_transformation,[],[f10])).
% 0.96/0.92  
% 0.96/0.92  fof(f27,plain,(
% 0.96/0.92    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.96/0.92    inference(flattening,[],[f26])).
% 0.96/0.92  
% 0.96/0.92  fof(f45,plain,(
% 0.96/0.92    ( ! [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_subset_1(sK4,u1_struct_0(X0)) & v3_tex_2(sK4,X0) & (v4_pre_topc(sK4,X0) | v3_pre_topc(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.96/0.92    introduced(choice_axiom,[])).
% 0.96/0.92  
% 0.96/0.92  fof(f44,plain,(
% 0.96/0.92    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v1_subset_1(X1,u1_struct_0(sK3)) & v3_tex_2(X1,sK3) & (v4_pre_topc(X1,sK3) | v3_pre_topc(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v3_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.96/0.92    introduced(choice_axiom,[])).
% 0.96/0.92  
% 0.96/0.92  fof(f46,plain,(
% 0.96/0.92    (v1_subset_1(sK4,u1_struct_0(sK3)) & v3_tex_2(sK4,sK3) & (v4_pre_topc(sK4,sK3) | v3_pre_topc(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v3_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 0.96/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f27,f45,f44])).
% 0.96/0.92  
% 0.96/0.92  fof(f77,plain,(
% 0.96/0.92    v1_subset_1(sK4,u1_struct_0(sK3))),
% 0.96/0.92    inference(cnf_transformation,[],[f46])).
% 0.96/0.92  
% 0.96/0.92  fof(f70,plain,(
% 0.96/0.92    ~v2_struct_0(sK3)),
% 0.96/0.92    inference(cnf_transformation,[],[f46])).
% 0.96/0.92  
% 0.96/0.92  fof(f71,plain,(
% 0.96/0.92    v2_pre_topc(sK3)),
% 0.96/0.92    inference(cnf_transformation,[],[f46])).
% 0.96/0.92  
% 0.96/0.92  fof(f73,plain,(
% 0.96/0.92    l1_pre_topc(sK3)),
% 0.96/0.92    inference(cnf_transformation,[],[f46])).
% 0.96/0.92  
% 0.96/0.92  fof(f74,plain,(
% 0.96/0.92    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.96/0.92    inference(cnf_transformation,[],[f46])).
% 0.96/0.92  
% 0.96/0.92  fof(f76,plain,(
% 0.96/0.92    v3_tex_2(sK4,sK3)),
% 0.96/0.92    inference(cnf_transformation,[],[f46])).
% 0.96/0.92  
% 0.96/0.92  fof(f75,plain,(
% 0.96/0.92    v4_pre_topc(sK4,sK3) | v3_pre_topc(sK4,sK3)),
% 0.96/0.92    inference(cnf_transformation,[],[f46])).
% 0.96/0.92  
% 0.96/0.92  fof(f4,axiom,(
% 0.96/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => v4_pre_topc(X1,X0)))))),
% 0.96/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.92  
% 0.96/0.92  fof(f16,plain,(
% 0.96/0.92    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.96/0.92    inference(ennf_transformation,[],[f4])).
% 0.96/0.92  
% 0.96/0.92  fof(f17,plain,(
% 0.96/0.92    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.96/0.92    inference(flattening,[],[f16])).
% 0.96/0.92  
% 0.96/0.92  fof(f34,plain,(
% 0.96/0.92    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.96/0.92    inference(nnf_transformation,[],[f17])).
% 0.96/0.92  
% 0.96/0.92  fof(f35,plain,(
% 0.96/0.92    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.96/0.92    inference(rectify,[],[f34])).
% 0.96/0.92  
% 0.96/0.92  fof(f36,plain,(
% 0.96/0.92    ! [X0] : (? [X1] : (~v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK1(X0),X0) & v3_pre_topc(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.96/0.92    introduced(choice_axiom,[])).
% 0.96/0.92  
% 0.96/0.92  fof(f37,plain,(
% 0.96/0.92    ! [X0] : (((v3_tdlat_3(X0) | (~v4_pre_topc(sK1(X0),X0) & v3_pre_topc(sK1(X0),X0) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.96/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 0.96/0.92  
% 0.96/0.92  fof(f57,plain,(
% 0.96/0.92    ( ! [X2,X0] : (v4_pre_topc(X2,X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.96/0.92    inference(cnf_transformation,[],[f37])).
% 0.96/0.92  
% 0.96/0.92  fof(f72,plain,(
% 0.96/0.92    v3_tdlat_3(sK3)),
% 0.96/0.92    inference(cnf_transformation,[],[f46])).
% 0.96/0.92  
% 0.96/0.92  fof(f5,axiom,(
% 0.96/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.96/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.92  
% 0.96/0.92  fof(f18,plain,(
% 0.96/0.92    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.96/0.92    inference(ennf_transformation,[],[f5])).
% 0.96/0.92  
% 0.96/0.92  fof(f19,plain,(
% 0.96/0.92    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.96/0.92    inference(flattening,[],[f18])).
% 0.96/0.92  
% 0.96/0.92  fof(f38,plain,(
% 0.96/0.92    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.96/0.92    inference(nnf_transformation,[],[f19])).
% 0.96/0.92  
% 0.96/0.92  fof(f39,plain,(
% 0.96/0.92    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.96/0.92    inference(rectify,[],[f38])).
% 0.96/0.92  
% 0.96/0.92  fof(f40,plain,(
% 0.96/0.92    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0),X0) & v4_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.96/0.92    introduced(choice_axiom,[])).
% 0.96/0.92  
% 0.96/0.92  fof(f41,plain,(
% 0.96/0.92    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK2(X0),X0) & v4_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.96/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 0.96/0.93  
% 0.96/0.93  fof(f61,plain,(
% 0.96/0.93    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.96/0.93    inference(cnf_transformation,[],[f41])).
% 0.96/0.93  
% 0.96/0.93  fof(f7,axiom,(
% 0.96/0.93    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.96/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.93  
% 0.96/0.93  fof(f22,plain,(
% 0.96/0.93    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.96/0.93    inference(ennf_transformation,[],[f7])).
% 0.96/0.93  
% 0.96/0.93  fof(f23,plain,(
% 0.96/0.93    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.96/0.93    inference(flattening,[],[f22])).
% 0.96/0.93  
% 0.96/0.93  fof(f67,plain,(
% 0.96/0.93    ( ! [X0,X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.96/0.93    inference(cnf_transformation,[],[f23])).
% 0.96/0.93  
% 0.96/0.93  fof(f2,axiom,(
% 0.96/0.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.96/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.93  
% 0.96/0.93  fof(f13,plain,(
% 0.96/0.93    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.96/0.93    inference(ennf_transformation,[],[f2])).
% 0.96/0.93  
% 0.96/0.93  fof(f28,plain,(
% 0.96/0.93    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.96/0.93    inference(nnf_transformation,[],[f13])).
% 0.96/0.93  
% 0.96/0.93  fof(f49,plain,(
% 0.96/0.93    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.96/0.93    inference(cnf_transformation,[],[f28])).
% 0.96/0.93  
% 0.96/0.93  fof(f1,axiom,(
% 0.96/0.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.96/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.93  
% 0.96/0.93  fof(f11,plain,(
% 0.96/0.93    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.96/0.93    inference(ennf_transformation,[],[f1])).
% 0.96/0.93  
% 0.96/0.93  fof(f12,plain,(
% 0.96/0.93    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.96/0.93    inference(flattening,[],[f11])).
% 0.96/0.93  
% 0.96/0.93  fof(f47,plain,(
% 0.96/0.93    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.96/0.93    inference(cnf_transformation,[],[f12])).
% 0.96/0.93  
% 0.96/0.93  fof(f3,axiom,(
% 0.96/0.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.96/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.93  
% 0.96/0.93  fof(f14,plain,(
% 0.96/0.93    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.96/0.93    inference(ennf_transformation,[],[f3])).
% 0.96/0.93  
% 0.96/0.93  fof(f15,plain,(
% 0.96/0.93    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.96/0.93    inference(flattening,[],[f14])).
% 0.96/0.93  
% 0.96/0.93  fof(f29,plain,(
% 0.96/0.93    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.96/0.93    inference(nnf_transformation,[],[f15])).
% 0.96/0.93  
% 0.96/0.93  fof(f30,plain,(
% 0.96/0.93    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.96/0.93    inference(flattening,[],[f29])).
% 0.96/0.93  
% 0.96/0.93  fof(f31,plain,(
% 0.96/0.93    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.96/0.93    inference(rectify,[],[f30])).
% 0.96/0.93  
% 0.96/0.93  fof(f32,plain,(
% 0.96/0.93    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.96/0.93    introduced(choice_axiom,[])).
% 0.96/0.93  
% 0.96/0.93  fof(f33,plain,(
% 0.96/0.93    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.96/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 0.96/0.93  
% 0.96/0.93  fof(f51,plain,(
% 0.96/0.93    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.96/0.93    inference(cnf_transformation,[],[f33])).
% 0.96/0.93  
% 0.96/0.93  cnf(c_19,plain,
% 0.96/0.93      ( ~ v2_tex_2(u1_struct_0(X0),X0)
% 0.96/0.93      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 0.96/0.93      | v2_struct_0(X0)
% 0.96/0.93      | v1_tdlat_3(X0)
% 0.96/0.93      | ~ l1_pre_topc(X0) ),
% 0.96/0.93      inference(cnf_transformation,[],[f79]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_22,plain,
% 0.96/0.93      ( ~ v1_subset_1(X0,u1_struct_0(X1))
% 0.96/0.93      | ~ v3_tex_2(X0,X1)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.96/0.93      | v2_struct_0(X1)
% 0.96/0.93      | ~ v1_tdlat_3(X1)
% 0.96/0.93      | ~ l1_pre_topc(X1)
% 0.96/0.93      | ~ v2_pre_topc(X1) ),
% 0.96/0.93      inference(cnf_transformation,[],[f68]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_23,negated_conjecture,
% 0.96/0.93      ( v1_subset_1(sK4,u1_struct_0(sK3)) ),
% 0.96/0.93      inference(cnf_transformation,[],[f77]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_410,plain,
% 0.96/0.93      ( ~ v3_tex_2(X0,X1)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.96/0.93      | v2_struct_0(X1)
% 0.96/0.93      | ~ v1_tdlat_3(X1)
% 0.96/0.93      | ~ l1_pre_topc(X1)
% 0.96/0.93      | ~ v2_pre_topc(X1)
% 0.96/0.93      | u1_struct_0(X1) != u1_struct_0(sK3)
% 0.96/0.93      | sK4 != X0 ),
% 0.96/0.93      inference(resolution_lifted,[status(thm)],[c_22,c_23]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_411,plain,
% 0.96/0.93      ( ~ v3_tex_2(sK4,X0)
% 0.96/0.93      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 0.96/0.93      | v2_struct_0(X0)
% 0.96/0.93      | ~ v1_tdlat_3(X0)
% 0.96/0.93      | ~ l1_pre_topc(X0)
% 0.96/0.93      | ~ v2_pre_topc(X0)
% 0.96/0.93      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 0.96/0.93      inference(unflattening,[status(thm)],[c_410]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_445,plain,
% 0.96/0.93      ( ~ v2_tex_2(u1_struct_0(X0),X0)
% 0.96/0.93      | ~ v3_tex_2(sK4,X0)
% 0.96/0.93      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 0.96/0.93      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 0.96/0.93      | v2_struct_0(X0)
% 0.96/0.93      | ~ l1_pre_topc(X0)
% 0.96/0.93      | ~ v2_pre_topc(X0)
% 0.96/0.93      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 0.96/0.93      inference(resolution,[status(thm)],[c_19,c_411]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_30,negated_conjecture,
% 0.96/0.93      ( ~ v2_struct_0(sK3) ),
% 0.96/0.93      inference(cnf_transformation,[],[f70]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_508,plain,
% 0.96/0.93      ( ~ v2_tex_2(u1_struct_0(X0),X0)
% 0.96/0.93      | ~ v3_tex_2(sK4,X0)
% 0.96/0.93      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 0.96/0.93      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 0.96/0.93      | ~ l1_pre_topc(X0)
% 0.96/0.93      | ~ v2_pre_topc(X0)
% 0.96/0.93      | u1_struct_0(X0) != u1_struct_0(sK3)
% 0.96/0.93      | sK3 != X0 ),
% 0.96/0.93      inference(resolution_lifted,[status(thm)],[c_445,c_30]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_509,plain,
% 0.96/0.93      ( ~ v2_tex_2(u1_struct_0(sK3),sK3)
% 0.96/0.93      | ~ v3_tex_2(sK4,sK3)
% 0.96/0.93      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 0.96/0.93      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.96/0.93      | ~ l1_pre_topc(sK3)
% 0.96/0.93      | ~ v2_pre_topc(sK3)
% 0.96/0.93      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 0.96/0.93      inference(unflattening,[status(thm)],[c_508]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_29,negated_conjecture,
% 0.96/0.93      ( v2_pre_topc(sK3) ),
% 0.96/0.93      inference(cnf_transformation,[],[f71]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_27,negated_conjecture,
% 0.96/0.93      ( l1_pre_topc(sK3) ),
% 0.96/0.93      inference(cnf_transformation,[],[f73]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_26,negated_conjecture,
% 0.96/0.93      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 0.96/0.93      inference(cnf_transformation,[],[f74]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_24,negated_conjecture,
% 0.96/0.93      ( v3_tex_2(sK4,sK3) ),
% 0.96/0.93      inference(cnf_transformation,[],[f76]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_447,plain,
% 0.96/0.93      ( ~ v2_tex_2(u1_struct_0(sK3),sK3)
% 0.96/0.93      | ~ v3_tex_2(sK4,sK3)
% 0.96/0.93      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 0.96/0.93      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.96/0.93      | v2_struct_0(sK3)
% 0.96/0.93      | ~ l1_pre_topc(sK3)
% 0.96/0.93      | ~ v2_pre_topc(sK3)
% 0.96/0.93      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 0.96/0.93      inference(instantiation,[status(thm)],[c_445]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_511,plain,
% 0.96/0.93      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 0.96/0.93      | ~ v2_tex_2(u1_struct_0(sK3),sK3)
% 0.96/0.93      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 0.96/0.93      inference(global_propositional_subsumption,
% 0.96/0.93                [status(thm)],
% 0.96/0.93                [c_509,c_30,c_29,c_27,c_26,c_24,c_447]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_512,plain,
% 0.96/0.93      ( ~ v2_tex_2(u1_struct_0(sK3),sK3)
% 0.96/0.93      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 0.96/0.93      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 0.96/0.93      inference(renaming,[status(thm)],[c_511]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_950,plain,
% 0.96/0.93      ( ~ v2_tex_2(u1_struct_0(sK3),sK3)
% 0.96/0.93      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 0.96/0.93      inference(equality_resolution_simp,[status(thm)],[c_512]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_1083,plain,
% 0.96/0.93      ( ~ v2_tex_2(u1_struct_0(sK3),sK3)
% 0.96/0.93      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 0.96/0.93      inference(subtyping,[status(esa)],[c_950]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_1272,plain,
% 0.96/0.93      ( v2_tex_2(u1_struct_0(sK3),sK3) != iProver_top
% 0.96/0.93      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 0.96/0.93      inference(predicate_to_equality,[status(thm)],[c_1083]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_25,negated_conjecture,
% 0.96/0.93      ( v3_pre_topc(sK4,sK3) | v4_pre_topc(sK4,sK3) ),
% 0.96/0.93      inference(cnf_transformation,[],[f75]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_13,plain,
% 0.96/0.93      ( ~ v3_pre_topc(X0,X1)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.96/0.93      | v4_pre_topc(X0,X1)
% 0.96/0.93      | ~ v3_tdlat_3(X1)
% 0.96/0.93      | ~ l1_pre_topc(X1)
% 0.96/0.93      | ~ v2_pre_topc(X1) ),
% 0.96/0.93      inference(cnf_transformation,[],[f57]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_555,plain,
% 0.96/0.93      ( ~ v3_pre_topc(X0,X1)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.96/0.93      | v4_pre_topc(X0,X1)
% 0.96/0.93      | ~ v3_tdlat_3(X1)
% 0.96/0.93      | ~ l1_pre_topc(X1)
% 0.96/0.93      | sK3 != X1 ),
% 0.96/0.93      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_556,plain,
% 0.96/0.93      ( ~ v3_pre_topc(X0,sK3)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.96/0.93      | v4_pre_topc(X0,sK3)
% 0.96/0.93      | ~ v3_tdlat_3(sK3)
% 0.96/0.93      | ~ l1_pre_topc(sK3) ),
% 0.96/0.93      inference(unflattening,[status(thm)],[c_555]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_28,negated_conjecture,
% 0.96/0.93      ( v3_tdlat_3(sK3) ),
% 0.96/0.93      inference(cnf_transformation,[],[f72]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_560,plain,
% 0.96/0.93      ( ~ v3_pre_topc(X0,sK3)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.96/0.93      | v4_pre_topc(X0,sK3) ),
% 0.96/0.93      inference(global_propositional_subsumption,
% 0.96/0.93                [status(thm)],
% 0.96/0.93                [c_556,c_28,c_27]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_639,plain,
% 0.96/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.96/0.93      | v4_pre_topc(X0,sK3)
% 0.96/0.93      | v4_pre_topc(sK4,sK3)
% 0.96/0.93      | sK3 != sK3
% 0.96/0.93      | sK4 != X0 ),
% 0.96/0.93      inference(resolution_lifted,[status(thm)],[c_25,c_560]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_640,plain,
% 0.96/0.93      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.96/0.93      | v4_pre_topc(sK4,sK3) ),
% 0.96/0.93      inference(unflattening,[status(thm)],[c_639]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_642,plain,
% 0.96/0.93      ( v4_pre_topc(sK4,sK3) ),
% 0.96/0.93      inference(global_propositional_subsumption,
% 0.96/0.93                [status(thm)],
% 0.96/0.93                [c_640,c_26]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_17,plain,
% 0.96/0.93      ( v3_pre_topc(X0,X1)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.96/0.93      | ~ v4_pre_topc(X0,X1)
% 0.96/0.93      | ~ v3_tdlat_3(X1)
% 0.96/0.93      | ~ l1_pre_topc(X1)
% 0.96/0.93      | ~ v2_pre_topc(X1) ),
% 0.96/0.93      inference(cnf_transformation,[],[f61]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_534,plain,
% 0.96/0.93      ( v3_pre_topc(X0,X1)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.96/0.93      | ~ v4_pre_topc(X0,X1)
% 0.96/0.93      | ~ v3_tdlat_3(X1)
% 0.96/0.93      | ~ l1_pre_topc(X1)
% 0.96/0.93      | sK3 != X1 ),
% 0.96/0.93      inference(resolution_lifted,[status(thm)],[c_17,c_29]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_535,plain,
% 0.96/0.93      ( v3_pre_topc(X0,sK3)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.96/0.93      | ~ v4_pre_topc(X0,sK3)
% 0.96/0.93      | ~ v3_tdlat_3(sK3)
% 0.96/0.93      | ~ l1_pre_topc(sK3) ),
% 0.96/0.93      inference(unflattening,[status(thm)],[c_534]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_539,plain,
% 0.96/0.93      ( v3_pre_topc(X0,sK3)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.96/0.93      | ~ v4_pre_topc(X0,sK3) ),
% 0.96/0.93      inference(global_propositional_subsumption,
% 0.96/0.93                [status(thm)],
% 0.96/0.93                [c_535,c_28,c_27]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_20,plain,
% 0.96/0.93      ( ~ v3_pre_topc(X0,X1)
% 0.96/0.93      | ~ v3_tex_2(X0,X1)
% 0.96/0.93      | v1_tops_1(X0,X1)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.96/0.93      | v2_struct_0(X1)
% 0.96/0.93      | ~ l1_pre_topc(X1)
% 0.96/0.93      | ~ v2_pre_topc(X1) ),
% 0.96/0.93      inference(cnf_transformation,[],[f67]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_3,plain,
% 0.96/0.93      ( ~ v1_tops_1(X0,X1)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.96/0.93      | ~ l1_pre_topc(X1)
% 0.96/0.93      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 0.96/0.93      inference(cnf_transformation,[],[f49]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_374,plain,
% 0.96/0.93      ( ~ v3_pre_topc(X0,X1)
% 0.96/0.93      | ~ v3_tex_2(X0,X1)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.96/0.93      | v2_struct_0(X1)
% 0.96/0.93      | ~ l1_pre_topc(X1)
% 0.96/0.93      | ~ v2_pre_topc(X1)
% 0.96/0.93      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 0.96/0.93      inference(resolution,[status(thm)],[c_20,c_3]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_484,plain,
% 0.96/0.93      ( ~ v3_pre_topc(X0,X1)
% 0.96/0.93      | ~ v3_tex_2(X0,X1)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.96/0.93      | ~ l1_pre_topc(X1)
% 0.96/0.93      | ~ v2_pre_topc(X1)
% 0.96/0.93      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 0.96/0.93      | sK3 != X1 ),
% 0.96/0.93      inference(resolution_lifted,[status(thm)],[c_374,c_30]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_485,plain,
% 0.96/0.93      ( ~ v3_pre_topc(X0,sK3)
% 0.96/0.93      | ~ v3_tex_2(X0,sK3)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.96/0.93      | ~ l1_pre_topc(sK3)
% 0.96/0.93      | ~ v2_pre_topc(sK3)
% 0.96/0.93      | k2_pre_topc(sK3,X0) = u1_struct_0(sK3) ),
% 0.96/0.93      inference(unflattening,[status(thm)],[c_484]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_489,plain,
% 0.96/0.93      ( ~ v3_pre_topc(X0,sK3)
% 0.96/0.93      | ~ v3_tex_2(X0,sK3)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.96/0.93      | k2_pre_topc(sK3,X0) = u1_struct_0(sK3) ),
% 0.96/0.93      inference(global_propositional_subsumption,
% 0.96/0.93                [status(thm)],
% 0.96/0.93                [c_485,c_29,c_27]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_622,plain,
% 0.96/0.93      ( ~ v3_tex_2(X0,sK3)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.96/0.93      | ~ v4_pre_topc(X0,sK3)
% 0.96/0.93      | k2_pre_topc(sK3,X0) = u1_struct_0(sK3) ),
% 0.96/0.93      inference(resolution,[status(thm)],[c_539,c_489]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_686,plain,
% 0.96/0.93      ( ~ v3_tex_2(X0,sK3)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.96/0.93      | k2_pre_topc(sK3,X0) = u1_struct_0(sK3)
% 0.96/0.93      | sK3 != sK3
% 0.96/0.93      | sK4 != X0 ),
% 0.96/0.93      inference(resolution_lifted,[status(thm)],[c_642,c_622]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_687,plain,
% 0.96/0.93      ( ~ v3_tex_2(sK4,sK3)
% 0.96/0.93      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.96/0.93      | k2_pre_topc(sK3,sK4) = u1_struct_0(sK3) ),
% 0.96/0.93      inference(unflattening,[status(thm)],[c_686]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_689,plain,
% 0.96/0.93      ( k2_pre_topc(sK3,sK4) = u1_struct_0(sK3) ),
% 0.96/0.93      inference(global_propositional_subsumption,
% 0.96/0.93                [status(thm)],
% 0.96/0.93                [c_687,c_26,c_24]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_1088,plain,
% 0.96/0.93      ( k2_pre_topc(sK3,sK4) = u1_struct_0(sK3) ),
% 0.96/0.93      inference(subtyping,[status(esa)],[c_689]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_1,plain,
% 0.96/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.96/0.93      | ~ v4_pre_topc(X0,X1)
% 0.96/0.93      | ~ l1_pre_topc(X1)
% 0.96/0.93      | k2_pre_topc(X1,X0) = X0 ),
% 0.96/0.93      inference(cnf_transformation,[],[f47]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_676,plain,
% 0.96/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.96/0.93      | ~ l1_pre_topc(X1)
% 0.96/0.93      | k2_pre_topc(X1,X0) = X0
% 0.96/0.93      | sK3 != X1
% 0.96/0.93      | sK4 != X0 ),
% 0.96/0.93      inference(resolution_lifted,[status(thm)],[c_1,c_642]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_677,plain,
% 0.96/0.93      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.96/0.93      | ~ l1_pre_topc(sK3)
% 0.96/0.93      | k2_pre_topc(sK3,sK4) = sK4 ),
% 0.96/0.93      inference(unflattening,[status(thm)],[c_676]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_679,plain,
% 0.96/0.93      ( k2_pre_topc(sK3,sK4) = sK4 ),
% 0.96/0.93      inference(global_propositional_subsumption,
% 0.96/0.93                [status(thm)],
% 0.96/0.93                [c_677,c_27,c_26]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_1089,plain,
% 0.96/0.93      ( k2_pre_topc(sK3,sK4) = sK4 ),
% 0.96/0.93      inference(subtyping,[status(esa)],[c_679]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_1277,plain,
% 0.96/0.93      ( u1_struct_0(sK3) = sK4 ),
% 0.96/0.93      inference(light_normalisation,[status(thm)],[c_1088,c_1089]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_1283,plain,
% 0.96/0.93      ( v2_tex_2(sK4,sK3) != iProver_top
% 0.96/0.93      | m1_subset_1(sK4,k1_zfmisc_1(sK4)) != iProver_top ),
% 0.96/0.93      inference(light_normalisation,[status(thm)],[c_1272,c_1277]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_1091,negated_conjecture,
% 0.96/0.93      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 0.96/0.93      inference(subtyping,[status(esa)],[c_26]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_1266,plain,
% 0.96/0.93      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 0.96/0.93      inference(predicate_to_equality,[status(thm)],[c_1091]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_1280,plain,
% 0.96/0.93      ( m1_subset_1(sK4,k1_zfmisc_1(sK4)) = iProver_top ),
% 0.96/0.93      inference(light_normalisation,[status(thm)],[c_1266,c_1277]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_1286,plain,
% 0.96/0.93      ( v2_tex_2(sK4,sK3) != iProver_top ),
% 0.96/0.93      inference(forward_subsumption_resolution,
% 0.96/0.93                [status(thm)],
% 0.96/0.93                [c_1283,c_1280]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_9,plain,
% 0.96/0.93      ( v2_tex_2(X0,X1)
% 0.96/0.93      | ~ v3_tex_2(X0,X1)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.96/0.93      | ~ l1_pre_topc(X1) ),
% 0.96/0.93      inference(cnf_transformation,[],[f51]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_701,plain,
% 0.96/0.93      ( v2_tex_2(X0,X1)
% 0.96/0.93      | ~ v3_tex_2(X0,X1)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.96/0.93      | sK3 != X1 ),
% 0.96/0.93      inference(resolution_lifted,[status(thm)],[c_9,c_27]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_702,plain,
% 0.96/0.93      ( v2_tex_2(X0,sK3)
% 0.96/0.93      | ~ v3_tex_2(X0,sK3)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 0.96/0.93      inference(unflattening,[status(thm)],[c_701]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_908,plain,
% 0.96/0.93      ( v2_tex_2(X0,sK3)
% 0.96/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 0.96/0.93      | sK3 != sK3
% 0.96/0.93      | sK4 != X0 ),
% 0.96/0.93      inference(resolution_lifted,[status(thm)],[c_24,c_702]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_909,plain,
% 0.96/0.93      ( v2_tex_2(sK4,sK3)
% 0.96/0.93      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 0.96/0.93      inference(unflattening,[status(thm)],[c_908]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_910,plain,
% 0.96/0.93      ( v2_tex_2(sK4,sK3) = iProver_top
% 0.96/0.93      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 0.96/0.93      inference(predicate_to_equality,[status(thm)],[c_909]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(c_35,plain,
% 0.96/0.93      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 0.96/0.93      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 0.96/0.93  
% 0.96/0.93  cnf(contradiction,plain,
% 0.96/0.93      ( $false ),
% 0.96/0.93      inference(minisat,[status(thm)],[c_1286,c_910,c_35]) ).
% 0.96/0.93  
% 0.96/0.93  
% 0.96/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 0.96/0.93  
% 0.96/0.93  ------                               Statistics
% 0.96/0.93  
% 0.96/0.93  ------ General
% 0.96/0.93  
% 0.96/0.93  abstr_ref_over_cycles:                  0
% 0.96/0.93  abstr_ref_under_cycles:                 0
% 0.96/0.93  gc_basic_clause_elim:                   0
% 0.96/0.93  forced_gc_time:                         0
% 0.96/0.93  parsing_time:                           0.008
% 0.96/0.93  unif_index_cands_time:                  0.
% 0.96/0.93  unif_index_add_time:                    0.
% 0.96/0.93  orderings_time:                         0.
% 0.96/0.93  out_proof_time:                         0.01
% 0.96/0.93  total_time:                             0.069
% 0.96/0.93  num_of_symbols:                         52
% 0.96/0.93  num_of_terms:                           873
% 0.96/0.93  
% 0.96/0.93  ------ Preprocessing
% 0.96/0.93  
% 0.96/0.93  num_of_splits:                          0
% 0.96/0.93  num_of_split_atoms:                     0
% 0.96/0.93  num_of_reused_defs:                     0
% 0.96/0.93  num_eq_ax_congr_red:                    18
% 0.96/0.93  num_of_sem_filtered_clauses:            1
% 0.96/0.93  num_of_subtypes:                        3
% 0.96/0.93  monotx_restored_types:                  0
% 0.96/0.93  sat_num_of_epr_types:                   0
% 0.96/0.93  sat_num_of_non_cyclic_types:            0
% 0.96/0.93  sat_guarded_non_collapsed_types:        0
% 0.96/0.93  num_pure_diseq_elim:                    0
% 0.96/0.93  simp_replaced_by:                       0
% 0.96/0.93  res_preprocessed:                       78
% 0.96/0.93  prep_upred:                             0
% 0.96/0.93  prep_unflattend:                        33
% 0.96/0.93  smt_new_axioms:                         0
% 0.96/0.93  pred_elim_cands:                        3
% 0.96/0.93  pred_elim:                              10
% 0.96/0.93  pred_elim_cl:                           21
% 0.96/0.93  pred_elim_cycles:                       13
% 0.96/0.93  merged_defs:                            0
% 0.96/0.93  merged_defs_ncl:                        0
% 0.96/0.93  bin_hyper_res:                          0
% 0.96/0.93  prep_cycles:                            4
% 0.96/0.93  pred_elim_time:                         0.014
% 0.96/0.93  splitting_time:                         0.
% 0.96/0.93  sem_filter_time:                        0.
% 0.96/0.93  monotx_time:                            0.
% 0.96/0.93  subtype_inf_time:                       0.
% 0.96/0.93  
% 0.96/0.93  ------ Problem properties
% 0.96/0.93  
% 0.96/0.93  clauses:                                10
% 0.96/0.93  conjectures:                            2
% 0.96/0.93  epr:                                    1
% 0.96/0.93  horn:                                   8
% 0.96/0.93  ground:                                 5
% 0.96/0.93  unary:                                  4
% 0.96/0.93  binary:                                 1
% 0.96/0.93  lits:                                   25
% 0.96/0.93  lits_eq:                                5
% 0.96/0.93  fd_pure:                                0
% 0.96/0.93  fd_pseudo:                              0
% 0.96/0.93  fd_cond:                                0
% 0.96/0.93  fd_pseudo_cond:                         0
% 0.96/0.93  ac_symbols:                             0
% 0.96/0.93  
% 0.96/0.93  ------ Propositional Solver
% 0.96/0.93  
% 0.96/0.93  prop_solver_calls:                      21
% 0.96/0.93  prop_fast_solver_calls:                 640
% 0.96/0.93  smt_solver_calls:                       0
% 0.96/0.93  smt_fast_solver_calls:                  0
% 0.96/0.93  prop_num_of_clauses:                    239
% 0.96/0.93  prop_preprocess_simplified:             1845
% 0.96/0.93  prop_fo_subsumed:                       19
% 0.96/0.93  prop_solver_time:                       0.
% 0.96/0.93  smt_solver_time:                        0.
% 0.96/0.93  smt_fast_solver_time:                   0.
% 0.96/0.93  prop_fast_solver_time:                  0.
% 0.96/0.93  prop_unsat_core_time:                   0.
% 0.96/0.93  
% 0.96/0.93  ------ QBF
% 0.96/0.93  
% 0.96/0.93  qbf_q_res:                              0
% 0.96/0.93  qbf_num_tautologies:                    0
% 0.96/0.93  qbf_prep_cycles:                        0
% 0.96/0.93  
% 0.96/0.93  ------ BMC1
% 0.96/0.93  
% 0.96/0.93  bmc1_current_bound:                     -1
% 0.96/0.93  bmc1_last_solved_bound:                 -1
% 0.96/0.93  bmc1_unsat_core_size:                   -1
% 0.96/0.93  bmc1_unsat_core_parents_size:           -1
% 0.96/0.93  bmc1_merge_next_fun:                    0
% 0.96/0.93  bmc1_unsat_core_clauses_time:           0.
% 0.96/0.93  
% 0.96/0.93  ------ Instantiation
% 0.96/0.93  
% 0.96/0.93  inst_num_of_clauses:                    18
% 0.96/0.93  inst_num_in_passive:                    0
% 0.96/0.93  inst_num_in_active:                     0
% 0.96/0.93  inst_num_in_unprocessed:                18
% 0.96/0.93  inst_num_of_loops:                      0
% 0.96/0.93  inst_num_of_learning_restarts:          0
% 0.96/0.93  inst_num_moves_active_passive:          0
% 0.96/0.93  inst_lit_activity:                      0
% 0.96/0.93  inst_lit_activity_moves:                0
% 0.96/0.93  inst_num_tautologies:                   0
% 0.96/0.93  inst_num_prop_implied:                  0
% 0.96/0.93  inst_num_existing_simplified:           0
% 0.96/0.93  inst_num_eq_res_simplified:             0
% 0.96/0.93  inst_num_child_elim:                    0
% 0.96/0.93  inst_num_of_dismatching_blockings:      0
% 0.96/0.93  inst_num_of_non_proper_insts:           0
% 0.96/0.93  inst_num_of_duplicates:                 0
% 0.96/0.93  inst_inst_num_from_inst_to_res:         0
% 0.96/0.93  inst_dismatching_checking_time:         0.
% 0.96/0.93  
% 0.96/0.93  ------ Resolution
% 0.96/0.93  
% 0.96/0.93  res_num_of_clauses:                     0
% 0.96/0.93  res_num_in_passive:                     0
% 0.96/0.93  res_num_in_active:                      0
% 0.96/0.93  res_num_of_loops:                       82
% 0.96/0.93  res_forward_subset_subsumed:            9
% 0.96/0.93  res_backward_subset_subsumed:           0
% 0.96/0.93  res_forward_subsumed:                   0
% 0.96/0.93  res_backward_subsumed:                  0
% 0.96/0.93  res_forward_subsumption_resolution:     0
% 0.96/0.93  res_backward_subsumption_resolution:    0
% 0.96/0.93  res_clause_to_clause_subsumption:       19
% 0.96/0.93  res_orphan_elimination:                 0
% 0.96/0.93  res_tautology_del:                      12
% 0.96/0.93  res_num_eq_res_simplified:              1
% 0.96/0.93  res_num_sel_changes:                    0
% 0.96/0.93  res_moves_from_active_to_pass:          0
% 0.96/0.93  
% 0.96/0.93  ------ Superposition
% 0.96/0.93  
% 0.96/0.93  sup_time_total:                         0.
% 0.96/0.93  sup_time_generating:                    0.
% 0.96/0.93  sup_time_sim_full:                      0.
% 0.96/0.93  sup_time_sim_immed:                     0.
% 0.96/0.93  
% 0.96/0.93  sup_num_of_clauses:                     1
% 0.96/0.93  sup_num_in_active:                      0
% 0.96/0.93  sup_num_in_passive:                     1
% 0.96/0.93  sup_num_of_loops:                       0
% 0.96/0.93  sup_fw_superposition:                   0
% 0.96/0.93  sup_bw_superposition:                   0
% 0.96/0.93  sup_immediate_simplified:               0
% 0.96/0.93  sup_given_eliminated:                   0
% 0.96/0.93  comparisons_done:                       0
% 0.96/0.93  comparisons_avoided:                    0
% 0.96/0.93  
% 0.96/0.93  ------ Simplifications
% 0.96/0.93  
% 0.96/0.93  
% 0.96/0.93  sim_fw_subset_subsumed:                 0
% 0.96/0.93  sim_bw_subset_subsumed:                 0
% 0.96/0.93  sim_fw_subsumed:                        0
% 0.96/0.93  sim_bw_subsumed:                        0
% 0.96/0.93  sim_fw_subsumption_res:                 1
% 0.96/0.93  sim_bw_subsumption_res:                 0
% 0.96/0.93  sim_tautology_del:                      0
% 0.96/0.93  sim_eq_tautology_del:                   0
% 0.96/0.93  sim_eq_res_simp:                        0
% 0.96/0.93  sim_fw_demodulated:                     0
% 0.96/0.93  sim_bw_demodulated:                     0
% 0.96/0.93  sim_light_normalised:                   8
% 0.96/0.93  sim_joinable_taut:                      0
% 0.96/0.93  sim_joinable_simp:                      0
% 0.96/0.93  sim_ac_normalised:                      0
% 0.96/0.93  sim_smt_subsumption:                    0
% 0.96/0.93  
%------------------------------------------------------------------------------
