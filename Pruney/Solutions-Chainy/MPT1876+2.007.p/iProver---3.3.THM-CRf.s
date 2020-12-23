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
% DateTime   : Thu Dec  3 12:26:47 EST 2020

% Result     : Theorem 1.24s
% Output     : CNFRefutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 718 expanded)
%              Number of clauses        :  102 ( 174 expanded)
%              Number of leaves         :   18 ( 162 expanded)
%              Depth                    :   25
%              Number of atoms          :  883 (5401 expanded)
%              Number of equality atoms :  140 ( 257 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   20 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ( ~ v1_zfmisc_1(sK2)
          | ~ v2_tex_2(sK2,X0) )
        & ( v1_zfmisc_1(sK2)
          | v2_tex_2(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,sK1) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK1)
      & v2_tdlat_3(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ~ v1_zfmisc_1(sK2)
      | ~ v2_tex_2(sK2,sK1) )
    & ( v1_zfmisc_1(sK2)
      | v2_tex_2(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & ~ v1_xboole_0(sK2)
    & l1_pre_topc(sK1)
    & v2_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f41,f43,f42])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK0(X0,X1)) = X1
        & m1_pre_topc(sK0(X0,X1),X0)
        & ~ v2_struct_0(sK0(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK0(X0,X1)) = X1
            & m1_pre_topc(sK0(X0,X1),X0)
            & ~ v2_struct_0(sK0(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f37])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,
    ( ~ v1_zfmisc_1(sK2)
    | ~ v2_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f55,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,
    ( v1_zfmisc_1(sK2)
    | v2_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v2_pre_topc(X1)
              & v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( v2_tdlat_3(X1)
              & v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tdlat_3(X1)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_pre_topc(X1)
          | ~ v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tdlat_3(X1)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_pre_topc(X1)
          | ~ v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_pre_topc(X1)
      | ~ v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(sK0(X1,X0),X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_21,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(sK0(X1,X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_407,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_pre_topc(sK0(X0,sK2),X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_739,plain,
    ( m1_pre_topc(sK0(X0,sK2),X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_407])).

cnf(c_16,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_306,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_4])).

cnf(c_18,negated_conjecture,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_179,plain,
    ( ~ v1_zfmisc_1(sK2)
    | ~ v2_tex_2(sK2,sK1) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_180,plain,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ v1_zfmisc_1(sK2) ),
    inference(renaming,[status(thm)],[c_179])).

cnf(c_344,plain,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_306,c_180])).

cnf(c_628,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X2) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_344])).

cnf(c_629,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(X0,sK1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X1) != sK2 ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_633,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v7_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(X0,sK1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X1) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_629,c_25,c_22])).

cnf(c_634,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(X0,sK1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X1) != sK2 ),
    inference(renaming,[status(thm)],[c_633])).

cnf(c_804,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X1) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_634])).

cnf(c_1078,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v7_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK0(X1,sK2) != X0
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X2) != sK2
    | sK1 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_739,c_804])).

cnf(c_1079,plain,
    ( ~ v1_tdlat_3(sK0(sK1,sK2))
    | v2_struct_0(sK0(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0) != sK2
    | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_1078])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK0(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_388,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK0(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_389,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK0(X0,sK2))
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_391,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_struct_0(sK0(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK0(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_424,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK0(X1,X0)) = X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_425,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(sK0(X0,sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_427,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK0(sK1,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_425])).

cnf(c_1083,plain,
    ( u1_struct_0(X0) != sK2
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | ~ v1_tdlat_3(sK0(sK1,sK2))
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1079,c_25,c_22,c_20,c_391,c_427])).

cnf(c_1084,plain,
    ( ~ v1_tdlat_3(sK0(sK1,sK2))
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0) != sK2 ),
    inference(renaming,[status(thm)],[c_1083])).

cnf(c_1279,plain,
    ( ~ v1_tdlat_3(sK0(sK1,sK2))
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_1084])).

cnf(c_1473,plain,
    ( ~ v1_tdlat_3(sK0(sK1,sK2))
    | ~ v7_struct_0(X0_45)
    | ~ l1_pre_topc(X0_45)
    | u1_struct_0(X0_45) != sK2 ),
    inference(subtyping,[status(esa)],[c_1279])).

cnf(c_2159,plain,
    ( ~ v1_tdlat_3(sK0(sK1,sK2))
    | ~ v7_struct_0(sK0(sK1,sK2))
    | ~ l1_pre_topc(sK0(sK1,sK2))
    | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1473])).

cnf(c_10,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_8,plain,
    ( ~ v2_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_139,plain,
    ( ~ l1_pre_topc(X0)
    | v7_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | v2_struct_0(X0)
    | ~ v1_tdlat_3(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_8])).

cnf(c_140,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_139])).

cnf(c_1479,plain,
    ( ~ v1_tdlat_3(X0_45)
    | v2_struct_0(X0_45)
    | ~ v2_tdlat_3(X0_45)
    | v7_struct_0(X0_45)
    | ~ l1_pre_topc(X0_45) ),
    inference(subtyping,[status(esa)],[c_140])).

cnf(c_2127,plain,
    ( ~ v1_tdlat_3(sK0(sK1,sK2))
    | v2_struct_0(sK0(sK1,sK2))
    | ~ v2_tdlat_3(sK0(sK1,sK2))
    | v7_struct_0(sK0(sK1,sK2))
    | ~ l1_pre_topc(sK0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1479])).

cnf(c_17,plain,
    ( ~ v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3,plain,
    ( v7_struct_0(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_320,plain,
    ( v7_struct_0(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_3])).

cnf(c_19,negated_conjecture,
    ( v2_tex_2(sK2,sK1)
    | v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_181,plain,
    ( v1_zfmisc_1(sK2)
    | v2_tex_2(sK2,sK1) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_182,plain,
    ( v2_tex_2(sK2,sK1)
    | v1_zfmisc_1(sK2) ),
    inference(renaming,[status(thm)],[c_181])).

cnf(c_361,plain,
    ( v2_tex_2(sK2,sK1)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_320,c_182])).

cnf(c_662,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v7_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X2) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_361])).

cnf(c_663,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(X0,sK1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X1) != sK2 ),
    inference(unflattening,[status(thm)],[c_662])).

cnf(c_667,plain,
    ( ~ l1_pre_topc(X1)
    | v7_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(X0,sK1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X1) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_663,c_25,c_22])).

cnf(c_668,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(X0,sK1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X1) != sK2 ),
    inference(renaming,[status(thm)],[c_667])).

cnf(c_775,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X1) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_668])).

cnf(c_1105,plain,
    ( v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v7_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | sK0(X1,sK2) != X0
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X2) != sK2
    | sK1 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_739,c_775])).

cnf(c_1106,plain,
    ( v1_tdlat_3(sK0(sK1,sK2))
    | v2_struct_0(sK0(sK1,sK2))
    | v2_struct_0(sK1)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0) != sK2
    | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_1105])).

cnf(c_1110,plain,
    ( u1_struct_0(X0) != sK2
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | v1_tdlat_3(sK0(sK1,sK2))
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1106,c_25,c_22,c_20,c_391,c_427])).

cnf(c_1111,plain,
    ( v1_tdlat_3(sK0(sK1,sK2))
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0) != sK2 ),
    inference(renaming,[status(thm)],[c_1110])).

cnf(c_1275,plain,
    ( v1_tdlat_3(sK0(sK1,sK2))
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_1111])).

cnf(c_1474,plain,
    ( v1_tdlat_3(sK0(sK1,sK2))
    | v7_struct_0(X0_45)
    | ~ l1_pre_topc(X0_45)
    | u1_struct_0(X0_45) != sK2 ),
    inference(subtyping,[status(esa)],[c_1275])).

cnf(c_2097,plain,
    ( v1_tdlat_3(sK0(sK1,sK2))
    | v7_struct_0(sK0(X0_45,sK2))
    | ~ l1_pre_topc(sK0(X0_45,sK2))
    | u1_struct_0(sK0(X0_45,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1474])).

cnf(c_2099,plain,
    ( v1_tdlat_3(sK0(sK1,sK2))
    | v7_struct_0(sK0(sK1,sK2))
    | ~ l1_pre_topc(sK0(sK1,sK2))
    | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_2097])).

cnf(c_1502,plain,
    ( k1_zfmisc_1(X0_46) = k1_zfmisc_1(X1_46)
    | X0_46 != X1_46 ),
    theory(equality)).

cnf(c_2066,plain,
    ( k1_zfmisc_1(u1_struct_0(X0_45)) = k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0_45) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1502])).

cnf(c_2067,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2066])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_985,plain,
    ( v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X0)
    | X2 != X1
    | sK0(X2,sK2) != X0
    | k1_zfmisc_1(u1_struct_0(X2)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_739])).

cnf(c_986,plain,
    ( v1_tdlat_3(sK0(X0,sK2))
    | v2_struct_0(X0)
    | v2_struct_0(sK0(X0,sK2))
    | ~ v7_struct_0(sK0(X0,sK2))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(sK0(X0,sK2))
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_985])).

cnf(c_757,plain,
    ( v2_struct_0(X0)
    | ~ v2_struct_0(sK0(X0,sK2))
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_389])).

cnf(c_1289,plain,
    ( v2_struct_0(X0)
    | ~ v2_struct_0(sK0(X0,sK2))
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_757])).

cnf(c_1348,plain,
    ( v2_struct_0(X0)
    | v1_tdlat_3(sK0(X0,sK2))
    | ~ v7_struct_0(sK0(X0,sK2))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(sK0(X0,sK2))
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_986,c_1289])).

cnf(c_1349,plain,
    ( v1_tdlat_3(sK0(X0,sK2))
    | v2_struct_0(X0)
    | ~ v7_struct_0(sK0(X0,sK2))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(sK0(X0,sK2))
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_1348])).

cnf(c_1470,plain,
    ( v1_tdlat_3(sK0(X0_45,sK2))
    | v2_struct_0(X0_45)
    | ~ v7_struct_0(sK0(X0_45,sK2))
    | ~ l1_pre_topc(X0_45)
    | ~ v2_pre_topc(sK0(X0_45,sK2))
    | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_1349])).

cnf(c_1551,plain,
    ( v1_tdlat_3(sK0(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ v7_struct_0(sK0(sK1,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0(sK1,sK2))
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1470])).

cnf(c_721,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK0(X0,sK2)) = sK2
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_425])).

cnf(c_1293,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK0(X0,sK2)) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_721])).

cnf(c_1471,plain,
    ( v2_struct_0(X0_45)
    | ~ l1_pre_topc(X0_45)
    | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK0(X0_45,sK2)) = sK2 ),
    inference(subtyping,[status(esa)],[c_1293])).

cnf(c_1548,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK0(sK1,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_1471])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1057,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X2)
    | X0 != X1
    | sK0(X0,sK2) != X2
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_739])).

cnf(c_1058,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK0(X0,sK2))
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1057])).

cnf(c_1475,plain,
    ( v2_struct_0(X0_45)
    | ~ l1_pre_topc(X0_45)
    | ~ v2_pre_topc(X0_45)
    | v2_pre_topc(sK0(X0_45,sK2))
    | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_1058])).

cnf(c_1536,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK0(sK1,sK2))
    | ~ v2_pre_topc(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1475])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1039,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(X2)
    | X0 != X1
    | sK0(X0,sK2) != X2
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_739])).

cnf(c_1040,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK0(X0,sK2))
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1039])).

cnf(c_1476,plain,
    ( v2_struct_0(X0_45)
    | ~ l1_pre_topc(X0_45)
    | l1_pre_topc(sK0(X0_45,sK2))
    | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_1040])).

cnf(c_1533,plain,
    ( v2_struct_0(sK1)
    | l1_pre_topc(sK0(sK1,sK2))
    | ~ l1_pre_topc(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1476])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_958,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X0)
    | v2_tdlat_3(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | X1 != X0
    | sK0(X1,sK2) != X2
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_739])).

cnf(c_959,plain,
    ( v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | v2_tdlat_3(sK0(X0,sK2))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_958])).

cnf(c_963,plain,
    ( ~ l1_pre_topc(X0)
    | v2_tdlat_3(sK0(X0,sK2))
    | ~ v2_tdlat_3(X0)
    | v2_struct_0(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_959,c_8])).

cnf(c_964,plain,
    ( v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | v2_tdlat_3(sK0(X0,sK2))
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_963])).

cnf(c_1477,plain,
    ( v2_struct_0(X0_45)
    | ~ v2_tdlat_3(X0_45)
    | v2_tdlat_3(sK0(X0_45,sK2))
    | ~ l1_pre_topc(X0_45)
    | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_964])).

cnf(c_1530,plain,
    ( v2_struct_0(sK1)
    | v2_tdlat_3(sK0(sK1,sK2))
    | ~ v2_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1477])).

cnf(c_1489,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_1513,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_1496,plain,
    ( u1_struct_0(X0_45) = u1_struct_0(X1_45)
    | X0_45 != X1_45 ),
    theory(equality)).

cnf(c_1505,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1496])).

cnf(c_23,negated_conjecture,
    ( v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2159,c_2127,c_2099,c_2067,c_1551,c_1548,c_1536,c_1533,c_1530,c_1513,c_1505,c_391,c_20,c_22,c_23,c_24,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:47:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.24/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.24/0.99  
% 1.24/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.24/0.99  
% 1.24/0.99  ------  iProver source info
% 1.24/0.99  
% 1.24/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.24/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.24/0.99  git: non_committed_changes: false
% 1.24/0.99  git: last_make_outside_of_git: false
% 1.24/0.99  
% 1.24/0.99  ------ 
% 1.24/0.99  
% 1.24/0.99  ------ Input Options
% 1.24/0.99  
% 1.24/0.99  --out_options                           all
% 1.24/0.99  --tptp_safe_out                         true
% 1.24/0.99  --problem_path                          ""
% 1.24/0.99  --include_path                          ""
% 1.24/0.99  --clausifier                            res/vclausify_rel
% 1.24/0.99  --clausifier_options                    --mode clausify
% 1.24/0.99  --stdin                                 false
% 1.24/0.99  --stats_out                             all
% 1.24/0.99  
% 1.24/0.99  ------ General Options
% 1.24/0.99  
% 1.24/0.99  --fof                                   false
% 1.24/0.99  --time_out_real                         305.
% 1.24/0.99  --time_out_virtual                      -1.
% 1.24/0.99  --symbol_type_check                     false
% 1.24/0.99  --clausify_out                          false
% 1.24/0.99  --sig_cnt_out                           false
% 1.24/0.99  --trig_cnt_out                          false
% 1.24/0.99  --trig_cnt_out_tolerance                1.
% 1.24/0.99  --trig_cnt_out_sk_spl                   false
% 1.24/0.99  --abstr_cl_out                          false
% 1.24/0.99  
% 1.24/0.99  ------ Global Options
% 1.24/0.99  
% 1.24/0.99  --schedule                              default
% 1.24/0.99  --add_important_lit                     false
% 1.24/0.99  --prop_solver_per_cl                    1000
% 1.24/0.99  --min_unsat_core                        false
% 1.24/0.99  --soft_assumptions                      false
% 1.24/0.99  --soft_lemma_size                       3
% 1.24/0.99  --prop_impl_unit_size                   0
% 1.24/0.99  --prop_impl_unit                        []
% 1.24/0.99  --share_sel_clauses                     true
% 1.24/0.99  --reset_solvers                         false
% 1.24/0.99  --bc_imp_inh                            [conj_cone]
% 1.24/0.99  --conj_cone_tolerance                   3.
% 1.24/0.99  --extra_neg_conj                        none
% 1.24/0.99  --large_theory_mode                     true
% 1.24/0.99  --prolific_symb_bound                   200
% 1.24/0.99  --lt_threshold                          2000
% 1.24/0.99  --clause_weak_htbl                      true
% 1.24/0.99  --gc_record_bc_elim                     false
% 1.24/0.99  
% 1.24/0.99  ------ Preprocessing Options
% 1.24/0.99  
% 1.24/0.99  --preprocessing_flag                    true
% 1.24/0.99  --time_out_prep_mult                    0.1
% 1.24/0.99  --splitting_mode                        input
% 1.24/0.99  --splitting_grd                         true
% 1.24/0.99  --splitting_cvd                         false
% 1.24/0.99  --splitting_cvd_svl                     false
% 1.24/0.99  --splitting_nvd                         32
% 1.24/0.99  --sub_typing                            true
% 1.24/0.99  --prep_gs_sim                           true
% 1.24/0.99  --prep_unflatten                        true
% 1.24/0.99  --prep_res_sim                          true
% 1.24/0.99  --prep_upred                            true
% 1.24/0.99  --prep_sem_filter                       exhaustive
% 1.24/0.99  --prep_sem_filter_out                   false
% 1.24/0.99  --pred_elim                             true
% 1.24/0.99  --res_sim_input                         true
% 1.24/0.99  --eq_ax_congr_red                       true
% 1.24/0.99  --pure_diseq_elim                       true
% 1.24/0.99  --brand_transform                       false
% 1.24/0.99  --non_eq_to_eq                          false
% 1.24/0.99  --prep_def_merge                        true
% 1.24/0.99  --prep_def_merge_prop_impl              false
% 1.24/0.99  --prep_def_merge_mbd                    true
% 1.24/0.99  --prep_def_merge_tr_red                 false
% 1.24/0.99  --prep_def_merge_tr_cl                  false
% 1.24/0.99  --smt_preprocessing                     true
% 1.24/0.99  --smt_ac_axioms                         fast
% 1.24/0.99  --preprocessed_out                      false
% 1.24/0.99  --preprocessed_stats                    false
% 1.24/0.99  
% 1.24/0.99  ------ Abstraction refinement Options
% 1.24/0.99  
% 1.24/0.99  --abstr_ref                             []
% 1.24/0.99  --abstr_ref_prep                        false
% 1.24/0.99  --abstr_ref_until_sat                   false
% 1.24/0.99  --abstr_ref_sig_restrict                funpre
% 1.24/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.24/0.99  --abstr_ref_under                       []
% 1.24/0.99  
% 1.24/0.99  ------ SAT Options
% 1.24/0.99  
% 1.24/0.99  --sat_mode                              false
% 1.24/0.99  --sat_fm_restart_options                ""
% 1.24/0.99  --sat_gr_def                            false
% 1.24/0.99  --sat_epr_types                         true
% 1.24/0.99  --sat_non_cyclic_types                  false
% 1.24/0.99  --sat_finite_models                     false
% 1.24/0.99  --sat_fm_lemmas                         false
% 1.24/0.99  --sat_fm_prep                           false
% 1.24/0.99  --sat_fm_uc_incr                        true
% 1.24/0.99  --sat_out_model                         small
% 1.24/0.99  --sat_out_clauses                       false
% 1.24/0.99  
% 1.24/0.99  ------ QBF Options
% 1.24/0.99  
% 1.24/0.99  --qbf_mode                              false
% 1.24/0.99  --qbf_elim_univ                         false
% 1.24/0.99  --qbf_dom_inst                          none
% 1.24/0.99  --qbf_dom_pre_inst                      false
% 1.24/0.99  --qbf_sk_in                             false
% 1.24/0.99  --qbf_pred_elim                         true
% 1.24/0.99  --qbf_split                             512
% 1.24/0.99  
% 1.24/0.99  ------ BMC1 Options
% 1.24/0.99  
% 1.24/0.99  --bmc1_incremental                      false
% 1.24/0.99  --bmc1_axioms                           reachable_all
% 1.24/0.99  --bmc1_min_bound                        0
% 1.24/0.99  --bmc1_max_bound                        -1
% 1.24/0.99  --bmc1_max_bound_default                -1
% 1.24/0.99  --bmc1_symbol_reachability              true
% 1.24/0.99  --bmc1_property_lemmas                  false
% 1.24/0.99  --bmc1_k_induction                      false
% 1.24/0.99  --bmc1_non_equiv_states                 false
% 1.24/0.99  --bmc1_deadlock                         false
% 1.24/0.99  --bmc1_ucm                              false
% 1.24/0.99  --bmc1_add_unsat_core                   none
% 1.24/0.99  --bmc1_unsat_core_children              false
% 1.24/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.24/0.99  --bmc1_out_stat                         full
% 1.24/0.99  --bmc1_ground_init                      false
% 1.24/0.99  --bmc1_pre_inst_next_state              false
% 1.24/0.99  --bmc1_pre_inst_state                   false
% 1.24/0.99  --bmc1_pre_inst_reach_state             false
% 1.24/0.99  --bmc1_out_unsat_core                   false
% 1.24/0.99  --bmc1_aig_witness_out                  false
% 1.24/0.99  --bmc1_verbose                          false
% 1.24/0.99  --bmc1_dump_clauses_tptp                false
% 1.24/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.24/0.99  --bmc1_dump_file                        -
% 1.24/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.24/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.24/0.99  --bmc1_ucm_extend_mode                  1
% 1.24/0.99  --bmc1_ucm_init_mode                    2
% 1.24/0.99  --bmc1_ucm_cone_mode                    none
% 1.24/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.24/0.99  --bmc1_ucm_relax_model                  4
% 1.24/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.24/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.24/0.99  --bmc1_ucm_layered_model                none
% 1.24/0.99  --bmc1_ucm_max_lemma_size               10
% 1.24/0.99  
% 1.24/0.99  ------ AIG Options
% 1.24/0.99  
% 1.24/0.99  --aig_mode                              false
% 1.24/0.99  
% 1.24/0.99  ------ Instantiation Options
% 1.24/0.99  
% 1.24/0.99  --instantiation_flag                    true
% 1.24/0.99  --inst_sos_flag                         false
% 1.24/0.99  --inst_sos_phase                        true
% 1.24/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.24/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.24/0.99  --inst_lit_sel_side                     num_symb
% 1.24/0.99  --inst_solver_per_active                1400
% 1.24/0.99  --inst_solver_calls_frac                1.
% 1.24/0.99  --inst_passive_queue_type               priority_queues
% 1.24/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.24/0.99  --inst_passive_queues_freq              [25;2]
% 1.24/0.99  --inst_dismatching                      true
% 1.24/0.99  --inst_eager_unprocessed_to_passive     true
% 1.24/0.99  --inst_prop_sim_given                   true
% 1.24/0.99  --inst_prop_sim_new                     false
% 1.24/0.99  --inst_subs_new                         false
% 1.24/0.99  --inst_eq_res_simp                      false
% 1.24/0.99  --inst_subs_given                       false
% 1.24/0.99  --inst_orphan_elimination               true
% 1.24/0.99  --inst_learning_loop_flag               true
% 1.24/0.99  --inst_learning_start                   3000
% 1.24/0.99  --inst_learning_factor                  2
% 1.24/0.99  --inst_start_prop_sim_after_learn       3
% 1.24/0.99  --inst_sel_renew                        solver
% 1.24/0.99  --inst_lit_activity_flag                true
% 1.24/0.99  --inst_restr_to_given                   false
% 1.24/0.99  --inst_activity_threshold               500
% 1.24/0.99  --inst_out_proof                        true
% 1.24/0.99  
% 1.24/0.99  ------ Resolution Options
% 1.24/0.99  
% 1.24/0.99  --resolution_flag                       true
% 1.24/0.99  --res_lit_sel                           adaptive
% 1.24/0.99  --res_lit_sel_side                      none
% 1.24/0.99  --res_ordering                          kbo
% 1.24/0.99  --res_to_prop_solver                    active
% 1.24/0.99  --res_prop_simpl_new                    false
% 1.24/0.99  --res_prop_simpl_given                  true
% 1.24/0.99  --res_passive_queue_type                priority_queues
% 1.24/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.24/0.99  --res_passive_queues_freq               [15;5]
% 1.24/0.99  --res_forward_subs                      full
% 1.24/0.99  --res_backward_subs                     full
% 1.24/0.99  --res_forward_subs_resolution           true
% 1.24/0.99  --res_backward_subs_resolution          true
% 1.24/0.99  --res_orphan_elimination                true
% 1.24/0.99  --res_time_limit                        2.
% 1.24/0.99  --res_out_proof                         true
% 1.24/0.99  
% 1.24/0.99  ------ Superposition Options
% 1.24/0.99  
% 1.24/0.99  --superposition_flag                    true
% 1.24/0.99  --sup_passive_queue_type                priority_queues
% 1.24/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.24/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.24/0.99  --demod_completeness_check              fast
% 1.24/0.99  --demod_use_ground                      true
% 1.24/0.99  --sup_to_prop_solver                    passive
% 1.24/0.99  --sup_prop_simpl_new                    true
% 1.24/0.99  --sup_prop_simpl_given                  true
% 1.24/0.99  --sup_fun_splitting                     false
% 1.24/0.99  --sup_smt_interval                      50000
% 1.24/0.99  
% 1.24/0.99  ------ Superposition Simplification Setup
% 1.24/0.99  
% 1.24/0.99  --sup_indices_passive                   []
% 1.24/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.24/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.24/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.24/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.24/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.24/0.99  --sup_full_bw                           [BwDemod]
% 1.24/0.99  --sup_immed_triv                        [TrivRules]
% 1.24/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.24/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.24/0.99  --sup_immed_bw_main                     []
% 1.24/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.24/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.24/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.24/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.24/0.99  
% 1.24/0.99  ------ Combination Options
% 1.24/0.99  
% 1.24/0.99  --comb_res_mult                         3
% 1.24/0.99  --comb_sup_mult                         2
% 1.24/0.99  --comb_inst_mult                        10
% 1.24/0.99  
% 1.24/0.99  ------ Debug Options
% 1.24/0.99  
% 1.24/0.99  --dbg_backtrace                         false
% 1.24/0.99  --dbg_dump_prop_clauses                 false
% 1.24/0.99  --dbg_dump_prop_clauses_file            -
% 1.24/0.99  --dbg_out_stat                          false
% 1.24/0.99  ------ Parsing...
% 1.24/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.24/0.99  
% 1.24/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.24/0.99  
% 1.24/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.24/0.99  
% 1.24/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.24/0.99  ------ Proving...
% 1.24/0.99  ------ Problem Properties 
% 1.24/0.99  
% 1.24/0.99  
% 1.24/0.99  clauses                                 18
% 1.24/0.99  conjectures                             4
% 1.24/0.99  EPR                                     7
% 1.24/0.99  Horn                                    9
% 1.24/0.99  unary                                   4
% 1.24/0.99  binary                                  1
% 1.24/0.99  lits                                    64
% 1.24/0.99  lits eq                                 12
% 1.24/0.99  fd_pure                                 0
% 1.24/0.99  fd_pseudo                               0
% 1.24/0.99  fd_cond                                 0
% 1.24/0.99  fd_pseudo_cond                          0
% 1.24/0.99  AC symbols                              0
% 1.24/0.99  
% 1.24/0.99  ------ Schedule dynamic 5 is on 
% 1.24/0.99  
% 1.24/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.24/0.99  
% 1.24/0.99  
% 1.24/0.99  ------ 
% 1.24/0.99  Current options:
% 1.24/0.99  ------ 
% 1.24/0.99  
% 1.24/0.99  ------ Input Options
% 1.24/0.99  
% 1.24/0.99  --out_options                           all
% 1.24/0.99  --tptp_safe_out                         true
% 1.24/0.99  --problem_path                          ""
% 1.24/0.99  --include_path                          ""
% 1.24/0.99  --clausifier                            res/vclausify_rel
% 1.24/0.99  --clausifier_options                    --mode clausify
% 1.24/0.99  --stdin                                 false
% 1.24/0.99  --stats_out                             all
% 1.24/0.99  
% 1.24/0.99  ------ General Options
% 1.24/0.99  
% 1.24/0.99  --fof                                   false
% 1.24/0.99  --time_out_real                         305.
% 1.24/0.99  --time_out_virtual                      -1.
% 1.24/0.99  --symbol_type_check                     false
% 1.24/0.99  --clausify_out                          false
% 1.24/0.99  --sig_cnt_out                           false
% 1.24/0.99  --trig_cnt_out                          false
% 1.24/0.99  --trig_cnt_out_tolerance                1.
% 1.24/0.99  --trig_cnt_out_sk_spl                   false
% 1.24/0.99  --abstr_cl_out                          false
% 1.24/0.99  
% 1.24/0.99  ------ Global Options
% 1.24/0.99  
% 1.24/0.99  --schedule                              default
% 1.24/0.99  --add_important_lit                     false
% 1.24/0.99  --prop_solver_per_cl                    1000
% 1.24/0.99  --min_unsat_core                        false
% 1.24/0.99  --soft_assumptions                      false
% 1.24/0.99  --soft_lemma_size                       3
% 1.24/0.99  --prop_impl_unit_size                   0
% 1.24/0.99  --prop_impl_unit                        []
% 1.24/0.99  --share_sel_clauses                     true
% 1.24/0.99  --reset_solvers                         false
% 1.24/0.99  --bc_imp_inh                            [conj_cone]
% 1.24/0.99  --conj_cone_tolerance                   3.
% 1.24/0.99  --extra_neg_conj                        none
% 1.24/0.99  --large_theory_mode                     true
% 1.24/0.99  --prolific_symb_bound                   200
% 1.24/0.99  --lt_threshold                          2000
% 1.24/0.99  --clause_weak_htbl                      true
% 1.24/0.99  --gc_record_bc_elim                     false
% 1.24/0.99  
% 1.24/0.99  ------ Preprocessing Options
% 1.24/0.99  
% 1.24/0.99  --preprocessing_flag                    true
% 1.24/0.99  --time_out_prep_mult                    0.1
% 1.24/0.99  --splitting_mode                        input
% 1.24/0.99  --splitting_grd                         true
% 1.24/0.99  --splitting_cvd                         false
% 1.24/0.99  --splitting_cvd_svl                     false
% 1.24/0.99  --splitting_nvd                         32
% 1.24/0.99  --sub_typing                            true
% 1.24/0.99  --prep_gs_sim                           true
% 1.24/0.99  --prep_unflatten                        true
% 1.24/0.99  --prep_res_sim                          true
% 1.24/0.99  --prep_upred                            true
% 1.24/0.99  --prep_sem_filter                       exhaustive
% 1.24/0.99  --prep_sem_filter_out                   false
% 1.24/0.99  --pred_elim                             true
% 1.24/0.99  --res_sim_input                         true
% 1.24/0.99  --eq_ax_congr_red                       true
% 1.24/0.99  --pure_diseq_elim                       true
% 1.24/0.99  --brand_transform                       false
% 1.24/0.99  --non_eq_to_eq                          false
% 1.24/0.99  --prep_def_merge                        true
% 1.24/0.99  --prep_def_merge_prop_impl              false
% 1.24/0.99  --prep_def_merge_mbd                    true
% 1.24/0.99  --prep_def_merge_tr_red                 false
% 1.24/0.99  --prep_def_merge_tr_cl                  false
% 1.24/0.99  --smt_preprocessing                     true
% 1.24/0.99  --smt_ac_axioms                         fast
% 1.24/0.99  --preprocessed_out                      false
% 1.24/0.99  --preprocessed_stats                    false
% 1.24/0.99  
% 1.24/0.99  ------ Abstraction refinement Options
% 1.24/0.99  
% 1.24/0.99  --abstr_ref                             []
% 1.24/0.99  --abstr_ref_prep                        false
% 1.24/0.99  --abstr_ref_until_sat                   false
% 1.24/0.99  --abstr_ref_sig_restrict                funpre
% 1.24/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.24/0.99  --abstr_ref_under                       []
% 1.24/0.99  
% 1.24/0.99  ------ SAT Options
% 1.24/0.99  
% 1.24/0.99  --sat_mode                              false
% 1.24/0.99  --sat_fm_restart_options                ""
% 1.24/0.99  --sat_gr_def                            false
% 1.24/0.99  --sat_epr_types                         true
% 1.24/0.99  --sat_non_cyclic_types                  false
% 1.24/0.99  --sat_finite_models                     false
% 1.24/0.99  --sat_fm_lemmas                         false
% 1.24/0.99  --sat_fm_prep                           false
% 1.24/0.99  --sat_fm_uc_incr                        true
% 1.24/0.99  --sat_out_model                         small
% 1.24/0.99  --sat_out_clauses                       false
% 1.24/0.99  
% 1.24/0.99  ------ QBF Options
% 1.24/0.99  
% 1.24/0.99  --qbf_mode                              false
% 1.24/0.99  --qbf_elim_univ                         false
% 1.24/0.99  --qbf_dom_inst                          none
% 1.24/0.99  --qbf_dom_pre_inst                      false
% 1.24/0.99  --qbf_sk_in                             false
% 1.24/0.99  --qbf_pred_elim                         true
% 1.24/0.99  --qbf_split                             512
% 1.24/0.99  
% 1.24/0.99  ------ BMC1 Options
% 1.24/0.99  
% 1.24/0.99  --bmc1_incremental                      false
% 1.24/0.99  --bmc1_axioms                           reachable_all
% 1.24/0.99  --bmc1_min_bound                        0
% 1.24/0.99  --bmc1_max_bound                        -1
% 1.24/0.99  --bmc1_max_bound_default                -1
% 1.24/0.99  --bmc1_symbol_reachability              true
% 1.24/0.99  --bmc1_property_lemmas                  false
% 1.24/0.99  --bmc1_k_induction                      false
% 1.24/0.99  --bmc1_non_equiv_states                 false
% 1.24/0.99  --bmc1_deadlock                         false
% 1.24/0.99  --bmc1_ucm                              false
% 1.24/0.99  --bmc1_add_unsat_core                   none
% 1.24/0.99  --bmc1_unsat_core_children              false
% 1.24/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.24/0.99  --bmc1_out_stat                         full
% 1.24/0.99  --bmc1_ground_init                      false
% 1.24/0.99  --bmc1_pre_inst_next_state              false
% 1.24/0.99  --bmc1_pre_inst_state                   false
% 1.24/0.99  --bmc1_pre_inst_reach_state             false
% 1.24/0.99  --bmc1_out_unsat_core                   false
% 1.24/0.99  --bmc1_aig_witness_out                  false
% 1.24/0.99  --bmc1_verbose                          false
% 1.24/0.99  --bmc1_dump_clauses_tptp                false
% 1.24/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.24/0.99  --bmc1_dump_file                        -
% 1.24/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.24/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.24/0.99  --bmc1_ucm_extend_mode                  1
% 1.24/0.99  --bmc1_ucm_init_mode                    2
% 1.24/0.99  --bmc1_ucm_cone_mode                    none
% 1.24/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.24/0.99  --bmc1_ucm_relax_model                  4
% 1.24/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.24/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.24/0.99  --bmc1_ucm_layered_model                none
% 1.24/0.99  --bmc1_ucm_max_lemma_size               10
% 1.24/0.99  
% 1.24/0.99  ------ AIG Options
% 1.24/0.99  
% 1.24/0.99  --aig_mode                              false
% 1.24/0.99  
% 1.24/0.99  ------ Instantiation Options
% 1.24/0.99  
% 1.24/0.99  --instantiation_flag                    true
% 1.24/0.99  --inst_sos_flag                         false
% 1.24/0.99  --inst_sos_phase                        true
% 1.24/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.24/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.24/0.99  --inst_lit_sel_side                     none
% 1.24/0.99  --inst_solver_per_active                1400
% 1.24/0.99  --inst_solver_calls_frac                1.
% 1.24/0.99  --inst_passive_queue_type               priority_queues
% 1.24/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.24/0.99  --inst_passive_queues_freq              [25;2]
% 1.24/0.99  --inst_dismatching                      true
% 1.24/0.99  --inst_eager_unprocessed_to_passive     true
% 1.24/0.99  --inst_prop_sim_given                   true
% 1.24/0.99  --inst_prop_sim_new                     false
% 1.24/0.99  --inst_subs_new                         false
% 1.24/0.99  --inst_eq_res_simp                      false
% 1.24/0.99  --inst_subs_given                       false
% 1.24/0.99  --inst_orphan_elimination               true
% 1.24/0.99  --inst_learning_loop_flag               true
% 1.24/0.99  --inst_learning_start                   3000
% 1.24/0.99  --inst_learning_factor                  2
% 1.24/0.99  --inst_start_prop_sim_after_learn       3
% 1.24/0.99  --inst_sel_renew                        solver
% 1.24/0.99  --inst_lit_activity_flag                true
% 1.24/0.99  --inst_restr_to_given                   false
% 1.24/0.99  --inst_activity_threshold               500
% 1.24/0.99  --inst_out_proof                        true
% 1.24/0.99  
% 1.24/0.99  ------ Resolution Options
% 1.24/0.99  
% 1.24/0.99  --resolution_flag                       false
% 1.24/0.99  --res_lit_sel                           adaptive
% 1.24/0.99  --res_lit_sel_side                      none
% 1.24/0.99  --res_ordering                          kbo
% 1.24/0.99  --res_to_prop_solver                    active
% 1.24/0.99  --res_prop_simpl_new                    false
% 1.24/0.99  --res_prop_simpl_given                  true
% 1.24/0.99  --res_passive_queue_type                priority_queues
% 1.24/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.24/0.99  --res_passive_queues_freq               [15;5]
% 1.24/0.99  --res_forward_subs                      full
% 1.24/0.99  --res_backward_subs                     full
% 1.24/0.99  --res_forward_subs_resolution           true
% 1.24/0.99  --res_backward_subs_resolution          true
% 1.24/0.99  --res_orphan_elimination                true
% 1.24/0.99  --res_time_limit                        2.
% 1.24/0.99  --res_out_proof                         true
% 1.24/0.99  
% 1.24/0.99  ------ Superposition Options
% 1.24/0.99  
% 1.24/0.99  --superposition_flag                    true
% 1.24/0.99  --sup_passive_queue_type                priority_queues
% 1.24/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.24/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.24/0.99  --demod_completeness_check              fast
% 1.24/0.99  --demod_use_ground                      true
% 1.24/0.99  --sup_to_prop_solver                    passive
% 1.24/0.99  --sup_prop_simpl_new                    true
% 1.24/0.99  --sup_prop_simpl_given                  true
% 1.24/0.99  --sup_fun_splitting                     false
% 1.24/0.99  --sup_smt_interval                      50000
% 1.24/0.99  
% 1.24/0.99  ------ Superposition Simplification Setup
% 1.24/0.99  
% 1.24/0.99  --sup_indices_passive                   []
% 1.24/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.24/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.24/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.24/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.24/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.24/0.99  --sup_full_bw                           [BwDemod]
% 1.24/0.99  --sup_immed_triv                        [TrivRules]
% 1.24/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.24/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.24/0.99  --sup_immed_bw_main                     []
% 1.24/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.24/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.24/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.24/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.24/0.99  
% 1.24/0.99  ------ Combination Options
% 1.24/0.99  
% 1.24/0.99  --comb_res_mult                         3
% 1.24/0.99  --comb_sup_mult                         2
% 1.24/0.99  --comb_inst_mult                        10
% 1.24/0.99  
% 1.24/0.99  ------ Debug Options
% 1.24/0.99  
% 1.24/0.99  --dbg_backtrace                         false
% 1.24/0.99  --dbg_dump_prop_clauses                 false
% 1.24/0.99  --dbg_dump_prop_clauses_file            -
% 1.24/0.99  --dbg_out_stat                          false
% 1.24/0.99  
% 1.24/0.99  
% 1.24/0.99  
% 1.24/0.99  
% 1.24/0.99  ------ Proving...
% 1.24/0.99  
% 1.24/0.99  
% 1.24/0.99  % SZS status Theorem for theBenchmark.p
% 1.24/0.99  
% 1.24/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.24/0.99  
% 1.24/0.99  fof(f12,conjecture,(
% 1.24/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/0.99  
% 1.24/0.99  fof(f13,negated_conjecture,(
% 1.24/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.24/0.99    inference(negated_conjecture,[],[f12])).
% 1.24/0.99  
% 1.24/0.99  fof(f35,plain,(
% 1.24/0.99    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.24/0.99    inference(ennf_transformation,[],[f13])).
% 1.24/0.99  
% 1.24/0.99  fof(f36,plain,(
% 1.24/0.99    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.24/0.99    inference(flattening,[],[f35])).
% 1.24/0.99  
% 1.24/0.99  fof(f40,plain,(
% 1.24/0.99    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.24/0.99    inference(nnf_transformation,[],[f36])).
% 1.24/0.99  
% 1.24/0.99  fof(f41,plain,(
% 1.24/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.24/0.99    inference(flattening,[],[f40])).
% 1.24/0.99  
% 1.24/0.99  fof(f43,plain,(
% 1.24/0.99    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK2) | ~v2_tex_2(sK2,X0)) & (v1_zfmisc_1(sK2) | v2_tex_2(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK2))) )),
% 1.24/0.99    introduced(choice_axiom,[])).
% 1.24/0.99  
% 1.24/0.99  fof(f42,plain,(
% 1.24/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK1)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK1) & v2_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.24/0.99    introduced(choice_axiom,[])).
% 1.24/0.99  
% 1.24/0.99  fof(f44,plain,(
% 1.24/0.99    ((~v1_zfmisc_1(sK2) | ~v2_tex_2(sK2,sK1)) & (v1_zfmisc_1(sK2) | v2_tex_2(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(sK2)) & l1_pre_topc(sK1) & v2_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.24/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f41,f43,f42])).
% 1.24/0.99  
% 1.24/0.99  fof(f68,plain,(
% 1.24/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.24/0.99    inference(cnf_transformation,[],[f44])).
% 1.24/0.99  
% 1.24/0.99  fof(f10,axiom,(
% 1.24/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 1.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/0.99  
% 1.24/0.99  fof(f14,plain,(
% 1.24/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 1.24/0.99    inference(pure_predicate_removal,[],[f10])).
% 1.24/0.99  
% 1.24/0.99  fof(f31,plain,(
% 1.24/0.99    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.24/0.99    inference(ennf_transformation,[],[f14])).
% 1.24/0.99  
% 1.24/0.99  fof(f32,plain,(
% 1.24/0.99    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.24/0.99    inference(flattening,[],[f31])).
% 1.24/0.99  
% 1.24/0.99  fof(f37,plain,(
% 1.24/0.99    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK0(X0,X1)) = X1 & m1_pre_topc(sK0(X0,X1),X0) & ~v2_struct_0(sK0(X0,X1))))),
% 1.24/0.99    introduced(choice_axiom,[])).
% 1.24/0.99  
% 1.24/0.99  fof(f38,plain,(
% 1.24/0.99    ! [X0] : (! [X1] : ((u1_struct_0(sK0(X0,X1)) = X1 & m1_pre_topc(sK0(X0,X1),X0) & ~v2_struct_0(sK0(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.24/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f37])).
% 1.24/0.99  
% 1.24/0.99  fof(f59,plain,(
% 1.24/0.99    ( ! [X0,X1] : (m1_pre_topc(sK0(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.24/0.99    inference(cnf_transformation,[],[f38])).
% 1.24/0.99  
% 1.24/0.99  fof(f67,plain,(
% 1.24/0.99    ~v1_xboole_0(sK2)),
% 1.24/0.99    inference(cnf_transformation,[],[f44])).
% 1.24/0.99  
% 1.24/0.99  fof(f11,axiom,(
% 1.24/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 1.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/0.99  
% 1.24/0.99  fof(f33,plain,(
% 1.24/0.99    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.24/0.99    inference(ennf_transformation,[],[f11])).
% 1.24/0.99  
% 1.24/0.99  fof(f34,plain,(
% 1.24/0.99    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.24/0.99    inference(flattening,[],[f33])).
% 1.24/0.99  
% 1.24/0.99  fof(f39,plain,(
% 1.24/0.99    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.24/0.99    inference(nnf_transformation,[],[f34])).
% 1.24/0.99  
% 1.24/0.99  fof(f62,plain,(
% 1.24/0.99    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.24/0.99    inference(cnf_transformation,[],[f39])).
% 1.24/0.99  
% 1.24/0.99  fof(f71,plain,(
% 1.24/0.99    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.24/0.99    inference(equality_resolution,[],[f62])).
% 1.24/0.99  
% 1.24/0.99  fof(f2,axiom,(
% 1.24/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/0.99  
% 1.24/0.99  fof(f17,plain,(
% 1.24/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.24/0.99    inference(ennf_transformation,[],[f2])).
% 1.24/0.99  
% 1.24/0.99  fof(f46,plain,(
% 1.24/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.24/0.99    inference(cnf_transformation,[],[f17])).
% 1.24/0.99  
% 1.24/0.99  fof(f5,axiom,(
% 1.24/0.99    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 1.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/0.99  
% 1.24/0.99  fof(f21,plain,(
% 1.24/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 1.24/0.99    inference(ennf_transformation,[],[f5])).
% 1.24/0.99  
% 1.24/0.99  fof(f22,plain,(
% 1.24/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 1.24/0.99    inference(flattening,[],[f21])).
% 1.24/0.99  
% 1.24/0.99  fof(f49,plain,(
% 1.24/0.99    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 1.24/0.99    inference(cnf_transformation,[],[f22])).
% 1.24/0.99  
% 1.24/0.99  fof(f70,plain,(
% 1.24/0.99    ~v1_zfmisc_1(sK2) | ~v2_tex_2(sK2,sK1)),
% 1.24/0.99    inference(cnf_transformation,[],[f44])).
% 1.24/0.99  
% 1.24/0.99  fof(f63,plain,(
% 1.24/0.99    ~v2_struct_0(sK1)),
% 1.24/0.99    inference(cnf_transformation,[],[f44])).
% 1.24/0.99  
% 1.24/0.99  fof(f66,plain,(
% 1.24/0.99    l1_pre_topc(sK1)),
% 1.24/0.99    inference(cnf_transformation,[],[f44])).
% 1.24/0.99  
% 1.24/0.99  fof(f58,plain,(
% 1.24/0.99    ( ! [X0,X1] : (~v2_struct_0(sK0(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.24/0.99    inference(cnf_transformation,[],[f38])).
% 1.24/0.99  
% 1.24/0.99  fof(f60,plain,(
% 1.24/0.99    ( ! [X0,X1] : (u1_struct_0(sK0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.24/0.99    inference(cnf_transformation,[],[f38])).
% 1.24/0.99  
% 1.24/0.99  fof(f8,axiom,(
% 1.24/0.99    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 1.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/0.99  
% 1.24/0.99  fof(f27,plain,(
% 1.24/0.99    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.24/0.99    inference(ennf_transformation,[],[f8])).
% 1.24/0.99  
% 1.24/0.99  fof(f28,plain,(
% 1.24/0.99    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.24/0.99    inference(flattening,[],[f27])).
% 1.24/0.99  
% 1.24/0.99  fof(f55,plain,(
% 1.24/0.99    ( ! [X0] : (v7_struct_0(X0) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.24/0.99    inference(cnf_transformation,[],[f28])).
% 1.24/0.99  
% 1.24/0.99  fof(f7,axiom,(
% 1.24/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/0.99  
% 1.24/0.99  fof(f25,plain,(
% 1.24/0.99    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.24/0.99    inference(ennf_transformation,[],[f7])).
% 1.24/0.99  
% 1.24/0.99  fof(f26,plain,(
% 1.24/0.99    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.24/0.99    inference(flattening,[],[f25])).
% 1.24/0.99  
% 1.24/0.99  fof(f53,plain,(
% 1.24/0.99    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 1.24/0.99    inference(cnf_transformation,[],[f26])).
% 1.24/0.99  
% 1.24/0.99  fof(f61,plain,(
% 1.24/0.99    ( ! [X2,X0,X1] : (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.24/0.99    inference(cnf_transformation,[],[f39])).
% 1.24/0.99  
% 1.24/0.99  fof(f72,plain,(
% 1.24/0.99    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~v2_tex_2(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.24/0.99    inference(equality_resolution,[],[f61])).
% 1.24/0.99  
% 1.24/0.99  fof(f4,axiom,(
% 1.24/0.99    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 1.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/0.99  
% 1.24/0.99  fof(f19,plain,(
% 1.24/0.99    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 1.24/0.99    inference(ennf_transformation,[],[f4])).
% 1.24/0.99  
% 1.24/0.99  fof(f20,plain,(
% 1.24/0.99    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 1.24/0.99    inference(flattening,[],[f19])).
% 1.24/0.99  
% 1.24/0.99  fof(f48,plain,(
% 1.24/0.99    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 1.24/0.99    inference(cnf_transformation,[],[f20])).
% 1.24/0.99  
% 1.24/0.99  fof(f69,plain,(
% 1.24/0.99    v1_zfmisc_1(sK2) | v2_tex_2(sK2,sK1)),
% 1.24/0.99    inference(cnf_transformation,[],[f44])).
% 1.24/0.99  
% 1.24/0.99  fof(f6,axiom,(
% 1.24/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v2_pre_topc(X1) & v7_struct_0(X1) & ~v2_struct_0(X1)) => (v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 1.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/0.99  
% 1.24/0.99  fof(f23,plain,(
% 1.24/0.99    ! [X0] : (! [X1] : (((v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.24/0.99    inference(ennf_transformation,[],[f6])).
% 1.24/0.99  
% 1.24/0.99  fof(f24,plain,(
% 1.24/0.99    ! [X0] : (! [X1] : ((v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) | ~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.24/0.99    inference(flattening,[],[f23])).
% 1.24/0.99  
% 1.24/0.99  fof(f51,plain,(
% 1.24/0.99    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.24/0.99    inference(cnf_transformation,[],[f24])).
% 1.24/0.99  
% 1.24/0.99  fof(f1,axiom,(
% 1.24/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/0.99  
% 1.24/0.99  fof(f15,plain,(
% 1.24/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.24/0.99    inference(ennf_transformation,[],[f1])).
% 1.24/0.99  
% 1.24/0.99  fof(f16,plain,(
% 1.24/0.99    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.24/0.99    inference(flattening,[],[f15])).
% 1.24/0.99  
% 1.24/0.99  fof(f45,plain,(
% 1.24/0.99    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.24/0.99    inference(cnf_transformation,[],[f16])).
% 1.24/0.99  
% 1.24/0.99  fof(f3,axiom,(
% 1.24/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/0.99  
% 1.24/0.99  fof(f18,plain,(
% 1.24/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.24/0.99    inference(ennf_transformation,[],[f3])).
% 1.24/0.99  
% 1.24/0.99  fof(f47,plain,(
% 1.24/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.24/0.99    inference(cnf_transformation,[],[f18])).
% 1.24/0.99  
% 1.24/0.99  fof(f9,axiom,(
% 1.24/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 1.24/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.24/0.99  
% 1.24/0.99  fof(f29,plain,(
% 1.24/0.99    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.24/0.99    inference(ennf_transformation,[],[f9])).
% 1.24/0.99  
% 1.24/0.99  fof(f30,plain,(
% 1.24/0.99    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.24/0.99    inference(flattening,[],[f29])).
% 1.24/0.99  
% 1.24/0.99  fof(f57,plain,(
% 1.24/0.99    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.24/0.99    inference(cnf_transformation,[],[f30])).
% 1.24/0.99  
% 1.24/0.99  fof(f65,plain,(
% 1.24/0.99    v2_tdlat_3(sK1)),
% 1.24/0.99    inference(cnf_transformation,[],[f44])).
% 1.24/0.99  
% 1.24/0.99  fof(f64,plain,(
% 1.24/0.99    v2_pre_topc(sK1)),
% 1.24/0.99    inference(cnf_transformation,[],[f44])).
% 1.24/0.99  
% 1.24/0.99  cnf(c_20,negated_conjecture,
% 1.24/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.24/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_14,plain,
% 1.24/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.24/0.99      | m1_pre_topc(sK0(X1,X0),X1)
% 1.24/0.99      | v1_xboole_0(X0)
% 1.24/0.99      | v2_struct_0(X1)
% 1.24/0.99      | ~ l1_pre_topc(X1) ),
% 1.24/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_21,negated_conjecture,
% 1.24/0.99      ( ~ v1_xboole_0(sK2) ),
% 1.24/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_406,plain,
% 1.24/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.24/0.99      | m1_pre_topc(sK0(X1,X0),X1)
% 1.24/0.99      | v2_struct_0(X1)
% 1.24/0.99      | ~ l1_pre_topc(X1)
% 1.24/0.99      | sK2 != X0 ),
% 1.24/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_407,plain,
% 1.24/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.24/0.99      | m1_pre_topc(sK0(X0,sK2),X0)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X0) ),
% 1.24/0.99      inference(unflattening,[status(thm)],[c_406]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_739,plain,
% 1.24/0.99      ( m1_pre_topc(sK0(X0,sK2),X0)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | sK2 != sK2 ),
% 1.24/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_407]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_16,plain,
% 1.24/0.99      ( v2_tex_2(u1_struct_0(X0),X1)
% 1.24/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.24/0.99      | ~ m1_pre_topc(X0,X1)
% 1.24/0.99      | ~ v1_tdlat_3(X0)
% 1.24/0.99      | v2_struct_0(X1)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X1) ),
% 1.24/0.99      inference(cnf_transformation,[],[f71]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1,plain,
% 1.24/0.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 1.24/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_4,plain,
% 1.24/0.99      ( ~ v7_struct_0(X0)
% 1.24/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 1.24/0.99      | ~ l1_struct_0(X0) ),
% 1.24/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_306,plain,
% 1.24/0.99      ( ~ v7_struct_0(X0)
% 1.24/0.99      | v1_zfmisc_1(u1_struct_0(X0))
% 1.24/0.99      | ~ l1_pre_topc(X0) ),
% 1.24/0.99      inference(resolution,[status(thm)],[c_1,c_4]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_18,negated_conjecture,
% 1.24/0.99      ( ~ v2_tex_2(sK2,sK1) | ~ v1_zfmisc_1(sK2) ),
% 1.24/0.99      inference(cnf_transformation,[],[f70]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_179,plain,
% 1.24/0.99      ( ~ v1_zfmisc_1(sK2) | ~ v2_tex_2(sK2,sK1) ),
% 1.24/0.99      inference(prop_impl,[status(thm)],[c_18]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_180,plain,
% 1.24/0.99      ( ~ v2_tex_2(sK2,sK1) | ~ v1_zfmisc_1(sK2) ),
% 1.24/0.99      inference(renaming,[status(thm)],[c_179]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_344,plain,
% 1.24/0.99      ( ~ v2_tex_2(sK2,sK1)
% 1.24/0.99      | ~ v7_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | u1_struct_0(X0) != sK2 ),
% 1.24/0.99      inference(resolution_lifted,[status(thm)],[c_306,c_180]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_628,plain,
% 1.24/0.99      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.24/0.99      | ~ m1_pre_topc(X0,X1)
% 1.24/0.99      | ~ v1_tdlat_3(X0)
% 1.24/0.99      | v2_struct_0(X1)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | ~ v7_struct_0(X2)
% 1.24/0.99      | ~ l1_pre_topc(X1)
% 1.24/0.99      | ~ l1_pre_topc(X2)
% 1.24/0.99      | u1_struct_0(X0) != sK2
% 1.24/0.99      | u1_struct_0(X2) != sK2
% 1.24/0.99      | sK1 != X1 ),
% 1.24/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_344]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_629,plain,
% 1.24/0.99      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.24/0.99      | ~ m1_pre_topc(X0,sK1)
% 1.24/0.99      | ~ v1_tdlat_3(X0)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | v2_struct_0(sK1)
% 1.24/0.99      | ~ v7_struct_0(X1)
% 1.24/0.99      | ~ l1_pre_topc(X1)
% 1.24/0.99      | ~ l1_pre_topc(sK1)
% 1.24/0.99      | u1_struct_0(X0) != sK2
% 1.24/0.99      | u1_struct_0(X1) != sK2 ),
% 1.24/0.99      inference(unflattening,[status(thm)],[c_628]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_25,negated_conjecture,
% 1.24/0.99      ( ~ v2_struct_0(sK1) ),
% 1.24/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_22,negated_conjecture,
% 1.24/0.99      ( l1_pre_topc(sK1) ),
% 1.24/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_633,plain,
% 1.24/0.99      ( ~ l1_pre_topc(X1)
% 1.24/0.99      | ~ v7_struct_0(X1)
% 1.24/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.24/0.99      | ~ m1_pre_topc(X0,sK1)
% 1.24/0.99      | ~ v1_tdlat_3(X0)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | u1_struct_0(X0) != sK2
% 1.24/0.99      | u1_struct_0(X1) != sK2 ),
% 1.24/0.99      inference(global_propositional_subsumption,
% 1.24/0.99                [status(thm)],
% 1.24/0.99                [c_629,c_25,c_22]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_634,plain,
% 1.24/0.99      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.24/0.99      | ~ m1_pre_topc(X0,sK1)
% 1.24/0.99      | ~ v1_tdlat_3(X0)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | ~ v7_struct_0(X1)
% 1.24/0.99      | ~ l1_pre_topc(X1)
% 1.24/0.99      | u1_struct_0(X0) != sK2
% 1.24/0.99      | u1_struct_0(X1) != sK2 ),
% 1.24/0.99      inference(renaming,[status(thm)],[c_633]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_804,plain,
% 1.24/0.99      ( ~ m1_pre_topc(X0,sK1)
% 1.24/0.99      | ~ v1_tdlat_3(X0)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | ~ v7_struct_0(X1)
% 1.24/0.99      | ~ l1_pre_topc(X1)
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | u1_struct_0(X0) != sK2
% 1.24/0.99      | u1_struct_0(X1) != sK2 ),
% 1.24/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_634]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1078,plain,
% 1.24/0.99      ( ~ v1_tdlat_3(X0)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | v2_struct_0(X1)
% 1.24/0.99      | ~ v7_struct_0(X2)
% 1.24/0.99      | ~ l1_pre_topc(X1)
% 1.24/0.99      | ~ l1_pre_topc(X2)
% 1.24/0.99      | sK0(X1,sK2) != X0
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | u1_struct_0(X0) != sK2
% 1.24/0.99      | u1_struct_0(X2) != sK2
% 1.24/0.99      | sK1 != X1
% 1.24/0.99      | sK2 != sK2 ),
% 1.24/0.99      inference(resolution_lifted,[status(thm)],[c_739,c_804]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1079,plain,
% 1.24/0.99      ( ~ v1_tdlat_3(sK0(sK1,sK2))
% 1.24/0.99      | v2_struct_0(sK0(sK1,sK2))
% 1.24/0.99      | v2_struct_0(sK1)
% 1.24/0.99      | ~ v7_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | ~ l1_pre_topc(sK1)
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | u1_struct_0(X0) != sK2
% 1.24/0.99      | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
% 1.24/0.99      inference(unflattening,[status(thm)],[c_1078]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_15,plain,
% 1.24/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.24/0.99      | v1_xboole_0(X0)
% 1.24/0.99      | v2_struct_0(X1)
% 1.24/0.99      | ~ v2_struct_0(sK0(X1,X0))
% 1.24/0.99      | ~ l1_pre_topc(X1) ),
% 1.24/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_388,plain,
% 1.24/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.24/0.99      | v2_struct_0(X1)
% 1.24/0.99      | ~ v2_struct_0(sK0(X1,X0))
% 1.24/0.99      | ~ l1_pre_topc(X1)
% 1.24/0.99      | sK2 != X0 ),
% 1.24/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_389,plain,
% 1.24/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | ~ v2_struct_0(sK0(X0,sK2))
% 1.24/0.99      | ~ l1_pre_topc(X0) ),
% 1.24/0.99      inference(unflattening,[status(thm)],[c_388]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_391,plain,
% 1.24/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.24/0.99      | ~ v2_struct_0(sK0(sK1,sK2))
% 1.24/0.99      | v2_struct_0(sK1)
% 1.24/0.99      | ~ l1_pre_topc(sK1) ),
% 1.24/0.99      inference(instantiation,[status(thm)],[c_389]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_13,plain,
% 1.24/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.24/0.99      | v1_xboole_0(X0)
% 1.24/0.99      | v2_struct_0(X1)
% 1.24/0.99      | ~ l1_pre_topc(X1)
% 1.24/0.99      | u1_struct_0(sK0(X1,X0)) = X0 ),
% 1.24/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_424,plain,
% 1.24/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.24/0.99      | v2_struct_0(X1)
% 1.24/0.99      | ~ l1_pre_topc(X1)
% 1.24/0.99      | u1_struct_0(sK0(X1,X0)) = X0
% 1.24/0.99      | sK2 != X0 ),
% 1.24/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_425,plain,
% 1.24/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | u1_struct_0(sK0(X0,sK2)) = sK2 ),
% 1.24/0.99      inference(unflattening,[status(thm)],[c_424]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_427,plain,
% 1.24/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.24/0.99      | v2_struct_0(sK1)
% 1.24/0.99      | ~ l1_pre_topc(sK1)
% 1.24/0.99      | u1_struct_0(sK0(sK1,sK2)) = sK2 ),
% 1.24/0.99      inference(instantiation,[status(thm)],[c_425]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1083,plain,
% 1.24/0.99      ( u1_struct_0(X0) != sK2
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | ~ v1_tdlat_3(sK0(sK1,sK2))
% 1.24/0.99      | ~ v7_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X0) ),
% 1.24/0.99      inference(global_propositional_subsumption,
% 1.24/0.99                [status(thm)],
% 1.24/0.99                [c_1079,c_25,c_22,c_20,c_391,c_427]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1084,plain,
% 1.24/0.99      ( ~ v1_tdlat_3(sK0(sK1,sK2))
% 1.24/0.99      | ~ v7_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | u1_struct_0(X0) != sK2 ),
% 1.24/0.99      inference(renaming,[status(thm)],[c_1083]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1279,plain,
% 1.24/0.99      ( ~ v1_tdlat_3(sK0(sK1,sK2))
% 1.24/0.99      | ~ v7_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | u1_struct_0(X0) != sK2 ),
% 1.24/0.99      inference(equality_resolution_simp,[status(thm)],[c_1084]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1473,plain,
% 1.24/0.99      ( ~ v1_tdlat_3(sK0(sK1,sK2))
% 1.24/0.99      | ~ v7_struct_0(X0_45)
% 1.24/0.99      | ~ l1_pre_topc(X0_45)
% 1.24/0.99      | u1_struct_0(X0_45) != sK2 ),
% 1.24/0.99      inference(subtyping,[status(esa)],[c_1279]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_2159,plain,
% 1.24/0.99      ( ~ v1_tdlat_3(sK0(sK1,sK2))
% 1.24/0.99      | ~ v7_struct_0(sK0(sK1,sK2))
% 1.24/0.99      | ~ l1_pre_topc(sK0(sK1,sK2))
% 1.24/0.99      | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
% 1.24/0.99      inference(instantiation,[status(thm)],[c_1473]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_10,plain,
% 1.24/0.99      ( ~ v1_tdlat_3(X0)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | ~ v2_tdlat_3(X0)
% 1.24/0.99      | v7_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | ~ v2_pre_topc(X0) ),
% 1.24/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_8,plain,
% 1.24/0.99      ( ~ v2_tdlat_3(X0) | ~ l1_pre_topc(X0) | v2_pre_topc(X0) ),
% 1.24/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_139,plain,
% 1.24/0.99      ( ~ l1_pre_topc(X0)
% 1.24/0.99      | v7_struct_0(X0)
% 1.24/0.99      | ~ v2_tdlat_3(X0)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | ~ v1_tdlat_3(X0) ),
% 1.24/0.99      inference(global_propositional_subsumption,
% 1.24/0.99                [status(thm)],
% 1.24/0.99                [c_10,c_8]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_140,plain,
% 1.24/0.99      ( ~ v1_tdlat_3(X0)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | ~ v2_tdlat_3(X0)
% 1.24/0.99      | v7_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X0) ),
% 1.24/0.99      inference(renaming,[status(thm)],[c_139]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1479,plain,
% 1.24/0.99      ( ~ v1_tdlat_3(X0_45)
% 1.24/0.99      | v2_struct_0(X0_45)
% 1.24/0.99      | ~ v2_tdlat_3(X0_45)
% 1.24/0.99      | v7_struct_0(X0_45)
% 1.24/0.99      | ~ l1_pre_topc(X0_45) ),
% 1.24/0.99      inference(subtyping,[status(esa)],[c_140]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_2127,plain,
% 1.24/0.99      ( ~ v1_tdlat_3(sK0(sK1,sK2))
% 1.24/0.99      | v2_struct_0(sK0(sK1,sK2))
% 1.24/0.99      | ~ v2_tdlat_3(sK0(sK1,sK2))
% 1.24/0.99      | v7_struct_0(sK0(sK1,sK2))
% 1.24/0.99      | ~ l1_pre_topc(sK0(sK1,sK2)) ),
% 1.24/0.99      inference(instantiation,[status(thm)],[c_1479]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_17,plain,
% 1.24/0.99      ( ~ v2_tex_2(u1_struct_0(X0),X1)
% 1.24/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.24/0.99      | ~ m1_pre_topc(X0,X1)
% 1.24/0.99      | v1_tdlat_3(X0)
% 1.24/0.99      | v2_struct_0(X1)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X1) ),
% 1.24/0.99      inference(cnf_transformation,[],[f72]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_3,plain,
% 1.24/0.99      ( v7_struct_0(X0)
% 1.24/0.99      | ~ v1_zfmisc_1(u1_struct_0(X0))
% 1.24/0.99      | ~ l1_struct_0(X0) ),
% 1.24/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_320,plain,
% 1.24/0.99      ( v7_struct_0(X0)
% 1.24/0.99      | ~ v1_zfmisc_1(u1_struct_0(X0))
% 1.24/0.99      | ~ l1_pre_topc(X0) ),
% 1.24/0.99      inference(resolution,[status(thm)],[c_1,c_3]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_19,negated_conjecture,
% 1.24/0.99      ( v2_tex_2(sK2,sK1) | v1_zfmisc_1(sK2) ),
% 1.24/0.99      inference(cnf_transformation,[],[f69]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_181,plain,
% 1.24/0.99      ( v1_zfmisc_1(sK2) | v2_tex_2(sK2,sK1) ),
% 1.24/0.99      inference(prop_impl,[status(thm)],[c_19]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_182,plain,
% 1.24/0.99      ( v2_tex_2(sK2,sK1) | v1_zfmisc_1(sK2) ),
% 1.24/0.99      inference(renaming,[status(thm)],[c_181]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_361,plain,
% 1.24/0.99      ( v2_tex_2(sK2,sK1)
% 1.24/0.99      | v7_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | u1_struct_0(X0) != sK2 ),
% 1.24/0.99      inference(resolution_lifted,[status(thm)],[c_320,c_182]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_662,plain,
% 1.24/0.99      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.24/0.99      | ~ m1_pre_topc(X0,X1)
% 1.24/0.99      | v1_tdlat_3(X0)
% 1.24/0.99      | v2_struct_0(X1)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | v7_struct_0(X2)
% 1.24/0.99      | ~ l1_pre_topc(X1)
% 1.24/0.99      | ~ l1_pre_topc(X2)
% 1.24/0.99      | u1_struct_0(X0) != sK2
% 1.24/0.99      | u1_struct_0(X2) != sK2
% 1.24/0.99      | sK1 != X1 ),
% 1.24/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_361]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_663,plain,
% 1.24/0.99      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.24/0.99      | ~ m1_pre_topc(X0,sK1)
% 1.24/0.99      | v1_tdlat_3(X0)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | v2_struct_0(sK1)
% 1.24/0.99      | v7_struct_0(X1)
% 1.24/0.99      | ~ l1_pre_topc(X1)
% 1.24/0.99      | ~ l1_pre_topc(sK1)
% 1.24/0.99      | u1_struct_0(X0) != sK2
% 1.24/0.99      | u1_struct_0(X1) != sK2 ),
% 1.24/0.99      inference(unflattening,[status(thm)],[c_662]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_667,plain,
% 1.24/0.99      ( ~ l1_pre_topc(X1)
% 1.24/0.99      | v7_struct_0(X1)
% 1.24/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.24/0.99      | ~ m1_pre_topc(X0,sK1)
% 1.24/0.99      | v1_tdlat_3(X0)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | u1_struct_0(X0) != sK2
% 1.24/0.99      | u1_struct_0(X1) != sK2 ),
% 1.24/0.99      inference(global_propositional_subsumption,
% 1.24/0.99                [status(thm)],
% 1.24/0.99                [c_663,c_25,c_22]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_668,plain,
% 1.24/0.99      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.24/0.99      | ~ m1_pre_topc(X0,sK1)
% 1.24/0.99      | v1_tdlat_3(X0)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | v7_struct_0(X1)
% 1.24/0.99      | ~ l1_pre_topc(X1)
% 1.24/0.99      | u1_struct_0(X0) != sK2
% 1.24/0.99      | u1_struct_0(X1) != sK2 ),
% 1.24/0.99      inference(renaming,[status(thm)],[c_667]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_775,plain,
% 1.24/0.99      ( ~ m1_pre_topc(X0,sK1)
% 1.24/0.99      | v1_tdlat_3(X0)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | v7_struct_0(X1)
% 1.24/0.99      | ~ l1_pre_topc(X1)
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | u1_struct_0(X0) != sK2
% 1.24/0.99      | u1_struct_0(X1) != sK2 ),
% 1.24/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_668]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1105,plain,
% 1.24/0.99      ( v1_tdlat_3(X0)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | v2_struct_0(X1)
% 1.24/0.99      | v7_struct_0(X2)
% 1.24/0.99      | ~ l1_pre_topc(X1)
% 1.24/0.99      | ~ l1_pre_topc(X2)
% 1.24/0.99      | sK0(X1,sK2) != X0
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | u1_struct_0(X0) != sK2
% 1.24/0.99      | u1_struct_0(X2) != sK2
% 1.24/0.99      | sK1 != X1
% 1.24/0.99      | sK2 != sK2 ),
% 1.24/0.99      inference(resolution_lifted,[status(thm)],[c_739,c_775]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1106,plain,
% 1.24/0.99      ( v1_tdlat_3(sK0(sK1,sK2))
% 1.24/0.99      | v2_struct_0(sK0(sK1,sK2))
% 1.24/0.99      | v2_struct_0(sK1)
% 1.24/0.99      | v7_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | ~ l1_pre_topc(sK1)
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | u1_struct_0(X0) != sK2
% 1.24/0.99      | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
% 1.24/0.99      inference(unflattening,[status(thm)],[c_1105]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1110,plain,
% 1.24/0.99      ( u1_struct_0(X0) != sK2
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | v1_tdlat_3(sK0(sK1,sK2))
% 1.24/0.99      | v7_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X0) ),
% 1.24/0.99      inference(global_propositional_subsumption,
% 1.24/0.99                [status(thm)],
% 1.24/0.99                [c_1106,c_25,c_22,c_20,c_391,c_427]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1111,plain,
% 1.24/0.99      ( v1_tdlat_3(sK0(sK1,sK2))
% 1.24/0.99      | v7_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | u1_struct_0(X0) != sK2 ),
% 1.24/0.99      inference(renaming,[status(thm)],[c_1110]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1275,plain,
% 1.24/0.99      ( v1_tdlat_3(sK0(sK1,sK2))
% 1.24/0.99      | v7_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | u1_struct_0(X0) != sK2 ),
% 1.24/0.99      inference(equality_resolution_simp,[status(thm)],[c_1111]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1474,plain,
% 1.24/0.99      ( v1_tdlat_3(sK0(sK1,sK2))
% 1.24/0.99      | v7_struct_0(X0_45)
% 1.24/0.99      | ~ l1_pre_topc(X0_45)
% 1.24/0.99      | u1_struct_0(X0_45) != sK2 ),
% 1.24/0.99      inference(subtyping,[status(esa)],[c_1275]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_2097,plain,
% 1.24/0.99      ( v1_tdlat_3(sK0(sK1,sK2))
% 1.24/0.99      | v7_struct_0(sK0(X0_45,sK2))
% 1.24/0.99      | ~ l1_pre_topc(sK0(X0_45,sK2))
% 1.24/0.99      | u1_struct_0(sK0(X0_45,sK2)) != sK2 ),
% 1.24/0.99      inference(instantiation,[status(thm)],[c_1474]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_2099,plain,
% 1.24/0.99      ( v1_tdlat_3(sK0(sK1,sK2))
% 1.24/0.99      | v7_struct_0(sK0(sK1,sK2))
% 1.24/0.99      | ~ l1_pre_topc(sK0(sK1,sK2))
% 1.24/0.99      | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
% 1.24/0.99      inference(instantiation,[status(thm)],[c_2097]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1502,plain,
% 1.24/0.99      ( k1_zfmisc_1(X0_46) = k1_zfmisc_1(X1_46) | X0_46 != X1_46 ),
% 1.24/0.99      theory(equality) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_2066,plain,
% 1.24/0.99      ( k1_zfmisc_1(u1_struct_0(X0_45)) = k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | u1_struct_0(X0_45) != u1_struct_0(sK1) ),
% 1.24/0.99      inference(instantiation,[status(thm)],[c_1502]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_2067,plain,
% 1.24/0.99      ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.24/0.99      inference(instantiation,[status(thm)],[c_2066]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_6,plain,
% 1.24/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.24/0.99      | v1_tdlat_3(X0)
% 1.24/0.99      | v2_struct_0(X1)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | ~ v7_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X1)
% 1.24/0.99      | ~ v2_pre_topc(X0) ),
% 1.24/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_985,plain,
% 1.24/0.99      ( v1_tdlat_3(X0)
% 1.24/0.99      | v2_struct_0(X1)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | v2_struct_0(X2)
% 1.24/0.99      | ~ v7_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X1)
% 1.24/0.99      | ~ l1_pre_topc(X2)
% 1.24/0.99      | ~ v2_pre_topc(X0)
% 1.24/0.99      | X2 != X1
% 1.24/0.99      | sK0(X2,sK2) != X0
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X2)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | sK2 != sK2 ),
% 1.24/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_739]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_986,plain,
% 1.24/0.99      ( v1_tdlat_3(sK0(X0,sK2))
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | v2_struct_0(sK0(X0,sK2))
% 1.24/0.99      | ~ v7_struct_0(sK0(X0,sK2))
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | ~ v2_pre_topc(sK0(X0,sK2))
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.24/0.99      inference(unflattening,[status(thm)],[c_985]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_757,plain,
% 1.24/0.99      ( v2_struct_0(X0)
% 1.24/0.99      | ~ v2_struct_0(sK0(X0,sK2))
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | sK2 != sK2 ),
% 1.24/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_389]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1289,plain,
% 1.24/0.99      ( v2_struct_0(X0)
% 1.24/0.99      | ~ v2_struct_0(sK0(X0,sK2))
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.24/0.99      inference(equality_resolution_simp,[status(thm)],[c_757]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1348,plain,
% 1.24/0.99      ( v2_struct_0(X0)
% 1.24/0.99      | v1_tdlat_3(sK0(X0,sK2))
% 1.24/0.99      | ~ v7_struct_0(sK0(X0,sK2))
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | ~ v2_pre_topc(sK0(X0,sK2))
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.24/0.99      inference(global_propositional_subsumption,
% 1.24/0.99                [status(thm)],
% 1.24/0.99                [c_986,c_1289]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1349,plain,
% 1.24/0.99      ( v1_tdlat_3(sK0(X0,sK2))
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | ~ v7_struct_0(sK0(X0,sK2))
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | ~ v2_pre_topc(sK0(X0,sK2))
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.24/0.99      inference(renaming,[status(thm)],[c_1348]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1470,plain,
% 1.24/0.99      ( v1_tdlat_3(sK0(X0_45,sK2))
% 1.24/0.99      | v2_struct_0(X0_45)
% 1.24/0.99      | ~ v7_struct_0(sK0(X0_45,sK2))
% 1.24/0.99      | ~ l1_pre_topc(X0_45)
% 1.24/0.99      | ~ v2_pre_topc(sK0(X0_45,sK2))
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.24/0.99      inference(subtyping,[status(esa)],[c_1349]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1551,plain,
% 1.24/0.99      ( v1_tdlat_3(sK0(sK1,sK2))
% 1.24/0.99      | v2_struct_0(sK1)
% 1.24/0.99      | ~ v7_struct_0(sK0(sK1,sK2))
% 1.24/0.99      | ~ l1_pre_topc(sK1)
% 1.24/0.99      | ~ v2_pre_topc(sK0(sK1,sK2))
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.24/0.99      inference(instantiation,[status(thm)],[c_1470]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_721,plain,
% 1.24/0.99      ( v2_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | u1_struct_0(sK0(X0,sK2)) = sK2
% 1.24/0.99      | sK2 != sK2 ),
% 1.24/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_425]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1293,plain,
% 1.24/0.99      ( v2_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | u1_struct_0(sK0(X0,sK2)) = sK2 ),
% 1.24/0.99      inference(equality_resolution_simp,[status(thm)],[c_721]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1471,plain,
% 1.24/0.99      ( v2_struct_0(X0_45)
% 1.24/0.99      | ~ l1_pre_topc(X0_45)
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | u1_struct_0(sK0(X0_45,sK2)) = sK2 ),
% 1.24/0.99      inference(subtyping,[status(esa)],[c_1293]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1548,plain,
% 1.24/0.99      ( v2_struct_0(sK1)
% 1.24/0.99      | ~ l1_pre_topc(sK1)
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | u1_struct_0(sK0(sK1,sK2)) = sK2 ),
% 1.24/0.99      inference(instantiation,[status(thm)],[c_1471]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_0,plain,
% 1.24/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.24/0.99      | ~ l1_pre_topc(X1)
% 1.24/0.99      | ~ v2_pre_topc(X1)
% 1.24/0.99      | v2_pre_topc(X0) ),
% 1.24/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1057,plain,
% 1.24/0.99      ( v2_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X1)
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | ~ v2_pre_topc(X1)
% 1.24/0.99      | v2_pre_topc(X2)
% 1.24/0.99      | X0 != X1
% 1.24/0.99      | sK0(X0,sK2) != X2
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | sK2 != sK2 ),
% 1.24/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_739]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1058,plain,
% 1.24/0.99      ( v2_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | ~ v2_pre_topc(X0)
% 1.24/0.99      | v2_pre_topc(sK0(X0,sK2))
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.24/0.99      inference(unflattening,[status(thm)],[c_1057]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1475,plain,
% 1.24/0.99      ( v2_struct_0(X0_45)
% 1.24/0.99      | ~ l1_pre_topc(X0_45)
% 1.24/0.99      | ~ v2_pre_topc(X0_45)
% 1.24/0.99      | v2_pre_topc(sK0(X0_45,sK2))
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.24/0.99      inference(subtyping,[status(esa)],[c_1058]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1536,plain,
% 1.24/0.99      ( v2_struct_0(sK1)
% 1.24/0.99      | ~ l1_pre_topc(sK1)
% 1.24/0.99      | v2_pre_topc(sK0(sK1,sK2))
% 1.24/0.99      | ~ v2_pre_topc(sK1)
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.24/0.99      inference(instantiation,[status(thm)],[c_1475]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_2,plain,
% 1.24/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.24/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1039,plain,
% 1.24/0.99      ( v2_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X1)
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | l1_pre_topc(X2)
% 1.24/0.99      | X0 != X1
% 1.24/0.99      | sK0(X0,sK2) != X2
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | sK2 != sK2 ),
% 1.24/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_739]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1040,plain,
% 1.24/0.99      ( v2_struct_0(X0)
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | l1_pre_topc(sK0(X0,sK2))
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.24/0.99      inference(unflattening,[status(thm)],[c_1039]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1476,plain,
% 1.24/0.99      ( v2_struct_0(X0_45)
% 1.24/0.99      | ~ l1_pre_topc(X0_45)
% 1.24/0.99      | l1_pre_topc(sK0(X0_45,sK2))
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.24/0.99      inference(subtyping,[status(esa)],[c_1040]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1533,plain,
% 1.24/0.99      ( v2_struct_0(sK1)
% 1.24/0.99      | l1_pre_topc(sK0(sK1,sK2))
% 1.24/0.99      | ~ l1_pre_topc(sK1)
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.24/0.99      inference(instantiation,[status(thm)],[c_1476]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_12,plain,
% 1.24/0.99      ( ~ m1_pre_topc(X0,X1)
% 1.24/0.99      | v2_struct_0(X1)
% 1.24/0.99      | ~ v2_tdlat_3(X1)
% 1.24/0.99      | v2_tdlat_3(X0)
% 1.24/0.99      | ~ l1_pre_topc(X1)
% 1.24/0.99      | ~ v2_pre_topc(X1) ),
% 1.24/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_958,plain,
% 1.24/0.99      ( v2_struct_0(X0)
% 1.24/0.99      | v2_struct_0(X1)
% 1.24/0.99      | ~ v2_tdlat_3(X0)
% 1.24/0.99      | v2_tdlat_3(X2)
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | ~ l1_pre_topc(X1)
% 1.24/0.99      | ~ v2_pre_topc(X0)
% 1.24/0.99      | X1 != X0
% 1.24/0.99      | sK0(X1,sK2) != X2
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.24/0.99      | sK2 != sK2 ),
% 1.24/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_739]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_959,plain,
% 1.24/0.99      ( v2_struct_0(X0)
% 1.24/0.99      | ~ v2_tdlat_3(X0)
% 1.24/0.99      | v2_tdlat_3(sK0(X0,sK2))
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | ~ v2_pre_topc(X0)
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.24/0.99      inference(unflattening,[status(thm)],[c_958]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_963,plain,
% 1.24/0.99      ( ~ l1_pre_topc(X0)
% 1.24/0.99      | v2_tdlat_3(sK0(X0,sK2))
% 1.24/0.99      | ~ v2_tdlat_3(X0)
% 1.24/0.99      | v2_struct_0(X0)
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.24/0.99      inference(global_propositional_subsumption,
% 1.24/0.99                [status(thm)],
% 1.24/0.99                [c_959,c_8]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_964,plain,
% 1.24/0.99      ( v2_struct_0(X0)
% 1.24/0.99      | ~ v2_tdlat_3(X0)
% 1.24/0.99      | v2_tdlat_3(sK0(X0,sK2))
% 1.24/0.99      | ~ l1_pre_topc(X0)
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.24/0.99      inference(renaming,[status(thm)],[c_963]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1477,plain,
% 1.24/0.99      ( v2_struct_0(X0_45)
% 1.24/0.99      | ~ v2_tdlat_3(X0_45)
% 1.24/0.99      | v2_tdlat_3(sK0(X0_45,sK2))
% 1.24/0.99      | ~ l1_pre_topc(X0_45)
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.24/0.99      inference(subtyping,[status(esa)],[c_964]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1530,plain,
% 1.24/0.99      ( v2_struct_0(sK1)
% 1.24/0.99      | v2_tdlat_3(sK0(sK1,sK2))
% 1.24/0.99      | ~ v2_tdlat_3(sK1)
% 1.24/0.99      | ~ l1_pre_topc(sK1)
% 1.24/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.24/0.99      inference(instantiation,[status(thm)],[c_1477]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1489,plain,( X0_45 = X0_45 ),theory(equality) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1513,plain,
% 1.24/0.99      ( sK1 = sK1 ),
% 1.24/0.99      inference(instantiation,[status(thm)],[c_1489]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1496,plain,
% 1.24/0.99      ( u1_struct_0(X0_45) = u1_struct_0(X1_45) | X0_45 != X1_45 ),
% 1.24/0.99      theory(equality) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_1505,plain,
% 1.24/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK1) | sK1 != sK1 ),
% 1.24/0.99      inference(instantiation,[status(thm)],[c_1496]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_23,negated_conjecture,
% 1.24/0.99      ( v2_tdlat_3(sK1) ),
% 1.24/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(c_24,negated_conjecture,
% 1.24/0.99      ( v2_pre_topc(sK1) ),
% 1.24/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.24/0.99  
% 1.24/0.99  cnf(contradiction,plain,
% 1.24/0.99      ( $false ),
% 1.24/0.99      inference(minisat,
% 1.24/0.99                [status(thm)],
% 1.24/0.99                [c_2159,c_2127,c_2099,c_2067,c_1551,c_1548,c_1536,c_1533,
% 1.24/0.99                 c_1530,c_1513,c_1505,c_391,c_20,c_22,c_23,c_24,c_25]) ).
% 1.24/0.99  
% 1.24/0.99  
% 1.24/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.24/0.99  
% 1.24/0.99  ------                               Statistics
% 1.24/0.99  
% 1.24/0.99  ------ General
% 1.24/0.99  
% 1.24/0.99  abstr_ref_over_cycles:                  0
% 1.24/0.99  abstr_ref_under_cycles:                 0
% 1.24/0.99  gc_basic_clause_elim:                   0
% 1.24/0.99  forced_gc_time:                         0
% 1.24/0.99  parsing_time:                           0.012
% 1.24/0.99  unif_index_cands_time:                  0.
% 1.24/0.99  unif_index_add_time:                    0.
% 1.24/0.99  orderings_time:                         0.
% 1.24/0.99  out_proof_time:                         0.012
% 1.24/0.99  total_time:                             0.12
% 1.24/0.99  num_of_symbols:                         50
% 1.24/0.99  num_of_terms:                           719
% 1.24/0.99  
% 1.24/0.99  ------ Preprocessing
% 1.24/0.99  
% 1.24/0.99  num_of_splits:                          2
% 1.24/0.99  num_of_split_atoms:                     2
% 1.24/0.99  num_of_reused_defs:                     0
% 1.24/0.99  num_eq_ax_congr_red:                    6
% 1.24/0.99  num_of_sem_filtered_clauses:            1
% 1.24/0.99  num_of_subtypes:                        3
% 1.24/0.99  monotx_restored_types:                  0
% 1.24/0.99  sat_num_of_epr_types:                   0
% 1.24/0.99  sat_num_of_non_cyclic_types:            0
% 1.24/0.99  sat_guarded_non_collapsed_types:        0
% 1.24/0.99  num_pure_diseq_elim:                    0
% 1.24/0.99  simp_replaced_by:                       0
% 1.24/0.99  res_preprocessed:                       104
% 1.24/0.99  prep_upred:                             0
% 1.24/0.99  prep_unflattend:                        23
% 1.24/0.99  smt_new_axioms:                         0
% 1.24/0.99  pred_elim_cands:                        6
% 1.24/0.99  pred_elim:                              6
% 1.24/0.99  pred_elim_cl:                           7
% 1.24/0.99  pred_elim_cycles:                       10
% 1.24/0.99  merged_defs:                            2
% 1.24/0.99  merged_defs_ncl:                        0
% 1.24/0.99  bin_hyper_res:                          2
% 1.24/0.99  prep_cycles:                            4
% 1.24/0.99  pred_elim_time:                         0.035
% 1.24/0.99  splitting_time:                         0.
% 1.24/0.99  sem_filter_time:                        0.
% 1.24/0.99  monotx_time:                            0.
% 1.24/0.99  subtype_inf_time:                       0.
% 1.24/0.99  
% 1.24/0.99  ------ Problem properties
% 1.24/0.99  
% 1.24/0.99  clauses:                                18
% 1.24/0.99  conjectures:                            4
% 1.24/0.99  epr:                                    7
% 1.24/0.99  horn:                                   9
% 1.24/0.99  ground:                                 5
% 1.24/0.99  unary:                                  4
% 1.24/0.99  binary:                                 1
% 1.24/0.99  lits:                                   64
% 1.24/0.99  lits_eq:                                12
% 1.24/0.99  fd_pure:                                0
% 1.24/0.99  fd_pseudo:                              0
% 1.24/0.99  fd_cond:                                0
% 1.24/0.99  fd_pseudo_cond:                         0
% 1.24/0.99  ac_symbols:                             0
% 1.24/0.99  
% 1.24/0.99  ------ Propositional Solver
% 1.24/0.99  
% 1.24/0.99  prop_solver_calls:                      25
% 1.24/0.99  prop_fast_solver_calls:                 1033
% 1.24/0.99  smt_solver_calls:                       0
% 1.24/0.99  smt_fast_solver_calls:                  0
% 1.24/0.99  prop_num_of_clauses:                    352
% 1.24/0.99  prop_preprocess_simplified:             2854
% 1.24/0.99  prop_fo_subsumed:                       20
% 1.24/0.99  prop_solver_time:                       0.
% 1.24/0.99  smt_solver_time:                        0.
% 1.24/0.99  smt_fast_solver_time:                   0.
% 1.24/0.99  prop_fast_solver_time:                  0.
% 1.24/0.99  prop_unsat_core_time:                   0.
% 1.24/0.99  
% 1.24/0.99  ------ QBF
% 1.24/0.99  
% 1.24/0.99  qbf_q_res:                              0
% 1.24/0.99  qbf_num_tautologies:                    0
% 1.24/0.99  qbf_prep_cycles:                        0
% 1.24/0.99  
% 1.24/0.99  ------ BMC1
% 1.24/0.99  
% 1.24/0.99  bmc1_current_bound:                     -1
% 1.24/0.99  bmc1_last_solved_bound:                 -1
% 1.24/0.99  bmc1_unsat_core_size:                   -1
% 1.24/0.99  bmc1_unsat_core_parents_size:           -1
% 1.24/0.99  bmc1_merge_next_fun:                    0
% 1.24/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.24/0.99  
% 1.24/0.99  ------ Instantiation
% 1.24/0.99  
% 1.24/0.99  inst_num_of_clauses:                    54
% 1.24/0.99  inst_num_in_passive:                    5
% 1.24/0.99  inst_num_in_active:                     44
% 1.24/0.99  inst_num_in_unprocessed:                4
% 1.24/0.99  inst_num_of_loops:                      55
% 1.24/0.99  inst_num_of_learning_restarts:          0
% 1.24/0.99  inst_num_moves_active_passive:          7
% 1.24/0.99  inst_lit_activity:                      0
% 1.24/0.99  inst_lit_activity_moves:                0
% 1.24/0.99  inst_num_tautologies:                   0
% 1.24/0.99  inst_num_prop_implied:                  0
% 1.24/0.99  inst_num_existing_simplified:           0
% 1.24/0.99  inst_num_eq_res_simplified:             0
% 1.24/0.99  inst_num_child_elim:                    0
% 1.24/0.99  inst_num_of_dismatching_blockings:      3
% 1.24/0.99  inst_num_of_non_proper_insts:           17
% 1.24/0.99  inst_num_of_duplicates:                 0
% 1.24/0.99  inst_inst_num_from_inst_to_res:         0
% 1.24/0.99  inst_dismatching_checking_time:         0.
% 1.24/0.99  
% 1.24/0.99  ------ Resolution
% 1.24/0.99  
% 1.24/0.99  res_num_of_clauses:                     0
% 1.24/0.99  res_num_in_passive:                     0
% 1.24/0.99  res_num_in_active:                      0
% 1.24/0.99  res_num_of_loops:                       108
% 1.24/0.99  res_forward_subset_subsumed:            1
% 1.24/0.99  res_backward_subset_subsumed:           0
% 1.24/0.99  res_forward_subsumed:                   2
% 1.24/0.99  res_backward_subsumed:                  0
% 1.24/0.99  res_forward_subsumption_resolution:     0
% 1.24/0.99  res_backward_subsumption_resolution:    0
% 1.24/0.99  res_clause_to_clause_subsumption:       39
% 1.24/0.99  res_orphan_elimination:                 0
% 1.24/0.99  res_tautology_del:                      16
% 1.24/0.99  res_num_eq_res_simplified:              4
% 1.24/0.99  res_num_sel_changes:                    0
% 1.24/0.99  res_moves_from_active_to_pass:          0
% 1.24/0.99  
% 1.24/0.99  ------ Superposition
% 1.24/0.99  
% 1.24/0.99  sup_time_total:                         0.
% 1.24/0.99  sup_time_generating:                    0.
% 1.24/0.99  sup_time_sim_full:                      0.
% 1.24/0.99  sup_time_sim_immed:                     0.
% 1.24/0.99  
% 1.24/0.99  sup_num_of_clauses:                     22
% 1.24/0.99  sup_num_in_active:                      10
% 1.24/0.99  sup_num_in_passive:                     12
% 1.24/0.99  sup_num_of_loops:                       10
% 1.24/0.99  sup_fw_superposition:                   1
% 1.24/0.99  sup_bw_superposition:                   0
% 1.24/0.99  sup_immediate_simplified:               1
% 1.24/0.99  sup_given_eliminated:                   0
% 1.24/0.99  comparisons_done:                       0
% 1.24/0.99  comparisons_avoided:                    0
% 1.24/0.99  
% 1.24/0.99  ------ Simplifications
% 1.24/0.99  
% 1.24/0.99  
% 1.24/0.99  sim_fw_subset_subsumed:                 1
% 1.24/0.99  sim_bw_subset_subsumed:                 0
% 1.24/0.99  sim_fw_subsumed:                        0
% 1.24/0.99  sim_bw_subsumed:                        0
% 1.24/0.99  sim_fw_subsumption_res:                 0
% 1.24/0.99  sim_bw_subsumption_res:                 0
% 1.24/0.99  sim_tautology_del:                      0
% 1.24/0.99  sim_eq_tautology_del:                   0
% 1.24/0.99  sim_eq_res_simp:                        0
% 1.24/0.99  sim_fw_demodulated:                     0
% 1.24/0.99  sim_bw_demodulated:                     0
% 1.24/0.99  sim_light_normalised:                   0
% 1.24/0.99  sim_joinable_taut:                      0
% 1.24/0.99  sim_joinable_simp:                      0
% 1.24/0.99  sim_ac_normalised:                      0
% 1.24/0.99  sim_smt_subsumption:                    0
% 1.24/0.99  
%------------------------------------------------------------------------------
