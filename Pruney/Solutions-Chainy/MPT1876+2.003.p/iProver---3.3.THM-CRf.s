%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:47 EST 2020

% Result     : Theorem 1.19s
% Output     : CNFRefutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  192 (1249 expanded)
%              Number of clauses        :  121 ( 306 expanded)
%              Number of leaves         :   19 ( 279 expanded)
%              Depth                    :   28
%              Number of atoms          :  972 (9273 expanded)
%              Number of equality atoms :  204 ( 447 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   20 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f43,f45,f44])).

fof(f72,plain,
    ( v1_zfmisc_1(sK2)
    | v2_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f51,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,
    ( ~ v1_zfmisc_1(sK2)
    | ~ v2_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
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

fof(f15,plain,(
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
    inference(pure_predicate_removal,[],[f11])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK0(X0,X1)) = X1
        & m1_pre_topc(sK0(X0,X1),X0)
        & ~ v2_struct_0(sK0(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK0(X0,X1)) = X1
            & m1_pre_topc(sK0(X0,X1),X0)
            & ~ v2_struct_0(sK0(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f39])).

fof(f63,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v2_tdlat_3(X1)
              & ~ v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( ~ v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_tdlat_3(X1)
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_tdlat_3(X1)
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | ~ v2_tdlat_3(X1)
      | v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f66,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f55,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f59,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3,plain,
    ( v7_struct_0(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_327,plain,
    ( v7_struct_0(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_3])).

cnf(c_20,negated_conjecture,
    ( v2_tex_2(sK2,sK1)
    | v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_184,plain,
    ( v1_zfmisc_1(sK2)
    | v2_tex_2(sK2,sK1) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_185,plain,
    ( v2_tex_2(sK2,sK1)
    | v1_zfmisc_1(sK2) ),
    inference(renaming,[status(thm)],[c_184])).

cnf(c_368,plain,
    ( v2_tex_2(sK2,sK1)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_327,c_185])).

cnf(c_4,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_313,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_4])).

cnf(c_19,negated_conjecture,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_182,plain,
    ( ~ v1_zfmisc_1(sK2)
    | ~ v2_tex_2(sK2,sK1) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_183,plain,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ v1_zfmisc_1(sK2) ),
    inference(renaming,[status(thm)],[c_182])).

cnf(c_351,plain,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_313,c_183])).

cnf(c_614,plain,
    ( ~ v7_struct_0(X0)
    | v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X1) != sK2 ),
    inference(resolution,[status(thm)],[c_368,c_351])).

cnf(c_1667,plain,
    ( ~ v7_struct_0(X0_45)
    | v7_struct_0(X1_45)
    | ~ l1_pre_topc(X1_45)
    | ~ l1_pre_topc(X0_45)
    | u1_struct_0(X1_45) != sK2
    | u1_struct_0(X0_45) != sK2 ),
    inference(subtyping,[status(esa)],[c_614])).

cnf(c_1675,plain,
    ( ~ v7_struct_0(X0_45)
    | ~ l1_pre_topc(X0_45)
    | u1_struct_0(X0_45) != sK2
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1667])).

cnf(c_2320,plain,
    ( ~ v7_struct_0(sK0(X0_45,sK2))
    | ~ l1_pre_topc(sK0(X0_45,sK2))
    | ~ sP1_iProver_split
    | u1_struct_0(sK0(X0_45,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1675])).

cnf(c_2321,plain,
    ( u1_struct_0(sK0(X0_45,sK2)) != sK2
    | v7_struct_0(sK0(X0_45,sK2)) != iProver_top
    | l1_pre_topc(sK0(X0_45,sK2)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2320])).

cnf(c_2323,plain,
    ( u1_struct_0(sK0(sK1,sK2)) != sK2
    | v7_struct_0(sK0(sK1,sK2)) != iProver_top
    | l1_pre_topc(sK0(sK1,sK2)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_2321])).

cnf(c_1674,plain,
    ( v7_struct_0(X0_45)
    | ~ l1_pre_topc(X0_45)
    | u1_struct_0(X0_45) != sK2
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1667])).

cnf(c_2274,plain,
    ( v7_struct_0(sK0(X0_45,sK2))
    | ~ l1_pre_topc(sK0(X0_45,sK2))
    | ~ sP0_iProver_split
    | u1_struct_0(sK0(X0_45,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_1674])).

cnf(c_2275,plain,
    ( u1_struct_0(sK0(X0_45,sK2)) != sK2
    | v7_struct_0(sK0(X0_45,sK2)) = iProver_top
    | l1_pre_topc(sK0(X0_45,sK2)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2274])).

cnf(c_2277,plain,
    ( u1_struct_0(sK0(sK1,sK2)) != sK2
    | v7_struct_0(sK0(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK0(sK1,sK2)) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_2275])).

cnf(c_1695,plain,
    ( k1_zfmisc_1(X0_46) = k1_zfmisc_1(X1_46)
    | X0_46 != X1_46 ),
    theory(equality)).

cnf(c_2248,plain,
    ( k1_zfmisc_1(u1_struct_0(X0_45)) = k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0_45) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1695])).

cnf(c_2249,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2248])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK0(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK0(X1,X0)) = X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_432,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(sK0(X0,sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_728,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK0(X0,sK2)) = sK2
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_432])).

cnf(c_1349,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK0(X0,sK2)) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_728])).

cnf(c_1659,plain,
    ( v2_struct_0(X0_45)
    | ~ l1_pre_topc(X0_45)
    | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK0(X0_45,sK2)) = sK2 ),
    inference(subtyping,[status(esa)],[c_1349])).

cnf(c_1738,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK0(sK1,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_1659])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_5,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_967,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | X2 != X1
    | X2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_5])).

cnf(c_968,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_967])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(sK0(X1,X0),X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_413,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(sK0(X1,X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_414,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_pre_topc(sK0(X0,sK2),X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_746,plain,
    ( m1_pre_topc(sK0(X0,sK2),X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_414])).

cnf(c_18,plain,
    ( ~ v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_669,plain,
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
    inference(resolution_lifted,[status(thm)],[c_18,c_368])).

cnf(c_670,plain,
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
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_674,plain,
    ( ~ l1_pre_topc(X1)
    | v7_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(X0,sK1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X1) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_670,c_26,c_23])).

cnf(c_675,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(X0,sK1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X1) != sK2 ),
    inference(renaming,[status(thm)],[c_674])).

cnf(c_782,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X1) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_675])).

cnf(c_1142,plain,
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
    inference(resolution_lifted,[status(thm)],[c_746,c_782])).

cnf(c_1143,plain,
    ( v1_tdlat_3(sK0(sK1,sK2))
    | v2_struct_0(sK0(sK1,sK2))
    | v2_struct_0(sK1)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0) != sK2
    | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_1142])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK0(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK0(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_396,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK0(X0,sK2))
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_398,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_struct_0(sK0(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_396])).

cnf(c_434,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK0(sK1,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_1145,plain,
    ( u1_struct_0(X0) != sK2
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | v1_tdlat_3(sK0(sK1,sK2))
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1143,c_26,c_23,c_21,c_398,c_434])).

cnf(c_1146,plain,
    ( v1_tdlat_3(sK0(sK1,sK2))
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0) != sK2 ),
    inference(renaming,[status(thm)],[c_1145])).

cnf(c_1335,plain,
    ( v1_tdlat_3(sK0(sK1,sK2))
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_1146])).

cnf(c_1477,plain,
    ( v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | v7_struct_0(X1)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | sK0(sK1,sK2) != X0
    | u1_struct_0(X1) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_968,c_1335])).

cnf(c_1478,plain,
    ( v2_struct_0(sK0(sK1,sK2))
    | ~ v2_tdlat_3(sK0(sK1,sK2))
    | v7_struct_0(X0)
    | v7_struct_0(sK0(sK1,sK2))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK0(sK1,sK2))
    | u1_struct_0(X0) != sK2 ),
    inference(unflattening,[status(thm)],[c_1477])).

cnf(c_1244,plain,
    ( v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | v7_struct_0(X1)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | sK0(sK1,sK2) != X0
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X1) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_968,c_1146])).

cnf(c_1245,plain,
    ( v2_struct_0(sK0(sK1,sK2))
    | ~ v2_tdlat_3(sK0(sK1,sK2))
    | v7_struct_0(X0)
    | v7_struct_0(sK0(sK1,sK2))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK0(sK1,sK2))
    | u1_struct_0(X0) != sK2 ),
    inference(unflattening,[status(thm)],[c_1244])).

cnf(c_1480,plain,
    ( ~ v2_tdlat_3(sK0(sK1,sK2))
    | v7_struct_0(X0)
    | v7_struct_0(sK0(sK1,sK2))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK0(sK1,sK2))
    | u1_struct_0(X0) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1478,c_26,c_23,c_21,c_398,c_1245])).

cnf(c_1661,plain,
    ( ~ v2_tdlat_3(sK0(sK1,sK2))
    | v7_struct_0(X0_45)
    | v7_struct_0(sK0(sK1,sK2))
    | ~ l1_pre_topc(X0_45)
    | ~ l1_pre_topc(sK0(sK1,sK2))
    | u1_struct_0(X0_45) != sK2 ),
    inference(subtyping,[status(esa)],[c_1480])).

cnf(c_1678,plain,
    ( ~ v2_tdlat_3(sK0(sK1,sK2))
    | v7_struct_0(sK0(sK1,sK2))
    | ~ l1_pre_topc(sK0(sK1,sK2))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1661])).

cnf(c_1732,plain,
    ( v2_tdlat_3(sK0(sK1,sK2)) != iProver_top
    | v7_struct_0(sK0(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK0(sK1,sK2)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1678])).

cnf(c_7,plain,
    ( v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_17,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_635,plain,
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
    inference(resolution_lifted,[status(thm)],[c_17,c_351])).

cnf(c_636,plain,
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
    inference(unflattening,[status(thm)],[c_635])).

cnf(c_640,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v7_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(X0,sK1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X1) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_636,c_26,c_23])).

cnf(c_641,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(X0,sK1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X1) != sK2 ),
    inference(renaming,[status(thm)],[c_640])).

cnf(c_811,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X1) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_641])).

cnf(c_1119,plain,
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
    inference(resolution_lifted,[status(thm)],[c_746,c_811])).

cnf(c_1120,plain,
    ( ~ v1_tdlat_3(sK0(sK1,sK2))
    | v2_struct_0(sK0(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0) != sK2
    | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_1119])).

cnf(c_1122,plain,
    ( u1_struct_0(X0) != sK2
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | ~ v1_tdlat_3(sK0(sK1,sK2))
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1120,c_26,c_23,c_21,c_398,c_434])).

cnf(c_1123,plain,
    ( ~ v1_tdlat_3(sK0(sK1,sK2))
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0) != sK2 ),
    inference(renaming,[status(thm)],[c_1122])).

cnf(c_1337,plain,
    ( ~ v1_tdlat_3(sK0(sK1,sK2))
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_1123])).

cnf(c_1451,plain,
    ( v2_struct_0(X0)
    | ~ v7_struct_0(X1)
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | sK0(sK1,sK2) != X0
    | u1_struct_0(X1) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_1337])).

cnf(c_1452,plain,
    ( v2_struct_0(sK0(sK1,sK2))
    | ~ v7_struct_0(X0)
    | ~ v7_struct_0(sK0(sK1,sK2))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK0(sK1,sK2))
    | ~ v2_pre_topc(sK0(sK1,sK2))
    | u1_struct_0(X0) != sK2 ),
    inference(unflattening,[status(thm)],[c_1451])).

cnf(c_1218,plain,
    ( v2_struct_0(X0)
    | ~ v7_struct_0(X1)
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | sK0(sK1,sK2) != X0
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X1) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_1123])).

cnf(c_1219,plain,
    ( v2_struct_0(sK0(sK1,sK2))
    | ~ v7_struct_0(X0)
    | ~ v7_struct_0(sK0(sK1,sK2))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK0(sK1,sK2))
    | ~ v2_pre_topc(sK0(sK1,sK2))
    | u1_struct_0(X0) != sK2 ),
    inference(unflattening,[status(thm)],[c_1218])).

cnf(c_1454,plain,
    ( ~ v7_struct_0(X0)
    | ~ v7_struct_0(sK0(sK1,sK2))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK0(sK1,sK2))
    | ~ v2_pre_topc(sK0(sK1,sK2))
    | u1_struct_0(X0) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1452,c_26,c_23,c_21,c_398,c_1219])).

cnf(c_1662,plain,
    ( ~ v7_struct_0(X0_45)
    | ~ v7_struct_0(sK0(sK1,sK2))
    | ~ l1_pre_topc(X0_45)
    | ~ l1_pre_topc(sK0(sK1,sK2))
    | ~ v2_pre_topc(sK0(sK1,sK2))
    | u1_struct_0(X0_45) != sK2 ),
    inference(subtyping,[status(esa)],[c_1454])).

cnf(c_1677,plain,
    ( ~ v7_struct_0(sK0(sK1,sK2))
    | ~ l1_pre_topc(sK0(sK1,sK2))
    | ~ v2_pre_topc(sK0(sK1,sK2))
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1662])).

cnf(c_1730,plain,
    ( v7_struct_0(sK0(sK1,sK2)) != iProver_top
    | l1_pre_topc(sK0(sK1,sK2)) != iProver_top
    | v2_pre_topc(sK0(sK1,sK2)) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1677])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1064,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X2)
    | X0 != X1
    | sK0(X0,sK2) != X2
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_746])).

cnf(c_1065,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(sK0(X0,sK2))
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1064])).

cnf(c_1664,plain,
    ( v2_struct_0(X0_45)
    | ~ l1_pre_topc(X0_45)
    | ~ v2_pre_topc(X0_45)
    | v2_pre_topc(sK0(X0_45,sK2))
    | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_1065])).

cnf(c_1727,plain,
    ( k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1))
    | v2_struct_0(X0_45) = iProver_top
    | l1_pre_topc(X0_45) != iProver_top
    | v2_pre_topc(X0_45) != iProver_top
    | v2_pre_topc(sK0(X0_45,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1664])).

cnf(c_1729,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0(sK1,sK2)) = iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1727])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1046,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(X2)
    | X0 != X1
    | sK0(X0,sK2) != X2
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_746])).

cnf(c_1047,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK0(X0,sK2))
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1046])).

cnf(c_1665,plain,
    ( v2_struct_0(X0_45)
    | ~ l1_pre_topc(X0_45)
    | l1_pre_topc(sK0(X0_45,sK2))
    | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_1047])).

cnf(c_1724,plain,
    ( k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1))
    | v2_struct_0(X0_45) = iProver_top
    | l1_pre_topc(X0_45) != iProver_top
    | l1_pre_topc(sK0(X0_45,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1665])).

cnf(c_1726,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1724])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_992,plain,
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
    inference(resolution_lifted,[status(thm)],[c_13,c_746])).

cnf(c_993,plain,
    ( v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | v2_tdlat_3(sK0(X0,sK2))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_992])).

cnf(c_12,plain,
    ( ~ v2_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_997,plain,
    ( ~ l1_pre_topc(X0)
    | v2_tdlat_3(sK0(X0,sK2))
    | ~ v2_tdlat_3(X0)
    | v2_struct_0(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_993,c_12])).

cnf(c_998,plain,
    ( v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | v2_tdlat_3(sK0(X0,sK2))
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_997])).

cnf(c_1666,plain,
    ( v2_struct_0(X0_45)
    | ~ v2_tdlat_3(X0_45)
    | v2_tdlat_3(sK0(X0_45,sK2))
    | ~ l1_pre_topc(X0_45)
    | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_998])).

cnf(c_1721,plain,
    ( k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1))
    | v2_struct_0(X0_45) = iProver_top
    | v2_tdlat_3(X0_45) != iProver_top
    | v2_tdlat_3(sK0(X0_45,sK2)) = iProver_top
    | l1_pre_topc(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1666])).

cnf(c_1723,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | v2_struct_0(sK1) = iProver_top
    | v2_tdlat_3(sK0(sK1,sK2)) = iProver_top
    | v2_tdlat_3(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1721])).

cnf(c_1682,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_1705,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1682])).

cnf(c_1690,plain,
    ( u1_struct_0(X0_45) = u1_struct_0(X1_45)
    | X0_45 != X1_45 ),
    theory(equality)).

cnf(c_1698,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1690])).

cnf(c_30,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_29,plain,
    ( v2_tdlat_3(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_28,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_27,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2323,c_2277,c_2249,c_1738,c_1732,c_1730,c_1729,c_1726,c_1723,c_1705,c_1698,c_30,c_23,c_29,c_28,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:23:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.19/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.19/0.97  
% 1.19/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.19/0.97  
% 1.19/0.97  ------  iProver source info
% 1.19/0.97  
% 1.19/0.97  git: date: 2020-06-30 10:37:57 +0100
% 1.19/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.19/0.97  git: non_committed_changes: false
% 1.19/0.97  git: last_make_outside_of_git: false
% 1.19/0.97  
% 1.19/0.97  ------ 
% 1.19/0.97  
% 1.19/0.97  ------ Input Options
% 1.19/0.97  
% 1.19/0.97  --out_options                           all
% 1.19/0.97  --tptp_safe_out                         true
% 1.19/0.97  --problem_path                          ""
% 1.19/0.97  --include_path                          ""
% 1.19/0.97  --clausifier                            res/vclausify_rel
% 1.19/0.97  --clausifier_options                    --mode clausify
% 1.19/0.97  --stdin                                 false
% 1.19/0.97  --stats_out                             all
% 1.19/0.97  
% 1.19/0.97  ------ General Options
% 1.19/0.97  
% 1.19/0.97  --fof                                   false
% 1.19/0.97  --time_out_real                         305.
% 1.19/0.97  --time_out_virtual                      -1.
% 1.19/0.97  --symbol_type_check                     false
% 1.19/0.97  --clausify_out                          false
% 1.19/0.97  --sig_cnt_out                           false
% 1.19/0.97  --trig_cnt_out                          false
% 1.19/0.97  --trig_cnt_out_tolerance                1.
% 1.19/0.97  --trig_cnt_out_sk_spl                   false
% 1.19/0.97  --abstr_cl_out                          false
% 1.19/0.97  
% 1.19/0.97  ------ Global Options
% 1.19/0.97  
% 1.19/0.97  --schedule                              default
% 1.19/0.97  --add_important_lit                     false
% 1.19/0.97  --prop_solver_per_cl                    1000
% 1.19/0.97  --min_unsat_core                        false
% 1.19/0.97  --soft_assumptions                      false
% 1.19/0.97  --soft_lemma_size                       3
% 1.19/0.97  --prop_impl_unit_size                   0
% 1.19/0.97  --prop_impl_unit                        []
% 1.19/0.97  --share_sel_clauses                     true
% 1.19/0.97  --reset_solvers                         false
% 1.19/0.97  --bc_imp_inh                            [conj_cone]
% 1.19/0.97  --conj_cone_tolerance                   3.
% 1.19/0.97  --extra_neg_conj                        none
% 1.19/0.97  --large_theory_mode                     true
% 1.19/0.97  --prolific_symb_bound                   200
% 1.19/0.97  --lt_threshold                          2000
% 1.19/0.97  --clause_weak_htbl                      true
% 1.19/0.97  --gc_record_bc_elim                     false
% 1.19/0.97  
% 1.19/0.97  ------ Preprocessing Options
% 1.19/0.97  
% 1.19/0.97  --preprocessing_flag                    true
% 1.19/0.97  --time_out_prep_mult                    0.1
% 1.19/0.97  --splitting_mode                        input
% 1.19/0.97  --splitting_grd                         true
% 1.19/0.97  --splitting_cvd                         false
% 1.19/0.97  --splitting_cvd_svl                     false
% 1.19/0.97  --splitting_nvd                         32
% 1.19/0.97  --sub_typing                            true
% 1.19/0.97  --prep_gs_sim                           true
% 1.19/0.97  --prep_unflatten                        true
% 1.19/0.97  --prep_res_sim                          true
% 1.19/0.97  --prep_upred                            true
% 1.19/0.97  --prep_sem_filter                       exhaustive
% 1.19/0.97  --prep_sem_filter_out                   false
% 1.19/0.97  --pred_elim                             true
% 1.19/0.97  --res_sim_input                         true
% 1.19/0.97  --eq_ax_congr_red                       true
% 1.19/0.97  --pure_diseq_elim                       true
% 1.19/0.97  --brand_transform                       false
% 1.19/0.97  --non_eq_to_eq                          false
% 1.19/0.97  --prep_def_merge                        true
% 1.19/0.97  --prep_def_merge_prop_impl              false
% 1.19/0.97  --prep_def_merge_mbd                    true
% 1.19/0.97  --prep_def_merge_tr_red                 false
% 1.19/0.97  --prep_def_merge_tr_cl                  false
% 1.19/0.97  --smt_preprocessing                     true
% 1.19/0.97  --smt_ac_axioms                         fast
% 1.19/0.97  --preprocessed_out                      false
% 1.19/0.97  --preprocessed_stats                    false
% 1.19/0.97  
% 1.19/0.97  ------ Abstraction refinement Options
% 1.19/0.97  
% 1.19/0.97  --abstr_ref                             []
% 1.19/0.97  --abstr_ref_prep                        false
% 1.19/0.97  --abstr_ref_until_sat                   false
% 1.19/0.97  --abstr_ref_sig_restrict                funpre
% 1.19/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.19/0.97  --abstr_ref_under                       []
% 1.19/0.97  
% 1.19/0.97  ------ SAT Options
% 1.19/0.97  
% 1.19/0.97  --sat_mode                              false
% 1.19/0.97  --sat_fm_restart_options                ""
% 1.19/0.97  --sat_gr_def                            false
% 1.19/0.97  --sat_epr_types                         true
% 1.19/0.97  --sat_non_cyclic_types                  false
% 1.19/0.97  --sat_finite_models                     false
% 1.19/0.97  --sat_fm_lemmas                         false
% 1.19/0.97  --sat_fm_prep                           false
% 1.19/0.97  --sat_fm_uc_incr                        true
% 1.19/0.97  --sat_out_model                         small
% 1.19/0.97  --sat_out_clauses                       false
% 1.19/0.97  
% 1.19/0.97  ------ QBF Options
% 1.19/0.97  
% 1.19/0.97  --qbf_mode                              false
% 1.19/0.97  --qbf_elim_univ                         false
% 1.19/0.97  --qbf_dom_inst                          none
% 1.19/0.97  --qbf_dom_pre_inst                      false
% 1.19/0.97  --qbf_sk_in                             false
% 1.19/0.97  --qbf_pred_elim                         true
% 1.19/0.97  --qbf_split                             512
% 1.19/0.97  
% 1.19/0.97  ------ BMC1 Options
% 1.19/0.97  
% 1.19/0.97  --bmc1_incremental                      false
% 1.19/0.97  --bmc1_axioms                           reachable_all
% 1.19/0.97  --bmc1_min_bound                        0
% 1.19/0.97  --bmc1_max_bound                        -1
% 1.19/0.97  --bmc1_max_bound_default                -1
% 1.19/0.97  --bmc1_symbol_reachability              true
% 1.19/0.97  --bmc1_property_lemmas                  false
% 1.19/0.97  --bmc1_k_induction                      false
% 1.19/0.97  --bmc1_non_equiv_states                 false
% 1.19/0.97  --bmc1_deadlock                         false
% 1.19/0.97  --bmc1_ucm                              false
% 1.19/0.97  --bmc1_add_unsat_core                   none
% 1.19/0.97  --bmc1_unsat_core_children              false
% 1.19/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.19/0.97  --bmc1_out_stat                         full
% 1.19/0.97  --bmc1_ground_init                      false
% 1.19/0.97  --bmc1_pre_inst_next_state              false
% 1.19/0.97  --bmc1_pre_inst_state                   false
% 1.19/0.97  --bmc1_pre_inst_reach_state             false
% 1.19/0.97  --bmc1_out_unsat_core                   false
% 1.19/0.97  --bmc1_aig_witness_out                  false
% 1.19/0.97  --bmc1_verbose                          false
% 1.19/0.97  --bmc1_dump_clauses_tptp                false
% 1.19/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.19/0.97  --bmc1_dump_file                        -
% 1.19/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.19/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.19/0.97  --bmc1_ucm_extend_mode                  1
% 1.19/0.97  --bmc1_ucm_init_mode                    2
% 1.19/0.97  --bmc1_ucm_cone_mode                    none
% 1.19/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.19/0.97  --bmc1_ucm_relax_model                  4
% 1.19/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.19/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.19/0.97  --bmc1_ucm_layered_model                none
% 1.19/0.97  --bmc1_ucm_max_lemma_size               10
% 1.19/0.97  
% 1.19/0.97  ------ AIG Options
% 1.19/0.97  
% 1.19/0.97  --aig_mode                              false
% 1.19/0.97  
% 1.19/0.97  ------ Instantiation Options
% 1.19/0.97  
% 1.19/0.97  --instantiation_flag                    true
% 1.19/0.97  --inst_sos_flag                         false
% 1.19/0.97  --inst_sos_phase                        true
% 1.19/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.19/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.19/0.97  --inst_lit_sel_side                     num_symb
% 1.19/0.97  --inst_solver_per_active                1400
% 1.19/0.97  --inst_solver_calls_frac                1.
% 1.19/0.97  --inst_passive_queue_type               priority_queues
% 1.19/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.19/0.97  --inst_passive_queues_freq              [25;2]
% 1.19/0.97  --inst_dismatching                      true
% 1.19/0.97  --inst_eager_unprocessed_to_passive     true
% 1.19/0.97  --inst_prop_sim_given                   true
% 1.19/0.97  --inst_prop_sim_new                     false
% 1.19/0.97  --inst_subs_new                         false
% 1.19/0.97  --inst_eq_res_simp                      false
% 1.19/0.97  --inst_subs_given                       false
% 1.19/0.97  --inst_orphan_elimination               true
% 1.19/0.97  --inst_learning_loop_flag               true
% 1.19/0.97  --inst_learning_start                   3000
% 1.19/0.97  --inst_learning_factor                  2
% 1.19/0.97  --inst_start_prop_sim_after_learn       3
% 1.19/0.97  --inst_sel_renew                        solver
% 1.19/0.97  --inst_lit_activity_flag                true
% 1.19/0.97  --inst_restr_to_given                   false
% 1.19/0.97  --inst_activity_threshold               500
% 1.19/0.97  --inst_out_proof                        true
% 1.19/0.97  
% 1.19/0.97  ------ Resolution Options
% 1.19/0.97  
% 1.19/0.97  --resolution_flag                       true
% 1.19/0.97  --res_lit_sel                           adaptive
% 1.19/0.97  --res_lit_sel_side                      none
% 1.19/0.97  --res_ordering                          kbo
% 1.19/0.97  --res_to_prop_solver                    active
% 1.19/0.97  --res_prop_simpl_new                    false
% 1.19/0.97  --res_prop_simpl_given                  true
% 1.19/0.97  --res_passive_queue_type                priority_queues
% 1.19/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.19/0.97  --res_passive_queues_freq               [15;5]
% 1.19/0.97  --res_forward_subs                      full
% 1.19/0.97  --res_backward_subs                     full
% 1.19/0.97  --res_forward_subs_resolution           true
% 1.19/0.97  --res_backward_subs_resolution          true
% 1.19/0.97  --res_orphan_elimination                true
% 1.19/0.97  --res_time_limit                        2.
% 1.19/0.97  --res_out_proof                         true
% 1.19/0.97  
% 1.19/0.97  ------ Superposition Options
% 1.19/0.97  
% 1.19/0.97  --superposition_flag                    true
% 1.19/0.97  --sup_passive_queue_type                priority_queues
% 1.19/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.19/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.19/0.97  --demod_completeness_check              fast
% 1.19/0.97  --demod_use_ground                      true
% 1.19/0.97  --sup_to_prop_solver                    passive
% 1.19/0.97  --sup_prop_simpl_new                    true
% 1.19/0.97  --sup_prop_simpl_given                  true
% 1.19/0.97  --sup_fun_splitting                     false
% 1.19/0.97  --sup_smt_interval                      50000
% 1.19/0.97  
% 1.19/0.97  ------ Superposition Simplification Setup
% 1.19/0.97  
% 1.19/0.97  --sup_indices_passive                   []
% 1.19/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.19/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.19/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.19/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.19/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.19/0.97  --sup_full_bw                           [BwDemod]
% 1.19/0.97  --sup_immed_triv                        [TrivRules]
% 1.19/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.19/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.19/0.97  --sup_immed_bw_main                     []
% 1.19/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.19/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.19/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.19/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.19/0.97  
% 1.19/0.97  ------ Combination Options
% 1.19/0.97  
% 1.19/0.97  --comb_res_mult                         3
% 1.19/0.97  --comb_sup_mult                         2
% 1.19/0.97  --comb_inst_mult                        10
% 1.19/0.97  
% 1.19/0.97  ------ Debug Options
% 1.19/0.97  
% 1.19/0.97  --dbg_backtrace                         false
% 1.19/0.97  --dbg_dump_prop_clauses                 false
% 1.19/0.97  --dbg_dump_prop_clauses_file            -
% 1.19/0.97  --dbg_out_stat                          false
% 1.19/0.97  ------ Parsing...
% 1.19/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.19/0.97  
% 1.19/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.19/0.97  
% 1.19/0.97  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.19/0.97  
% 1.19/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.19/0.97  ------ Proving...
% 1.19/0.97  ------ Problem Properties 
% 1.19/0.97  
% 1.19/0.97  
% 1.19/0.97  clauses                                 22
% 1.19/0.97  conjectures                             4
% 1.19/0.97  EPR                                     8
% 1.19/0.97  Horn                                    13
% 1.19/0.97  unary                                   5
% 1.19/0.97  binary                                  2
% 1.19/0.97  lits                                    74
% 1.19/0.97  lits eq                                 14
% 1.19/0.97  fd_pure                                 0
% 1.19/0.97  fd_pseudo                               0
% 1.19/0.97  fd_cond                                 0
% 1.19/0.97  fd_pseudo_cond                          0
% 1.19/0.97  AC symbols                              0
% 1.19/0.97  
% 1.19/0.97  ------ Schedule dynamic 5 is on 
% 1.19/0.97  
% 1.19/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.19/0.97  
% 1.19/0.97  
% 1.19/0.97  ------ 
% 1.19/0.97  Current options:
% 1.19/0.97  ------ 
% 1.19/0.97  
% 1.19/0.97  ------ Input Options
% 1.19/0.97  
% 1.19/0.97  --out_options                           all
% 1.19/0.97  --tptp_safe_out                         true
% 1.19/0.97  --problem_path                          ""
% 1.19/0.97  --include_path                          ""
% 1.19/0.97  --clausifier                            res/vclausify_rel
% 1.19/0.97  --clausifier_options                    --mode clausify
% 1.19/0.97  --stdin                                 false
% 1.19/0.97  --stats_out                             all
% 1.19/0.97  
% 1.19/0.97  ------ General Options
% 1.19/0.97  
% 1.19/0.97  --fof                                   false
% 1.19/0.97  --time_out_real                         305.
% 1.19/0.97  --time_out_virtual                      -1.
% 1.19/0.97  --symbol_type_check                     false
% 1.19/0.97  --clausify_out                          false
% 1.19/0.97  --sig_cnt_out                           false
% 1.19/0.97  --trig_cnt_out                          false
% 1.19/0.97  --trig_cnt_out_tolerance                1.
% 1.19/0.97  --trig_cnt_out_sk_spl                   false
% 1.19/0.97  --abstr_cl_out                          false
% 1.19/0.97  
% 1.19/0.97  ------ Global Options
% 1.19/0.97  
% 1.19/0.97  --schedule                              default
% 1.19/0.97  --add_important_lit                     false
% 1.19/0.97  --prop_solver_per_cl                    1000
% 1.19/0.97  --min_unsat_core                        false
% 1.19/0.97  --soft_assumptions                      false
% 1.19/0.97  --soft_lemma_size                       3
% 1.19/0.97  --prop_impl_unit_size                   0
% 1.19/0.97  --prop_impl_unit                        []
% 1.19/0.97  --share_sel_clauses                     true
% 1.19/0.97  --reset_solvers                         false
% 1.19/0.97  --bc_imp_inh                            [conj_cone]
% 1.19/0.97  --conj_cone_tolerance                   3.
% 1.19/0.97  --extra_neg_conj                        none
% 1.19/0.97  --large_theory_mode                     true
% 1.19/0.97  --prolific_symb_bound                   200
% 1.19/0.97  --lt_threshold                          2000
% 1.19/0.97  --clause_weak_htbl                      true
% 1.19/0.97  --gc_record_bc_elim                     false
% 1.19/0.97  
% 1.19/0.97  ------ Preprocessing Options
% 1.19/0.97  
% 1.19/0.97  --preprocessing_flag                    true
% 1.19/0.97  --time_out_prep_mult                    0.1
% 1.19/0.97  --splitting_mode                        input
% 1.19/0.97  --splitting_grd                         true
% 1.19/0.97  --splitting_cvd                         false
% 1.19/0.97  --splitting_cvd_svl                     false
% 1.19/0.97  --splitting_nvd                         32
% 1.19/0.97  --sub_typing                            true
% 1.19/0.97  --prep_gs_sim                           true
% 1.19/0.97  --prep_unflatten                        true
% 1.19/0.97  --prep_res_sim                          true
% 1.19/0.97  --prep_upred                            true
% 1.19/0.97  --prep_sem_filter                       exhaustive
% 1.19/0.97  --prep_sem_filter_out                   false
% 1.19/0.97  --pred_elim                             true
% 1.19/0.97  --res_sim_input                         true
% 1.19/0.97  --eq_ax_congr_red                       true
% 1.19/0.97  --pure_diseq_elim                       true
% 1.19/0.97  --brand_transform                       false
% 1.19/0.97  --non_eq_to_eq                          false
% 1.19/0.97  --prep_def_merge                        true
% 1.19/0.97  --prep_def_merge_prop_impl              false
% 1.19/0.97  --prep_def_merge_mbd                    true
% 1.19/0.97  --prep_def_merge_tr_red                 false
% 1.19/0.97  --prep_def_merge_tr_cl                  false
% 1.19/0.97  --smt_preprocessing                     true
% 1.19/0.97  --smt_ac_axioms                         fast
% 1.19/0.97  --preprocessed_out                      false
% 1.19/0.97  --preprocessed_stats                    false
% 1.19/0.97  
% 1.19/0.97  ------ Abstraction refinement Options
% 1.19/0.97  
% 1.19/0.97  --abstr_ref                             []
% 1.19/0.97  --abstr_ref_prep                        false
% 1.19/0.97  --abstr_ref_until_sat                   false
% 1.19/0.97  --abstr_ref_sig_restrict                funpre
% 1.19/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.19/0.97  --abstr_ref_under                       []
% 1.19/0.97  
% 1.19/0.97  ------ SAT Options
% 1.19/0.97  
% 1.19/0.97  --sat_mode                              false
% 1.19/0.97  --sat_fm_restart_options                ""
% 1.19/0.97  --sat_gr_def                            false
% 1.19/0.97  --sat_epr_types                         true
% 1.19/0.97  --sat_non_cyclic_types                  false
% 1.19/0.97  --sat_finite_models                     false
% 1.19/0.97  --sat_fm_lemmas                         false
% 1.19/0.97  --sat_fm_prep                           false
% 1.19/0.97  --sat_fm_uc_incr                        true
% 1.19/0.97  --sat_out_model                         small
% 1.19/0.97  --sat_out_clauses                       false
% 1.19/0.97  
% 1.19/0.97  ------ QBF Options
% 1.19/0.97  
% 1.19/0.97  --qbf_mode                              false
% 1.19/0.97  --qbf_elim_univ                         false
% 1.19/0.97  --qbf_dom_inst                          none
% 1.19/0.97  --qbf_dom_pre_inst                      false
% 1.19/0.97  --qbf_sk_in                             false
% 1.19/0.97  --qbf_pred_elim                         true
% 1.19/0.97  --qbf_split                             512
% 1.19/0.97  
% 1.19/0.97  ------ BMC1 Options
% 1.19/0.97  
% 1.19/0.97  --bmc1_incremental                      false
% 1.19/0.97  --bmc1_axioms                           reachable_all
% 1.19/0.97  --bmc1_min_bound                        0
% 1.19/0.97  --bmc1_max_bound                        -1
% 1.19/0.97  --bmc1_max_bound_default                -1
% 1.19/0.97  --bmc1_symbol_reachability              true
% 1.19/0.97  --bmc1_property_lemmas                  false
% 1.19/0.97  --bmc1_k_induction                      false
% 1.19/0.97  --bmc1_non_equiv_states                 false
% 1.19/0.97  --bmc1_deadlock                         false
% 1.19/0.97  --bmc1_ucm                              false
% 1.19/0.97  --bmc1_add_unsat_core                   none
% 1.19/0.97  --bmc1_unsat_core_children              false
% 1.19/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.19/0.97  --bmc1_out_stat                         full
% 1.19/0.97  --bmc1_ground_init                      false
% 1.19/0.97  --bmc1_pre_inst_next_state              false
% 1.19/0.97  --bmc1_pre_inst_state                   false
% 1.19/0.97  --bmc1_pre_inst_reach_state             false
% 1.19/0.97  --bmc1_out_unsat_core                   false
% 1.19/0.97  --bmc1_aig_witness_out                  false
% 1.19/0.97  --bmc1_verbose                          false
% 1.19/0.97  --bmc1_dump_clauses_tptp                false
% 1.19/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.19/0.97  --bmc1_dump_file                        -
% 1.19/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.19/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.19/0.97  --bmc1_ucm_extend_mode                  1
% 1.19/0.97  --bmc1_ucm_init_mode                    2
% 1.19/0.97  --bmc1_ucm_cone_mode                    none
% 1.19/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.19/0.97  --bmc1_ucm_relax_model                  4
% 1.19/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.19/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.19/0.97  --bmc1_ucm_layered_model                none
% 1.19/0.97  --bmc1_ucm_max_lemma_size               10
% 1.19/0.97  
% 1.19/0.97  ------ AIG Options
% 1.19/0.97  
% 1.19/0.97  --aig_mode                              false
% 1.19/0.97  
% 1.19/0.97  ------ Instantiation Options
% 1.19/0.97  
% 1.19/0.97  --instantiation_flag                    true
% 1.19/0.97  --inst_sos_flag                         false
% 1.19/0.97  --inst_sos_phase                        true
% 1.19/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.19/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.19/0.97  --inst_lit_sel_side                     none
% 1.19/0.97  --inst_solver_per_active                1400
% 1.19/0.97  --inst_solver_calls_frac                1.
% 1.19/0.97  --inst_passive_queue_type               priority_queues
% 1.19/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.19/0.97  --inst_passive_queues_freq              [25;2]
% 1.19/0.97  --inst_dismatching                      true
% 1.19/0.97  --inst_eager_unprocessed_to_passive     true
% 1.19/0.97  --inst_prop_sim_given                   true
% 1.19/0.97  --inst_prop_sim_new                     false
% 1.19/0.97  --inst_subs_new                         false
% 1.19/0.97  --inst_eq_res_simp                      false
% 1.19/0.97  --inst_subs_given                       false
% 1.19/0.97  --inst_orphan_elimination               true
% 1.19/0.97  --inst_learning_loop_flag               true
% 1.19/0.97  --inst_learning_start                   3000
% 1.19/0.97  --inst_learning_factor                  2
% 1.19/0.97  --inst_start_prop_sim_after_learn       3
% 1.19/0.97  --inst_sel_renew                        solver
% 1.19/0.97  --inst_lit_activity_flag                true
% 1.19/0.97  --inst_restr_to_given                   false
% 1.19/0.97  --inst_activity_threshold               500
% 1.19/0.97  --inst_out_proof                        true
% 1.19/0.97  
% 1.19/0.97  ------ Resolution Options
% 1.19/0.97  
% 1.19/0.97  --resolution_flag                       false
% 1.19/0.97  --res_lit_sel                           adaptive
% 1.19/0.97  --res_lit_sel_side                      none
% 1.19/0.97  --res_ordering                          kbo
% 1.19/0.97  --res_to_prop_solver                    active
% 1.19/0.97  --res_prop_simpl_new                    false
% 1.19/0.97  --res_prop_simpl_given                  true
% 1.19/0.97  --res_passive_queue_type                priority_queues
% 1.19/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.19/0.97  --res_passive_queues_freq               [15;5]
% 1.19/0.97  --res_forward_subs                      full
% 1.19/0.97  --res_backward_subs                     full
% 1.19/0.97  --res_forward_subs_resolution           true
% 1.19/0.97  --res_backward_subs_resolution          true
% 1.19/0.97  --res_orphan_elimination                true
% 1.19/0.97  --res_time_limit                        2.
% 1.19/0.97  --res_out_proof                         true
% 1.19/0.97  
% 1.19/0.97  ------ Superposition Options
% 1.19/0.97  
% 1.19/0.97  --superposition_flag                    true
% 1.19/0.97  --sup_passive_queue_type                priority_queues
% 1.19/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.19/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.19/0.97  --demod_completeness_check              fast
% 1.19/0.97  --demod_use_ground                      true
% 1.19/0.97  --sup_to_prop_solver                    passive
% 1.19/0.97  --sup_prop_simpl_new                    true
% 1.19/0.97  --sup_prop_simpl_given                  true
% 1.19/0.97  --sup_fun_splitting                     false
% 1.19/0.97  --sup_smt_interval                      50000
% 1.19/0.97  
% 1.19/0.97  ------ Superposition Simplification Setup
% 1.19/0.97  
% 1.19/0.97  --sup_indices_passive                   []
% 1.19/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.19/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.19/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.19/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.19/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.19/0.97  --sup_full_bw                           [BwDemod]
% 1.19/0.97  --sup_immed_triv                        [TrivRules]
% 1.19/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.19/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.19/0.97  --sup_immed_bw_main                     []
% 1.19/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.19/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.19/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.19/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.19/0.97  
% 1.19/0.97  ------ Combination Options
% 1.19/0.97  
% 1.19/0.97  --comb_res_mult                         3
% 1.19/0.97  --comb_sup_mult                         2
% 1.19/0.97  --comb_inst_mult                        10
% 1.19/0.97  
% 1.19/0.97  ------ Debug Options
% 1.19/0.97  
% 1.19/0.97  --dbg_backtrace                         false
% 1.19/0.97  --dbg_dump_prop_clauses                 false
% 1.19/0.97  --dbg_dump_prop_clauses_file            -
% 1.19/0.97  --dbg_out_stat                          false
% 1.19/0.97  
% 1.19/0.97  
% 1.19/0.97  
% 1.19/0.97  
% 1.19/0.97  ------ Proving...
% 1.19/0.97  
% 1.19/0.97  
% 1.19/0.97  % SZS status Theorem for theBenchmark.p
% 1.19/0.97  
% 1.19/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 1.19/0.97  
% 1.19/0.97  fof(f2,axiom,(
% 1.19/0.97    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.97  
% 1.19/0.97  fof(f18,plain,(
% 1.19/0.97    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.19/0.97    inference(ennf_transformation,[],[f2])).
% 1.19/0.97  
% 1.19/0.97  fof(f48,plain,(
% 1.19/0.97    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.19/0.97    inference(cnf_transformation,[],[f18])).
% 1.19/0.97  
% 1.19/0.97  fof(f4,axiom,(
% 1.19/0.97    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 1.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.97  
% 1.19/0.97  fof(f20,plain,(
% 1.19/0.97    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 1.19/0.97    inference(ennf_transformation,[],[f4])).
% 1.19/0.97  
% 1.19/0.97  fof(f21,plain,(
% 1.19/0.97    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 1.19/0.97    inference(flattening,[],[f20])).
% 1.19/0.97  
% 1.19/0.97  fof(f50,plain,(
% 1.19/0.97    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 1.19/0.97    inference(cnf_transformation,[],[f21])).
% 1.19/0.97  
% 1.19/0.97  fof(f13,conjecture,(
% 1.19/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.97  
% 1.19/0.97  fof(f14,negated_conjecture,(
% 1.19/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.19/0.97    inference(negated_conjecture,[],[f13])).
% 1.19/0.97  
% 1.19/0.97  fof(f37,plain,(
% 1.19/0.97    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.19/0.97    inference(ennf_transformation,[],[f14])).
% 1.19/0.97  
% 1.19/0.97  fof(f38,plain,(
% 1.19/0.97    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.19/0.97    inference(flattening,[],[f37])).
% 1.19/0.97  
% 1.19/0.97  fof(f42,plain,(
% 1.19/0.97    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.19/0.97    inference(nnf_transformation,[],[f38])).
% 1.19/0.97  
% 1.19/0.97  fof(f43,plain,(
% 1.19/0.97    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.19/0.97    inference(flattening,[],[f42])).
% 1.19/0.97  
% 1.19/0.97  fof(f45,plain,(
% 1.19/0.97    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK2) | ~v2_tex_2(sK2,X0)) & (v1_zfmisc_1(sK2) | v2_tex_2(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK2))) )),
% 1.19/0.97    introduced(choice_axiom,[])).
% 1.19/0.97  
% 1.19/0.97  fof(f44,plain,(
% 1.19/0.97    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK1)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK1) & v2_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.19/0.97    introduced(choice_axiom,[])).
% 1.19/0.97  
% 1.19/0.97  fof(f46,plain,(
% 1.19/0.97    ((~v1_zfmisc_1(sK2) | ~v2_tex_2(sK2,sK1)) & (v1_zfmisc_1(sK2) | v2_tex_2(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(sK2)) & l1_pre_topc(sK1) & v2_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.19/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f43,f45,f44])).
% 1.19/0.97  
% 1.19/0.97  fof(f72,plain,(
% 1.19/0.97    v1_zfmisc_1(sK2) | v2_tex_2(sK2,sK1)),
% 1.19/0.97    inference(cnf_transformation,[],[f46])).
% 1.19/0.97  
% 1.19/0.97  fof(f5,axiom,(
% 1.19/0.97    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 1.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.97  
% 1.19/0.97  fof(f22,plain,(
% 1.19/0.97    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 1.19/0.97    inference(ennf_transformation,[],[f5])).
% 1.19/0.97  
% 1.19/0.97  fof(f23,plain,(
% 1.19/0.97    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 1.19/0.97    inference(flattening,[],[f22])).
% 1.19/0.97  
% 1.19/0.97  fof(f51,plain,(
% 1.19/0.97    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 1.19/0.97    inference(cnf_transformation,[],[f23])).
% 1.19/0.97  
% 1.19/0.97  fof(f73,plain,(
% 1.19/0.97    ~v1_zfmisc_1(sK2) | ~v2_tex_2(sK2,sK1)),
% 1.19/0.97    inference(cnf_transformation,[],[f46])).
% 1.19/0.97  
% 1.19/0.97  fof(f71,plain,(
% 1.19/0.97    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.19/0.97    inference(cnf_transformation,[],[f46])).
% 1.19/0.97  
% 1.19/0.97  fof(f11,axiom,(
% 1.19/0.97    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 1.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.97  
% 1.19/0.97  fof(f15,plain,(
% 1.19/0.97    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 1.19/0.97    inference(pure_predicate_removal,[],[f11])).
% 1.19/0.97  
% 1.19/0.97  fof(f33,plain,(
% 1.19/0.97    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.19/0.97    inference(ennf_transformation,[],[f15])).
% 1.19/0.97  
% 1.19/0.97  fof(f34,plain,(
% 1.19/0.97    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.19/0.97    inference(flattening,[],[f33])).
% 1.19/0.97  
% 1.19/0.97  fof(f39,plain,(
% 1.19/0.97    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK0(X0,X1)) = X1 & m1_pre_topc(sK0(X0,X1),X0) & ~v2_struct_0(sK0(X0,X1))))),
% 1.19/0.97    introduced(choice_axiom,[])).
% 1.19/0.97  
% 1.19/0.97  fof(f40,plain,(
% 1.19/0.97    ! [X0] : (! [X1] : ((u1_struct_0(sK0(X0,X1)) = X1 & m1_pre_topc(sK0(X0,X1),X0) & ~v2_struct_0(sK0(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.19/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f39])).
% 1.19/0.97  
% 1.19/0.97  fof(f63,plain,(
% 1.19/0.97    ( ! [X0,X1] : (u1_struct_0(sK0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.19/0.97    inference(cnf_transformation,[],[f40])).
% 1.19/0.97  
% 1.19/0.97  fof(f70,plain,(
% 1.19/0.97    ~v1_xboole_0(sK2)),
% 1.19/0.97    inference(cnf_transformation,[],[f46])).
% 1.19/0.97  
% 1.19/0.97  fof(f8,axiom,(
% 1.19/0.97    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v2_tdlat_3(X1) & ~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 1.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.97  
% 1.19/0.97  fof(f27,plain,(
% 1.19/0.97    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (~v2_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.19/0.97    inference(ennf_transformation,[],[f8])).
% 1.19/0.97  
% 1.19/0.97  fof(f28,plain,(
% 1.19/0.97    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | ~v2_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.19/0.97    inference(flattening,[],[f27])).
% 1.19/0.97  
% 1.19/0.97  fof(f58,plain,(
% 1.19/0.97    ( ! [X0,X1] : (~v1_tdlat_3(X1) | ~v2_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.19/0.97    inference(cnf_transformation,[],[f28])).
% 1.19/0.97  
% 1.19/0.97  fof(f6,axiom,(
% 1.19/0.97    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.97  
% 1.19/0.97  fof(f24,plain,(
% 1.19/0.97    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.19/0.97    inference(ennf_transformation,[],[f6])).
% 1.19/0.97  
% 1.19/0.97  fof(f52,plain,(
% 1.19/0.97    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.19/0.97    inference(cnf_transformation,[],[f24])).
% 1.19/0.97  
% 1.19/0.97  fof(f62,plain,(
% 1.19/0.97    ( ! [X0,X1] : (m1_pre_topc(sK0(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.19/0.97    inference(cnf_transformation,[],[f40])).
% 1.19/0.97  
% 1.19/0.97  fof(f12,axiom,(
% 1.19/0.97    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 1.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.97  
% 1.19/0.97  fof(f35,plain,(
% 1.19/0.97    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.19/0.97    inference(ennf_transformation,[],[f12])).
% 1.19/0.97  
% 1.19/0.97  fof(f36,plain,(
% 1.19/0.97    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.19/0.97    inference(flattening,[],[f35])).
% 1.19/0.97  
% 1.19/0.97  fof(f41,plain,(
% 1.19/0.97    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.19/0.97    inference(nnf_transformation,[],[f36])).
% 1.19/0.97  
% 1.19/0.97  fof(f64,plain,(
% 1.19/0.97    ( ! [X2,X0,X1] : (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.19/0.97    inference(cnf_transformation,[],[f41])).
% 1.19/0.97  
% 1.19/0.97  fof(f75,plain,(
% 1.19/0.97    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~v2_tex_2(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.19/0.97    inference(equality_resolution,[],[f64])).
% 1.19/0.97  
% 1.19/0.97  fof(f66,plain,(
% 1.19/0.97    ~v2_struct_0(sK1)),
% 1.19/0.97    inference(cnf_transformation,[],[f46])).
% 1.19/0.97  
% 1.19/0.97  fof(f69,plain,(
% 1.19/0.97    l1_pre_topc(sK1)),
% 1.19/0.97    inference(cnf_transformation,[],[f46])).
% 1.19/0.97  
% 1.19/0.97  fof(f61,plain,(
% 1.19/0.97    ( ! [X0,X1] : (~v2_struct_0(sK0(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.19/0.97    inference(cnf_transformation,[],[f40])).
% 1.19/0.97  
% 1.19/0.97  fof(f7,axiom,(
% 1.19/0.97    ! [X0] : (l1_pre_topc(X0) => ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => (v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))))),
% 1.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.97  
% 1.19/0.97  fof(f25,plain,(
% 1.19/0.97    ! [X0] : (((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) | (~v2_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.19/0.97    inference(ennf_transformation,[],[f7])).
% 1.19/0.97  
% 1.19/0.97  fof(f26,plain,(
% 1.19/0.97    ! [X0] : ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) | ~v2_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.19/0.97    inference(flattening,[],[f25])).
% 1.19/0.97  
% 1.19/0.97  fof(f55,plain,(
% 1.19/0.97    ( ! [X0] : (v1_tdlat_3(X0) | ~v2_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.19/0.97    inference(cnf_transformation,[],[f26])).
% 1.19/0.97  
% 1.19/0.97  fof(f65,plain,(
% 1.19/0.97    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.19/0.97    inference(cnf_transformation,[],[f41])).
% 1.19/0.97  
% 1.19/0.97  fof(f74,plain,(
% 1.19/0.97    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.19/0.97    inference(equality_resolution,[],[f65])).
% 1.19/0.97  
% 1.19/0.97  fof(f1,axiom,(
% 1.19/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.97  
% 1.19/0.97  fof(f16,plain,(
% 1.19/0.97    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.19/0.97    inference(ennf_transformation,[],[f1])).
% 1.19/0.97  
% 1.19/0.97  fof(f17,plain,(
% 1.19/0.97    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.19/0.97    inference(flattening,[],[f16])).
% 1.19/0.97  
% 1.19/0.97  fof(f47,plain,(
% 1.19/0.97    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.19/0.97    inference(cnf_transformation,[],[f17])).
% 1.19/0.97  
% 1.19/0.97  fof(f3,axiom,(
% 1.19/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.97  
% 1.19/0.97  fof(f19,plain,(
% 1.19/0.97    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.19/0.97    inference(ennf_transformation,[],[f3])).
% 1.19/0.97  
% 1.19/0.97  fof(f49,plain,(
% 1.19/0.97    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.19/0.97    inference(cnf_transformation,[],[f19])).
% 1.19/0.97  
% 1.19/0.97  fof(f10,axiom,(
% 1.19/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 1.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.97  
% 1.19/0.97  fof(f31,plain,(
% 1.19/0.97    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.19/0.97    inference(ennf_transformation,[],[f10])).
% 1.19/0.97  
% 1.19/0.97  fof(f32,plain,(
% 1.19/0.97    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.19/0.97    inference(flattening,[],[f31])).
% 1.19/0.97  
% 1.19/0.97  fof(f60,plain,(
% 1.19/0.97    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.19/0.97    inference(cnf_transformation,[],[f32])).
% 1.19/0.97  
% 1.19/0.97  fof(f9,axiom,(
% 1.19/0.97    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.19/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.97  
% 1.19/0.97  fof(f29,plain,(
% 1.19/0.97    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.19/0.97    inference(ennf_transformation,[],[f9])).
% 1.19/0.97  
% 1.19/0.97  fof(f30,plain,(
% 1.19/0.97    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.19/0.97    inference(flattening,[],[f29])).
% 1.19/0.97  
% 1.19/0.97  fof(f59,plain,(
% 1.19/0.97    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 1.19/0.97    inference(cnf_transformation,[],[f30])).
% 1.19/0.97  
% 1.19/0.97  fof(f68,plain,(
% 1.19/0.97    v2_tdlat_3(sK1)),
% 1.19/0.97    inference(cnf_transformation,[],[f46])).
% 1.19/0.97  
% 1.19/0.97  fof(f67,plain,(
% 1.19/0.97    v2_pre_topc(sK1)),
% 1.19/0.97    inference(cnf_transformation,[],[f46])).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1,plain,
% 1.19/0.97      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 1.19/0.97      inference(cnf_transformation,[],[f48]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_3,plain,
% 1.19/0.97      ( v7_struct_0(X0)
% 1.19/0.97      | ~ v1_zfmisc_1(u1_struct_0(X0))
% 1.19/0.97      | ~ l1_struct_0(X0) ),
% 1.19/0.97      inference(cnf_transformation,[],[f50]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_327,plain,
% 1.19/0.97      ( v7_struct_0(X0)
% 1.19/0.97      | ~ v1_zfmisc_1(u1_struct_0(X0))
% 1.19/0.97      | ~ l1_pre_topc(X0) ),
% 1.19/0.97      inference(resolution,[status(thm)],[c_1,c_3]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_20,negated_conjecture,
% 1.19/0.97      ( v2_tex_2(sK2,sK1) | v1_zfmisc_1(sK2) ),
% 1.19/0.97      inference(cnf_transformation,[],[f72]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_184,plain,
% 1.19/0.97      ( v1_zfmisc_1(sK2) | v2_tex_2(sK2,sK1) ),
% 1.19/0.97      inference(prop_impl,[status(thm)],[c_20]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_185,plain,
% 1.19/0.97      ( v2_tex_2(sK2,sK1) | v1_zfmisc_1(sK2) ),
% 1.19/0.97      inference(renaming,[status(thm)],[c_184]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_368,plain,
% 1.19/0.97      ( v2_tex_2(sK2,sK1)
% 1.19/0.97      | v7_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | u1_struct_0(X0) != sK2 ),
% 1.19/0.97      inference(resolution_lifted,[status(thm)],[c_327,c_185]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_4,plain,
% 1.19/0.97      ( ~ v7_struct_0(X0)
% 1.19/0.97      | v1_zfmisc_1(u1_struct_0(X0))
% 1.19/0.97      | ~ l1_struct_0(X0) ),
% 1.19/0.97      inference(cnf_transformation,[],[f51]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_313,plain,
% 1.19/0.97      ( ~ v7_struct_0(X0)
% 1.19/0.97      | v1_zfmisc_1(u1_struct_0(X0))
% 1.19/0.97      | ~ l1_pre_topc(X0) ),
% 1.19/0.97      inference(resolution,[status(thm)],[c_1,c_4]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_19,negated_conjecture,
% 1.19/0.97      ( ~ v2_tex_2(sK2,sK1) | ~ v1_zfmisc_1(sK2) ),
% 1.19/0.97      inference(cnf_transformation,[],[f73]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_182,plain,
% 1.19/0.97      ( ~ v1_zfmisc_1(sK2) | ~ v2_tex_2(sK2,sK1) ),
% 1.19/0.97      inference(prop_impl,[status(thm)],[c_19]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_183,plain,
% 1.19/0.97      ( ~ v2_tex_2(sK2,sK1) | ~ v1_zfmisc_1(sK2) ),
% 1.19/0.97      inference(renaming,[status(thm)],[c_182]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_351,plain,
% 1.19/0.97      ( ~ v2_tex_2(sK2,sK1)
% 1.19/0.97      | ~ v7_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | u1_struct_0(X0) != sK2 ),
% 1.19/0.97      inference(resolution_lifted,[status(thm)],[c_313,c_183]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_614,plain,
% 1.19/0.97      ( ~ v7_struct_0(X0)
% 1.19/0.97      | v7_struct_0(X1)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | u1_struct_0(X0) != sK2
% 1.19/0.97      | u1_struct_0(X1) != sK2 ),
% 1.19/0.97      inference(resolution,[status(thm)],[c_368,c_351]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1667,plain,
% 1.19/0.97      ( ~ v7_struct_0(X0_45)
% 1.19/0.97      | v7_struct_0(X1_45)
% 1.19/0.97      | ~ l1_pre_topc(X1_45)
% 1.19/0.97      | ~ l1_pre_topc(X0_45)
% 1.19/0.97      | u1_struct_0(X1_45) != sK2
% 1.19/0.97      | u1_struct_0(X0_45) != sK2 ),
% 1.19/0.97      inference(subtyping,[status(esa)],[c_614]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1675,plain,
% 1.19/0.97      ( ~ v7_struct_0(X0_45)
% 1.19/0.97      | ~ l1_pre_topc(X0_45)
% 1.19/0.97      | u1_struct_0(X0_45) != sK2
% 1.19/0.97      | ~ sP1_iProver_split ),
% 1.19/0.97      inference(splitting,
% 1.19/0.97                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.19/0.97                [c_1667]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_2320,plain,
% 1.19/0.97      ( ~ v7_struct_0(sK0(X0_45,sK2))
% 1.19/0.97      | ~ l1_pre_topc(sK0(X0_45,sK2))
% 1.19/0.97      | ~ sP1_iProver_split
% 1.19/0.97      | u1_struct_0(sK0(X0_45,sK2)) != sK2 ),
% 1.19/0.97      inference(instantiation,[status(thm)],[c_1675]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_2321,plain,
% 1.19/0.97      ( u1_struct_0(sK0(X0_45,sK2)) != sK2
% 1.19/0.97      | v7_struct_0(sK0(X0_45,sK2)) != iProver_top
% 1.19/0.97      | l1_pre_topc(sK0(X0_45,sK2)) != iProver_top
% 1.19/0.97      | sP1_iProver_split != iProver_top ),
% 1.19/0.97      inference(predicate_to_equality,[status(thm)],[c_2320]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_2323,plain,
% 1.19/0.97      ( u1_struct_0(sK0(sK1,sK2)) != sK2
% 1.19/0.97      | v7_struct_0(sK0(sK1,sK2)) != iProver_top
% 1.19/0.97      | l1_pre_topc(sK0(sK1,sK2)) != iProver_top
% 1.19/0.97      | sP1_iProver_split != iProver_top ),
% 1.19/0.97      inference(instantiation,[status(thm)],[c_2321]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1674,plain,
% 1.19/0.97      ( v7_struct_0(X0_45)
% 1.19/0.97      | ~ l1_pre_topc(X0_45)
% 1.19/0.97      | u1_struct_0(X0_45) != sK2
% 1.19/0.97      | ~ sP0_iProver_split ),
% 1.19/0.97      inference(splitting,
% 1.19/0.97                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.19/0.97                [c_1667]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_2274,plain,
% 1.19/0.97      ( v7_struct_0(sK0(X0_45,sK2))
% 1.19/0.97      | ~ l1_pre_topc(sK0(X0_45,sK2))
% 1.19/0.97      | ~ sP0_iProver_split
% 1.19/0.97      | u1_struct_0(sK0(X0_45,sK2)) != sK2 ),
% 1.19/0.97      inference(instantiation,[status(thm)],[c_1674]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_2275,plain,
% 1.19/0.97      ( u1_struct_0(sK0(X0_45,sK2)) != sK2
% 1.19/0.97      | v7_struct_0(sK0(X0_45,sK2)) = iProver_top
% 1.19/0.97      | l1_pre_topc(sK0(X0_45,sK2)) != iProver_top
% 1.19/0.97      | sP0_iProver_split != iProver_top ),
% 1.19/0.97      inference(predicate_to_equality,[status(thm)],[c_2274]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_2277,plain,
% 1.19/0.97      ( u1_struct_0(sK0(sK1,sK2)) != sK2
% 1.19/0.97      | v7_struct_0(sK0(sK1,sK2)) = iProver_top
% 1.19/0.97      | l1_pre_topc(sK0(sK1,sK2)) != iProver_top
% 1.19/0.97      | sP0_iProver_split != iProver_top ),
% 1.19/0.97      inference(instantiation,[status(thm)],[c_2275]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1695,plain,
% 1.19/0.97      ( k1_zfmisc_1(X0_46) = k1_zfmisc_1(X1_46) | X0_46 != X1_46 ),
% 1.19/0.97      theory(equality) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_2248,plain,
% 1.19/0.97      ( k1_zfmisc_1(u1_struct_0(X0_45)) = k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | u1_struct_0(X0_45) != u1_struct_0(sK1) ),
% 1.19/0.97      inference(instantiation,[status(thm)],[c_1695]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_2249,plain,
% 1.19/0.97      ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.19/0.97      inference(instantiation,[status(thm)],[c_2248]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_21,negated_conjecture,
% 1.19/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.19/0.97      inference(cnf_transformation,[],[f71]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_14,plain,
% 1.19/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.19/0.97      | v1_xboole_0(X0)
% 1.19/0.97      | v2_struct_0(X1)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | u1_struct_0(sK0(X1,X0)) = X0 ),
% 1.19/0.97      inference(cnf_transformation,[],[f63]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_22,negated_conjecture,
% 1.19/0.97      ( ~ v1_xboole_0(sK2) ),
% 1.19/0.97      inference(cnf_transformation,[],[f70]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_431,plain,
% 1.19/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.19/0.97      | v2_struct_0(X1)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | u1_struct_0(sK0(X1,X0)) = X0
% 1.19/0.97      | sK2 != X0 ),
% 1.19/0.97      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_432,plain,
% 1.19/0.97      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | u1_struct_0(sK0(X0,sK2)) = sK2 ),
% 1.19/0.97      inference(unflattening,[status(thm)],[c_431]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_728,plain,
% 1.19/0.97      ( v2_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | u1_struct_0(sK0(X0,sK2)) = sK2
% 1.19/0.97      | sK2 != sK2 ),
% 1.19/0.97      inference(resolution_lifted,[status(thm)],[c_21,c_432]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1349,plain,
% 1.19/0.97      ( v2_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | u1_struct_0(sK0(X0,sK2)) = sK2 ),
% 1.19/0.97      inference(equality_resolution_simp,[status(thm)],[c_728]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1659,plain,
% 1.19/0.97      ( v2_struct_0(X0_45)
% 1.19/0.97      | ~ l1_pre_topc(X0_45)
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | u1_struct_0(sK0(X0_45,sK2)) = sK2 ),
% 1.19/0.97      inference(subtyping,[status(esa)],[c_1349]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1738,plain,
% 1.19/0.97      ( v2_struct_0(sK1)
% 1.19/0.97      | ~ l1_pre_topc(sK1)
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | u1_struct_0(sK0(sK1,sK2)) = sK2 ),
% 1.19/0.97      inference(instantiation,[status(thm)],[c_1659]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_10,plain,
% 1.19/0.97      ( ~ m1_pre_topc(X0,X1)
% 1.19/0.97      | ~ v1_tdlat_3(X0)
% 1.19/0.97      | v2_struct_0(X1)
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | ~ v2_tdlat_3(X0)
% 1.19/0.97      | v7_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X1) ),
% 1.19/0.97      inference(cnf_transformation,[],[f58]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_5,plain,
% 1.19/0.97      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 1.19/0.97      inference(cnf_transformation,[],[f52]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_967,plain,
% 1.19/0.97      ( ~ v1_tdlat_3(X0)
% 1.19/0.97      | v2_struct_0(X1)
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | ~ v2_tdlat_3(X0)
% 1.19/0.97      | v7_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | ~ l1_pre_topc(X2)
% 1.19/0.97      | X2 != X1
% 1.19/0.97      | X2 != X0 ),
% 1.19/0.97      inference(resolution_lifted,[status(thm)],[c_10,c_5]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_968,plain,
% 1.19/0.97      ( ~ v1_tdlat_3(X0)
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | ~ v2_tdlat_3(X0)
% 1.19/0.97      | v7_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X0) ),
% 1.19/0.97      inference(unflattening,[status(thm)],[c_967]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_15,plain,
% 1.19/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.19/0.97      | m1_pre_topc(sK0(X1,X0),X1)
% 1.19/0.97      | v1_xboole_0(X0)
% 1.19/0.97      | v2_struct_0(X1)
% 1.19/0.97      | ~ l1_pre_topc(X1) ),
% 1.19/0.97      inference(cnf_transformation,[],[f62]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_413,plain,
% 1.19/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.19/0.97      | m1_pre_topc(sK0(X1,X0),X1)
% 1.19/0.97      | v2_struct_0(X1)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | sK2 != X0 ),
% 1.19/0.97      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_414,plain,
% 1.19/0.97      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.19/0.97      | m1_pre_topc(sK0(X0,sK2),X0)
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X0) ),
% 1.19/0.97      inference(unflattening,[status(thm)],[c_413]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_746,plain,
% 1.19/0.97      ( m1_pre_topc(sK0(X0,sK2),X0)
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | sK2 != sK2 ),
% 1.19/0.97      inference(resolution_lifted,[status(thm)],[c_21,c_414]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_18,plain,
% 1.19/0.97      ( ~ v2_tex_2(u1_struct_0(X0),X1)
% 1.19/0.97      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.19/0.97      | ~ m1_pre_topc(X0,X1)
% 1.19/0.97      | v1_tdlat_3(X0)
% 1.19/0.97      | v2_struct_0(X1)
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X1) ),
% 1.19/0.97      inference(cnf_transformation,[],[f75]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_669,plain,
% 1.19/0.97      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.19/0.97      | ~ m1_pre_topc(X0,X1)
% 1.19/0.97      | v1_tdlat_3(X0)
% 1.19/0.97      | v2_struct_0(X1)
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | v7_struct_0(X2)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | ~ l1_pre_topc(X2)
% 1.19/0.97      | u1_struct_0(X0) != sK2
% 1.19/0.97      | u1_struct_0(X2) != sK2
% 1.19/0.97      | sK1 != X1 ),
% 1.19/0.97      inference(resolution_lifted,[status(thm)],[c_18,c_368]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_670,plain,
% 1.19/0.97      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.19/0.97      | ~ m1_pre_topc(X0,sK1)
% 1.19/0.97      | v1_tdlat_3(X0)
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | v2_struct_0(sK1)
% 1.19/0.97      | v7_struct_0(X1)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | ~ l1_pre_topc(sK1)
% 1.19/0.97      | u1_struct_0(X0) != sK2
% 1.19/0.97      | u1_struct_0(X1) != sK2 ),
% 1.19/0.97      inference(unflattening,[status(thm)],[c_669]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_26,negated_conjecture,
% 1.19/0.97      ( ~ v2_struct_0(sK1) ),
% 1.19/0.97      inference(cnf_transformation,[],[f66]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_23,negated_conjecture,
% 1.19/0.97      ( l1_pre_topc(sK1) ),
% 1.19/0.97      inference(cnf_transformation,[],[f69]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_674,plain,
% 1.19/0.97      ( ~ l1_pre_topc(X1)
% 1.19/0.97      | v7_struct_0(X1)
% 1.19/0.97      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.19/0.97      | ~ m1_pre_topc(X0,sK1)
% 1.19/0.97      | v1_tdlat_3(X0)
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | u1_struct_0(X0) != sK2
% 1.19/0.97      | u1_struct_0(X1) != sK2 ),
% 1.19/0.97      inference(global_propositional_subsumption,
% 1.19/0.97                [status(thm)],
% 1.19/0.97                [c_670,c_26,c_23]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_675,plain,
% 1.19/0.97      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.19/0.97      | ~ m1_pre_topc(X0,sK1)
% 1.19/0.97      | v1_tdlat_3(X0)
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | v7_struct_0(X1)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | u1_struct_0(X0) != sK2
% 1.19/0.97      | u1_struct_0(X1) != sK2 ),
% 1.19/0.97      inference(renaming,[status(thm)],[c_674]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_782,plain,
% 1.19/0.97      ( ~ m1_pre_topc(X0,sK1)
% 1.19/0.97      | v1_tdlat_3(X0)
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | v7_struct_0(X1)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | u1_struct_0(X0) != sK2
% 1.19/0.97      | u1_struct_0(X1) != sK2 ),
% 1.19/0.97      inference(resolution_lifted,[status(thm)],[c_21,c_675]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1142,plain,
% 1.19/0.97      ( v1_tdlat_3(X0)
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | v2_struct_0(X1)
% 1.19/0.97      | v7_struct_0(X2)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | ~ l1_pre_topc(X2)
% 1.19/0.97      | sK0(X1,sK2) != X0
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | u1_struct_0(X0) != sK2
% 1.19/0.97      | u1_struct_0(X2) != sK2
% 1.19/0.97      | sK1 != X1
% 1.19/0.97      | sK2 != sK2 ),
% 1.19/0.97      inference(resolution_lifted,[status(thm)],[c_746,c_782]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1143,plain,
% 1.19/0.97      ( v1_tdlat_3(sK0(sK1,sK2))
% 1.19/0.97      | v2_struct_0(sK0(sK1,sK2))
% 1.19/0.97      | v2_struct_0(sK1)
% 1.19/0.97      | v7_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | ~ l1_pre_topc(sK1)
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | u1_struct_0(X0) != sK2
% 1.19/0.97      | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
% 1.19/0.97      inference(unflattening,[status(thm)],[c_1142]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_16,plain,
% 1.19/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.19/0.97      | v1_xboole_0(X0)
% 1.19/0.97      | v2_struct_0(X1)
% 1.19/0.97      | ~ v2_struct_0(sK0(X1,X0))
% 1.19/0.97      | ~ l1_pre_topc(X1) ),
% 1.19/0.97      inference(cnf_transformation,[],[f61]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_395,plain,
% 1.19/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.19/0.97      | v2_struct_0(X1)
% 1.19/0.97      | ~ v2_struct_0(sK0(X1,X0))
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | sK2 != X0 ),
% 1.19/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_396,plain,
% 1.19/0.97      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | ~ v2_struct_0(sK0(X0,sK2))
% 1.19/0.97      | ~ l1_pre_topc(X0) ),
% 1.19/0.97      inference(unflattening,[status(thm)],[c_395]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_398,plain,
% 1.19/0.97      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.19/0.97      | ~ v2_struct_0(sK0(sK1,sK2))
% 1.19/0.97      | v2_struct_0(sK1)
% 1.19/0.97      | ~ l1_pre_topc(sK1) ),
% 1.19/0.97      inference(instantiation,[status(thm)],[c_396]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_434,plain,
% 1.19/0.97      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.19/0.97      | v2_struct_0(sK1)
% 1.19/0.97      | ~ l1_pre_topc(sK1)
% 1.19/0.97      | u1_struct_0(sK0(sK1,sK2)) = sK2 ),
% 1.19/0.97      inference(instantiation,[status(thm)],[c_432]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1145,plain,
% 1.19/0.97      ( u1_struct_0(X0) != sK2
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | v1_tdlat_3(sK0(sK1,sK2))
% 1.19/0.97      | v7_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X0) ),
% 1.19/0.97      inference(global_propositional_subsumption,
% 1.19/0.97                [status(thm)],
% 1.19/0.97                [c_1143,c_26,c_23,c_21,c_398,c_434]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1146,plain,
% 1.19/0.97      ( v1_tdlat_3(sK0(sK1,sK2))
% 1.19/0.97      | v7_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | u1_struct_0(X0) != sK2 ),
% 1.19/0.97      inference(renaming,[status(thm)],[c_1145]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1335,plain,
% 1.19/0.97      ( v1_tdlat_3(sK0(sK1,sK2))
% 1.19/0.97      | v7_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | u1_struct_0(X0) != sK2 ),
% 1.19/0.97      inference(equality_resolution_simp,[status(thm)],[c_1146]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1477,plain,
% 1.19/0.97      ( v2_struct_0(X0)
% 1.19/0.97      | ~ v2_tdlat_3(X0)
% 1.19/0.97      | v7_struct_0(X1)
% 1.19/0.97      | v7_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | sK0(sK1,sK2) != X0
% 1.19/0.97      | u1_struct_0(X1) != sK2 ),
% 1.19/0.97      inference(resolution_lifted,[status(thm)],[c_968,c_1335]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1478,plain,
% 1.19/0.97      ( v2_struct_0(sK0(sK1,sK2))
% 1.19/0.97      | ~ v2_tdlat_3(sK0(sK1,sK2))
% 1.19/0.97      | v7_struct_0(X0)
% 1.19/0.97      | v7_struct_0(sK0(sK1,sK2))
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | ~ l1_pre_topc(sK0(sK1,sK2))
% 1.19/0.97      | u1_struct_0(X0) != sK2 ),
% 1.19/0.97      inference(unflattening,[status(thm)],[c_1477]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1244,plain,
% 1.19/0.97      ( v2_struct_0(X0)
% 1.19/0.97      | ~ v2_tdlat_3(X0)
% 1.19/0.97      | v7_struct_0(X1)
% 1.19/0.97      | v7_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | sK0(sK1,sK2) != X0
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | u1_struct_0(X1) != sK2 ),
% 1.19/0.97      inference(resolution_lifted,[status(thm)],[c_968,c_1146]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1245,plain,
% 1.19/0.97      ( v2_struct_0(sK0(sK1,sK2))
% 1.19/0.97      | ~ v2_tdlat_3(sK0(sK1,sK2))
% 1.19/0.97      | v7_struct_0(X0)
% 1.19/0.97      | v7_struct_0(sK0(sK1,sK2))
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | ~ l1_pre_topc(sK0(sK1,sK2))
% 1.19/0.97      | u1_struct_0(X0) != sK2 ),
% 1.19/0.97      inference(unflattening,[status(thm)],[c_1244]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1480,plain,
% 1.19/0.97      ( ~ v2_tdlat_3(sK0(sK1,sK2))
% 1.19/0.97      | v7_struct_0(X0)
% 1.19/0.97      | v7_struct_0(sK0(sK1,sK2))
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | ~ l1_pre_topc(sK0(sK1,sK2))
% 1.19/0.97      | u1_struct_0(X0) != sK2 ),
% 1.19/0.97      inference(global_propositional_subsumption,
% 1.19/0.97                [status(thm)],
% 1.19/0.97                [c_1478,c_26,c_23,c_21,c_398,c_1245]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1661,plain,
% 1.19/0.97      ( ~ v2_tdlat_3(sK0(sK1,sK2))
% 1.19/0.97      | v7_struct_0(X0_45)
% 1.19/0.97      | v7_struct_0(sK0(sK1,sK2))
% 1.19/0.97      | ~ l1_pre_topc(X0_45)
% 1.19/0.97      | ~ l1_pre_topc(sK0(sK1,sK2))
% 1.19/0.97      | u1_struct_0(X0_45) != sK2 ),
% 1.19/0.97      inference(subtyping,[status(esa)],[c_1480]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1678,plain,
% 1.19/0.97      ( ~ v2_tdlat_3(sK0(sK1,sK2))
% 1.19/0.97      | v7_struct_0(sK0(sK1,sK2))
% 1.19/0.97      | ~ l1_pre_topc(sK0(sK1,sK2))
% 1.19/0.97      | sP0_iProver_split ),
% 1.19/0.97      inference(splitting,
% 1.19/0.97                [splitting(split),new_symbols(definition,[])],
% 1.19/0.97                [c_1661]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1732,plain,
% 1.19/0.97      ( v2_tdlat_3(sK0(sK1,sK2)) != iProver_top
% 1.19/0.97      | v7_struct_0(sK0(sK1,sK2)) = iProver_top
% 1.19/0.97      | l1_pre_topc(sK0(sK1,sK2)) != iProver_top
% 1.19/0.97      | sP0_iProver_split = iProver_top ),
% 1.19/0.97      inference(predicate_to_equality,[status(thm)],[c_1678]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_7,plain,
% 1.19/0.97      ( v1_tdlat_3(X0)
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | ~ v7_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | ~ v2_pre_topc(X0) ),
% 1.19/0.97      inference(cnf_transformation,[],[f55]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_17,plain,
% 1.19/0.97      ( v2_tex_2(u1_struct_0(X0),X1)
% 1.19/0.97      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.19/0.97      | ~ m1_pre_topc(X0,X1)
% 1.19/0.97      | ~ v1_tdlat_3(X0)
% 1.19/0.97      | v2_struct_0(X1)
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X1) ),
% 1.19/0.97      inference(cnf_transformation,[],[f74]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_635,plain,
% 1.19/0.97      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.19/0.97      | ~ m1_pre_topc(X0,X1)
% 1.19/0.97      | ~ v1_tdlat_3(X0)
% 1.19/0.97      | v2_struct_0(X1)
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | ~ v7_struct_0(X2)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | ~ l1_pre_topc(X2)
% 1.19/0.97      | u1_struct_0(X0) != sK2
% 1.19/0.97      | u1_struct_0(X2) != sK2
% 1.19/0.97      | sK1 != X1 ),
% 1.19/0.97      inference(resolution_lifted,[status(thm)],[c_17,c_351]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_636,plain,
% 1.19/0.97      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.19/0.97      | ~ m1_pre_topc(X0,sK1)
% 1.19/0.97      | ~ v1_tdlat_3(X0)
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | v2_struct_0(sK1)
% 1.19/0.97      | ~ v7_struct_0(X1)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | ~ l1_pre_topc(sK1)
% 1.19/0.97      | u1_struct_0(X0) != sK2
% 1.19/0.97      | u1_struct_0(X1) != sK2 ),
% 1.19/0.97      inference(unflattening,[status(thm)],[c_635]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_640,plain,
% 1.19/0.97      ( ~ l1_pre_topc(X1)
% 1.19/0.97      | ~ v7_struct_0(X1)
% 1.19/0.97      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.19/0.97      | ~ m1_pre_topc(X0,sK1)
% 1.19/0.97      | ~ v1_tdlat_3(X0)
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | u1_struct_0(X0) != sK2
% 1.19/0.97      | u1_struct_0(X1) != sK2 ),
% 1.19/0.97      inference(global_propositional_subsumption,
% 1.19/0.97                [status(thm)],
% 1.19/0.97                [c_636,c_26,c_23]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_641,plain,
% 1.19/0.97      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.19/0.97      | ~ m1_pre_topc(X0,sK1)
% 1.19/0.97      | ~ v1_tdlat_3(X0)
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | ~ v7_struct_0(X1)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | u1_struct_0(X0) != sK2
% 1.19/0.97      | u1_struct_0(X1) != sK2 ),
% 1.19/0.97      inference(renaming,[status(thm)],[c_640]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_811,plain,
% 1.19/0.97      ( ~ m1_pre_topc(X0,sK1)
% 1.19/0.97      | ~ v1_tdlat_3(X0)
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | ~ v7_struct_0(X1)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | u1_struct_0(X0) != sK2
% 1.19/0.97      | u1_struct_0(X1) != sK2 ),
% 1.19/0.97      inference(resolution_lifted,[status(thm)],[c_21,c_641]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1119,plain,
% 1.19/0.97      ( ~ v1_tdlat_3(X0)
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | v2_struct_0(X1)
% 1.19/0.97      | ~ v7_struct_0(X2)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | ~ l1_pre_topc(X2)
% 1.19/0.97      | sK0(X1,sK2) != X0
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | u1_struct_0(X0) != sK2
% 1.19/0.97      | u1_struct_0(X2) != sK2
% 1.19/0.97      | sK1 != X1
% 1.19/0.97      | sK2 != sK2 ),
% 1.19/0.97      inference(resolution_lifted,[status(thm)],[c_746,c_811]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1120,plain,
% 1.19/0.97      ( ~ v1_tdlat_3(sK0(sK1,sK2))
% 1.19/0.97      | v2_struct_0(sK0(sK1,sK2))
% 1.19/0.97      | v2_struct_0(sK1)
% 1.19/0.97      | ~ v7_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | ~ l1_pre_topc(sK1)
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | u1_struct_0(X0) != sK2
% 1.19/0.97      | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
% 1.19/0.97      inference(unflattening,[status(thm)],[c_1119]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1122,plain,
% 1.19/0.97      ( u1_struct_0(X0) != sK2
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | ~ v1_tdlat_3(sK0(sK1,sK2))
% 1.19/0.97      | ~ v7_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X0) ),
% 1.19/0.97      inference(global_propositional_subsumption,
% 1.19/0.97                [status(thm)],
% 1.19/0.97                [c_1120,c_26,c_23,c_21,c_398,c_434]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1123,plain,
% 1.19/0.97      ( ~ v1_tdlat_3(sK0(sK1,sK2))
% 1.19/0.97      | ~ v7_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | u1_struct_0(X0) != sK2 ),
% 1.19/0.97      inference(renaming,[status(thm)],[c_1122]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1337,plain,
% 1.19/0.97      ( ~ v1_tdlat_3(sK0(sK1,sK2))
% 1.19/0.97      | ~ v7_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | u1_struct_0(X0) != sK2 ),
% 1.19/0.97      inference(equality_resolution_simp,[status(thm)],[c_1123]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1451,plain,
% 1.19/0.97      ( v2_struct_0(X0)
% 1.19/0.97      | ~ v7_struct_0(X1)
% 1.19/0.97      | ~ v7_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | ~ v2_pre_topc(X0)
% 1.19/0.97      | sK0(sK1,sK2) != X0
% 1.19/0.97      | u1_struct_0(X1) != sK2 ),
% 1.19/0.97      inference(resolution_lifted,[status(thm)],[c_7,c_1337]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1452,plain,
% 1.19/0.97      ( v2_struct_0(sK0(sK1,sK2))
% 1.19/0.97      | ~ v7_struct_0(X0)
% 1.19/0.97      | ~ v7_struct_0(sK0(sK1,sK2))
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | ~ l1_pre_topc(sK0(sK1,sK2))
% 1.19/0.97      | ~ v2_pre_topc(sK0(sK1,sK2))
% 1.19/0.97      | u1_struct_0(X0) != sK2 ),
% 1.19/0.97      inference(unflattening,[status(thm)],[c_1451]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1218,plain,
% 1.19/0.97      ( v2_struct_0(X0)
% 1.19/0.97      | ~ v7_struct_0(X1)
% 1.19/0.97      | ~ v7_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | ~ v2_pre_topc(X0)
% 1.19/0.97      | sK0(sK1,sK2) != X0
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | u1_struct_0(X1) != sK2 ),
% 1.19/0.97      inference(resolution_lifted,[status(thm)],[c_7,c_1123]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1219,plain,
% 1.19/0.97      ( v2_struct_0(sK0(sK1,sK2))
% 1.19/0.97      | ~ v7_struct_0(X0)
% 1.19/0.97      | ~ v7_struct_0(sK0(sK1,sK2))
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | ~ l1_pre_topc(sK0(sK1,sK2))
% 1.19/0.97      | ~ v2_pre_topc(sK0(sK1,sK2))
% 1.19/0.97      | u1_struct_0(X0) != sK2 ),
% 1.19/0.97      inference(unflattening,[status(thm)],[c_1218]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1454,plain,
% 1.19/0.97      ( ~ v7_struct_0(X0)
% 1.19/0.97      | ~ v7_struct_0(sK0(sK1,sK2))
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | ~ l1_pre_topc(sK0(sK1,sK2))
% 1.19/0.97      | ~ v2_pre_topc(sK0(sK1,sK2))
% 1.19/0.97      | u1_struct_0(X0) != sK2 ),
% 1.19/0.97      inference(global_propositional_subsumption,
% 1.19/0.97                [status(thm)],
% 1.19/0.97                [c_1452,c_26,c_23,c_21,c_398,c_1219]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1662,plain,
% 1.19/0.97      ( ~ v7_struct_0(X0_45)
% 1.19/0.97      | ~ v7_struct_0(sK0(sK1,sK2))
% 1.19/0.97      | ~ l1_pre_topc(X0_45)
% 1.19/0.97      | ~ l1_pre_topc(sK0(sK1,sK2))
% 1.19/0.97      | ~ v2_pre_topc(sK0(sK1,sK2))
% 1.19/0.97      | u1_struct_0(X0_45) != sK2 ),
% 1.19/0.97      inference(subtyping,[status(esa)],[c_1454]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1677,plain,
% 1.19/0.97      ( ~ v7_struct_0(sK0(sK1,sK2))
% 1.19/0.97      | ~ l1_pre_topc(sK0(sK1,sK2))
% 1.19/0.97      | ~ v2_pre_topc(sK0(sK1,sK2))
% 1.19/0.97      | sP1_iProver_split ),
% 1.19/0.97      inference(splitting,
% 1.19/0.97                [splitting(split),new_symbols(definition,[])],
% 1.19/0.97                [c_1662]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1730,plain,
% 1.19/0.97      ( v7_struct_0(sK0(sK1,sK2)) != iProver_top
% 1.19/0.97      | l1_pre_topc(sK0(sK1,sK2)) != iProver_top
% 1.19/0.97      | v2_pre_topc(sK0(sK1,sK2)) != iProver_top
% 1.19/0.97      | sP1_iProver_split = iProver_top ),
% 1.19/0.97      inference(predicate_to_equality,[status(thm)],[c_1677]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_0,plain,
% 1.19/0.97      ( ~ m1_pre_topc(X0,X1)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | ~ v2_pre_topc(X1)
% 1.19/0.97      | v2_pre_topc(X0) ),
% 1.19/0.97      inference(cnf_transformation,[],[f47]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1064,plain,
% 1.19/0.97      ( v2_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | ~ v2_pre_topc(X1)
% 1.19/0.97      | v2_pre_topc(X2)
% 1.19/0.97      | X0 != X1
% 1.19/0.97      | sK0(X0,sK2) != X2
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | sK2 != sK2 ),
% 1.19/0.97      inference(resolution_lifted,[status(thm)],[c_0,c_746]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1065,plain,
% 1.19/0.97      ( v2_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | ~ v2_pre_topc(X0)
% 1.19/0.97      | v2_pre_topc(sK0(X0,sK2))
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.19/0.97      inference(unflattening,[status(thm)],[c_1064]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1664,plain,
% 1.19/0.97      ( v2_struct_0(X0_45)
% 1.19/0.97      | ~ l1_pre_topc(X0_45)
% 1.19/0.97      | ~ v2_pre_topc(X0_45)
% 1.19/0.97      | v2_pre_topc(sK0(X0_45,sK2))
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.19/0.97      inference(subtyping,[status(esa)],[c_1065]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1727,plain,
% 1.19/0.97      ( k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | v2_struct_0(X0_45) = iProver_top
% 1.19/0.97      | l1_pre_topc(X0_45) != iProver_top
% 1.19/0.97      | v2_pre_topc(X0_45) != iProver_top
% 1.19/0.97      | v2_pre_topc(sK0(X0_45,sK2)) = iProver_top ),
% 1.19/0.97      inference(predicate_to_equality,[status(thm)],[c_1664]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1729,plain,
% 1.19/0.97      ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | v2_struct_0(sK1) = iProver_top
% 1.19/0.97      | l1_pre_topc(sK1) != iProver_top
% 1.19/0.97      | v2_pre_topc(sK0(sK1,sK2)) = iProver_top
% 1.19/0.97      | v2_pre_topc(sK1) != iProver_top ),
% 1.19/0.97      inference(instantiation,[status(thm)],[c_1727]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_2,plain,
% 1.19/0.97      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.19/0.97      inference(cnf_transformation,[],[f49]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1046,plain,
% 1.19/0.97      ( v2_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | l1_pre_topc(X2)
% 1.19/0.97      | X0 != X1
% 1.19/0.97      | sK0(X0,sK2) != X2
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | sK2 != sK2 ),
% 1.19/0.97      inference(resolution_lifted,[status(thm)],[c_2,c_746]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1047,plain,
% 1.19/0.97      ( v2_struct_0(X0)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | l1_pre_topc(sK0(X0,sK2))
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.19/0.97      inference(unflattening,[status(thm)],[c_1046]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1665,plain,
% 1.19/0.97      ( v2_struct_0(X0_45)
% 1.19/0.97      | ~ l1_pre_topc(X0_45)
% 1.19/0.97      | l1_pre_topc(sK0(X0_45,sK2))
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.19/0.97      inference(subtyping,[status(esa)],[c_1047]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1724,plain,
% 1.19/0.97      ( k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | v2_struct_0(X0_45) = iProver_top
% 1.19/0.97      | l1_pre_topc(X0_45) != iProver_top
% 1.19/0.97      | l1_pre_topc(sK0(X0_45,sK2)) = iProver_top ),
% 1.19/0.97      inference(predicate_to_equality,[status(thm)],[c_1665]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1726,plain,
% 1.19/0.97      ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | v2_struct_0(sK1) = iProver_top
% 1.19/0.97      | l1_pre_topc(sK0(sK1,sK2)) = iProver_top
% 1.19/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 1.19/0.97      inference(instantiation,[status(thm)],[c_1724]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_13,plain,
% 1.19/0.97      ( ~ m1_pre_topc(X0,X1)
% 1.19/0.97      | v2_struct_0(X1)
% 1.19/0.97      | ~ v2_tdlat_3(X1)
% 1.19/0.97      | v2_tdlat_3(X0)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | ~ v2_pre_topc(X1) ),
% 1.19/0.97      inference(cnf_transformation,[],[f60]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_992,plain,
% 1.19/0.97      ( v2_struct_0(X0)
% 1.19/0.97      | v2_struct_0(X1)
% 1.19/0.97      | ~ v2_tdlat_3(X0)
% 1.19/0.97      | v2_tdlat_3(X2)
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | ~ l1_pre_topc(X1)
% 1.19/0.97      | ~ v2_pre_topc(X0)
% 1.19/0.97      | X1 != X0
% 1.19/0.97      | sK0(X1,sK2) != X2
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | sK2 != sK2 ),
% 1.19/0.97      inference(resolution_lifted,[status(thm)],[c_13,c_746]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_993,plain,
% 1.19/0.97      ( v2_struct_0(X0)
% 1.19/0.97      | ~ v2_tdlat_3(X0)
% 1.19/0.97      | v2_tdlat_3(sK0(X0,sK2))
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | ~ v2_pre_topc(X0)
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.19/0.97      inference(unflattening,[status(thm)],[c_992]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_12,plain,
% 1.19/0.97      ( ~ v2_tdlat_3(X0) | ~ l1_pre_topc(X0) | v2_pre_topc(X0) ),
% 1.19/0.97      inference(cnf_transformation,[],[f59]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_997,plain,
% 1.19/0.97      ( ~ l1_pre_topc(X0)
% 1.19/0.97      | v2_tdlat_3(sK0(X0,sK2))
% 1.19/0.97      | ~ v2_tdlat_3(X0)
% 1.19/0.97      | v2_struct_0(X0)
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.19/0.97      inference(global_propositional_subsumption,
% 1.19/0.97                [status(thm)],
% 1.19/0.97                [c_993,c_12]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_998,plain,
% 1.19/0.97      ( v2_struct_0(X0)
% 1.19/0.97      | ~ v2_tdlat_3(X0)
% 1.19/0.97      | v2_tdlat_3(sK0(X0,sK2))
% 1.19/0.97      | ~ l1_pre_topc(X0)
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.19/0.97      inference(renaming,[status(thm)],[c_997]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1666,plain,
% 1.19/0.97      ( v2_struct_0(X0_45)
% 1.19/0.97      | ~ v2_tdlat_3(X0_45)
% 1.19/0.97      | v2_tdlat_3(sK0(X0_45,sK2))
% 1.19/0.97      | ~ l1_pre_topc(X0_45)
% 1.19/0.97      | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.19/0.97      inference(subtyping,[status(esa)],[c_998]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1721,plain,
% 1.19/0.97      ( k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | v2_struct_0(X0_45) = iProver_top
% 1.19/0.97      | v2_tdlat_3(X0_45) != iProver_top
% 1.19/0.97      | v2_tdlat_3(sK0(X0_45,sK2)) = iProver_top
% 1.19/0.97      | l1_pre_topc(X0_45) != iProver_top ),
% 1.19/0.97      inference(predicate_to_equality,[status(thm)],[c_1666]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1723,plain,
% 1.19/0.97      ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.19/0.97      | v2_struct_0(sK1) = iProver_top
% 1.19/0.97      | v2_tdlat_3(sK0(sK1,sK2)) = iProver_top
% 1.19/0.97      | v2_tdlat_3(sK1) != iProver_top
% 1.19/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 1.19/0.97      inference(instantiation,[status(thm)],[c_1721]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1682,plain,( X0_45 = X0_45 ),theory(equality) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1705,plain,
% 1.19/0.97      ( sK1 = sK1 ),
% 1.19/0.97      inference(instantiation,[status(thm)],[c_1682]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1690,plain,
% 1.19/0.97      ( u1_struct_0(X0_45) = u1_struct_0(X1_45) | X0_45 != X1_45 ),
% 1.19/0.97      theory(equality) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_1698,plain,
% 1.19/0.97      ( u1_struct_0(sK1) = u1_struct_0(sK1) | sK1 != sK1 ),
% 1.19/0.97      inference(instantiation,[status(thm)],[c_1690]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_30,plain,
% 1.19/0.97      ( l1_pre_topc(sK1) = iProver_top ),
% 1.19/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_24,negated_conjecture,
% 1.19/0.97      ( v2_tdlat_3(sK1) ),
% 1.19/0.97      inference(cnf_transformation,[],[f68]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_29,plain,
% 1.19/0.97      ( v2_tdlat_3(sK1) = iProver_top ),
% 1.19/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_25,negated_conjecture,
% 1.19/0.97      ( v2_pre_topc(sK1) ),
% 1.19/0.97      inference(cnf_transformation,[],[f67]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_28,plain,
% 1.19/0.97      ( v2_pre_topc(sK1) = iProver_top ),
% 1.19/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(c_27,plain,
% 1.19/0.97      ( v2_struct_0(sK1) != iProver_top ),
% 1.19/0.97      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.19/0.97  
% 1.19/0.97  cnf(contradiction,plain,
% 1.19/0.97      ( $false ),
% 1.19/0.97      inference(minisat,
% 1.19/0.97                [status(thm)],
% 1.19/0.97                [c_2323,c_2277,c_2249,c_1738,c_1732,c_1730,c_1729,c_1726,
% 1.19/0.97                 c_1723,c_1705,c_1698,c_30,c_23,c_29,c_28,c_27,c_26]) ).
% 1.19/0.97  
% 1.19/0.97  
% 1.19/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 1.19/0.97  
% 1.19/0.97  ------                               Statistics
% 1.19/0.97  
% 1.19/0.97  ------ General
% 1.19/0.97  
% 1.19/0.97  abstr_ref_over_cycles:                  0
% 1.19/0.97  abstr_ref_under_cycles:                 0
% 1.19/0.97  gc_basic_clause_elim:                   0
% 1.19/0.97  forced_gc_time:                         0
% 1.19/0.97  parsing_time:                           0.008
% 1.19/0.97  unif_index_cands_time:                  0.
% 1.19/0.97  unif_index_add_time:                    0.
% 1.19/0.97  orderings_time:                         0.
% 1.19/0.97  out_proof_time:                         0.012
% 1.19/0.97  total_time:                             0.094
% 1.19/0.97  num_of_symbols:                         51
% 1.19/0.97  num_of_terms:                           741
% 1.19/0.97  
% 1.19/0.97  ------ Preprocessing
% 1.19/0.97  
% 1.19/0.97  num_of_splits:                          6
% 1.19/0.97  num_of_split_atoms:                     3
% 1.19/0.97  num_of_reused_defs:                     3
% 1.19/0.97  num_eq_ax_congr_red:                    6
% 1.19/0.97  num_of_sem_filtered_clauses:            1
% 1.19/0.97  num_of_subtypes:                        3
% 1.19/0.97  monotx_restored_types:                  0
% 1.19/0.97  sat_num_of_epr_types:                   0
% 1.19/0.97  sat_num_of_non_cyclic_types:            0
% 1.19/0.97  sat_guarded_non_collapsed_types:        0
% 1.19/0.97  num_pure_diseq_elim:                    0
% 1.19/0.97  simp_replaced_by:                       0
% 1.19/0.97  res_preprocessed:                       125
% 1.19/0.97  prep_upred:                             0
% 1.19/0.97  prep_unflattend:                        35
% 1.19/0.97  smt_new_axioms:                         0
% 1.19/0.97  pred_elim_cands:                        5
% 1.19/0.97  pred_elim:                              7
% 1.19/0.97  pred_elim_cl:                           8
% 1.19/0.97  pred_elim_cycles:                       12
% 1.19/0.97  merged_defs:                            2
% 1.19/0.97  merged_defs_ncl:                        0
% 1.19/0.97  bin_hyper_res:                          2
% 1.19/0.97  prep_cycles:                            5
% 1.19/0.97  pred_elim_time:                         0.023
% 1.19/0.97  splitting_time:                         0.
% 1.19/0.97  sem_filter_time:                        0.
% 1.19/0.97  monotx_time:                            0.
% 1.19/0.97  subtype_inf_time:                       0.
% 1.19/0.97  
% 1.19/0.97  ------ Problem properties
% 1.19/0.97  
% 1.19/0.97  clauses:                                22
% 1.19/0.97  conjectures:                            4
% 1.19/0.97  epr:                                    8
% 1.19/0.97  horn:                                   13
% 1.19/0.97  ground:                                 9
% 1.19/0.97  unary:                                  5
% 1.19/0.97  binary:                                 2
% 1.19/0.97  lits:                                   74
% 1.19/0.97  lits_eq:                                14
% 1.19/0.97  fd_pure:                                0
% 1.19/0.97  fd_pseudo:                              0
% 1.19/0.97  fd_cond:                                0
% 1.19/0.97  fd_pseudo_cond:                         0
% 1.19/0.97  ac_symbols:                             0
% 1.19/0.97  
% 1.19/0.97  ------ Propositional Solver
% 1.19/0.97  
% 1.19/0.97  prop_solver_calls:                      29
% 1.19/0.97  prop_fast_solver_calls:                 1190
% 1.19/0.97  smt_solver_calls:                       0
% 1.19/0.97  smt_fast_solver_calls:                  0
% 1.19/0.97  prop_num_of_clauses:                    330
% 1.19/0.97  prop_preprocess_simplified:             3217
% 1.19/0.97  prop_fo_subsumed:                       29
% 1.19/0.97  prop_solver_time:                       0.
% 1.19/0.97  smt_solver_time:                        0.
% 1.19/0.97  smt_fast_solver_time:                   0.
% 1.19/0.97  prop_fast_solver_time:                  0.
% 1.19/0.97  prop_unsat_core_time:                   0.
% 1.19/0.97  
% 1.19/0.97  ------ QBF
% 1.19/0.97  
% 1.19/0.97  qbf_q_res:                              0
% 1.19/0.97  qbf_num_tautologies:                    0
% 1.19/0.97  qbf_prep_cycles:                        0
% 1.19/0.97  
% 1.19/0.97  ------ BMC1
% 1.19/0.97  
% 1.19/0.97  bmc1_current_bound:                     -1
% 1.19/0.97  bmc1_last_solved_bound:                 -1
% 1.19/0.97  bmc1_unsat_core_size:                   -1
% 1.19/0.97  bmc1_unsat_core_parents_size:           -1
% 1.19/0.97  bmc1_merge_next_fun:                    0
% 1.19/0.97  bmc1_unsat_core_clauses_time:           0.
% 1.19/0.97  
% 1.19/0.97  ------ Instantiation
% 1.19/0.97  
% 1.19/0.97  inst_num_of_clauses:                    51
% 1.19/0.97  inst_num_in_passive:                    4
% 1.19/0.97  inst_num_in_active:                     46
% 1.19/0.97  inst_num_in_unprocessed:                0
% 1.19/0.97  inst_num_of_loops:                      56
% 1.19/0.97  inst_num_of_learning_restarts:          0
% 1.19/0.97  inst_num_moves_active_passive:          6
% 1.19/0.97  inst_lit_activity:                      0
% 1.19/0.97  inst_lit_activity_moves:                0
% 1.19/0.97  inst_num_tautologies:                   0
% 1.19/0.97  inst_num_prop_implied:                  0
% 1.19/0.97  inst_num_existing_simplified:           0
% 1.19/0.97  inst_num_eq_res_simplified:             0
% 1.19/0.97  inst_num_child_elim:                    0
% 1.19/0.97  inst_num_of_dismatching_blockings:      4
% 1.19/0.97  inst_num_of_non_proper_insts:           15
% 1.19/0.97  inst_num_of_duplicates:                 0
% 1.19/0.97  inst_inst_num_from_inst_to_res:         0
% 1.19/0.97  inst_dismatching_checking_time:         0.
% 1.19/0.97  
% 1.19/0.97  ------ Resolution
% 1.19/0.97  
% 1.19/0.97  res_num_of_clauses:                     0
% 1.19/0.97  res_num_in_passive:                     0
% 1.19/0.97  res_num_in_active:                      0
% 1.19/0.97  res_num_of_loops:                       130
% 1.19/0.97  res_forward_subset_subsumed:            1
% 1.19/0.97  res_backward_subset_subsumed:           0
% 1.19/0.97  res_forward_subsumed:                   2
% 1.19/0.97  res_backward_subsumed:                  1
% 1.19/0.97  res_forward_subsumption_resolution:     0
% 1.19/0.97  res_backward_subsumption_resolution:    0
% 1.19/0.97  res_clause_to_clause_subsumption:       114
% 1.19/0.97  res_orphan_elimination:                 0
% 1.19/0.97  res_tautology_del:                      20
% 1.19/0.97  res_num_eq_res_simplified:              4
% 1.19/0.97  res_num_sel_changes:                    0
% 1.19/0.97  res_moves_from_active_to_pass:          0
% 1.19/0.97  
% 1.19/0.97  ------ Superposition
% 1.19/0.97  
% 1.19/0.97  sup_time_total:                         0.
% 1.19/0.97  sup_time_generating:                    0.
% 1.19/0.97  sup_time_sim_full:                      0.
% 1.19/0.97  sup_time_sim_immed:                     0.
% 1.19/0.97  
% 1.19/0.97  sup_num_of_clauses:                     22
% 1.19/0.97  sup_num_in_active:                      10
% 1.19/0.97  sup_num_in_passive:                     12
% 1.19/0.97  sup_num_of_loops:                       10
% 1.19/0.97  sup_fw_superposition:                   2
% 1.19/0.97  sup_bw_superposition:                   0
% 1.19/0.97  sup_immediate_simplified:               2
% 1.19/0.97  sup_given_eliminated:                   0
% 1.19/0.97  comparisons_done:                       0
% 1.19/0.97  comparisons_avoided:                    0
% 1.19/0.97  
% 1.19/0.97  ------ Simplifications
% 1.19/0.97  
% 1.19/0.97  
% 1.19/0.97  sim_fw_subset_subsumed:                 2
% 1.19/0.97  sim_bw_subset_subsumed:                 0
% 1.19/0.97  sim_fw_subsumed:                        0
% 1.19/0.97  sim_bw_subsumed:                        0
% 1.19/0.97  sim_fw_subsumption_res:                 0
% 1.19/0.97  sim_bw_subsumption_res:                 0
% 1.19/0.97  sim_tautology_del:                      0
% 1.19/0.97  sim_eq_tautology_del:                   0
% 1.19/0.97  sim_eq_res_simp:                        0
% 1.19/0.97  sim_fw_demodulated:                     0
% 1.19/0.97  sim_bw_demodulated:                     0
% 1.19/0.97  sim_light_normalised:                   0
% 1.19/0.97  sim_joinable_taut:                      0
% 1.19/0.97  sim_joinable_simp:                      0
% 1.19/0.97  sim_ac_normalised:                      0
% 1.19/0.97  sim_smt_subsumption:                    0
% 1.19/0.97  
%------------------------------------------------------------------------------
