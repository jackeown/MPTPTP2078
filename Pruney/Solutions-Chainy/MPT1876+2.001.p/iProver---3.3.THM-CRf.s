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
% DateTime   : Thu Dec  3 12:26:46 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 743 expanded)
%              Number of clauses        :  102 ( 180 expanded)
%              Number of leaves         :   17 ( 168 expanded)
%              Depth                    :   25
%              Number of atoms          :  906 (5672 expanded)
%              Number of equality atoms :  148 ( 278 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   20 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f38,f40,f39])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
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

fof(f13,plain,(
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
    inference(pure_predicate_removal,[],[f9])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK0(X0,X1)) = X1
        & m1_pre_topc(sK0(X0,X1),X0)
        & ~ v2_struct_0(sK0(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK0(X0,X1)) = X1
            & m1_pre_topc(sK0(X0,X1),X0)
            & ~ v2_struct_0(sK0(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f34])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,
    ( ~ v1_zfmisc_1(sK2)
    | ~ v2_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,
    ( v1_zfmisc_1(sK2)
    | v2_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) )
           => ( v7_struct_0(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_tdlat_3(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_tdlat_3(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v7_struct_0(X1)
      | ~ v1_tdlat_3(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f22,plain,(
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
    inference(flattening,[],[f22])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_pre_topc(X1)
      | ~ v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v2_tdlat_3(X1)
           => v2_pre_topc(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f59,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(sK0(X1,X0),X1)
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_19,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_387,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(sK0(X1,X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_388,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_pre_topc(sK0(X0,sK2),X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_720,plain,
    ( m1_pre_topc(sK0(X0,sK2),X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_388])).

cnf(c_14,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_287,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_3])).

cnf(c_16,negated_conjecture,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_163,plain,
    ( ~ v1_zfmisc_1(sK2)
    | ~ v2_tex_2(sK2,sK1) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_164,plain,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ v1_zfmisc_1(sK2) ),
    inference(renaming,[status(thm)],[c_163])).

cnf(c_325,plain,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_287,c_164])).

cnf(c_609,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v7_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X2) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_325])).

cnf(c_610,plain,
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
    inference(unflattening,[status(thm)],[c_609])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_614,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v7_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(X0,sK1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X1) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_610,c_23,c_20])).

cnf(c_615,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(X0,sK1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X1) != sK2 ),
    inference(renaming,[status(thm)],[c_614])).

cnf(c_785,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X1) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_615])).

cnf(c_1277,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
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
    inference(resolution_lifted,[status(thm)],[c_720,c_785])).

cnf(c_1278,plain,
    ( ~ v1_tdlat_3(sK0(sK1,sK2))
    | v2_struct_0(sK0(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0) != sK2
    | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_1277])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK0(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK0(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_370,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK0(X0,sK2))
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_372,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_struct_0(sK0(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK0(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_405,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(sK0(X1,X0)) = X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_406,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(sK0(X0,sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_408,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(sK0(sK1,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_406])).

cnf(c_1282,plain,
    ( u1_struct_0(X0) != sK2
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | ~ v1_tdlat_3(sK0(sK1,sK2))
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1278,c_23,c_20,c_18,c_372,c_408])).

cnf(c_1283,plain,
    ( ~ v1_tdlat_3(sK0(sK1,sK2))
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0) != sK2 ),
    inference(renaming,[status(thm)],[c_1282])).

cnf(c_1713,plain,
    ( ~ v1_tdlat_3(sK0(sK1,sK2))
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_1283])).

cnf(c_2114,plain,
    ( ~ v1_tdlat_3(sK0(sK1,sK2))
    | ~ v7_struct_0(X0_45)
    | ~ l1_pre_topc(X0_45)
    | u1_struct_0(X0_45) != sK2 ),
    inference(subtyping,[status(esa)],[c_1713])).

cnf(c_2790,plain,
    ( ~ v1_tdlat_3(sK0(sK1,sK2))
    | ~ v7_struct_0(sK0(X0_45,sK2))
    | ~ l1_pre_topc(sK0(X0_45,sK2))
    | u1_struct_0(sK0(X0_45,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_2114])).

cnf(c_2792,plain,
    ( ~ v1_tdlat_3(sK0(sK1,sK2))
    | ~ v7_struct_0(sK0(sK1,sK2))
    | ~ l1_pre_topc(sK0(sK1,sK2))
    | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_2790])).

cnf(c_15,plain,
    ( ~ v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2,plain,
    ( v7_struct_0(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_301,plain,
    ( v7_struct_0(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_0,c_2])).

cnf(c_17,negated_conjecture,
    ( v2_tex_2(sK2,sK1)
    | v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_165,plain,
    ( v1_zfmisc_1(sK2)
    | v2_tex_2(sK2,sK1) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_166,plain,
    ( v2_tex_2(sK2,sK1)
    | v1_zfmisc_1(sK2) ),
    inference(renaming,[status(thm)],[c_165])).

cnf(c_342,plain,
    ( v2_tex_2(sK2,sK1)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_301,c_166])).

cnf(c_643,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v7_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X2) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_342])).

cnf(c_644,plain,
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
    inference(unflattening,[status(thm)],[c_643])).

cnf(c_648,plain,
    ( ~ l1_pre_topc(X1)
    | v7_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(X0,sK1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X1) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_644,c_23,c_20])).

cnf(c_649,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(X0,sK1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X1) != sK2 ),
    inference(renaming,[status(thm)],[c_648])).

cnf(c_756,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0) != sK2
    | u1_struct_0(X1) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_649])).

cnf(c_1304,plain,
    ( v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
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
    inference(resolution_lifted,[status(thm)],[c_720,c_756])).

cnf(c_1305,plain,
    ( v1_tdlat_3(sK0(sK1,sK2))
    | v2_struct_0(sK0(sK1,sK2))
    | v2_struct_0(sK1)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0) != sK2
    | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_1304])).

cnf(c_1309,plain,
    ( u1_struct_0(X0) != sK2
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | v1_tdlat_3(sK0(sK1,sK2))
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1305,c_23,c_20,c_18,c_372,c_408])).

cnf(c_1310,plain,
    ( v1_tdlat_3(sK0(sK1,sK2))
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0) != sK2 ),
    inference(renaming,[status(thm)],[c_1309])).

cnf(c_1709,plain,
    ( v1_tdlat_3(sK0(sK1,sK2))
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_1310])).

cnf(c_2115,plain,
    ( v1_tdlat_3(sK0(sK1,sK2))
    | v7_struct_0(X0_45)
    | ~ l1_pre_topc(X0_45)
    | u1_struct_0(X0_45) != sK2 ),
    inference(subtyping,[status(esa)],[c_1709])).

cnf(c_2728,plain,
    ( v1_tdlat_3(sK0(sK1,sK2))
    | v7_struct_0(sK0(X0_45,sK2))
    | ~ l1_pre_topc(sK0(X0_45,sK2))
    | u1_struct_0(sK0(X0_45,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_2115])).

cnf(c_2730,plain,
    ( v1_tdlat_3(sK0(sK1,sK2))
    | v7_struct_0(sK0(sK1,sK2))
    | ~ l1_pre_topc(sK0(sK1,sK2))
    | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_2728])).

cnf(c_2141,plain,
    ( k1_zfmisc_1(X0_46) = k1_zfmisc_1(X1_46)
    | X0_46 != X1_46 ),
    theory(equality)).

cnf(c_2700,plain,
    ( k1_zfmisc_1(u1_struct_0(X0_45)) = k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(X0_45) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2141])).

cnf(c_2701,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2700])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1154,plain,
    ( ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v7_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | X2 != X1
    | sK0(X2,sK2) != X0
    | k1_zfmisc_1(u1_struct_0(X2)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_720])).

cnf(c_1155,plain,
    ( ~ v1_tdlat_3(sK0(X0,sK2))
    | v2_struct_0(X0)
    | v2_struct_0(sK0(X0,sK2))
    | ~ v2_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | v7_struct_0(sK0(X0,sK2))
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1154])).

cnf(c_738,plain,
    ( v2_struct_0(X0)
    | ~ v2_struct_0(sK0(X0,sK2))
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_370])).

cnf(c_1724,plain,
    ( v2_struct_0(X0)
    | ~ v2_struct_0(sK0(X0,sK2))
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_738])).

cnf(c_1792,plain,
    ( v2_struct_0(X0)
    | ~ v1_tdlat_3(sK0(X0,sK2))
    | ~ v2_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | v7_struct_0(sK0(X0,sK2))
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1155,c_1724])).

cnf(c_1793,plain,
    ( ~ v1_tdlat_3(sK0(X0,sK2))
    | v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | ~ v2_pre_topc(X0)
    | v7_struct_0(sK0(X0,sK2))
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_1792])).

cnf(c_2109,plain,
    ( ~ v1_tdlat_3(sK0(X0_45,sK2))
    | v2_struct_0(X0_45)
    | ~ v2_tdlat_3(X0_45)
    | ~ v2_pre_topc(X0_45)
    | v7_struct_0(sK0(X0_45,sK2))
    | ~ l1_pre_topc(X0_45)
    | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_1793])).

cnf(c_2194,plain,
    ( ~ v1_tdlat_3(sK0(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ v2_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v7_struct_0(sK0(sK1,sK2))
    | ~ l1_pre_topc(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2109])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1184,plain,
    ( v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X0)
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | X2 != X1
    | sK0(X2,sK2) != X0
    | k1_zfmisc_1(u1_struct_0(X2)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_720])).

cnf(c_1185,plain,
    ( v1_tdlat_3(sK0(X0,sK2))
    | v2_struct_0(X0)
    | v2_struct_0(sK0(X0,sK2))
    | ~ v2_pre_topc(sK0(X0,sK2))
    | ~ v7_struct_0(sK0(X0,sK2))
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1184])).

cnf(c_1776,plain,
    ( v2_struct_0(X0)
    | v1_tdlat_3(sK0(X0,sK2))
    | ~ v2_pre_topc(sK0(X0,sK2))
    | ~ v7_struct_0(sK0(X0,sK2))
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1185,c_1724])).

cnf(c_1777,plain,
    ( v1_tdlat_3(sK0(X0,sK2))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(sK0(X0,sK2))
    | ~ v7_struct_0(sK0(X0,sK2))
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_1776])).

cnf(c_2111,plain,
    ( v1_tdlat_3(sK0(X0_45,sK2))
    | v2_struct_0(X0_45)
    | ~ v2_pre_topc(sK0(X0_45,sK2))
    | ~ v7_struct_0(sK0(X0_45,sK2))
    | ~ l1_pre_topc(X0_45)
    | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_1777])).

cnf(c_2188,plain,
    ( v1_tdlat_3(sK0(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK0(sK1,sK2))
    | ~ v7_struct_0(sK0(sK1,sK2))
    | ~ l1_pre_topc(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2111])).

cnf(c_702,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK0(X0,sK2)) = sK2
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_406])).

cnf(c_1728,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK0(X0,sK2)) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_702])).

cnf(c_2112,plain,
    ( v2_struct_0(X0_45)
    | ~ l1_pre_topc(X0_45)
    | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK0(X0_45,sK2)) = sK2 ),
    inference(subtyping,[status(esa)],[c_1728])).

cnf(c_2185,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | u1_struct_0(sK0(sK1,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_2112])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1259,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(X2)
    | X0 != X1
    | sK0(X0,sK2) != X2
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_720])).

cnf(c_1260,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK0(X0,sK2))
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1259])).

cnf(c_2116,plain,
    ( v2_struct_0(X0_45)
    | ~ l1_pre_topc(X0_45)
    | l1_pre_topc(sK0(X0_45,sK2))
    | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_1260])).

cnf(c_2173,plain,
    ( v2_struct_0(sK1)
    | l1_pre_topc(sK0(sK1,sK2))
    | ~ l1_pre_topc(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2116])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X0)
    | v2_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1238,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X2)
    | v2_pre_topc(X2)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | X1 != X0
    | sK0(X1,sK2) != X2
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_720])).

cnf(c_1239,plain,
    ( v2_struct_0(X0)
    | ~ v2_tdlat_3(sK0(X0,sK2))
    | v2_pre_topc(sK0(X0,sK2))
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1238])).

cnf(c_2117,plain,
    ( v2_struct_0(X0_45)
    | ~ v2_tdlat_3(sK0(X0_45,sK2))
    | v2_pre_topc(sK0(X0_45,sK2))
    | ~ l1_pre_topc(X0_45)
    | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_1239])).

cnf(c_2170,plain,
    ( v2_struct_0(sK1)
    | ~ v2_tdlat_3(sK0(sK1,sK2))
    | v2_pre_topc(sK0(sK1,sK2))
    | ~ l1_pre_topc(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2117])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | v2_tdlat_3(X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1130,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X0)
    | v2_tdlat_3(X2)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | X1 != X0
    | sK0(X1,sK2) != X2
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_720])).

cnf(c_1131,plain,
    ( v2_struct_0(X0)
    | ~ v2_tdlat_3(X0)
    | v2_tdlat_3(sK0(X0,sK2))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1130])).

cnf(c_2118,plain,
    ( v2_struct_0(X0_45)
    | ~ v2_tdlat_3(X0_45)
    | v2_tdlat_3(sK0(X0_45,sK2))
    | ~ v2_pre_topc(X0_45)
    | ~ l1_pre_topc(X0_45)
    | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_1131])).

cnf(c_2167,plain,
    ( v2_struct_0(sK1)
    | v2_tdlat_3(sK0(sK1,sK2))
    | ~ v2_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2118])).

cnf(c_2128,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_2152,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_2128])).

cnf(c_2134,plain,
    ( u1_struct_0(X0_45) = u1_struct_0(X1_45)
    | X0_45 != X1_45 ),
    theory(equality)).

cnf(c_2143,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2134])).

cnf(c_21,negated_conjecture,
    ( v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2792,c_2730,c_2701,c_2194,c_2188,c_2185,c_2173,c_2170,c_2167,c_2152,c_2143,c_20,c_21,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:14:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.55/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.01  
% 1.55/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.55/1.01  
% 1.55/1.01  ------  iProver source info
% 1.55/1.01  
% 1.55/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.55/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.55/1.01  git: non_committed_changes: false
% 1.55/1.01  git: last_make_outside_of_git: false
% 1.55/1.01  
% 1.55/1.01  ------ 
% 1.55/1.01  
% 1.55/1.01  ------ Input Options
% 1.55/1.01  
% 1.55/1.01  --out_options                           all
% 1.55/1.01  --tptp_safe_out                         true
% 1.55/1.01  --problem_path                          ""
% 1.55/1.01  --include_path                          ""
% 1.55/1.01  --clausifier                            res/vclausify_rel
% 1.55/1.01  --clausifier_options                    --mode clausify
% 1.55/1.01  --stdin                                 false
% 1.55/1.01  --stats_out                             all
% 1.55/1.01  
% 1.55/1.01  ------ General Options
% 1.55/1.01  
% 1.55/1.01  --fof                                   false
% 1.55/1.01  --time_out_real                         305.
% 1.55/1.01  --time_out_virtual                      -1.
% 1.55/1.01  --symbol_type_check                     false
% 1.55/1.01  --clausify_out                          false
% 1.55/1.01  --sig_cnt_out                           false
% 1.55/1.01  --trig_cnt_out                          false
% 1.55/1.01  --trig_cnt_out_tolerance                1.
% 1.55/1.01  --trig_cnt_out_sk_spl                   false
% 1.55/1.01  --abstr_cl_out                          false
% 1.55/1.01  
% 1.55/1.01  ------ Global Options
% 1.55/1.01  
% 1.55/1.01  --schedule                              default
% 1.55/1.01  --add_important_lit                     false
% 1.55/1.01  --prop_solver_per_cl                    1000
% 1.55/1.01  --min_unsat_core                        false
% 1.55/1.01  --soft_assumptions                      false
% 1.55/1.01  --soft_lemma_size                       3
% 1.55/1.01  --prop_impl_unit_size                   0
% 1.55/1.01  --prop_impl_unit                        []
% 1.55/1.01  --share_sel_clauses                     true
% 1.55/1.01  --reset_solvers                         false
% 1.55/1.01  --bc_imp_inh                            [conj_cone]
% 1.55/1.01  --conj_cone_tolerance                   3.
% 1.55/1.01  --extra_neg_conj                        none
% 1.55/1.01  --large_theory_mode                     true
% 1.55/1.01  --prolific_symb_bound                   200
% 1.55/1.01  --lt_threshold                          2000
% 1.55/1.01  --clause_weak_htbl                      true
% 1.55/1.01  --gc_record_bc_elim                     false
% 1.55/1.01  
% 1.55/1.01  ------ Preprocessing Options
% 1.55/1.01  
% 1.55/1.01  --preprocessing_flag                    true
% 1.55/1.01  --time_out_prep_mult                    0.1
% 1.55/1.01  --splitting_mode                        input
% 1.55/1.01  --splitting_grd                         true
% 1.55/1.01  --splitting_cvd                         false
% 1.55/1.01  --splitting_cvd_svl                     false
% 1.55/1.01  --splitting_nvd                         32
% 1.55/1.01  --sub_typing                            true
% 1.55/1.01  --prep_gs_sim                           true
% 1.55/1.01  --prep_unflatten                        true
% 1.55/1.01  --prep_res_sim                          true
% 1.55/1.01  --prep_upred                            true
% 1.55/1.01  --prep_sem_filter                       exhaustive
% 1.55/1.01  --prep_sem_filter_out                   false
% 1.55/1.01  --pred_elim                             true
% 1.55/1.01  --res_sim_input                         true
% 1.55/1.01  --eq_ax_congr_red                       true
% 1.55/1.01  --pure_diseq_elim                       true
% 1.55/1.01  --brand_transform                       false
% 1.55/1.01  --non_eq_to_eq                          false
% 1.55/1.01  --prep_def_merge                        true
% 1.55/1.01  --prep_def_merge_prop_impl              false
% 1.55/1.01  --prep_def_merge_mbd                    true
% 1.55/1.01  --prep_def_merge_tr_red                 false
% 1.55/1.01  --prep_def_merge_tr_cl                  false
% 1.55/1.01  --smt_preprocessing                     true
% 1.55/1.01  --smt_ac_axioms                         fast
% 1.55/1.01  --preprocessed_out                      false
% 1.55/1.01  --preprocessed_stats                    false
% 1.55/1.01  
% 1.55/1.01  ------ Abstraction refinement Options
% 1.55/1.01  
% 1.55/1.01  --abstr_ref                             []
% 1.55/1.01  --abstr_ref_prep                        false
% 1.55/1.01  --abstr_ref_until_sat                   false
% 1.55/1.01  --abstr_ref_sig_restrict                funpre
% 1.55/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.55/1.01  --abstr_ref_under                       []
% 1.55/1.01  
% 1.55/1.01  ------ SAT Options
% 1.55/1.01  
% 1.55/1.01  --sat_mode                              false
% 1.55/1.01  --sat_fm_restart_options                ""
% 1.55/1.01  --sat_gr_def                            false
% 1.55/1.01  --sat_epr_types                         true
% 1.55/1.01  --sat_non_cyclic_types                  false
% 1.55/1.01  --sat_finite_models                     false
% 1.55/1.01  --sat_fm_lemmas                         false
% 1.55/1.01  --sat_fm_prep                           false
% 1.55/1.01  --sat_fm_uc_incr                        true
% 1.55/1.01  --sat_out_model                         small
% 1.55/1.01  --sat_out_clauses                       false
% 1.55/1.01  
% 1.55/1.01  ------ QBF Options
% 1.55/1.01  
% 1.55/1.01  --qbf_mode                              false
% 1.55/1.01  --qbf_elim_univ                         false
% 1.55/1.01  --qbf_dom_inst                          none
% 1.55/1.01  --qbf_dom_pre_inst                      false
% 1.55/1.01  --qbf_sk_in                             false
% 1.55/1.01  --qbf_pred_elim                         true
% 1.55/1.01  --qbf_split                             512
% 1.55/1.01  
% 1.55/1.01  ------ BMC1 Options
% 1.55/1.01  
% 1.55/1.01  --bmc1_incremental                      false
% 1.55/1.01  --bmc1_axioms                           reachable_all
% 1.55/1.01  --bmc1_min_bound                        0
% 1.55/1.01  --bmc1_max_bound                        -1
% 1.55/1.01  --bmc1_max_bound_default                -1
% 1.55/1.01  --bmc1_symbol_reachability              true
% 1.55/1.01  --bmc1_property_lemmas                  false
% 1.55/1.01  --bmc1_k_induction                      false
% 1.55/1.01  --bmc1_non_equiv_states                 false
% 1.55/1.01  --bmc1_deadlock                         false
% 1.55/1.01  --bmc1_ucm                              false
% 1.55/1.01  --bmc1_add_unsat_core                   none
% 1.55/1.01  --bmc1_unsat_core_children              false
% 1.55/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.55/1.01  --bmc1_out_stat                         full
% 1.55/1.01  --bmc1_ground_init                      false
% 1.55/1.01  --bmc1_pre_inst_next_state              false
% 1.55/1.01  --bmc1_pre_inst_state                   false
% 1.55/1.01  --bmc1_pre_inst_reach_state             false
% 1.55/1.01  --bmc1_out_unsat_core                   false
% 1.55/1.01  --bmc1_aig_witness_out                  false
% 1.55/1.01  --bmc1_verbose                          false
% 1.55/1.01  --bmc1_dump_clauses_tptp                false
% 1.55/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.55/1.01  --bmc1_dump_file                        -
% 1.55/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.55/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.55/1.01  --bmc1_ucm_extend_mode                  1
% 1.55/1.01  --bmc1_ucm_init_mode                    2
% 1.55/1.01  --bmc1_ucm_cone_mode                    none
% 1.55/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.55/1.01  --bmc1_ucm_relax_model                  4
% 1.55/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.55/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.55/1.01  --bmc1_ucm_layered_model                none
% 1.55/1.01  --bmc1_ucm_max_lemma_size               10
% 1.55/1.01  
% 1.55/1.01  ------ AIG Options
% 1.55/1.01  
% 1.55/1.01  --aig_mode                              false
% 1.55/1.01  
% 1.55/1.01  ------ Instantiation Options
% 1.55/1.01  
% 1.55/1.01  --instantiation_flag                    true
% 1.55/1.01  --inst_sos_flag                         false
% 1.55/1.01  --inst_sos_phase                        true
% 1.55/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.55/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.55/1.01  --inst_lit_sel_side                     num_symb
% 1.55/1.01  --inst_solver_per_active                1400
% 1.55/1.01  --inst_solver_calls_frac                1.
% 1.55/1.01  --inst_passive_queue_type               priority_queues
% 1.55/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.55/1.01  --inst_passive_queues_freq              [25;2]
% 1.55/1.01  --inst_dismatching                      true
% 1.55/1.01  --inst_eager_unprocessed_to_passive     true
% 1.55/1.01  --inst_prop_sim_given                   true
% 1.55/1.01  --inst_prop_sim_new                     false
% 1.55/1.01  --inst_subs_new                         false
% 1.55/1.01  --inst_eq_res_simp                      false
% 1.55/1.01  --inst_subs_given                       false
% 1.55/1.01  --inst_orphan_elimination               true
% 1.55/1.01  --inst_learning_loop_flag               true
% 1.55/1.01  --inst_learning_start                   3000
% 1.55/1.01  --inst_learning_factor                  2
% 1.55/1.01  --inst_start_prop_sim_after_learn       3
% 1.55/1.01  --inst_sel_renew                        solver
% 1.55/1.01  --inst_lit_activity_flag                true
% 1.55/1.01  --inst_restr_to_given                   false
% 1.55/1.01  --inst_activity_threshold               500
% 1.55/1.01  --inst_out_proof                        true
% 1.55/1.01  
% 1.55/1.01  ------ Resolution Options
% 1.55/1.01  
% 1.55/1.01  --resolution_flag                       true
% 1.55/1.01  --res_lit_sel                           adaptive
% 1.55/1.01  --res_lit_sel_side                      none
% 1.55/1.01  --res_ordering                          kbo
% 1.55/1.01  --res_to_prop_solver                    active
% 1.55/1.01  --res_prop_simpl_new                    false
% 1.55/1.01  --res_prop_simpl_given                  true
% 1.55/1.01  --res_passive_queue_type                priority_queues
% 1.55/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.55/1.01  --res_passive_queues_freq               [15;5]
% 1.55/1.01  --res_forward_subs                      full
% 1.55/1.01  --res_backward_subs                     full
% 1.55/1.01  --res_forward_subs_resolution           true
% 1.55/1.01  --res_backward_subs_resolution          true
% 1.55/1.01  --res_orphan_elimination                true
% 1.55/1.01  --res_time_limit                        2.
% 1.55/1.01  --res_out_proof                         true
% 1.55/1.01  
% 1.55/1.01  ------ Superposition Options
% 1.55/1.01  
% 1.55/1.01  --superposition_flag                    true
% 1.55/1.01  --sup_passive_queue_type                priority_queues
% 1.55/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.55/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.55/1.01  --demod_completeness_check              fast
% 1.55/1.01  --demod_use_ground                      true
% 1.55/1.01  --sup_to_prop_solver                    passive
% 1.55/1.01  --sup_prop_simpl_new                    true
% 1.55/1.01  --sup_prop_simpl_given                  true
% 1.55/1.01  --sup_fun_splitting                     false
% 1.55/1.01  --sup_smt_interval                      50000
% 1.55/1.01  
% 1.55/1.01  ------ Superposition Simplification Setup
% 1.55/1.01  
% 1.55/1.01  --sup_indices_passive                   []
% 1.55/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.55/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.01  --sup_full_bw                           [BwDemod]
% 1.55/1.01  --sup_immed_triv                        [TrivRules]
% 1.55/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.55/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.01  --sup_immed_bw_main                     []
% 1.55/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.55/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.55/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.55/1.01  
% 1.55/1.01  ------ Combination Options
% 1.55/1.01  
% 1.55/1.01  --comb_res_mult                         3
% 1.55/1.01  --comb_sup_mult                         2
% 1.55/1.01  --comb_inst_mult                        10
% 1.55/1.01  
% 1.55/1.01  ------ Debug Options
% 1.55/1.01  
% 1.55/1.01  --dbg_backtrace                         false
% 1.55/1.01  --dbg_dump_prop_clauses                 false
% 1.55/1.01  --dbg_dump_prop_clauses_file            -
% 1.55/1.01  --dbg_out_stat                          false
% 1.55/1.01  ------ Parsing...
% 1.55/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.55/1.01  
% 1.55/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.55/1.01  
% 1.55/1.01  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.55/1.01  
% 1.55/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.55/1.01  ------ Proving...
% 1.55/1.01  ------ Problem Properties 
% 1.55/1.01  
% 1.55/1.01  
% 1.55/1.01  clauses                                 17
% 1.55/1.01  conjectures                             4
% 1.55/1.01  EPR                                     5
% 1.55/1.01  Horn                                    8
% 1.55/1.01  unary                                   4
% 1.55/1.01  binary                                  1
% 1.55/1.01  lits                                    64
% 1.55/1.01  lits eq                                 13
% 1.55/1.01  fd_pure                                 0
% 1.55/1.01  fd_pseudo                               0
% 1.55/1.01  fd_cond                                 0
% 1.55/1.01  fd_pseudo_cond                          0
% 1.55/1.01  AC symbols                              0
% 1.55/1.01  
% 1.55/1.01  ------ Schedule dynamic 5 is on 
% 1.55/1.01  
% 1.55/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.55/1.01  
% 1.55/1.01  
% 1.55/1.01  ------ 
% 1.55/1.01  Current options:
% 1.55/1.01  ------ 
% 1.55/1.01  
% 1.55/1.01  ------ Input Options
% 1.55/1.01  
% 1.55/1.01  --out_options                           all
% 1.55/1.01  --tptp_safe_out                         true
% 1.55/1.01  --problem_path                          ""
% 1.55/1.01  --include_path                          ""
% 1.55/1.01  --clausifier                            res/vclausify_rel
% 1.55/1.01  --clausifier_options                    --mode clausify
% 1.55/1.01  --stdin                                 false
% 1.55/1.01  --stats_out                             all
% 1.55/1.01  
% 1.55/1.01  ------ General Options
% 1.55/1.01  
% 1.55/1.01  --fof                                   false
% 1.55/1.01  --time_out_real                         305.
% 1.55/1.01  --time_out_virtual                      -1.
% 1.55/1.01  --symbol_type_check                     false
% 1.55/1.01  --clausify_out                          false
% 1.55/1.01  --sig_cnt_out                           false
% 1.55/1.01  --trig_cnt_out                          false
% 1.55/1.01  --trig_cnt_out_tolerance                1.
% 1.55/1.01  --trig_cnt_out_sk_spl                   false
% 1.55/1.01  --abstr_cl_out                          false
% 1.55/1.01  
% 1.55/1.01  ------ Global Options
% 1.55/1.01  
% 1.55/1.01  --schedule                              default
% 1.55/1.01  --add_important_lit                     false
% 1.55/1.01  --prop_solver_per_cl                    1000
% 1.55/1.01  --min_unsat_core                        false
% 1.55/1.01  --soft_assumptions                      false
% 1.55/1.01  --soft_lemma_size                       3
% 1.55/1.01  --prop_impl_unit_size                   0
% 1.55/1.01  --prop_impl_unit                        []
% 1.55/1.01  --share_sel_clauses                     true
% 1.55/1.01  --reset_solvers                         false
% 1.55/1.01  --bc_imp_inh                            [conj_cone]
% 1.55/1.01  --conj_cone_tolerance                   3.
% 1.55/1.01  --extra_neg_conj                        none
% 1.55/1.01  --large_theory_mode                     true
% 1.55/1.01  --prolific_symb_bound                   200
% 1.55/1.01  --lt_threshold                          2000
% 1.55/1.01  --clause_weak_htbl                      true
% 1.55/1.01  --gc_record_bc_elim                     false
% 1.55/1.01  
% 1.55/1.01  ------ Preprocessing Options
% 1.55/1.01  
% 1.55/1.01  --preprocessing_flag                    true
% 1.55/1.01  --time_out_prep_mult                    0.1
% 1.55/1.01  --splitting_mode                        input
% 1.55/1.01  --splitting_grd                         true
% 1.55/1.01  --splitting_cvd                         false
% 1.55/1.01  --splitting_cvd_svl                     false
% 1.55/1.01  --splitting_nvd                         32
% 1.55/1.01  --sub_typing                            true
% 1.55/1.01  --prep_gs_sim                           true
% 1.55/1.01  --prep_unflatten                        true
% 1.55/1.01  --prep_res_sim                          true
% 1.55/1.01  --prep_upred                            true
% 1.55/1.01  --prep_sem_filter                       exhaustive
% 1.55/1.01  --prep_sem_filter_out                   false
% 1.55/1.01  --pred_elim                             true
% 1.55/1.01  --res_sim_input                         true
% 1.55/1.01  --eq_ax_congr_red                       true
% 1.55/1.01  --pure_diseq_elim                       true
% 1.55/1.01  --brand_transform                       false
% 1.55/1.01  --non_eq_to_eq                          false
% 1.55/1.01  --prep_def_merge                        true
% 1.55/1.01  --prep_def_merge_prop_impl              false
% 1.55/1.01  --prep_def_merge_mbd                    true
% 1.55/1.01  --prep_def_merge_tr_red                 false
% 1.55/1.01  --prep_def_merge_tr_cl                  false
% 1.55/1.01  --smt_preprocessing                     true
% 1.55/1.01  --smt_ac_axioms                         fast
% 1.55/1.01  --preprocessed_out                      false
% 1.55/1.01  --preprocessed_stats                    false
% 1.55/1.01  
% 1.55/1.01  ------ Abstraction refinement Options
% 1.55/1.01  
% 1.55/1.01  --abstr_ref                             []
% 1.55/1.01  --abstr_ref_prep                        false
% 1.55/1.01  --abstr_ref_until_sat                   false
% 1.55/1.01  --abstr_ref_sig_restrict                funpre
% 1.55/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.55/1.01  --abstr_ref_under                       []
% 1.55/1.01  
% 1.55/1.01  ------ SAT Options
% 1.55/1.01  
% 1.55/1.01  --sat_mode                              false
% 1.55/1.01  --sat_fm_restart_options                ""
% 1.55/1.01  --sat_gr_def                            false
% 1.55/1.01  --sat_epr_types                         true
% 1.55/1.01  --sat_non_cyclic_types                  false
% 1.55/1.01  --sat_finite_models                     false
% 1.55/1.01  --sat_fm_lemmas                         false
% 1.55/1.01  --sat_fm_prep                           false
% 1.55/1.01  --sat_fm_uc_incr                        true
% 1.55/1.01  --sat_out_model                         small
% 1.55/1.01  --sat_out_clauses                       false
% 1.55/1.01  
% 1.55/1.01  ------ QBF Options
% 1.55/1.01  
% 1.55/1.01  --qbf_mode                              false
% 1.55/1.01  --qbf_elim_univ                         false
% 1.55/1.01  --qbf_dom_inst                          none
% 1.55/1.01  --qbf_dom_pre_inst                      false
% 1.55/1.01  --qbf_sk_in                             false
% 1.55/1.01  --qbf_pred_elim                         true
% 1.55/1.01  --qbf_split                             512
% 1.55/1.01  
% 1.55/1.01  ------ BMC1 Options
% 1.55/1.01  
% 1.55/1.01  --bmc1_incremental                      false
% 1.55/1.01  --bmc1_axioms                           reachable_all
% 1.55/1.01  --bmc1_min_bound                        0
% 1.55/1.01  --bmc1_max_bound                        -1
% 1.55/1.01  --bmc1_max_bound_default                -1
% 1.55/1.01  --bmc1_symbol_reachability              true
% 1.55/1.01  --bmc1_property_lemmas                  false
% 1.55/1.01  --bmc1_k_induction                      false
% 1.55/1.01  --bmc1_non_equiv_states                 false
% 1.55/1.01  --bmc1_deadlock                         false
% 1.55/1.01  --bmc1_ucm                              false
% 1.55/1.01  --bmc1_add_unsat_core                   none
% 1.55/1.01  --bmc1_unsat_core_children              false
% 1.55/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.55/1.01  --bmc1_out_stat                         full
% 1.55/1.01  --bmc1_ground_init                      false
% 1.55/1.01  --bmc1_pre_inst_next_state              false
% 1.55/1.01  --bmc1_pre_inst_state                   false
% 1.55/1.01  --bmc1_pre_inst_reach_state             false
% 1.55/1.01  --bmc1_out_unsat_core                   false
% 1.55/1.01  --bmc1_aig_witness_out                  false
% 1.55/1.01  --bmc1_verbose                          false
% 1.55/1.01  --bmc1_dump_clauses_tptp                false
% 1.55/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.55/1.01  --bmc1_dump_file                        -
% 1.55/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.55/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.55/1.01  --bmc1_ucm_extend_mode                  1
% 1.55/1.01  --bmc1_ucm_init_mode                    2
% 1.55/1.01  --bmc1_ucm_cone_mode                    none
% 1.55/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.55/1.01  --bmc1_ucm_relax_model                  4
% 1.55/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.55/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.55/1.01  --bmc1_ucm_layered_model                none
% 1.55/1.01  --bmc1_ucm_max_lemma_size               10
% 1.55/1.01  
% 1.55/1.01  ------ AIG Options
% 1.55/1.01  
% 1.55/1.01  --aig_mode                              false
% 1.55/1.01  
% 1.55/1.01  ------ Instantiation Options
% 1.55/1.01  
% 1.55/1.01  --instantiation_flag                    true
% 1.55/1.01  --inst_sos_flag                         false
% 1.55/1.01  --inst_sos_phase                        true
% 1.55/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.55/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.55/1.01  --inst_lit_sel_side                     none
% 1.55/1.01  --inst_solver_per_active                1400
% 1.55/1.01  --inst_solver_calls_frac                1.
% 1.55/1.01  --inst_passive_queue_type               priority_queues
% 1.55/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.55/1.01  --inst_passive_queues_freq              [25;2]
% 1.55/1.01  --inst_dismatching                      true
% 1.55/1.01  --inst_eager_unprocessed_to_passive     true
% 1.55/1.01  --inst_prop_sim_given                   true
% 1.55/1.01  --inst_prop_sim_new                     false
% 1.55/1.01  --inst_subs_new                         false
% 1.55/1.01  --inst_eq_res_simp                      false
% 1.55/1.01  --inst_subs_given                       false
% 1.55/1.01  --inst_orphan_elimination               true
% 1.55/1.01  --inst_learning_loop_flag               true
% 1.55/1.01  --inst_learning_start                   3000
% 1.55/1.01  --inst_learning_factor                  2
% 1.55/1.01  --inst_start_prop_sim_after_learn       3
% 1.55/1.01  --inst_sel_renew                        solver
% 1.55/1.01  --inst_lit_activity_flag                true
% 1.55/1.01  --inst_restr_to_given                   false
% 1.55/1.01  --inst_activity_threshold               500
% 1.55/1.01  --inst_out_proof                        true
% 1.55/1.01  
% 1.55/1.01  ------ Resolution Options
% 1.55/1.01  
% 1.55/1.01  --resolution_flag                       false
% 1.55/1.01  --res_lit_sel                           adaptive
% 1.55/1.01  --res_lit_sel_side                      none
% 1.55/1.01  --res_ordering                          kbo
% 1.55/1.01  --res_to_prop_solver                    active
% 1.55/1.01  --res_prop_simpl_new                    false
% 1.55/1.01  --res_prop_simpl_given                  true
% 1.55/1.01  --res_passive_queue_type                priority_queues
% 1.55/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.55/1.01  --res_passive_queues_freq               [15;5]
% 1.55/1.01  --res_forward_subs                      full
% 1.55/1.01  --res_backward_subs                     full
% 1.55/1.01  --res_forward_subs_resolution           true
% 1.55/1.01  --res_backward_subs_resolution          true
% 1.55/1.01  --res_orphan_elimination                true
% 1.55/1.01  --res_time_limit                        2.
% 1.55/1.01  --res_out_proof                         true
% 1.55/1.01  
% 1.55/1.01  ------ Superposition Options
% 1.55/1.01  
% 1.55/1.01  --superposition_flag                    true
% 1.55/1.01  --sup_passive_queue_type                priority_queues
% 1.55/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.55/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.55/1.01  --demod_completeness_check              fast
% 1.55/1.01  --demod_use_ground                      true
% 1.55/1.01  --sup_to_prop_solver                    passive
% 1.55/1.01  --sup_prop_simpl_new                    true
% 1.55/1.01  --sup_prop_simpl_given                  true
% 1.55/1.01  --sup_fun_splitting                     false
% 1.55/1.01  --sup_smt_interval                      50000
% 1.55/1.01  
% 1.55/1.01  ------ Superposition Simplification Setup
% 1.55/1.01  
% 1.55/1.01  --sup_indices_passive                   []
% 1.55/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.55/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.55/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.01  --sup_full_bw                           [BwDemod]
% 1.55/1.01  --sup_immed_triv                        [TrivRules]
% 1.55/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.55/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.01  --sup_immed_bw_main                     []
% 1.55/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.55/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.55/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.55/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.55/1.01  
% 1.55/1.01  ------ Combination Options
% 1.55/1.01  
% 1.55/1.01  --comb_res_mult                         3
% 1.55/1.01  --comb_sup_mult                         2
% 1.55/1.01  --comb_inst_mult                        10
% 1.55/1.01  
% 1.55/1.01  ------ Debug Options
% 1.55/1.01  
% 1.55/1.01  --dbg_backtrace                         false
% 1.55/1.01  --dbg_dump_prop_clauses                 false
% 1.55/1.01  --dbg_dump_prop_clauses_file            -
% 1.55/1.01  --dbg_out_stat                          false
% 1.55/1.01  
% 1.55/1.01  
% 1.55/1.01  
% 1.55/1.01  
% 1.55/1.01  ------ Proving...
% 1.55/1.01  
% 1.55/1.01  
% 1.55/1.01  % SZS status Theorem for theBenchmark.p
% 1.55/1.01  
% 1.55/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.55/1.01  
% 1.55/1.01  fof(f11,conjecture,(
% 1.55/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.01  
% 1.55/1.01  fof(f12,negated_conjecture,(
% 1.55/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.55/1.01    inference(negated_conjecture,[],[f11])).
% 1.55/1.01  
% 1.55/1.01  fof(f32,plain,(
% 1.55/1.01    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.55/1.01    inference(ennf_transformation,[],[f12])).
% 1.55/1.01  
% 1.55/1.01  fof(f33,plain,(
% 1.55/1.01    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.55/1.01    inference(flattening,[],[f32])).
% 1.55/1.01  
% 1.55/1.01  fof(f37,plain,(
% 1.55/1.01    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.55/1.01    inference(nnf_transformation,[],[f33])).
% 1.55/1.01  
% 1.55/1.01  fof(f38,plain,(
% 1.55/1.01    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.55/1.01    inference(flattening,[],[f37])).
% 1.55/1.01  
% 1.55/1.01  fof(f40,plain,(
% 1.55/1.01    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK2) | ~v2_tex_2(sK2,X0)) & (v1_zfmisc_1(sK2) | v2_tex_2(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK2))) )),
% 1.55/1.01    introduced(choice_axiom,[])).
% 1.55/1.01  
% 1.55/1.01  fof(f39,plain,(
% 1.55/1.01    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK1)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK1) & v2_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.55/1.01    introduced(choice_axiom,[])).
% 1.55/1.01  
% 1.55/1.01  fof(f41,plain,(
% 1.55/1.01    ((~v1_zfmisc_1(sK2) | ~v2_tex_2(sK2,sK1)) & (v1_zfmisc_1(sK2) | v2_tex_2(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(sK2)) & l1_pre_topc(sK1) & v2_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.55/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f38,f40,f39])).
% 1.55/1.01  
% 1.55/1.01  fof(f63,plain,(
% 1.55/1.01    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.55/1.01    inference(cnf_transformation,[],[f41])).
% 1.55/1.01  
% 1.55/1.01  fof(f9,axiom,(
% 1.55/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 1.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.01  
% 1.55/1.01  fof(f13,plain,(
% 1.55/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 1.55/1.01    inference(pure_predicate_removal,[],[f9])).
% 1.55/1.01  
% 1.55/1.01  fof(f28,plain,(
% 1.55/1.01    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.55/1.01    inference(ennf_transformation,[],[f13])).
% 1.55/1.01  
% 1.55/1.01  fof(f29,plain,(
% 1.55/1.01    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.55/1.01    inference(flattening,[],[f28])).
% 1.55/1.01  
% 1.55/1.01  fof(f34,plain,(
% 1.55/1.01    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK0(X0,X1)) = X1 & m1_pre_topc(sK0(X0,X1),X0) & ~v2_struct_0(sK0(X0,X1))))),
% 1.55/1.01    introduced(choice_axiom,[])).
% 1.55/1.01  
% 1.55/1.01  fof(f35,plain,(
% 1.55/1.01    ! [X0] : (! [X1] : ((u1_struct_0(sK0(X0,X1)) = X1 & m1_pre_topc(sK0(X0,X1),X0) & ~v2_struct_0(sK0(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.55/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f34])).
% 1.55/1.01  
% 1.55/1.01  fof(f54,plain,(
% 1.55/1.01    ( ! [X0,X1] : (m1_pre_topc(sK0(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.55/1.01    inference(cnf_transformation,[],[f35])).
% 1.55/1.01  
% 1.55/1.01  fof(f62,plain,(
% 1.55/1.01    ~v1_xboole_0(sK2)),
% 1.55/1.01    inference(cnf_transformation,[],[f41])).
% 1.55/1.01  
% 1.55/1.01  fof(f10,axiom,(
% 1.55/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 1.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.01  
% 1.55/1.01  fof(f30,plain,(
% 1.55/1.01    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.55/1.01    inference(ennf_transformation,[],[f10])).
% 1.55/1.01  
% 1.55/1.01  fof(f31,plain,(
% 1.55/1.01    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.55/1.01    inference(flattening,[],[f30])).
% 1.55/1.01  
% 1.55/1.01  fof(f36,plain,(
% 1.55/1.01    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.55/1.01    inference(nnf_transformation,[],[f31])).
% 1.55/1.01  
% 1.55/1.01  fof(f57,plain,(
% 1.55/1.01    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.55/1.01    inference(cnf_transformation,[],[f36])).
% 1.55/1.01  
% 1.55/1.01  fof(f66,plain,(
% 1.55/1.01    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.55/1.01    inference(equality_resolution,[],[f57])).
% 1.55/1.01  
% 1.55/1.01  fof(f1,axiom,(
% 1.55/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.01  
% 1.55/1.01  fof(f14,plain,(
% 1.55/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.55/1.01    inference(ennf_transformation,[],[f1])).
% 1.55/1.01  
% 1.55/1.01  fof(f42,plain,(
% 1.55/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.55/1.01    inference(cnf_transformation,[],[f14])).
% 1.55/1.01  
% 1.55/1.01  fof(f4,axiom,(
% 1.55/1.01    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 1.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.01  
% 1.55/1.01  fof(f18,plain,(
% 1.55/1.01    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 1.55/1.01    inference(ennf_transformation,[],[f4])).
% 1.55/1.01  
% 1.55/1.01  fof(f19,plain,(
% 1.55/1.01    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 1.55/1.01    inference(flattening,[],[f18])).
% 1.55/1.01  
% 1.55/1.01  fof(f45,plain,(
% 1.55/1.01    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 1.55/1.01    inference(cnf_transformation,[],[f19])).
% 1.55/1.01  
% 1.55/1.01  fof(f65,plain,(
% 1.55/1.01    ~v1_zfmisc_1(sK2) | ~v2_tex_2(sK2,sK1)),
% 1.55/1.01    inference(cnf_transformation,[],[f41])).
% 1.55/1.01  
% 1.55/1.01  fof(f58,plain,(
% 1.55/1.01    ~v2_struct_0(sK1)),
% 1.55/1.01    inference(cnf_transformation,[],[f41])).
% 1.55/1.01  
% 1.55/1.01  fof(f61,plain,(
% 1.55/1.01    l1_pre_topc(sK1)),
% 1.55/1.01    inference(cnf_transformation,[],[f41])).
% 1.55/1.01  
% 1.55/1.01  fof(f53,plain,(
% 1.55/1.01    ( ! [X0,X1] : (~v2_struct_0(sK0(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.55/1.01    inference(cnf_transformation,[],[f35])).
% 1.55/1.01  
% 1.55/1.01  fof(f55,plain,(
% 1.55/1.01    ( ! [X0,X1] : (u1_struct_0(sK0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.55/1.01    inference(cnf_transformation,[],[f35])).
% 1.55/1.01  
% 1.55/1.01  fof(f56,plain,(
% 1.55/1.01    ( ! [X2,X0,X1] : (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.55/1.01    inference(cnf_transformation,[],[f36])).
% 1.55/1.01  
% 1.55/1.01  fof(f67,plain,(
% 1.55/1.01    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~v2_tex_2(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.55/1.01    inference(equality_resolution,[],[f56])).
% 1.55/1.01  
% 1.55/1.01  fof(f3,axiom,(
% 1.55/1.01    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 1.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.01  
% 1.55/1.01  fof(f16,plain,(
% 1.55/1.01    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 1.55/1.01    inference(ennf_transformation,[],[f3])).
% 1.55/1.01  
% 1.55/1.01  fof(f17,plain,(
% 1.55/1.01    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 1.55/1.01    inference(flattening,[],[f16])).
% 1.55/1.01  
% 1.55/1.01  fof(f44,plain,(
% 1.55/1.01    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 1.55/1.01    inference(cnf_transformation,[],[f17])).
% 1.55/1.01  
% 1.55/1.01  fof(f64,plain,(
% 1.55/1.01    v1_zfmisc_1(sK2) | v2_tex_2(sK2,sK1)),
% 1.55/1.01    inference(cnf_transformation,[],[f41])).
% 1.55/1.01  
% 1.55/1.01  fof(f7,axiom,(
% 1.55/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v1_tdlat_3(X1) & ~v2_struct_0(X1)) => (v7_struct_0(X1) & ~v2_struct_0(X1)))))),
% 1.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.01  
% 1.55/1.01  fof(f24,plain,(
% 1.55/1.01    ! [X0] : (! [X1] : (((v7_struct_0(X1) & ~v2_struct_0(X1)) | (~v1_tdlat_3(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.55/1.01    inference(ennf_transformation,[],[f7])).
% 1.55/1.01  
% 1.55/1.01  fof(f25,plain,(
% 1.55/1.01    ! [X0] : (! [X1] : ((v7_struct_0(X1) & ~v2_struct_0(X1)) | ~v1_tdlat_3(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.55/1.01    inference(flattening,[],[f24])).
% 1.55/1.01  
% 1.55/1.01  fof(f51,plain,(
% 1.55/1.01    ( ! [X0,X1] : (v7_struct_0(X1) | ~v1_tdlat_3(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.55/1.01    inference(cnf_transformation,[],[f25])).
% 1.55/1.01  
% 1.55/1.01  fof(f6,axiom,(
% 1.55/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v2_pre_topc(X1) & v7_struct_0(X1) & ~v2_struct_0(X1)) => (v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 1.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.01  
% 1.55/1.01  fof(f22,plain,(
% 1.55/1.01    ! [X0] : (! [X1] : (((v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.55/1.01    inference(ennf_transformation,[],[f6])).
% 1.55/1.01  
% 1.55/1.01  fof(f23,plain,(
% 1.55/1.01    ! [X0] : (! [X1] : ((v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) | ~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.55/1.01    inference(flattening,[],[f22])).
% 1.55/1.01  
% 1.55/1.01  fof(f48,plain,(
% 1.55/1.01    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.55/1.01    inference(cnf_transformation,[],[f23])).
% 1.55/1.01  
% 1.55/1.01  fof(f2,axiom,(
% 1.55/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.01  
% 1.55/1.01  fof(f15,plain,(
% 1.55/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.55/1.01    inference(ennf_transformation,[],[f2])).
% 1.55/1.01  
% 1.55/1.01  fof(f43,plain,(
% 1.55/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.55/1.01    inference(cnf_transformation,[],[f15])).
% 1.55/1.01  
% 1.55/1.01  fof(f5,axiom,(
% 1.55/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v2_tdlat_3(X1) => v2_pre_topc(X1))))),
% 1.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.01  
% 1.55/1.01  fof(f20,plain,(
% 1.55/1.01    ! [X0] : (! [X1] : ((v2_pre_topc(X1) | ~v2_tdlat_3(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.55/1.01    inference(ennf_transformation,[],[f5])).
% 1.55/1.01  
% 1.55/1.01  fof(f21,plain,(
% 1.55/1.01    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.55/1.01    inference(flattening,[],[f20])).
% 1.55/1.01  
% 1.55/1.01  fof(f46,plain,(
% 1.55/1.01    ( ! [X0,X1] : (v2_pre_topc(X1) | ~v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.55/1.01    inference(cnf_transformation,[],[f21])).
% 1.55/1.01  
% 1.55/1.01  fof(f8,axiom,(
% 1.55/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 1.55/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.55/1.01  
% 1.55/1.01  fof(f26,plain,(
% 1.55/1.01    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.55/1.01    inference(ennf_transformation,[],[f8])).
% 1.55/1.01  
% 1.55/1.01  fof(f27,plain,(
% 1.55/1.01    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.55/1.01    inference(flattening,[],[f26])).
% 1.55/1.01  
% 1.55/1.01  fof(f52,plain,(
% 1.55/1.01    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.55/1.01    inference(cnf_transformation,[],[f27])).
% 1.55/1.01  
% 1.55/1.01  fof(f60,plain,(
% 1.55/1.01    v2_tdlat_3(sK1)),
% 1.55/1.01    inference(cnf_transformation,[],[f41])).
% 1.55/1.01  
% 1.55/1.01  fof(f59,plain,(
% 1.55/1.01    v2_pre_topc(sK1)),
% 1.55/1.01    inference(cnf_transformation,[],[f41])).
% 1.55/1.01  
% 1.55/1.01  cnf(c_18,negated_conjecture,
% 1.55/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.55/1.01      inference(cnf_transformation,[],[f63]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_12,plain,
% 1.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.55/1.01      | m1_pre_topc(sK0(X1,X0),X1)
% 1.55/1.01      | v1_xboole_0(X0)
% 1.55/1.01      | v2_struct_0(X1)
% 1.55/1.01      | ~ l1_pre_topc(X1) ),
% 1.55/1.01      inference(cnf_transformation,[],[f54]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_19,negated_conjecture,
% 1.55/1.01      ( ~ v1_xboole_0(sK2) ),
% 1.55/1.01      inference(cnf_transformation,[],[f62]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_387,plain,
% 1.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.55/1.01      | m1_pre_topc(sK0(X1,X0),X1)
% 1.55/1.01      | v2_struct_0(X1)
% 1.55/1.01      | ~ l1_pre_topc(X1)
% 1.55/1.01      | sK2 != X0 ),
% 1.55/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_388,plain,
% 1.55/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.55/1.01      | m1_pre_topc(sK0(X0,sK2),X0)
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X0) ),
% 1.55/1.01      inference(unflattening,[status(thm)],[c_387]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_720,plain,
% 1.55/1.01      ( m1_pre_topc(sK0(X0,sK2),X0)
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | sK2 != sK2 ),
% 1.55/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_388]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_14,plain,
% 1.55/1.01      ( v2_tex_2(u1_struct_0(X0),X1)
% 1.55/1.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.55/1.01      | ~ m1_pre_topc(X0,X1)
% 1.55/1.01      | ~ v1_tdlat_3(X0)
% 1.55/1.01      | v2_struct_0(X1)
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X1) ),
% 1.55/1.01      inference(cnf_transformation,[],[f66]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_0,plain,
% 1.55/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.55/1.01      inference(cnf_transformation,[],[f42]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_3,plain,
% 1.55/1.01      ( ~ v7_struct_0(X0)
% 1.55/1.01      | v1_zfmisc_1(u1_struct_0(X0))
% 1.55/1.01      | ~ l1_struct_0(X0) ),
% 1.55/1.01      inference(cnf_transformation,[],[f45]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_287,plain,
% 1.55/1.01      ( ~ v7_struct_0(X0)
% 1.55/1.01      | v1_zfmisc_1(u1_struct_0(X0))
% 1.55/1.01      | ~ l1_pre_topc(X0) ),
% 1.55/1.01      inference(resolution,[status(thm)],[c_0,c_3]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_16,negated_conjecture,
% 1.55/1.01      ( ~ v2_tex_2(sK2,sK1) | ~ v1_zfmisc_1(sK2) ),
% 1.55/1.01      inference(cnf_transformation,[],[f65]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_163,plain,
% 1.55/1.01      ( ~ v1_zfmisc_1(sK2) | ~ v2_tex_2(sK2,sK1) ),
% 1.55/1.01      inference(prop_impl,[status(thm)],[c_16]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_164,plain,
% 1.55/1.01      ( ~ v2_tex_2(sK2,sK1) | ~ v1_zfmisc_1(sK2) ),
% 1.55/1.01      inference(renaming,[status(thm)],[c_163]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_325,plain,
% 1.55/1.01      ( ~ v2_tex_2(sK2,sK1)
% 1.55/1.01      | ~ v7_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | u1_struct_0(X0) != sK2 ),
% 1.55/1.01      inference(resolution_lifted,[status(thm)],[c_287,c_164]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_609,plain,
% 1.55/1.01      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.55/1.01      | ~ m1_pre_topc(X0,X1)
% 1.55/1.01      | ~ v1_tdlat_3(X0)
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | v2_struct_0(X1)
% 1.55/1.01      | ~ v7_struct_0(X2)
% 1.55/1.01      | ~ l1_pre_topc(X1)
% 1.55/1.01      | ~ l1_pre_topc(X2)
% 1.55/1.01      | u1_struct_0(X0) != sK2
% 1.55/1.01      | u1_struct_0(X2) != sK2
% 1.55/1.01      | sK1 != X1 ),
% 1.55/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_325]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_610,plain,
% 1.55/1.01      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.55/1.01      | ~ m1_pre_topc(X0,sK1)
% 1.55/1.01      | ~ v1_tdlat_3(X0)
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | v2_struct_0(sK1)
% 1.55/1.01      | ~ v7_struct_0(X1)
% 1.55/1.01      | ~ l1_pre_topc(X1)
% 1.55/1.01      | ~ l1_pre_topc(sK1)
% 1.55/1.01      | u1_struct_0(X0) != sK2
% 1.55/1.01      | u1_struct_0(X1) != sK2 ),
% 1.55/1.01      inference(unflattening,[status(thm)],[c_609]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_23,negated_conjecture,
% 1.55/1.01      ( ~ v2_struct_0(sK1) ),
% 1.55/1.01      inference(cnf_transformation,[],[f58]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_20,negated_conjecture,
% 1.55/1.01      ( l1_pre_topc(sK1) ),
% 1.55/1.01      inference(cnf_transformation,[],[f61]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_614,plain,
% 1.55/1.01      ( ~ l1_pre_topc(X1)
% 1.55/1.01      | ~ v7_struct_0(X1)
% 1.55/1.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.55/1.01      | ~ m1_pre_topc(X0,sK1)
% 1.55/1.01      | ~ v1_tdlat_3(X0)
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | u1_struct_0(X0) != sK2
% 1.55/1.01      | u1_struct_0(X1) != sK2 ),
% 1.55/1.01      inference(global_propositional_subsumption,
% 1.55/1.01                [status(thm)],
% 1.55/1.01                [c_610,c_23,c_20]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_615,plain,
% 1.55/1.01      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.55/1.01      | ~ m1_pre_topc(X0,sK1)
% 1.55/1.01      | ~ v1_tdlat_3(X0)
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | ~ v7_struct_0(X1)
% 1.55/1.01      | ~ l1_pre_topc(X1)
% 1.55/1.01      | u1_struct_0(X0) != sK2
% 1.55/1.01      | u1_struct_0(X1) != sK2 ),
% 1.55/1.01      inference(renaming,[status(thm)],[c_614]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_785,plain,
% 1.55/1.01      ( ~ m1_pre_topc(X0,sK1)
% 1.55/1.01      | ~ v1_tdlat_3(X0)
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | ~ v7_struct_0(X1)
% 1.55/1.01      | ~ l1_pre_topc(X1)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | u1_struct_0(X0) != sK2
% 1.55/1.01      | u1_struct_0(X1) != sK2 ),
% 1.55/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_615]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1277,plain,
% 1.55/1.01      ( ~ v1_tdlat_3(X0)
% 1.55/1.01      | v2_struct_0(X1)
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | ~ v7_struct_0(X2)
% 1.55/1.01      | ~ l1_pre_topc(X1)
% 1.55/1.01      | ~ l1_pre_topc(X2)
% 1.55/1.01      | sK0(X1,sK2) != X0
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | u1_struct_0(X0) != sK2
% 1.55/1.01      | u1_struct_0(X2) != sK2
% 1.55/1.01      | sK1 != X1
% 1.55/1.01      | sK2 != sK2 ),
% 1.55/1.01      inference(resolution_lifted,[status(thm)],[c_720,c_785]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1278,plain,
% 1.55/1.01      ( ~ v1_tdlat_3(sK0(sK1,sK2))
% 1.55/1.01      | v2_struct_0(sK0(sK1,sK2))
% 1.55/1.01      | v2_struct_0(sK1)
% 1.55/1.01      | ~ v7_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | ~ l1_pre_topc(sK1)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | u1_struct_0(X0) != sK2
% 1.55/1.01      | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
% 1.55/1.01      inference(unflattening,[status(thm)],[c_1277]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_13,plain,
% 1.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.55/1.01      | v1_xboole_0(X0)
% 1.55/1.01      | v2_struct_0(X1)
% 1.55/1.01      | ~ v2_struct_0(sK0(X1,X0))
% 1.55/1.01      | ~ l1_pre_topc(X1) ),
% 1.55/1.01      inference(cnf_transformation,[],[f53]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_369,plain,
% 1.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.55/1.01      | v2_struct_0(X1)
% 1.55/1.01      | ~ v2_struct_0(sK0(X1,X0))
% 1.55/1.01      | ~ l1_pre_topc(X1)
% 1.55/1.01      | sK2 != X0 ),
% 1.55/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_370,plain,
% 1.55/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | ~ v2_struct_0(sK0(X0,sK2))
% 1.55/1.01      | ~ l1_pre_topc(X0) ),
% 1.55/1.01      inference(unflattening,[status(thm)],[c_369]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_372,plain,
% 1.55/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.55/1.01      | ~ v2_struct_0(sK0(sK1,sK2))
% 1.55/1.01      | v2_struct_0(sK1)
% 1.55/1.01      | ~ l1_pre_topc(sK1) ),
% 1.55/1.01      inference(instantiation,[status(thm)],[c_370]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_11,plain,
% 1.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.55/1.01      | v1_xboole_0(X0)
% 1.55/1.01      | v2_struct_0(X1)
% 1.55/1.01      | ~ l1_pre_topc(X1)
% 1.55/1.01      | u1_struct_0(sK0(X1,X0)) = X0 ),
% 1.55/1.01      inference(cnf_transformation,[],[f55]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_405,plain,
% 1.55/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.55/1.01      | v2_struct_0(X1)
% 1.55/1.01      | ~ l1_pre_topc(X1)
% 1.55/1.01      | u1_struct_0(sK0(X1,X0)) = X0
% 1.55/1.01      | sK2 != X0 ),
% 1.55/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_406,plain,
% 1.55/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | u1_struct_0(sK0(X0,sK2)) = sK2 ),
% 1.55/1.01      inference(unflattening,[status(thm)],[c_405]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_408,plain,
% 1.55/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.55/1.01      | v2_struct_0(sK1)
% 1.55/1.01      | ~ l1_pre_topc(sK1)
% 1.55/1.01      | u1_struct_0(sK0(sK1,sK2)) = sK2 ),
% 1.55/1.01      inference(instantiation,[status(thm)],[c_406]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1282,plain,
% 1.55/1.01      ( u1_struct_0(X0) != sK2
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | ~ v1_tdlat_3(sK0(sK1,sK2))
% 1.55/1.01      | ~ v7_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X0) ),
% 1.55/1.01      inference(global_propositional_subsumption,
% 1.55/1.01                [status(thm)],
% 1.55/1.01                [c_1278,c_23,c_20,c_18,c_372,c_408]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1283,plain,
% 1.55/1.01      ( ~ v1_tdlat_3(sK0(sK1,sK2))
% 1.55/1.01      | ~ v7_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | u1_struct_0(X0) != sK2 ),
% 1.55/1.01      inference(renaming,[status(thm)],[c_1282]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1713,plain,
% 1.55/1.01      ( ~ v1_tdlat_3(sK0(sK1,sK2))
% 1.55/1.01      | ~ v7_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | u1_struct_0(X0) != sK2 ),
% 1.55/1.01      inference(equality_resolution_simp,[status(thm)],[c_1283]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2114,plain,
% 1.55/1.01      ( ~ v1_tdlat_3(sK0(sK1,sK2))
% 1.55/1.01      | ~ v7_struct_0(X0_45)
% 1.55/1.01      | ~ l1_pre_topc(X0_45)
% 1.55/1.01      | u1_struct_0(X0_45) != sK2 ),
% 1.55/1.01      inference(subtyping,[status(esa)],[c_1713]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2790,plain,
% 1.55/1.01      ( ~ v1_tdlat_3(sK0(sK1,sK2))
% 1.55/1.01      | ~ v7_struct_0(sK0(X0_45,sK2))
% 1.55/1.01      | ~ l1_pre_topc(sK0(X0_45,sK2))
% 1.55/1.01      | u1_struct_0(sK0(X0_45,sK2)) != sK2 ),
% 1.55/1.01      inference(instantiation,[status(thm)],[c_2114]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2792,plain,
% 1.55/1.01      ( ~ v1_tdlat_3(sK0(sK1,sK2))
% 1.55/1.01      | ~ v7_struct_0(sK0(sK1,sK2))
% 1.55/1.01      | ~ l1_pre_topc(sK0(sK1,sK2))
% 1.55/1.01      | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
% 1.55/1.01      inference(instantiation,[status(thm)],[c_2790]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_15,plain,
% 1.55/1.01      ( ~ v2_tex_2(u1_struct_0(X0),X1)
% 1.55/1.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.55/1.01      | ~ m1_pre_topc(X0,X1)
% 1.55/1.01      | v1_tdlat_3(X0)
% 1.55/1.01      | v2_struct_0(X1)
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X1) ),
% 1.55/1.01      inference(cnf_transformation,[],[f67]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2,plain,
% 1.55/1.01      ( v7_struct_0(X0)
% 1.55/1.01      | ~ v1_zfmisc_1(u1_struct_0(X0))
% 1.55/1.01      | ~ l1_struct_0(X0) ),
% 1.55/1.01      inference(cnf_transformation,[],[f44]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_301,plain,
% 1.55/1.01      ( v7_struct_0(X0)
% 1.55/1.01      | ~ v1_zfmisc_1(u1_struct_0(X0))
% 1.55/1.01      | ~ l1_pre_topc(X0) ),
% 1.55/1.01      inference(resolution,[status(thm)],[c_0,c_2]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_17,negated_conjecture,
% 1.55/1.01      ( v2_tex_2(sK2,sK1) | v1_zfmisc_1(sK2) ),
% 1.55/1.01      inference(cnf_transformation,[],[f64]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_165,plain,
% 1.55/1.01      ( v1_zfmisc_1(sK2) | v2_tex_2(sK2,sK1) ),
% 1.55/1.01      inference(prop_impl,[status(thm)],[c_17]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_166,plain,
% 1.55/1.01      ( v2_tex_2(sK2,sK1) | v1_zfmisc_1(sK2) ),
% 1.55/1.01      inference(renaming,[status(thm)],[c_165]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_342,plain,
% 1.55/1.01      ( v2_tex_2(sK2,sK1)
% 1.55/1.01      | v7_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | u1_struct_0(X0) != sK2 ),
% 1.55/1.01      inference(resolution_lifted,[status(thm)],[c_301,c_166]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_643,plain,
% 1.55/1.01      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.55/1.01      | ~ m1_pre_topc(X0,X1)
% 1.55/1.01      | v1_tdlat_3(X0)
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | v2_struct_0(X1)
% 1.55/1.01      | v7_struct_0(X2)
% 1.55/1.01      | ~ l1_pre_topc(X1)
% 1.55/1.01      | ~ l1_pre_topc(X2)
% 1.55/1.01      | u1_struct_0(X0) != sK2
% 1.55/1.01      | u1_struct_0(X2) != sK2
% 1.55/1.01      | sK1 != X1 ),
% 1.55/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_342]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_644,plain,
% 1.55/1.01      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.55/1.01      | ~ m1_pre_topc(X0,sK1)
% 1.55/1.01      | v1_tdlat_3(X0)
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | v2_struct_0(sK1)
% 1.55/1.01      | v7_struct_0(X1)
% 1.55/1.01      | ~ l1_pre_topc(X1)
% 1.55/1.01      | ~ l1_pre_topc(sK1)
% 1.55/1.01      | u1_struct_0(X0) != sK2
% 1.55/1.01      | u1_struct_0(X1) != sK2 ),
% 1.55/1.01      inference(unflattening,[status(thm)],[c_643]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_648,plain,
% 1.55/1.01      ( ~ l1_pre_topc(X1)
% 1.55/1.01      | v7_struct_0(X1)
% 1.55/1.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.55/1.01      | ~ m1_pre_topc(X0,sK1)
% 1.55/1.01      | v1_tdlat_3(X0)
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | u1_struct_0(X0) != sK2
% 1.55/1.01      | u1_struct_0(X1) != sK2 ),
% 1.55/1.01      inference(global_propositional_subsumption,
% 1.55/1.01                [status(thm)],
% 1.55/1.01                [c_644,c_23,c_20]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_649,plain,
% 1.55/1.01      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.55/1.01      | ~ m1_pre_topc(X0,sK1)
% 1.55/1.01      | v1_tdlat_3(X0)
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | v7_struct_0(X1)
% 1.55/1.01      | ~ l1_pre_topc(X1)
% 1.55/1.01      | u1_struct_0(X0) != sK2
% 1.55/1.01      | u1_struct_0(X1) != sK2 ),
% 1.55/1.01      inference(renaming,[status(thm)],[c_648]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_756,plain,
% 1.55/1.01      ( ~ m1_pre_topc(X0,sK1)
% 1.55/1.01      | v1_tdlat_3(X0)
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | v7_struct_0(X1)
% 1.55/1.01      | ~ l1_pre_topc(X1)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | u1_struct_0(X0) != sK2
% 1.55/1.01      | u1_struct_0(X1) != sK2 ),
% 1.55/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_649]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1304,plain,
% 1.55/1.01      ( v1_tdlat_3(X0)
% 1.55/1.01      | v2_struct_0(X1)
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | v7_struct_0(X2)
% 1.55/1.01      | ~ l1_pre_topc(X1)
% 1.55/1.01      | ~ l1_pre_topc(X2)
% 1.55/1.01      | sK0(X1,sK2) != X0
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | u1_struct_0(X0) != sK2
% 1.55/1.01      | u1_struct_0(X2) != sK2
% 1.55/1.01      | sK1 != X1
% 1.55/1.01      | sK2 != sK2 ),
% 1.55/1.01      inference(resolution_lifted,[status(thm)],[c_720,c_756]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1305,plain,
% 1.55/1.01      ( v1_tdlat_3(sK0(sK1,sK2))
% 1.55/1.01      | v2_struct_0(sK0(sK1,sK2))
% 1.55/1.01      | v2_struct_0(sK1)
% 1.55/1.01      | v7_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | ~ l1_pre_topc(sK1)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | u1_struct_0(X0) != sK2
% 1.55/1.01      | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
% 1.55/1.01      inference(unflattening,[status(thm)],[c_1304]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1309,plain,
% 1.55/1.01      ( u1_struct_0(X0) != sK2
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | v1_tdlat_3(sK0(sK1,sK2))
% 1.55/1.01      | v7_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X0) ),
% 1.55/1.01      inference(global_propositional_subsumption,
% 1.55/1.01                [status(thm)],
% 1.55/1.01                [c_1305,c_23,c_20,c_18,c_372,c_408]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1310,plain,
% 1.55/1.01      ( v1_tdlat_3(sK0(sK1,sK2))
% 1.55/1.01      | v7_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | u1_struct_0(X0) != sK2 ),
% 1.55/1.01      inference(renaming,[status(thm)],[c_1309]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1709,plain,
% 1.55/1.01      ( v1_tdlat_3(sK0(sK1,sK2))
% 1.55/1.01      | v7_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | u1_struct_0(X0) != sK2 ),
% 1.55/1.01      inference(equality_resolution_simp,[status(thm)],[c_1310]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2115,plain,
% 1.55/1.01      ( v1_tdlat_3(sK0(sK1,sK2))
% 1.55/1.01      | v7_struct_0(X0_45)
% 1.55/1.01      | ~ l1_pre_topc(X0_45)
% 1.55/1.01      | u1_struct_0(X0_45) != sK2 ),
% 1.55/1.01      inference(subtyping,[status(esa)],[c_1709]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2728,plain,
% 1.55/1.01      ( v1_tdlat_3(sK0(sK1,sK2))
% 1.55/1.01      | v7_struct_0(sK0(X0_45,sK2))
% 1.55/1.01      | ~ l1_pre_topc(sK0(X0_45,sK2))
% 1.55/1.01      | u1_struct_0(sK0(X0_45,sK2)) != sK2 ),
% 1.55/1.01      inference(instantiation,[status(thm)],[c_2115]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2730,plain,
% 1.55/1.01      ( v1_tdlat_3(sK0(sK1,sK2))
% 1.55/1.01      | v7_struct_0(sK0(sK1,sK2))
% 1.55/1.01      | ~ l1_pre_topc(sK0(sK1,sK2))
% 1.55/1.01      | u1_struct_0(sK0(sK1,sK2)) != sK2 ),
% 1.55/1.01      inference(instantiation,[status(thm)],[c_2728]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2141,plain,
% 1.55/1.01      ( k1_zfmisc_1(X0_46) = k1_zfmisc_1(X1_46) | X0_46 != X1_46 ),
% 1.55/1.01      theory(equality) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2700,plain,
% 1.55/1.01      ( k1_zfmisc_1(u1_struct_0(X0_45)) = k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | u1_struct_0(X0_45) != u1_struct_0(sK1) ),
% 1.55/1.01      inference(instantiation,[status(thm)],[c_2141]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2701,plain,
% 1.55/1.01      ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 1.55/1.01      inference(instantiation,[status(thm)],[c_2700]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_8,plain,
% 1.55/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.55/1.01      | ~ v1_tdlat_3(X0)
% 1.55/1.01      | v2_struct_0(X1)
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | ~ v2_tdlat_3(X1)
% 1.55/1.01      | ~ v2_pre_topc(X1)
% 1.55/1.01      | v7_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X1) ),
% 1.55/1.01      inference(cnf_transformation,[],[f51]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1154,plain,
% 1.55/1.01      ( ~ v1_tdlat_3(X0)
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | v2_struct_0(X1)
% 1.55/1.01      | v2_struct_0(X2)
% 1.55/1.01      | ~ v2_tdlat_3(X1)
% 1.55/1.01      | ~ v2_pre_topc(X1)
% 1.55/1.01      | v7_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X1)
% 1.55/1.01      | ~ l1_pre_topc(X2)
% 1.55/1.01      | X2 != X1
% 1.55/1.01      | sK0(X2,sK2) != X0
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X2)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | sK2 != sK2 ),
% 1.55/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_720]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1155,plain,
% 1.55/1.01      ( ~ v1_tdlat_3(sK0(X0,sK2))
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | v2_struct_0(sK0(X0,sK2))
% 1.55/1.01      | ~ v2_tdlat_3(X0)
% 1.55/1.01      | ~ v2_pre_topc(X0)
% 1.55/1.01      | v7_struct_0(sK0(X0,sK2))
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.55/1.01      inference(unflattening,[status(thm)],[c_1154]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_738,plain,
% 1.55/1.01      ( v2_struct_0(X0)
% 1.55/1.01      | ~ v2_struct_0(sK0(X0,sK2))
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | sK2 != sK2 ),
% 1.55/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_370]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1724,plain,
% 1.55/1.01      ( v2_struct_0(X0)
% 1.55/1.01      | ~ v2_struct_0(sK0(X0,sK2))
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.55/1.01      inference(equality_resolution_simp,[status(thm)],[c_738]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1792,plain,
% 1.55/1.01      ( v2_struct_0(X0)
% 1.55/1.01      | ~ v1_tdlat_3(sK0(X0,sK2))
% 1.55/1.01      | ~ v2_tdlat_3(X0)
% 1.55/1.01      | ~ v2_pre_topc(X0)
% 1.55/1.01      | v7_struct_0(sK0(X0,sK2))
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.55/1.01      inference(global_propositional_subsumption,
% 1.55/1.01                [status(thm)],
% 1.55/1.01                [c_1155,c_1724]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1793,plain,
% 1.55/1.01      ( ~ v1_tdlat_3(sK0(X0,sK2))
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | ~ v2_tdlat_3(X0)
% 1.55/1.01      | ~ v2_pre_topc(X0)
% 1.55/1.01      | v7_struct_0(sK0(X0,sK2))
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.55/1.01      inference(renaming,[status(thm)],[c_1792]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2109,plain,
% 1.55/1.01      ( ~ v1_tdlat_3(sK0(X0_45,sK2))
% 1.55/1.01      | v2_struct_0(X0_45)
% 1.55/1.01      | ~ v2_tdlat_3(X0_45)
% 1.55/1.01      | ~ v2_pre_topc(X0_45)
% 1.55/1.01      | v7_struct_0(sK0(X0_45,sK2))
% 1.55/1.01      | ~ l1_pre_topc(X0_45)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.55/1.01      inference(subtyping,[status(esa)],[c_1793]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2194,plain,
% 1.55/1.01      ( ~ v1_tdlat_3(sK0(sK1,sK2))
% 1.55/1.01      | v2_struct_0(sK1)
% 1.55/1.01      | ~ v2_tdlat_3(sK1)
% 1.55/1.01      | ~ v2_pre_topc(sK1)
% 1.55/1.01      | v7_struct_0(sK0(sK1,sK2))
% 1.55/1.01      | ~ l1_pre_topc(sK1)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.55/1.01      inference(instantiation,[status(thm)],[c_2109]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_6,plain,
% 1.55/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.55/1.01      | v1_tdlat_3(X0)
% 1.55/1.01      | v2_struct_0(X1)
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | ~ v2_pre_topc(X0)
% 1.55/1.01      | ~ v7_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X1) ),
% 1.55/1.01      inference(cnf_transformation,[],[f48]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1184,plain,
% 1.55/1.01      ( v1_tdlat_3(X0)
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | v2_struct_0(X1)
% 1.55/1.01      | v2_struct_0(X2)
% 1.55/1.01      | ~ v2_pre_topc(X0)
% 1.55/1.01      | ~ v7_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X1)
% 1.55/1.01      | ~ l1_pre_topc(X2)
% 1.55/1.01      | X2 != X1
% 1.55/1.01      | sK0(X2,sK2) != X0
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X2)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | sK2 != sK2 ),
% 1.55/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_720]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1185,plain,
% 1.55/1.01      ( v1_tdlat_3(sK0(X0,sK2))
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | v2_struct_0(sK0(X0,sK2))
% 1.55/1.01      | ~ v2_pre_topc(sK0(X0,sK2))
% 1.55/1.01      | ~ v7_struct_0(sK0(X0,sK2))
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.55/1.01      inference(unflattening,[status(thm)],[c_1184]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1776,plain,
% 1.55/1.01      ( v2_struct_0(X0)
% 1.55/1.01      | v1_tdlat_3(sK0(X0,sK2))
% 1.55/1.01      | ~ v2_pre_topc(sK0(X0,sK2))
% 1.55/1.01      | ~ v7_struct_0(sK0(X0,sK2))
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.55/1.01      inference(global_propositional_subsumption,
% 1.55/1.01                [status(thm)],
% 1.55/1.01                [c_1185,c_1724]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1777,plain,
% 1.55/1.01      ( v1_tdlat_3(sK0(X0,sK2))
% 1.55/1.01      | v2_struct_0(X0)
% 1.55/1.01      | ~ v2_pre_topc(sK0(X0,sK2))
% 1.55/1.01      | ~ v7_struct_0(sK0(X0,sK2))
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.55/1.01      inference(renaming,[status(thm)],[c_1776]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2111,plain,
% 1.55/1.01      ( v1_tdlat_3(sK0(X0_45,sK2))
% 1.55/1.01      | v2_struct_0(X0_45)
% 1.55/1.01      | ~ v2_pre_topc(sK0(X0_45,sK2))
% 1.55/1.01      | ~ v7_struct_0(sK0(X0_45,sK2))
% 1.55/1.01      | ~ l1_pre_topc(X0_45)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.55/1.01      inference(subtyping,[status(esa)],[c_1777]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2188,plain,
% 1.55/1.01      ( v1_tdlat_3(sK0(sK1,sK2))
% 1.55/1.01      | v2_struct_0(sK1)
% 1.55/1.01      | ~ v2_pre_topc(sK0(sK1,sK2))
% 1.55/1.01      | ~ v7_struct_0(sK0(sK1,sK2))
% 1.55/1.01      | ~ l1_pre_topc(sK1)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.55/1.01      inference(instantiation,[status(thm)],[c_2111]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_702,plain,
% 1.55/1.01      ( v2_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | u1_struct_0(sK0(X0,sK2)) = sK2
% 1.55/1.01      | sK2 != sK2 ),
% 1.55/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_406]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1728,plain,
% 1.55/1.01      ( v2_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | u1_struct_0(sK0(X0,sK2)) = sK2 ),
% 1.55/1.01      inference(equality_resolution_simp,[status(thm)],[c_702]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2112,plain,
% 1.55/1.01      ( v2_struct_0(X0_45)
% 1.55/1.01      | ~ l1_pre_topc(X0_45)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | u1_struct_0(sK0(X0_45,sK2)) = sK2 ),
% 1.55/1.01      inference(subtyping,[status(esa)],[c_1728]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2185,plain,
% 1.55/1.01      ( v2_struct_0(sK1)
% 1.55/1.01      | ~ l1_pre_topc(sK1)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | u1_struct_0(sK0(sK1,sK2)) = sK2 ),
% 1.55/1.01      inference(instantiation,[status(thm)],[c_2112]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1,plain,
% 1.55/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.55/1.01      inference(cnf_transformation,[],[f43]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1259,plain,
% 1.55/1.01      ( v2_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X1)
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | l1_pre_topc(X2)
% 1.55/1.01      | X0 != X1
% 1.55/1.01      | sK0(X0,sK2) != X2
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | sK2 != sK2 ),
% 1.55/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_720]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1260,plain,
% 1.55/1.01      ( v2_struct_0(X0)
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | l1_pre_topc(sK0(X0,sK2))
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.55/1.01      inference(unflattening,[status(thm)],[c_1259]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2116,plain,
% 1.55/1.01      ( v2_struct_0(X0_45)
% 1.55/1.01      | ~ l1_pre_topc(X0_45)
% 1.55/1.01      | l1_pre_topc(sK0(X0_45,sK2))
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.55/1.01      inference(subtyping,[status(esa)],[c_1260]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2173,plain,
% 1.55/1.01      ( v2_struct_0(sK1)
% 1.55/1.01      | l1_pre_topc(sK0(sK1,sK2))
% 1.55/1.01      | ~ l1_pre_topc(sK1)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.55/1.01      inference(instantiation,[status(thm)],[c_2116]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_4,plain,
% 1.55/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.55/1.01      | v2_struct_0(X1)
% 1.55/1.01      | ~ v2_tdlat_3(X0)
% 1.55/1.01      | v2_pre_topc(X0)
% 1.55/1.01      | ~ l1_pre_topc(X1) ),
% 1.55/1.01      inference(cnf_transformation,[],[f46]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1238,plain,
% 1.55/1.01      ( v2_struct_0(X0)
% 1.55/1.01      | v2_struct_0(X1)
% 1.55/1.01      | ~ v2_tdlat_3(X2)
% 1.55/1.01      | v2_pre_topc(X2)
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | ~ l1_pre_topc(X1)
% 1.55/1.01      | X1 != X0
% 1.55/1.01      | sK0(X1,sK2) != X2
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | sK2 != sK2 ),
% 1.55/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_720]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1239,plain,
% 1.55/1.01      ( v2_struct_0(X0)
% 1.55/1.01      | ~ v2_tdlat_3(sK0(X0,sK2))
% 1.55/1.01      | v2_pre_topc(sK0(X0,sK2))
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.55/1.01      inference(unflattening,[status(thm)],[c_1238]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2117,plain,
% 1.55/1.01      ( v2_struct_0(X0_45)
% 1.55/1.01      | ~ v2_tdlat_3(sK0(X0_45,sK2))
% 1.55/1.01      | v2_pre_topc(sK0(X0_45,sK2))
% 1.55/1.01      | ~ l1_pre_topc(X0_45)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.55/1.01      inference(subtyping,[status(esa)],[c_1239]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2170,plain,
% 1.55/1.01      ( v2_struct_0(sK1)
% 1.55/1.01      | ~ v2_tdlat_3(sK0(sK1,sK2))
% 1.55/1.01      | v2_pre_topc(sK0(sK1,sK2))
% 1.55/1.01      | ~ l1_pre_topc(sK1)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.55/1.01      inference(instantiation,[status(thm)],[c_2117]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_10,plain,
% 1.55/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.55/1.01      | v2_struct_0(X1)
% 1.55/1.01      | ~ v2_tdlat_3(X1)
% 1.55/1.01      | v2_tdlat_3(X0)
% 1.55/1.01      | ~ v2_pre_topc(X1)
% 1.55/1.01      | ~ l1_pre_topc(X1) ),
% 1.55/1.01      inference(cnf_transformation,[],[f52]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1130,plain,
% 1.55/1.01      ( v2_struct_0(X0)
% 1.55/1.01      | v2_struct_0(X1)
% 1.55/1.01      | ~ v2_tdlat_3(X0)
% 1.55/1.01      | v2_tdlat_3(X2)
% 1.55/1.01      | ~ v2_pre_topc(X0)
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | ~ l1_pre_topc(X1)
% 1.55/1.01      | X1 != X0
% 1.55/1.01      | sK0(X1,sK2) != X2
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.55/1.01      | sK2 != sK2 ),
% 1.55/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_720]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_1131,plain,
% 1.55/1.01      ( v2_struct_0(X0)
% 1.55/1.01      | ~ v2_tdlat_3(X0)
% 1.55/1.01      | v2_tdlat_3(sK0(X0,sK2))
% 1.55/1.01      | ~ v2_pre_topc(X0)
% 1.55/1.01      | ~ l1_pre_topc(X0)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.55/1.01      inference(unflattening,[status(thm)],[c_1130]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2118,plain,
% 1.55/1.01      ( v2_struct_0(X0_45)
% 1.55/1.01      | ~ v2_tdlat_3(X0_45)
% 1.55/1.01      | v2_tdlat_3(sK0(X0_45,sK2))
% 1.55/1.01      | ~ v2_pre_topc(X0_45)
% 1.55/1.01      | ~ l1_pre_topc(X0_45)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(X0_45)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.55/1.01      inference(subtyping,[status(esa)],[c_1131]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2167,plain,
% 1.55/1.01      ( v2_struct_0(sK1)
% 1.55/1.01      | v2_tdlat_3(sK0(sK1,sK2))
% 1.55/1.01      | ~ v2_tdlat_3(sK1)
% 1.55/1.01      | ~ v2_pre_topc(sK1)
% 1.55/1.01      | ~ l1_pre_topc(sK1)
% 1.55/1.01      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 1.55/1.01      inference(instantiation,[status(thm)],[c_2118]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2128,plain,( X0_45 = X0_45 ),theory(equality) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2152,plain,
% 1.55/1.01      ( sK1 = sK1 ),
% 1.55/1.01      inference(instantiation,[status(thm)],[c_2128]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2134,plain,
% 1.55/1.01      ( u1_struct_0(X0_45) = u1_struct_0(X1_45) | X0_45 != X1_45 ),
% 1.55/1.01      theory(equality) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_2143,plain,
% 1.55/1.01      ( u1_struct_0(sK1) = u1_struct_0(sK1) | sK1 != sK1 ),
% 1.55/1.01      inference(instantiation,[status(thm)],[c_2134]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_21,negated_conjecture,
% 1.55/1.01      ( v2_tdlat_3(sK1) ),
% 1.55/1.01      inference(cnf_transformation,[],[f60]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(c_22,negated_conjecture,
% 1.55/1.01      ( v2_pre_topc(sK1) ),
% 1.55/1.01      inference(cnf_transformation,[],[f59]) ).
% 1.55/1.01  
% 1.55/1.01  cnf(contradiction,plain,
% 1.55/1.01      ( $false ),
% 1.55/1.01      inference(minisat,
% 1.55/1.01                [status(thm)],
% 1.55/1.01                [c_2792,c_2730,c_2701,c_2194,c_2188,c_2185,c_2173,c_2170,
% 1.55/1.01                 c_2167,c_2152,c_2143,c_20,c_21,c_22,c_23]) ).
% 1.55/1.01  
% 1.55/1.01  
% 1.55/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.55/1.01  
% 1.55/1.01  ------                               Statistics
% 1.55/1.01  
% 1.55/1.01  ------ General
% 1.55/1.01  
% 1.55/1.01  abstr_ref_over_cycles:                  0
% 1.55/1.01  abstr_ref_under_cycles:                 0
% 1.55/1.01  gc_basic_clause_elim:                   0
% 1.55/1.01  forced_gc_time:                         0
% 1.55/1.01  parsing_time:                           0.015
% 1.55/1.01  unif_index_cands_time:                  0.
% 1.55/1.01  unif_index_add_time:                    0.
% 1.55/1.01  orderings_time:                         0.
% 1.55/1.01  out_proof_time:                         0.018
% 1.55/1.01  total_time:                             0.124
% 1.55/1.01  num_of_symbols:                         50
% 1.55/1.01  num_of_terms:                           839
% 1.55/1.01  
% 1.55/1.01  ------ Preprocessing
% 1.55/1.01  
% 1.55/1.01  num_of_splits:                          2
% 1.55/1.01  num_of_split_atoms:                     2
% 1.55/1.01  num_of_reused_defs:                     0
% 1.55/1.01  num_eq_ax_congr_red:                    6
% 1.55/1.01  num_of_sem_filtered_clauses:            1
% 1.55/1.01  num_of_subtypes:                        3
% 1.55/1.01  monotx_restored_types:                  0
% 1.55/1.01  sat_num_of_epr_types:                   0
% 1.55/1.01  sat_num_of_non_cyclic_types:            0
% 1.55/1.01  sat_guarded_non_collapsed_types:        0
% 1.55/1.01  num_pure_diseq_elim:                    0
% 1.55/1.01  simp_replaced_by:                       0
% 1.55/1.01  res_preprocessed:                       100
% 1.55/1.01  prep_upred:                             0
% 1.55/1.01  prep_unflattend:                        35
% 1.55/1.01  smt_new_axioms:                         0
% 1.55/1.01  pred_elim_cands:                        6
% 1.55/1.01  pred_elim:                              6
% 1.55/1.01  pred_elim_cl:                           7
% 1.55/1.01  pred_elim_cycles:                       13
% 1.55/1.01  merged_defs:                            2
% 1.55/1.01  merged_defs_ncl:                        0
% 1.55/1.01  bin_hyper_res:                          2
% 1.55/1.01  prep_cycles:                            4
% 1.55/1.01  pred_elim_time:                         0.039
% 1.55/1.01  splitting_time:                         0.
% 1.55/1.01  sem_filter_time:                        0.
% 1.55/1.01  monotx_time:                            0.
% 1.55/1.01  subtype_inf_time:                       0.
% 1.55/1.01  
% 1.55/1.01  ------ Problem properties
% 1.55/1.01  
% 1.55/1.01  clauses:                                17
% 1.55/1.01  conjectures:                            4
% 1.55/1.01  epr:                                    5
% 1.55/1.01  horn:                                   8
% 1.55/1.01  ground:                                 5
% 1.55/1.01  unary:                                  4
% 1.55/1.01  binary:                                 1
% 1.55/1.01  lits:                                   64
% 1.55/1.01  lits_eq:                                13
% 1.55/1.01  fd_pure:                                0
% 1.55/1.01  fd_pseudo:                              0
% 1.55/1.01  fd_cond:                                0
% 1.55/1.01  fd_pseudo_cond:                         0
% 1.55/1.01  ac_symbols:                             0
% 1.55/1.01  
% 1.55/1.01  ------ Propositional Solver
% 1.55/1.01  
% 1.55/1.01  prop_solver_calls:                      24
% 1.55/1.01  prop_fast_solver_calls:                 1241
% 1.55/1.01  smt_solver_calls:                       0
% 1.55/1.01  smt_fast_solver_calls:                  0
% 1.55/1.01  prop_num_of_clauses:                    441
% 1.55/1.01  prop_preprocess_simplified:             2848
% 1.55/1.01  prop_fo_subsumed:                       48
% 1.55/1.01  prop_solver_time:                       0.
% 1.55/1.01  smt_solver_time:                        0.
% 1.55/1.01  smt_fast_solver_time:                   0.
% 1.55/1.01  prop_fast_solver_time:                  0.
% 1.55/1.01  prop_unsat_core_time:                   0.
% 1.55/1.01  
% 1.55/1.01  ------ QBF
% 1.55/1.01  
% 1.55/1.01  qbf_q_res:                              0
% 1.55/1.01  qbf_num_tautologies:                    0
% 1.55/1.01  qbf_prep_cycles:                        0
% 1.55/1.01  
% 1.55/1.01  ------ BMC1
% 1.55/1.01  
% 1.55/1.01  bmc1_current_bound:                     -1
% 1.55/1.01  bmc1_last_solved_bound:                 -1
% 1.55/1.01  bmc1_unsat_core_size:                   -1
% 1.55/1.01  bmc1_unsat_core_parents_size:           -1
% 1.55/1.01  bmc1_merge_next_fun:                    0
% 1.55/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.55/1.01  
% 1.55/1.01  ------ Instantiation
% 1.55/1.01  
% 1.55/1.01  inst_num_of_clauses:                    49
% 1.55/1.01  inst_num_in_passive:                    4
% 1.55/1.01  inst_num_in_active:                     40
% 1.55/1.01  inst_num_in_unprocessed:                4
% 1.55/1.01  inst_num_of_loops:                      52
% 1.55/1.01  inst_num_of_learning_restarts:          0
% 1.55/1.01  inst_num_moves_active_passive:          9
% 1.55/1.01  inst_lit_activity:                      0
% 1.55/1.01  inst_lit_activity_moves:                0
% 1.55/1.01  inst_num_tautologies:                   0
% 1.55/1.01  inst_num_prop_implied:                  0
% 1.55/1.01  inst_num_existing_simplified:           0
% 1.55/1.01  inst_num_eq_res_simplified:             0
% 1.55/1.01  inst_num_child_elim:                    0
% 1.55/1.01  inst_num_of_dismatching_blockings:      1
% 1.55/1.01  inst_num_of_non_proper_insts:           13
% 1.55/1.01  inst_num_of_duplicates:                 0
% 1.55/1.01  inst_inst_num_from_inst_to_res:         0
% 1.55/1.01  inst_dismatching_checking_time:         0.
% 1.55/1.01  
% 1.55/1.01  ------ Resolution
% 1.55/1.01  
% 1.55/1.01  res_num_of_clauses:                     0
% 1.55/1.01  res_num_in_passive:                     0
% 1.55/1.01  res_num_in_active:                      0
% 1.55/1.01  res_num_of_loops:                       104
% 1.55/1.01  res_forward_subset_subsumed:            2
% 1.55/1.01  res_backward_subset_subsumed:           0
% 1.55/1.01  res_forward_subsumed:                   2
% 1.55/1.01  res_backward_subsumed:                  0
% 1.55/1.01  res_forward_subsumption_resolution:     2
% 1.55/1.01  res_backward_subsumption_resolution:    0
% 1.55/1.01  res_clause_to_clause_subsumption:       66
% 1.55/1.01  res_orphan_elimination:                 0
% 1.55/1.01  res_tautology_del:                      17
% 1.55/1.01  res_num_eq_res_simplified:              4
% 1.55/1.01  res_num_sel_changes:                    0
% 1.55/1.01  res_moves_from_active_to_pass:          0
% 1.55/1.01  
% 1.55/1.01  ------ Superposition
% 1.55/1.01  
% 1.55/1.01  sup_time_total:                         0.
% 1.55/1.01  sup_time_generating:                    0.
% 1.55/1.01  sup_time_sim_full:                      0.
% 1.55/1.01  sup_time_sim_immed:                     0.
% 1.55/1.01  
% 1.55/1.01  sup_num_of_clauses:                     22
% 1.55/1.01  sup_num_in_active:                      10
% 1.55/1.01  sup_num_in_passive:                     12
% 1.55/1.01  sup_num_of_loops:                       10
% 1.55/1.01  sup_fw_superposition:                   0
% 1.55/1.01  sup_bw_superposition:                   0
% 1.55/1.01  sup_immediate_simplified:               0
% 1.55/1.01  sup_given_eliminated:                   0
% 1.55/1.01  comparisons_done:                       0
% 1.55/1.01  comparisons_avoided:                    0
% 1.55/1.01  
% 1.55/1.01  ------ Simplifications
% 1.55/1.01  
% 1.55/1.01  
% 1.55/1.01  sim_fw_subset_subsumed:                 0
% 1.55/1.01  sim_bw_subset_subsumed:                 0
% 1.55/1.01  sim_fw_subsumed:                        0
% 1.55/1.01  sim_bw_subsumed:                        0
% 1.55/1.01  sim_fw_subsumption_res:                 0
% 1.55/1.01  sim_bw_subsumption_res:                 0
% 1.55/1.01  sim_tautology_del:                      0
% 1.55/1.01  sim_eq_tautology_del:                   0
% 1.55/1.01  sim_eq_res_simp:                        0
% 1.55/1.01  sim_fw_demodulated:                     0
% 1.55/1.01  sim_bw_demodulated:                     0
% 1.55/1.01  sim_light_normalised:                   0
% 1.55/1.01  sim_joinable_taut:                      0
% 1.55/1.01  sim_joinable_simp:                      0
% 1.55/1.01  sim_ac_normalised:                      0
% 1.55/1.01  sim_smt_subsumption:                    0
% 1.55/1.01  
%------------------------------------------------------------------------------
