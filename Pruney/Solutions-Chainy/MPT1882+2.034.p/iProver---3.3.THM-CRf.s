%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:25 EST 2020

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 708 expanded)
%              Number of clauses        :   78 ( 152 expanded)
%              Number of leaves         :   14 ( 163 expanded)
%              Depth                    :   18
%              Number of atoms          :  614 (5661 expanded)
%              Number of equality atoms :   76 ( 139 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
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

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_zfmisc_1(X1) )
            & ( v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v3_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v3_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ( ~ v1_zfmisc_1(sK2)
          | ~ v3_tex_2(sK2,X0) )
        & ( v1_zfmisc_1(sK2)
          | v3_tex_2(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v3_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,sK1) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK1)
      & v2_tdlat_3(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ~ v1_zfmisc_1(sK2)
      | ~ v3_tex_2(sK2,sK1) )
    & ( v1_zfmisc_1(sK2)
      | v3_tex_2(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & ~ v1_xboole_0(sK2)
    & l1_pre_topc(sK1)
    & v2_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f35,f37,f36])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,
    ( ~ v1_zfmisc_1(sK2)
    | ~ v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f18])).

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
    inference(flattening,[],[f28])).

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
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK0(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK0(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK0(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,
    ( v1_zfmisc_1(sK2)
    | v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_1379,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2094,plain,
    ( sK0(sK1,sK2) != X0
    | sK0(sK1,sK2) = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1379])).

cnf(c_3805,plain,
    ( sK0(sK1,sK2) = sK2
    | sK0(sK1,sK2) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2094])).

cnf(c_1381,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_2554,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1381])).

cnf(c_3120,plain,
    ( ~ r1_tarski(sK2,sK0(sK1,sK2))
    | r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 != sK0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2554])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2271,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2665,plain,
    ( ~ v1_xboole_0(sK0(sK1,sK2))
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0(sK1,sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2271])).

cnf(c_2228,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK0(sK1,sK2))
    | X0 = sK0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2470,plain,
    ( ~ v1_xboole_0(sK0(sK1,sK2))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2228])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2149,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2370,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2149])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2139,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2022,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2138,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
    | r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_2022])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_17,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_zfmisc_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_338,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_zfmisc_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_339,plain,
    ( ~ v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_zfmisc_1(X0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_23,negated_conjecture,
    ( v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_343,plain,
    ( v1_zfmisc_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_24,c_23,c_22])).

cnf(c_344,plain,
    ( ~ v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_343])).

cnf(c_538,plain,
    ( ~ v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X0 != X2
    | X2 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_344])).

cnf(c_539,plain,
    ( ~ v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_2086,plain,
    ( ~ v2_tex_2(sK0(sK1,sK2),sK1)
    | ~ m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK2,sK0(sK1,sK2))
    | v1_xboole_0(sK0(sK1,sK2))
    | v1_xboole_0(sK2)
    | sK0(sK1,sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_18,negated_conjecture,
    ( ~ v3_tex_2(sK2,sK1)
    | ~ v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_193,plain,
    ( ~ v1_zfmisc_1(sK2)
    | ~ v3_tex_2(sK2,sK1) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_194,plain,
    ( ~ v3_tex_2(sK2,sK1)
    | ~ v1_zfmisc_1(sK2) ),
    inference(renaming,[status(thm)],[c_193])).

cnf(c_584,plain,
    ( ~ v2_tex_2(X0,sK1)
    | ~ v3_tex_2(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_344,c_194])).

cnf(c_585,plain,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ v3_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_21,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_587,plain,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ v3_tex_2(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_585,c_21,c_20])).

cnf(c_12,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_433,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_434,plain,
    ( ~ v2_tex_2(X0,sK1)
    | v3_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_699,plain,
    ( ~ v2_tex_2(X0,sK1)
    | ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_587,c_434])).

cnf(c_700,plain,
    ( ~ v2_tex_2(sK2,sK1)
    | m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_699])).

cnf(c_11,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_451,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_452,plain,
    ( ~ v2_tex_2(X0,sK1)
    | v2_tex_2(sK0(sK1,X0),sK1)
    | v3_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_688,plain,
    ( ~ v2_tex_2(X0,sK1)
    | v2_tex_2(sK0(sK1,X0),sK1)
    | ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_587,c_452])).

cnf(c_689,plain,
    ( v2_tex_2(sK0(sK1,sK2),sK1)
    | ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_10,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,sK0(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_469,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,sK0(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_470,plain,
    ( ~ v2_tex_2(X0,sK1)
    | v3_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,sK0(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_677,plain,
    ( ~ v2_tex_2(X0,sK1)
    | ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,sK0(sK1,X0))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_587,c_470])).

cnf(c_678,plain,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK2,sK0(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_677])).

cnf(c_9,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_487,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0(X1,X0) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_488,plain,
    ( ~ v2_tex_2(X0,sK1)
    | v3_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK0(sK1,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_669,plain,
    ( ~ v2_tex_2(X0,sK1)
    | ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK0(sK1,X0) != X0
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_587,c_488])).

cnf(c_670,plain,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK0(sK1,sK2) != sK2 ),
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_16,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_zfmisc_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_362,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_zfmisc_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_363,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_zfmisc_1(X0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_367,plain,
    ( ~ v1_zfmisc_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_363,c_24,c_23,c_22])).

cnf(c_368,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_367])).

cnf(c_19,negated_conjecture,
    ( v3_tex_2(sK2,sK1)
    | v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_195,plain,
    ( v1_zfmisc_1(sK2)
    | v3_tex_2(sK2,sK1) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_196,plain,
    ( v3_tex_2(sK2,sK1)
    | v1_zfmisc_1(sK2) ),
    inference(renaming,[status(thm)],[c_195])).

cnf(c_598,plain,
    ( v2_tex_2(X0,sK1)
    | v3_tex_2(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_368,c_196])).

cnf(c_599,plain,
    ( v2_tex_2(sK2,sK1)
    | v3_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_598])).

cnf(c_601,plain,
    ( v2_tex_2(sK2,sK1)
    | v3_tex_2(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_599,c_21,c_20])).

cnf(c_14,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_396,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_397,plain,
    ( v2_tex_2(X0,sK1)
    | ~ v3_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_652,plain,
    ( v2_tex_2(X0,sK1)
    | v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_601,c_397])).

cnf(c_653,plain,
    ( v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_652])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3805,c_3120,c_2665,c_2470,c_2370,c_2139,c_2138,c_2086,c_700,c_689,c_678,c_670,c_653,c_0,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:47:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.52/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/0.92  
% 1.52/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.52/0.92  
% 1.52/0.92  ------  iProver source info
% 1.52/0.92  
% 1.52/0.92  git: date: 2020-06-30 10:37:57 +0100
% 1.52/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.52/0.92  git: non_committed_changes: false
% 1.52/0.92  git: last_make_outside_of_git: false
% 1.52/0.92  
% 1.52/0.92  ------ 
% 1.52/0.92  
% 1.52/0.92  ------ Input Options
% 1.52/0.92  
% 1.52/0.92  --out_options                           all
% 1.52/0.92  --tptp_safe_out                         true
% 1.52/0.92  --problem_path                          ""
% 1.52/0.92  --include_path                          ""
% 1.52/0.92  --clausifier                            res/vclausify_rel
% 1.52/0.92  --clausifier_options                    --mode clausify
% 1.52/0.92  --stdin                                 false
% 1.52/0.92  --stats_out                             all
% 1.52/0.92  
% 1.52/0.92  ------ General Options
% 1.52/0.92  
% 1.52/0.92  --fof                                   false
% 1.52/0.92  --time_out_real                         305.
% 1.52/0.92  --time_out_virtual                      -1.
% 1.52/0.92  --symbol_type_check                     false
% 1.52/0.92  --clausify_out                          false
% 1.52/0.92  --sig_cnt_out                           false
% 1.52/0.92  --trig_cnt_out                          false
% 1.52/0.92  --trig_cnt_out_tolerance                1.
% 1.52/0.92  --trig_cnt_out_sk_spl                   false
% 1.52/0.92  --abstr_cl_out                          false
% 1.52/0.92  
% 1.52/0.92  ------ Global Options
% 1.52/0.92  
% 1.52/0.92  --schedule                              default
% 1.52/0.92  --add_important_lit                     false
% 1.52/0.92  --prop_solver_per_cl                    1000
% 1.52/0.92  --min_unsat_core                        false
% 1.52/0.92  --soft_assumptions                      false
% 1.52/0.92  --soft_lemma_size                       3
% 1.52/0.92  --prop_impl_unit_size                   0
% 1.52/0.92  --prop_impl_unit                        []
% 1.52/0.92  --share_sel_clauses                     true
% 1.52/0.92  --reset_solvers                         false
% 1.52/0.92  --bc_imp_inh                            [conj_cone]
% 1.52/0.92  --conj_cone_tolerance                   3.
% 1.52/0.92  --extra_neg_conj                        none
% 1.52/0.92  --large_theory_mode                     true
% 1.52/0.92  --prolific_symb_bound                   200
% 1.52/0.92  --lt_threshold                          2000
% 1.52/0.92  --clause_weak_htbl                      true
% 1.52/0.92  --gc_record_bc_elim                     false
% 1.52/0.92  
% 1.52/0.92  ------ Preprocessing Options
% 1.52/0.92  
% 1.52/0.92  --preprocessing_flag                    true
% 1.52/0.92  --time_out_prep_mult                    0.1
% 1.52/0.92  --splitting_mode                        input
% 1.52/0.92  --splitting_grd                         true
% 1.52/0.92  --splitting_cvd                         false
% 1.52/0.92  --splitting_cvd_svl                     false
% 1.52/0.92  --splitting_nvd                         32
% 1.52/0.92  --sub_typing                            true
% 1.52/0.92  --prep_gs_sim                           true
% 1.52/0.92  --prep_unflatten                        true
% 1.52/0.92  --prep_res_sim                          true
% 1.52/0.92  --prep_upred                            true
% 1.52/0.92  --prep_sem_filter                       exhaustive
% 1.52/0.92  --prep_sem_filter_out                   false
% 1.52/0.92  --pred_elim                             true
% 1.52/0.92  --res_sim_input                         true
% 1.52/0.92  --eq_ax_congr_red                       true
% 1.52/0.92  --pure_diseq_elim                       true
% 1.52/0.92  --brand_transform                       false
% 1.52/0.92  --non_eq_to_eq                          false
% 1.52/0.92  --prep_def_merge                        true
% 1.52/0.92  --prep_def_merge_prop_impl              false
% 1.52/0.92  --prep_def_merge_mbd                    true
% 1.52/0.92  --prep_def_merge_tr_red                 false
% 1.52/0.92  --prep_def_merge_tr_cl                  false
% 1.52/0.92  --smt_preprocessing                     true
% 1.52/0.92  --smt_ac_axioms                         fast
% 1.52/0.92  --preprocessed_out                      false
% 1.52/0.92  --preprocessed_stats                    false
% 1.52/0.92  
% 1.52/0.92  ------ Abstraction refinement Options
% 1.52/0.92  
% 1.52/0.92  --abstr_ref                             []
% 1.52/0.92  --abstr_ref_prep                        false
% 1.52/0.92  --abstr_ref_until_sat                   false
% 1.52/0.92  --abstr_ref_sig_restrict                funpre
% 1.52/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 1.52/0.92  --abstr_ref_under                       []
% 1.52/0.92  
% 1.52/0.92  ------ SAT Options
% 1.52/0.92  
% 1.52/0.92  --sat_mode                              false
% 1.52/0.92  --sat_fm_restart_options                ""
% 1.52/0.92  --sat_gr_def                            false
% 1.52/0.92  --sat_epr_types                         true
% 1.52/0.92  --sat_non_cyclic_types                  false
% 1.52/0.92  --sat_finite_models                     false
% 1.52/0.92  --sat_fm_lemmas                         false
% 1.52/0.92  --sat_fm_prep                           false
% 1.52/0.92  --sat_fm_uc_incr                        true
% 1.52/0.92  --sat_out_model                         small
% 1.52/0.92  --sat_out_clauses                       false
% 1.52/0.92  
% 1.52/0.92  ------ QBF Options
% 1.52/0.92  
% 1.52/0.92  --qbf_mode                              false
% 1.52/0.92  --qbf_elim_univ                         false
% 1.52/0.92  --qbf_dom_inst                          none
% 1.52/0.92  --qbf_dom_pre_inst                      false
% 1.52/0.92  --qbf_sk_in                             false
% 1.52/0.92  --qbf_pred_elim                         true
% 1.52/0.92  --qbf_split                             512
% 1.52/0.92  
% 1.52/0.92  ------ BMC1 Options
% 1.52/0.92  
% 1.52/0.92  --bmc1_incremental                      false
% 1.52/0.92  --bmc1_axioms                           reachable_all
% 1.52/0.92  --bmc1_min_bound                        0
% 1.52/0.92  --bmc1_max_bound                        -1
% 1.52/0.92  --bmc1_max_bound_default                -1
% 1.52/0.92  --bmc1_symbol_reachability              true
% 1.52/0.92  --bmc1_property_lemmas                  false
% 1.52/0.92  --bmc1_k_induction                      false
% 1.52/0.92  --bmc1_non_equiv_states                 false
% 1.52/0.92  --bmc1_deadlock                         false
% 1.52/0.92  --bmc1_ucm                              false
% 1.52/0.92  --bmc1_add_unsat_core                   none
% 1.52/0.92  --bmc1_unsat_core_children              false
% 1.52/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 1.52/0.92  --bmc1_out_stat                         full
% 1.52/0.92  --bmc1_ground_init                      false
% 1.52/0.92  --bmc1_pre_inst_next_state              false
% 1.52/0.92  --bmc1_pre_inst_state                   false
% 1.52/0.92  --bmc1_pre_inst_reach_state             false
% 1.52/0.92  --bmc1_out_unsat_core                   false
% 1.52/0.92  --bmc1_aig_witness_out                  false
% 1.52/0.92  --bmc1_verbose                          false
% 1.52/0.92  --bmc1_dump_clauses_tptp                false
% 1.52/0.92  --bmc1_dump_unsat_core_tptp             false
% 1.52/0.92  --bmc1_dump_file                        -
% 1.52/0.92  --bmc1_ucm_expand_uc_limit              128
% 1.52/0.92  --bmc1_ucm_n_expand_iterations          6
% 1.52/0.92  --bmc1_ucm_extend_mode                  1
% 1.52/0.92  --bmc1_ucm_init_mode                    2
% 1.52/0.92  --bmc1_ucm_cone_mode                    none
% 1.52/0.92  --bmc1_ucm_reduced_relation_type        0
% 1.52/0.92  --bmc1_ucm_relax_model                  4
% 1.52/0.92  --bmc1_ucm_full_tr_after_sat            true
% 1.52/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 1.52/0.92  --bmc1_ucm_layered_model                none
% 1.52/0.92  --bmc1_ucm_max_lemma_size               10
% 1.52/0.92  
% 1.52/0.92  ------ AIG Options
% 1.52/0.92  
% 1.52/0.92  --aig_mode                              false
% 1.52/0.92  
% 1.52/0.92  ------ Instantiation Options
% 1.52/0.92  
% 1.52/0.92  --instantiation_flag                    true
% 1.52/0.92  --inst_sos_flag                         false
% 1.52/0.92  --inst_sos_phase                        true
% 1.52/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.52/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.52/0.92  --inst_lit_sel_side                     num_symb
% 1.52/0.92  --inst_solver_per_active                1400
% 1.52/0.92  --inst_solver_calls_frac                1.
% 1.52/0.92  --inst_passive_queue_type               priority_queues
% 1.52/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.52/0.92  --inst_passive_queues_freq              [25;2]
% 1.52/0.92  --inst_dismatching                      true
% 1.52/0.92  --inst_eager_unprocessed_to_passive     true
% 1.52/0.92  --inst_prop_sim_given                   true
% 1.52/0.92  --inst_prop_sim_new                     false
% 1.52/0.92  --inst_subs_new                         false
% 1.52/0.92  --inst_eq_res_simp                      false
% 1.52/0.92  --inst_subs_given                       false
% 1.52/0.92  --inst_orphan_elimination               true
% 1.52/0.92  --inst_learning_loop_flag               true
% 1.52/0.92  --inst_learning_start                   3000
% 1.52/0.92  --inst_learning_factor                  2
% 1.52/0.92  --inst_start_prop_sim_after_learn       3
% 1.52/0.92  --inst_sel_renew                        solver
% 1.52/0.92  --inst_lit_activity_flag                true
% 1.52/0.92  --inst_restr_to_given                   false
% 1.52/0.92  --inst_activity_threshold               500
% 1.52/0.92  --inst_out_proof                        true
% 1.52/0.92  
% 1.52/0.92  ------ Resolution Options
% 1.52/0.92  
% 1.52/0.92  --resolution_flag                       true
% 1.52/0.92  --res_lit_sel                           adaptive
% 1.52/0.92  --res_lit_sel_side                      none
% 1.52/0.92  --res_ordering                          kbo
% 1.52/0.92  --res_to_prop_solver                    active
% 1.52/0.92  --res_prop_simpl_new                    false
% 1.52/0.92  --res_prop_simpl_given                  true
% 1.52/0.92  --res_passive_queue_type                priority_queues
% 1.52/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.52/0.92  --res_passive_queues_freq               [15;5]
% 1.52/0.92  --res_forward_subs                      full
% 1.52/0.92  --res_backward_subs                     full
% 1.52/0.92  --res_forward_subs_resolution           true
% 1.52/0.92  --res_backward_subs_resolution          true
% 1.52/0.92  --res_orphan_elimination                true
% 1.52/0.92  --res_time_limit                        2.
% 1.52/0.92  --res_out_proof                         true
% 1.52/0.92  
% 1.52/0.92  ------ Superposition Options
% 1.52/0.92  
% 1.52/0.92  --superposition_flag                    true
% 1.52/0.92  --sup_passive_queue_type                priority_queues
% 1.52/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.52/0.92  --sup_passive_queues_freq               [8;1;4]
% 1.52/0.92  --demod_completeness_check              fast
% 1.52/0.92  --demod_use_ground                      true
% 1.52/0.92  --sup_to_prop_solver                    passive
% 1.52/0.92  --sup_prop_simpl_new                    true
% 1.52/0.92  --sup_prop_simpl_given                  true
% 1.52/0.92  --sup_fun_splitting                     false
% 1.52/0.92  --sup_smt_interval                      50000
% 1.52/0.92  
% 1.52/0.92  ------ Superposition Simplification Setup
% 1.52/0.92  
% 1.52/0.92  --sup_indices_passive                   []
% 1.52/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 1.52/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.92  --sup_full_bw                           [BwDemod]
% 1.52/0.92  --sup_immed_triv                        [TrivRules]
% 1.52/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.52/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.92  --sup_immed_bw_main                     []
% 1.52/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 1.52/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.92  
% 1.52/0.92  ------ Combination Options
% 1.52/0.92  
% 1.52/0.92  --comb_res_mult                         3
% 1.52/0.92  --comb_sup_mult                         2
% 1.52/0.92  --comb_inst_mult                        10
% 1.52/0.92  
% 1.52/0.92  ------ Debug Options
% 1.52/0.92  
% 1.52/0.92  --dbg_backtrace                         false
% 1.52/0.92  --dbg_dump_prop_clauses                 false
% 1.52/0.92  --dbg_dump_prop_clauses_file            -
% 1.52/0.92  --dbg_out_stat                          false
% 1.52/0.92  ------ Parsing...
% 1.52/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.52/0.92  
% 1.52/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.52/0.92  
% 1.52/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.52/0.92  
% 1.52/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.52/0.92  ------ Proving...
% 1.52/0.92  ------ Problem Properties 
% 1.52/0.92  
% 1.52/0.92  
% 1.52/0.92  clauses                                 19
% 1.52/0.92  conjectures                             2
% 1.52/0.92  EPR                                     8
% 1.52/0.92  Horn                                    14
% 1.52/0.92  unary                                   7
% 1.52/0.92  binary                                  2
% 1.52/0.92  lits                                    51
% 1.52/0.92  lits eq                                 6
% 1.52/0.92  fd_pure                                 0
% 1.52/0.92  fd_pseudo                               0
% 1.52/0.92  fd_cond                                 1
% 1.52/0.92  fd_pseudo_cond                          4
% 1.52/0.92  AC symbols                              0
% 1.52/0.92  
% 1.52/0.92  ------ Schedule dynamic 5 is on 
% 1.52/0.92  
% 1.52/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.52/0.92  
% 1.52/0.92  
% 1.52/0.92  ------ 
% 1.52/0.92  Current options:
% 1.52/0.92  ------ 
% 1.52/0.92  
% 1.52/0.92  ------ Input Options
% 1.52/0.92  
% 1.52/0.92  --out_options                           all
% 1.52/0.92  --tptp_safe_out                         true
% 1.52/0.92  --problem_path                          ""
% 1.52/0.92  --include_path                          ""
% 1.52/0.92  --clausifier                            res/vclausify_rel
% 1.52/0.92  --clausifier_options                    --mode clausify
% 1.52/0.92  --stdin                                 false
% 1.52/0.92  --stats_out                             all
% 1.52/0.92  
% 1.52/0.92  ------ General Options
% 1.52/0.92  
% 1.52/0.92  --fof                                   false
% 1.52/0.92  --time_out_real                         305.
% 1.52/0.92  --time_out_virtual                      -1.
% 1.52/0.92  --symbol_type_check                     false
% 1.52/0.92  --clausify_out                          false
% 1.52/0.92  --sig_cnt_out                           false
% 1.52/0.92  --trig_cnt_out                          false
% 1.52/0.92  --trig_cnt_out_tolerance                1.
% 1.52/0.92  --trig_cnt_out_sk_spl                   false
% 1.52/0.92  --abstr_cl_out                          false
% 1.52/0.92  
% 1.52/0.92  ------ Global Options
% 1.52/0.92  
% 1.52/0.92  --schedule                              default
% 1.52/0.92  --add_important_lit                     false
% 1.52/0.92  --prop_solver_per_cl                    1000
% 1.52/0.92  --min_unsat_core                        false
% 1.52/0.92  --soft_assumptions                      false
% 1.52/0.92  --soft_lemma_size                       3
% 1.52/0.92  --prop_impl_unit_size                   0
% 1.52/0.92  --prop_impl_unit                        []
% 1.52/0.92  --share_sel_clauses                     true
% 1.52/0.92  --reset_solvers                         false
% 1.52/0.92  --bc_imp_inh                            [conj_cone]
% 1.52/0.92  --conj_cone_tolerance                   3.
% 1.52/0.92  --extra_neg_conj                        none
% 1.52/0.92  --large_theory_mode                     true
% 1.52/0.92  --prolific_symb_bound                   200
% 1.52/0.92  --lt_threshold                          2000
% 1.52/0.92  --clause_weak_htbl                      true
% 1.52/0.92  --gc_record_bc_elim                     false
% 1.52/0.92  
% 1.52/0.92  ------ Preprocessing Options
% 1.52/0.92  
% 1.52/0.92  --preprocessing_flag                    true
% 1.52/0.92  --time_out_prep_mult                    0.1
% 1.52/0.92  --splitting_mode                        input
% 1.52/0.92  --splitting_grd                         true
% 1.52/0.92  --splitting_cvd                         false
% 1.52/0.92  --splitting_cvd_svl                     false
% 1.52/0.92  --splitting_nvd                         32
% 1.52/0.92  --sub_typing                            true
% 1.52/0.92  --prep_gs_sim                           true
% 1.52/0.92  --prep_unflatten                        true
% 1.52/0.92  --prep_res_sim                          true
% 1.52/0.92  --prep_upred                            true
% 1.52/0.92  --prep_sem_filter                       exhaustive
% 1.52/0.92  --prep_sem_filter_out                   false
% 1.52/0.92  --pred_elim                             true
% 1.52/0.92  --res_sim_input                         true
% 1.52/0.92  --eq_ax_congr_red                       true
% 1.52/0.92  --pure_diseq_elim                       true
% 1.52/0.92  --brand_transform                       false
% 1.52/0.92  --non_eq_to_eq                          false
% 1.52/0.92  --prep_def_merge                        true
% 1.52/0.92  --prep_def_merge_prop_impl              false
% 1.52/0.92  --prep_def_merge_mbd                    true
% 1.52/0.92  --prep_def_merge_tr_red                 false
% 1.52/0.92  --prep_def_merge_tr_cl                  false
% 1.52/0.92  --smt_preprocessing                     true
% 1.52/0.92  --smt_ac_axioms                         fast
% 1.52/0.92  --preprocessed_out                      false
% 1.52/0.92  --preprocessed_stats                    false
% 1.52/0.92  
% 1.52/0.92  ------ Abstraction refinement Options
% 1.52/0.92  
% 1.52/0.92  --abstr_ref                             []
% 1.52/0.92  --abstr_ref_prep                        false
% 1.52/0.92  --abstr_ref_until_sat                   false
% 1.52/0.92  --abstr_ref_sig_restrict                funpre
% 1.52/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 1.52/0.92  --abstr_ref_under                       []
% 1.52/0.92  
% 1.52/0.92  ------ SAT Options
% 1.52/0.92  
% 1.52/0.92  --sat_mode                              false
% 1.52/0.92  --sat_fm_restart_options                ""
% 1.52/0.92  --sat_gr_def                            false
% 1.52/0.92  --sat_epr_types                         true
% 1.52/0.92  --sat_non_cyclic_types                  false
% 1.52/0.92  --sat_finite_models                     false
% 1.52/0.92  --sat_fm_lemmas                         false
% 1.52/0.92  --sat_fm_prep                           false
% 1.52/0.92  --sat_fm_uc_incr                        true
% 1.52/0.92  --sat_out_model                         small
% 1.52/0.92  --sat_out_clauses                       false
% 1.52/0.92  
% 1.52/0.92  ------ QBF Options
% 1.52/0.92  
% 1.52/0.92  --qbf_mode                              false
% 1.52/0.92  --qbf_elim_univ                         false
% 1.52/0.92  --qbf_dom_inst                          none
% 1.52/0.92  --qbf_dom_pre_inst                      false
% 1.52/0.92  --qbf_sk_in                             false
% 1.52/0.92  --qbf_pred_elim                         true
% 1.52/0.92  --qbf_split                             512
% 1.52/0.92  
% 1.52/0.92  ------ BMC1 Options
% 1.52/0.92  
% 1.52/0.92  --bmc1_incremental                      false
% 1.52/0.92  --bmc1_axioms                           reachable_all
% 1.52/0.92  --bmc1_min_bound                        0
% 1.52/0.92  --bmc1_max_bound                        -1
% 1.52/0.92  --bmc1_max_bound_default                -1
% 1.52/0.92  --bmc1_symbol_reachability              true
% 1.52/0.92  --bmc1_property_lemmas                  false
% 1.52/0.92  --bmc1_k_induction                      false
% 1.52/0.92  --bmc1_non_equiv_states                 false
% 1.52/0.92  --bmc1_deadlock                         false
% 1.52/0.92  --bmc1_ucm                              false
% 1.52/0.92  --bmc1_add_unsat_core                   none
% 1.52/0.92  --bmc1_unsat_core_children              false
% 1.52/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 1.52/0.92  --bmc1_out_stat                         full
% 1.52/0.92  --bmc1_ground_init                      false
% 1.52/0.92  --bmc1_pre_inst_next_state              false
% 1.52/0.92  --bmc1_pre_inst_state                   false
% 1.52/0.92  --bmc1_pre_inst_reach_state             false
% 1.52/0.92  --bmc1_out_unsat_core                   false
% 1.52/0.92  --bmc1_aig_witness_out                  false
% 1.52/0.92  --bmc1_verbose                          false
% 1.52/0.92  --bmc1_dump_clauses_tptp                false
% 1.52/0.92  --bmc1_dump_unsat_core_tptp             false
% 1.52/0.92  --bmc1_dump_file                        -
% 1.52/0.92  --bmc1_ucm_expand_uc_limit              128
% 1.52/0.92  --bmc1_ucm_n_expand_iterations          6
% 1.52/0.92  --bmc1_ucm_extend_mode                  1
% 1.52/0.92  --bmc1_ucm_init_mode                    2
% 1.52/0.92  --bmc1_ucm_cone_mode                    none
% 1.52/0.92  --bmc1_ucm_reduced_relation_type        0
% 1.52/0.92  --bmc1_ucm_relax_model                  4
% 1.52/0.92  --bmc1_ucm_full_tr_after_sat            true
% 1.52/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 1.52/0.92  --bmc1_ucm_layered_model                none
% 1.52/0.92  --bmc1_ucm_max_lemma_size               10
% 1.52/0.92  
% 1.52/0.92  ------ AIG Options
% 1.52/0.92  
% 1.52/0.92  --aig_mode                              false
% 1.52/0.92  
% 1.52/0.92  ------ Instantiation Options
% 1.52/0.92  
% 1.52/0.92  --instantiation_flag                    true
% 1.52/0.92  --inst_sos_flag                         false
% 1.52/0.92  --inst_sos_phase                        true
% 1.52/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.52/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.52/0.92  --inst_lit_sel_side                     none
% 1.52/0.92  --inst_solver_per_active                1400
% 1.52/0.92  --inst_solver_calls_frac                1.
% 1.52/0.92  --inst_passive_queue_type               priority_queues
% 1.52/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.52/0.92  --inst_passive_queues_freq              [25;2]
% 1.52/0.92  --inst_dismatching                      true
% 1.52/0.92  --inst_eager_unprocessed_to_passive     true
% 1.52/0.92  --inst_prop_sim_given                   true
% 1.52/0.92  --inst_prop_sim_new                     false
% 1.52/0.92  --inst_subs_new                         false
% 1.52/0.92  --inst_eq_res_simp                      false
% 1.52/0.92  --inst_subs_given                       false
% 1.52/0.92  --inst_orphan_elimination               true
% 1.52/0.92  --inst_learning_loop_flag               true
% 1.52/0.92  --inst_learning_start                   3000
% 1.52/0.92  --inst_learning_factor                  2
% 1.52/0.92  --inst_start_prop_sim_after_learn       3
% 1.52/0.92  --inst_sel_renew                        solver
% 1.52/0.92  --inst_lit_activity_flag                true
% 1.52/0.92  --inst_restr_to_given                   false
% 1.52/0.92  --inst_activity_threshold               500
% 1.52/0.92  --inst_out_proof                        true
% 1.52/0.92  
% 1.52/0.92  ------ Resolution Options
% 1.52/0.92  
% 1.52/0.92  --resolution_flag                       false
% 1.52/0.92  --res_lit_sel                           adaptive
% 1.52/0.92  --res_lit_sel_side                      none
% 1.52/0.92  --res_ordering                          kbo
% 1.52/0.92  --res_to_prop_solver                    active
% 1.52/0.92  --res_prop_simpl_new                    false
% 1.52/0.92  --res_prop_simpl_given                  true
% 1.52/0.92  --res_passive_queue_type                priority_queues
% 1.52/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.52/0.92  --res_passive_queues_freq               [15;5]
% 1.52/0.92  --res_forward_subs                      full
% 1.52/0.92  --res_backward_subs                     full
% 1.52/0.92  --res_forward_subs_resolution           true
% 1.52/0.92  --res_backward_subs_resolution          true
% 1.52/0.92  --res_orphan_elimination                true
% 1.52/0.92  --res_time_limit                        2.
% 1.52/0.92  --res_out_proof                         true
% 1.52/0.92  
% 1.52/0.92  ------ Superposition Options
% 1.52/0.92  
% 1.52/0.92  --superposition_flag                    true
% 1.52/0.92  --sup_passive_queue_type                priority_queues
% 1.52/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.52/0.92  --sup_passive_queues_freq               [8;1;4]
% 1.52/0.92  --demod_completeness_check              fast
% 1.52/0.92  --demod_use_ground                      true
% 1.52/0.92  --sup_to_prop_solver                    passive
% 1.52/0.92  --sup_prop_simpl_new                    true
% 1.52/0.92  --sup_prop_simpl_given                  true
% 1.52/0.92  --sup_fun_splitting                     false
% 1.52/0.92  --sup_smt_interval                      50000
% 1.52/0.92  
% 1.52/0.92  ------ Superposition Simplification Setup
% 1.52/0.92  
% 1.52/0.92  --sup_indices_passive                   []
% 1.52/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.52/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 1.52/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.92  --sup_full_bw                           [BwDemod]
% 1.52/0.92  --sup_immed_triv                        [TrivRules]
% 1.52/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.52/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.92  --sup_immed_bw_main                     []
% 1.52/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 1.52/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.52/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.52/0.92  
% 1.52/0.92  ------ Combination Options
% 1.52/0.92  
% 1.52/0.92  --comb_res_mult                         3
% 1.52/0.92  --comb_sup_mult                         2
% 1.52/0.92  --comb_inst_mult                        10
% 1.52/0.92  
% 1.52/0.92  ------ Debug Options
% 1.52/0.92  
% 1.52/0.92  --dbg_backtrace                         false
% 1.52/0.92  --dbg_dump_prop_clauses                 false
% 1.52/0.92  --dbg_dump_prop_clauses_file            -
% 1.52/0.92  --dbg_out_stat                          false
% 1.52/0.92  
% 1.52/0.92  
% 1.52/0.92  
% 1.52/0.92  
% 1.52/0.92  ------ Proving...
% 1.52/0.92  
% 1.52/0.92  
% 1.52/0.92  % SZS status Theorem for theBenchmark.p
% 1.52/0.92  
% 1.52/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 1.52/0.92  
% 1.52/0.92  fof(f3,axiom,(
% 1.52/0.92    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.52/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.92  
% 1.52/0.92  fof(f14,plain,(
% 1.52/0.92    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.52/0.92    inference(ennf_transformation,[],[f3])).
% 1.52/0.92  
% 1.52/0.92  fof(f43,plain,(
% 1.52/0.92    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.52/0.92    inference(cnf_transformation,[],[f14])).
% 1.52/0.92  
% 1.52/0.92  fof(f2,axiom,(
% 1.52/0.92    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.52/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.92  
% 1.52/0.92  fof(f25,plain,(
% 1.52/0.92    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.92    inference(nnf_transformation,[],[f2])).
% 1.52/0.92  
% 1.52/0.92  fof(f26,plain,(
% 1.52/0.92    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.92    inference(flattening,[],[f25])).
% 1.52/0.92  
% 1.52/0.92  fof(f42,plain,(
% 1.52/0.92    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.52/0.92    inference(cnf_transformation,[],[f26])).
% 1.52/0.92  
% 1.52/0.92  fof(f4,axiom,(
% 1.52/0.92    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.52/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.92  
% 1.52/0.92  fof(f44,plain,(
% 1.52/0.92    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.52/0.92    inference(cnf_transformation,[],[f4])).
% 1.52/0.92  
% 1.52/0.92  fof(f5,axiom,(
% 1.52/0.92    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.52/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.92  
% 1.52/0.92  fof(f27,plain,(
% 1.52/0.92    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.52/0.92    inference(nnf_transformation,[],[f5])).
% 1.52/0.92  
% 1.52/0.92  fof(f45,plain,(
% 1.52/0.92    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.52/0.92    inference(cnf_transformation,[],[f27])).
% 1.52/0.92  
% 1.52/0.92  fof(f9,axiom,(
% 1.52/0.92    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.52/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.92  
% 1.52/0.92  fof(f19,plain,(
% 1.52/0.92    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.52/0.92    inference(ennf_transformation,[],[f9])).
% 1.52/0.92  
% 1.52/0.92  fof(f20,plain,(
% 1.52/0.92    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.52/0.92    inference(flattening,[],[f19])).
% 1.52/0.92  
% 1.52/0.92  fof(f54,plain,(
% 1.52/0.92    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.52/0.92    inference(cnf_transformation,[],[f20])).
% 1.52/0.92  
% 1.52/0.92  fof(f10,axiom,(
% 1.52/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.52/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.92  
% 1.52/0.92  fof(f21,plain,(
% 1.52/0.92    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.52/0.92    inference(ennf_transformation,[],[f10])).
% 1.52/0.92  
% 1.52/0.92  fof(f22,plain,(
% 1.52/0.92    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.52/0.92    inference(flattening,[],[f21])).
% 1.52/0.92  
% 1.52/0.92  fof(f33,plain,(
% 1.52/0.92    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.52/0.92    inference(nnf_transformation,[],[f22])).
% 1.52/0.92  
% 1.52/0.92  fof(f55,plain,(
% 1.52/0.92    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.52/0.92    inference(cnf_transformation,[],[f33])).
% 1.52/0.92  
% 1.52/0.92  fof(f11,conjecture,(
% 1.52/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.52/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.92  
% 1.52/0.92  fof(f12,negated_conjecture,(
% 1.52/0.92    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.52/0.92    inference(negated_conjecture,[],[f11])).
% 1.52/0.92  
% 1.52/0.92  fof(f23,plain,(
% 1.52/0.92    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.52/0.92    inference(ennf_transformation,[],[f12])).
% 1.52/0.92  
% 1.52/0.92  fof(f24,plain,(
% 1.52/0.92    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.52/0.92    inference(flattening,[],[f23])).
% 1.52/0.92  
% 1.52/0.92  fof(f34,plain,(
% 1.52/0.92    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.52/0.92    inference(nnf_transformation,[],[f24])).
% 1.52/0.92  
% 1.52/0.92  fof(f35,plain,(
% 1.52/0.92    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.52/0.92    inference(flattening,[],[f34])).
% 1.52/0.92  
% 1.52/0.92  fof(f37,plain,(
% 1.52/0.92    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK2) | ~v3_tex_2(sK2,X0)) & (v1_zfmisc_1(sK2) | v3_tex_2(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK2))) )),
% 1.52/0.92    introduced(choice_axiom,[])).
% 1.52/0.92  
% 1.52/0.92  fof(f36,plain,(
% 1.52/0.92    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK1)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK1) & v2_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.52/0.92    introduced(choice_axiom,[])).
% 1.52/0.92  
% 1.52/0.92  fof(f38,plain,(
% 1.52/0.92    ((~v1_zfmisc_1(sK2) | ~v3_tex_2(sK2,sK1)) & (v1_zfmisc_1(sK2) | v3_tex_2(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(sK2)) & l1_pre_topc(sK1) & v2_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.52/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f35,f37,f36])).
% 1.52/0.92  
% 1.52/0.92  fof(f57,plain,(
% 1.52/0.92    ~v2_struct_0(sK1)),
% 1.52/0.92    inference(cnf_transformation,[],[f38])).
% 1.52/0.92  
% 1.52/0.92  fof(f58,plain,(
% 1.52/0.92    v2_pre_topc(sK1)),
% 1.52/0.92    inference(cnf_transformation,[],[f38])).
% 1.52/0.92  
% 1.52/0.92  fof(f59,plain,(
% 1.52/0.92    v2_tdlat_3(sK1)),
% 1.52/0.92    inference(cnf_transformation,[],[f38])).
% 1.52/0.92  
% 1.52/0.92  fof(f60,plain,(
% 1.52/0.92    l1_pre_topc(sK1)),
% 1.52/0.92    inference(cnf_transformation,[],[f38])).
% 1.52/0.92  
% 1.52/0.92  fof(f64,plain,(
% 1.52/0.92    ~v1_zfmisc_1(sK2) | ~v3_tex_2(sK2,sK1)),
% 1.52/0.92    inference(cnf_transformation,[],[f38])).
% 1.52/0.92  
% 1.52/0.92  fof(f61,plain,(
% 1.52/0.92    ~v1_xboole_0(sK2)),
% 1.52/0.92    inference(cnf_transformation,[],[f38])).
% 1.52/0.92  
% 1.52/0.92  fof(f62,plain,(
% 1.52/0.92    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.52/0.92    inference(cnf_transformation,[],[f38])).
% 1.52/0.92  
% 1.52/0.92  fof(f8,axiom,(
% 1.52/0.92    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.52/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.92  
% 1.52/0.92  fof(f17,plain,(
% 1.52/0.92    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.52/0.92    inference(ennf_transformation,[],[f8])).
% 1.52/0.92  
% 1.52/0.92  fof(f18,plain,(
% 1.52/0.92    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.52/0.92    inference(flattening,[],[f17])).
% 1.52/0.92  
% 1.52/0.92  fof(f28,plain,(
% 1.52/0.92    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.52/0.92    inference(nnf_transformation,[],[f18])).
% 1.52/0.92  
% 1.52/0.92  fof(f29,plain,(
% 1.52/0.92    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.52/0.92    inference(flattening,[],[f28])).
% 1.52/0.92  
% 1.52/0.92  fof(f30,plain,(
% 1.52/0.92    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.52/0.92    inference(rectify,[],[f29])).
% 1.52/0.92  
% 1.52/0.92  fof(f31,plain,(
% 1.52/0.92    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.52/0.92    introduced(choice_axiom,[])).
% 1.52/0.92  
% 1.52/0.92  fof(f32,plain,(
% 1.52/0.92    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.52/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 1.52/0.92  
% 1.52/0.92  fof(f50,plain,(
% 1.52/0.92    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.52/0.92    inference(cnf_transformation,[],[f32])).
% 1.52/0.92  
% 1.52/0.92  fof(f51,plain,(
% 1.52/0.92    ( ! [X0,X1] : (v3_tex_2(X1,X0) | v2_tex_2(sK0(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.52/0.92    inference(cnf_transformation,[],[f32])).
% 1.52/0.92  
% 1.52/0.92  fof(f52,plain,(
% 1.52/0.92    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK0(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.52/0.92    inference(cnf_transformation,[],[f32])).
% 1.52/0.92  
% 1.52/0.92  fof(f53,plain,(
% 1.52/0.92    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK0(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.52/0.92    inference(cnf_transformation,[],[f32])).
% 1.52/0.93  
% 1.52/0.93  fof(f56,plain,(
% 1.52/0.93    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.52/0.93    inference(cnf_transformation,[],[f33])).
% 1.52/0.93  
% 1.52/0.93  fof(f63,plain,(
% 1.52/0.93    v1_zfmisc_1(sK2) | v3_tex_2(sK2,sK1)),
% 1.52/0.93    inference(cnf_transformation,[],[f38])).
% 1.52/0.93  
% 1.52/0.93  fof(f48,plain,(
% 1.52/0.93    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.52/0.93    inference(cnf_transformation,[],[f32])).
% 1.52/0.93  
% 1.52/0.93  fof(f1,axiom,(
% 1.52/0.93    v1_xboole_0(k1_xboole_0)),
% 1.52/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.52/0.93  
% 1.52/0.93  fof(f39,plain,(
% 1.52/0.93    v1_xboole_0(k1_xboole_0)),
% 1.52/0.93    inference(cnf_transformation,[],[f1])).
% 1.52/0.93  
% 1.52/0.93  cnf(c_1379,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_2094,plain,
% 1.52/0.93      ( sK0(sK1,sK2) != X0 | sK0(sK1,sK2) = sK2 | sK2 != X0 ),
% 1.52/0.93      inference(instantiation,[status(thm)],[c_1379]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_3805,plain,
% 1.52/0.93      ( sK0(sK1,sK2) = sK2
% 1.52/0.93      | sK0(sK1,sK2) != k1_xboole_0
% 1.52/0.93      | sK2 != k1_xboole_0 ),
% 1.52/0.93      inference(instantiation,[status(thm)],[c_2094]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_1381,plain,
% 1.52/0.93      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,X2) | X2 != X1 ),
% 1.52/0.93      theory(equality) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_2554,plain,
% 1.52/0.93      ( ~ r1_tarski(sK2,X0)
% 1.52/0.93      | r1_tarski(sK2,k1_xboole_0)
% 1.52/0.93      | k1_xboole_0 != X0 ),
% 1.52/0.93      inference(instantiation,[status(thm)],[c_1381]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_3120,plain,
% 1.52/0.93      ( ~ r1_tarski(sK2,sK0(sK1,sK2))
% 1.52/0.93      | r1_tarski(sK2,k1_xboole_0)
% 1.52/0.93      | k1_xboole_0 != sK0(sK1,sK2) ),
% 1.52/0.93      inference(instantiation,[status(thm)],[c_2554]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_4,plain,
% 1.52/0.93      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 1.52/0.93      inference(cnf_transformation,[],[f43]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_2271,plain,
% 1.52/0.93      ( ~ v1_xboole_0(X0)
% 1.52/0.93      | ~ v1_xboole_0(k1_xboole_0)
% 1.52/0.93      | X0 = k1_xboole_0 ),
% 1.52/0.93      inference(instantiation,[status(thm)],[c_4]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_2665,plain,
% 1.52/0.93      ( ~ v1_xboole_0(sK0(sK1,sK2))
% 1.52/0.93      | ~ v1_xboole_0(k1_xboole_0)
% 1.52/0.93      | sK0(sK1,sK2) = k1_xboole_0 ),
% 1.52/0.93      inference(instantiation,[status(thm)],[c_2271]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_2228,plain,
% 1.52/0.93      ( ~ v1_xboole_0(X0)
% 1.52/0.93      | ~ v1_xboole_0(sK0(sK1,sK2))
% 1.52/0.93      | X0 = sK0(sK1,sK2) ),
% 1.52/0.93      inference(instantiation,[status(thm)],[c_4]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_2470,plain,
% 1.52/0.93      ( ~ v1_xboole_0(sK0(sK1,sK2))
% 1.52/0.93      | ~ v1_xboole_0(k1_xboole_0)
% 1.52/0.93      | k1_xboole_0 = sK0(sK1,sK2) ),
% 1.52/0.93      inference(instantiation,[status(thm)],[c_2228]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_1,plain,
% 1.52/0.93      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.52/0.93      inference(cnf_transformation,[],[f42]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_2149,plain,
% 1.52/0.93      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 1.52/0.93      inference(instantiation,[status(thm)],[c_1]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_2370,plain,
% 1.52/0.93      ( ~ r1_tarski(sK2,k1_xboole_0)
% 1.52/0.93      | ~ r1_tarski(k1_xboole_0,sK2)
% 1.52/0.93      | sK2 = k1_xboole_0 ),
% 1.52/0.93      inference(instantiation,[status(thm)],[c_2149]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_5,plain,
% 1.52/0.93      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.52/0.93      inference(cnf_transformation,[],[f44]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_2139,plain,
% 1.52/0.93      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
% 1.52/0.93      inference(instantiation,[status(thm)],[c_5]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_7,plain,
% 1.52/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.52/0.93      inference(cnf_transformation,[],[f45]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_2022,plain,
% 1.52/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) | r1_tarski(X0,sK2) ),
% 1.52/0.93      inference(instantiation,[status(thm)],[c_7]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_2138,plain,
% 1.52/0.93      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
% 1.52/0.93      | r1_tarski(k1_xboole_0,sK2) ),
% 1.52/0.93      inference(instantiation,[status(thm)],[c_2022]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_15,plain,
% 1.52/0.93      ( ~ r1_tarski(X0,X1)
% 1.52/0.93      | ~ v1_zfmisc_1(X1)
% 1.52/0.93      | v1_xboole_0(X1)
% 1.52/0.93      | v1_xboole_0(X0)
% 1.52/0.93      | X1 = X0 ),
% 1.52/0.93      inference(cnf_transformation,[],[f54]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_17,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,X1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.52/0.93      | v2_struct_0(X1)
% 1.52/0.93      | v1_zfmisc_1(X0)
% 1.52/0.93      | ~ l1_pre_topc(X1)
% 1.52/0.93      | ~ v2_tdlat_3(X1)
% 1.52/0.93      | ~ v2_pre_topc(X1)
% 1.52/0.93      | v1_xboole_0(X0) ),
% 1.52/0.93      inference(cnf_transformation,[],[f55]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_25,negated_conjecture,
% 1.52/0.93      ( ~ v2_struct_0(sK1) ),
% 1.52/0.93      inference(cnf_transformation,[],[f57]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_338,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,X1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.52/0.93      | v1_zfmisc_1(X0)
% 1.52/0.93      | ~ l1_pre_topc(X1)
% 1.52/0.93      | ~ v2_tdlat_3(X1)
% 1.52/0.93      | ~ v2_pre_topc(X1)
% 1.52/0.93      | v1_xboole_0(X0)
% 1.52/0.93      | sK1 != X1 ),
% 1.52/0.93      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_339,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,sK1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | v1_zfmisc_1(X0)
% 1.52/0.93      | ~ l1_pre_topc(sK1)
% 1.52/0.93      | ~ v2_tdlat_3(sK1)
% 1.52/0.93      | ~ v2_pre_topc(sK1)
% 1.52/0.93      | v1_xboole_0(X0) ),
% 1.52/0.93      inference(unflattening,[status(thm)],[c_338]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_24,negated_conjecture,
% 1.52/0.93      ( v2_pre_topc(sK1) ),
% 1.52/0.93      inference(cnf_transformation,[],[f58]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_23,negated_conjecture,
% 1.52/0.93      ( v2_tdlat_3(sK1) ),
% 1.52/0.93      inference(cnf_transformation,[],[f59]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_22,negated_conjecture,
% 1.52/0.93      ( l1_pre_topc(sK1) ),
% 1.52/0.93      inference(cnf_transformation,[],[f60]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_343,plain,
% 1.52/0.93      ( v1_zfmisc_1(X0)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | ~ v2_tex_2(X0,sK1)
% 1.52/0.93      | v1_xboole_0(X0) ),
% 1.52/0.93      inference(global_propositional_subsumption,
% 1.52/0.93                [status(thm)],
% 1.52/0.93                [c_339,c_24,c_23,c_22]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_344,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,sK1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | v1_zfmisc_1(X0)
% 1.52/0.93      | v1_xboole_0(X0) ),
% 1.52/0.93      inference(renaming,[status(thm)],[c_343]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_538,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,sK1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | ~ r1_tarski(X1,X2)
% 1.52/0.93      | v1_xboole_0(X2)
% 1.52/0.93      | v1_xboole_0(X1)
% 1.52/0.93      | v1_xboole_0(X0)
% 1.52/0.93      | X0 != X2
% 1.52/0.93      | X2 = X1 ),
% 1.52/0.93      inference(resolution_lifted,[status(thm)],[c_15,c_344]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_539,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,sK1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | ~ r1_tarski(X1,X0)
% 1.52/0.93      | v1_xboole_0(X1)
% 1.52/0.93      | v1_xboole_0(X0)
% 1.52/0.93      | X0 = X1 ),
% 1.52/0.93      inference(unflattening,[status(thm)],[c_538]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_2086,plain,
% 1.52/0.93      ( ~ v2_tex_2(sK0(sK1,sK2),sK1)
% 1.52/0.93      | ~ m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | ~ r1_tarski(sK2,sK0(sK1,sK2))
% 1.52/0.93      | v1_xboole_0(sK0(sK1,sK2))
% 1.52/0.93      | v1_xboole_0(sK2)
% 1.52/0.93      | sK0(sK1,sK2) = sK2 ),
% 1.52/0.93      inference(instantiation,[status(thm)],[c_539]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_18,negated_conjecture,
% 1.52/0.93      ( ~ v3_tex_2(sK2,sK1) | ~ v1_zfmisc_1(sK2) ),
% 1.52/0.93      inference(cnf_transformation,[],[f64]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_193,plain,
% 1.52/0.93      ( ~ v1_zfmisc_1(sK2) | ~ v3_tex_2(sK2,sK1) ),
% 1.52/0.93      inference(prop_impl,[status(thm)],[c_18]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_194,plain,
% 1.52/0.93      ( ~ v3_tex_2(sK2,sK1) | ~ v1_zfmisc_1(sK2) ),
% 1.52/0.93      inference(renaming,[status(thm)],[c_193]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_584,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,sK1)
% 1.52/0.93      | ~ v3_tex_2(sK2,sK1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | v1_xboole_0(X0)
% 1.52/0.93      | sK2 != X0 ),
% 1.52/0.93      inference(resolution_lifted,[status(thm)],[c_344,c_194]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_585,plain,
% 1.52/0.93      ( ~ v2_tex_2(sK2,sK1)
% 1.52/0.93      | ~ v3_tex_2(sK2,sK1)
% 1.52/0.93      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | v1_xboole_0(sK2) ),
% 1.52/0.93      inference(unflattening,[status(thm)],[c_584]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_21,negated_conjecture,
% 1.52/0.93      ( ~ v1_xboole_0(sK2) ),
% 1.52/0.93      inference(cnf_transformation,[],[f61]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_20,negated_conjecture,
% 1.52/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.52/0.93      inference(cnf_transformation,[],[f62]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_587,plain,
% 1.52/0.93      ( ~ v2_tex_2(sK2,sK1) | ~ v3_tex_2(sK2,sK1) ),
% 1.52/0.93      inference(global_propositional_subsumption,
% 1.52/0.93                [status(thm)],
% 1.52/0.93                [c_585,c_21,c_20]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_12,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,X1)
% 1.52/0.93      | v3_tex_2(X0,X1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.52/0.93      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.52/0.93      | ~ l1_pre_topc(X1) ),
% 1.52/0.93      inference(cnf_transformation,[],[f50]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_433,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,X1)
% 1.52/0.93      | v3_tex_2(X0,X1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.52/0.93      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.52/0.93      | sK1 != X1 ),
% 1.52/0.93      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_434,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,sK1)
% 1.52/0.93      | v3_tex_2(X0,sK1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.52/0.93      inference(unflattening,[status(thm)],[c_433]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_699,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,sK1)
% 1.52/0.93      | ~ v2_tex_2(sK2,sK1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | sK1 != sK1
% 1.52/0.93      | sK2 != X0 ),
% 1.52/0.93      inference(resolution_lifted,[status(thm)],[c_587,c_434]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_700,plain,
% 1.52/0.93      ( ~ v2_tex_2(sK2,sK1)
% 1.52/0.93      | m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.52/0.93      inference(unflattening,[status(thm)],[c_699]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_11,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,X1)
% 1.52/0.93      | v2_tex_2(sK0(X1,X0),X1)
% 1.52/0.93      | v3_tex_2(X0,X1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.52/0.93      | ~ l1_pre_topc(X1) ),
% 1.52/0.93      inference(cnf_transformation,[],[f51]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_451,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,X1)
% 1.52/0.93      | v2_tex_2(sK0(X1,X0),X1)
% 1.52/0.93      | v3_tex_2(X0,X1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.52/0.93      | sK1 != X1 ),
% 1.52/0.93      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_452,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,sK1)
% 1.52/0.93      | v2_tex_2(sK0(sK1,X0),sK1)
% 1.52/0.93      | v3_tex_2(X0,sK1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.52/0.93      inference(unflattening,[status(thm)],[c_451]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_688,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,sK1)
% 1.52/0.93      | v2_tex_2(sK0(sK1,X0),sK1)
% 1.52/0.93      | ~ v2_tex_2(sK2,sK1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | sK1 != sK1
% 1.52/0.93      | sK2 != X0 ),
% 1.52/0.93      inference(resolution_lifted,[status(thm)],[c_587,c_452]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_689,plain,
% 1.52/0.93      ( v2_tex_2(sK0(sK1,sK2),sK1)
% 1.52/0.93      | ~ v2_tex_2(sK2,sK1)
% 1.52/0.93      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.52/0.93      inference(unflattening,[status(thm)],[c_688]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_10,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,X1)
% 1.52/0.93      | v3_tex_2(X0,X1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.52/0.93      | r1_tarski(X0,sK0(X1,X0))
% 1.52/0.93      | ~ l1_pre_topc(X1) ),
% 1.52/0.93      inference(cnf_transformation,[],[f52]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_469,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,X1)
% 1.52/0.93      | v3_tex_2(X0,X1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.52/0.93      | r1_tarski(X0,sK0(X1,X0))
% 1.52/0.93      | sK1 != X1 ),
% 1.52/0.93      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_470,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,sK1)
% 1.52/0.93      | v3_tex_2(X0,sK1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | r1_tarski(X0,sK0(sK1,X0)) ),
% 1.52/0.93      inference(unflattening,[status(thm)],[c_469]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_677,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,sK1)
% 1.52/0.93      | ~ v2_tex_2(sK2,sK1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | r1_tarski(X0,sK0(sK1,X0))
% 1.52/0.93      | sK1 != sK1
% 1.52/0.93      | sK2 != X0 ),
% 1.52/0.93      inference(resolution_lifted,[status(thm)],[c_587,c_470]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_678,plain,
% 1.52/0.93      ( ~ v2_tex_2(sK2,sK1)
% 1.52/0.93      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | r1_tarski(sK2,sK0(sK1,sK2)) ),
% 1.52/0.93      inference(unflattening,[status(thm)],[c_677]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_9,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,X1)
% 1.52/0.93      | v3_tex_2(X0,X1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.52/0.93      | ~ l1_pre_topc(X1)
% 1.52/0.93      | sK0(X1,X0) != X0 ),
% 1.52/0.93      inference(cnf_transformation,[],[f53]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_487,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,X1)
% 1.52/0.93      | v3_tex_2(X0,X1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.52/0.93      | sK0(X1,X0) != X0
% 1.52/0.93      | sK1 != X1 ),
% 1.52/0.93      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_488,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,sK1)
% 1.52/0.93      | v3_tex_2(X0,sK1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | sK0(sK1,X0) != X0 ),
% 1.52/0.93      inference(unflattening,[status(thm)],[c_487]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_669,plain,
% 1.52/0.93      ( ~ v2_tex_2(X0,sK1)
% 1.52/0.93      | ~ v2_tex_2(sK2,sK1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | sK0(sK1,X0) != X0
% 1.52/0.93      | sK1 != sK1
% 1.52/0.93      | sK2 != X0 ),
% 1.52/0.93      inference(resolution_lifted,[status(thm)],[c_587,c_488]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_670,plain,
% 1.52/0.93      ( ~ v2_tex_2(sK2,sK1)
% 1.52/0.93      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | sK0(sK1,sK2) != sK2 ),
% 1.52/0.93      inference(unflattening,[status(thm)],[c_669]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_16,plain,
% 1.52/0.93      ( v2_tex_2(X0,X1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.52/0.93      | v2_struct_0(X1)
% 1.52/0.93      | ~ v1_zfmisc_1(X0)
% 1.52/0.93      | ~ l1_pre_topc(X1)
% 1.52/0.93      | ~ v2_tdlat_3(X1)
% 1.52/0.93      | ~ v2_pre_topc(X1)
% 1.52/0.93      | v1_xboole_0(X0) ),
% 1.52/0.93      inference(cnf_transformation,[],[f56]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_362,plain,
% 1.52/0.93      ( v2_tex_2(X0,X1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.52/0.93      | ~ v1_zfmisc_1(X0)
% 1.52/0.93      | ~ l1_pre_topc(X1)
% 1.52/0.93      | ~ v2_tdlat_3(X1)
% 1.52/0.93      | ~ v2_pre_topc(X1)
% 1.52/0.93      | v1_xboole_0(X0)
% 1.52/0.93      | sK1 != X1 ),
% 1.52/0.93      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_363,plain,
% 1.52/0.93      ( v2_tex_2(X0,sK1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | ~ v1_zfmisc_1(X0)
% 1.52/0.93      | ~ l1_pre_topc(sK1)
% 1.52/0.93      | ~ v2_tdlat_3(sK1)
% 1.52/0.93      | ~ v2_pre_topc(sK1)
% 1.52/0.93      | v1_xboole_0(X0) ),
% 1.52/0.93      inference(unflattening,[status(thm)],[c_362]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_367,plain,
% 1.52/0.93      ( ~ v1_zfmisc_1(X0)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | v2_tex_2(X0,sK1)
% 1.52/0.93      | v1_xboole_0(X0) ),
% 1.52/0.93      inference(global_propositional_subsumption,
% 1.52/0.93                [status(thm)],
% 1.52/0.93                [c_363,c_24,c_23,c_22]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_368,plain,
% 1.52/0.93      ( v2_tex_2(X0,sK1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | ~ v1_zfmisc_1(X0)
% 1.52/0.93      | v1_xboole_0(X0) ),
% 1.52/0.93      inference(renaming,[status(thm)],[c_367]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_19,negated_conjecture,
% 1.52/0.93      ( v3_tex_2(sK2,sK1) | v1_zfmisc_1(sK2) ),
% 1.52/0.93      inference(cnf_transformation,[],[f63]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_195,plain,
% 1.52/0.93      ( v1_zfmisc_1(sK2) | v3_tex_2(sK2,sK1) ),
% 1.52/0.93      inference(prop_impl,[status(thm)],[c_19]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_196,plain,
% 1.52/0.93      ( v3_tex_2(sK2,sK1) | v1_zfmisc_1(sK2) ),
% 1.52/0.93      inference(renaming,[status(thm)],[c_195]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_598,plain,
% 1.52/0.93      ( v2_tex_2(X0,sK1)
% 1.52/0.93      | v3_tex_2(sK2,sK1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | v1_xboole_0(X0)
% 1.52/0.93      | sK2 != X0 ),
% 1.52/0.93      inference(resolution_lifted,[status(thm)],[c_368,c_196]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_599,plain,
% 1.52/0.93      ( v2_tex_2(sK2,sK1)
% 1.52/0.93      | v3_tex_2(sK2,sK1)
% 1.52/0.93      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | v1_xboole_0(sK2) ),
% 1.52/0.93      inference(unflattening,[status(thm)],[c_598]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_601,plain,
% 1.52/0.93      ( v2_tex_2(sK2,sK1) | v3_tex_2(sK2,sK1) ),
% 1.52/0.93      inference(global_propositional_subsumption,
% 1.52/0.93                [status(thm)],
% 1.52/0.93                [c_599,c_21,c_20]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_14,plain,
% 1.52/0.93      ( v2_tex_2(X0,X1)
% 1.52/0.93      | ~ v3_tex_2(X0,X1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.52/0.93      | ~ l1_pre_topc(X1) ),
% 1.52/0.93      inference(cnf_transformation,[],[f48]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_396,plain,
% 1.52/0.93      ( v2_tex_2(X0,X1)
% 1.52/0.93      | ~ v3_tex_2(X0,X1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.52/0.93      | sK1 != X1 ),
% 1.52/0.93      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_397,plain,
% 1.52/0.93      ( v2_tex_2(X0,sK1)
% 1.52/0.93      | ~ v3_tex_2(X0,sK1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.52/0.93      inference(unflattening,[status(thm)],[c_396]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_652,plain,
% 1.52/0.93      ( v2_tex_2(X0,sK1)
% 1.52/0.93      | v2_tex_2(sK2,sK1)
% 1.52/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.52/0.93      | sK1 != sK1
% 1.52/0.93      | sK2 != X0 ),
% 1.52/0.93      inference(resolution_lifted,[status(thm)],[c_601,c_397]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_653,plain,
% 1.52/0.93      ( v2_tex_2(sK2,sK1)
% 1.52/0.93      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.52/0.93      inference(unflattening,[status(thm)],[c_652]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(c_0,plain,
% 1.52/0.93      ( v1_xboole_0(k1_xboole_0) ),
% 1.52/0.93      inference(cnf_transformation,[],[f39]) ).
% 1.52/0.93  
% 1.52/0.93  cnf(contradiction,plain,
% 1.52/0.93      ( $false ),
% 1.52/0.93      inference(minisat,
% 1.52/0.93                [status(thm)],
% 1.52/0.93                [c_3805,c_3120,c_2665,c_2470,c_2370,c_2139,c_2138,c_2086,
% 1.52/0.93                 c_700,c_689,c_678,c_670,c_653,c_0,c_20,c_21]) ).
% 1.52/0.93  
% 1.52/0.93  
% 1.52/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 1.52/0.93  
% 1.52/0.93  ------                               Statistics
% 1.52/0.93  
% 1.52/0.93  ------ General
% 1.52/0.93  
% 1.52/0.93  abstr_ref_over_cycles:                  0
% 1.52/0.93  abstr_ref_under_cycles:                 0
% 1.52/0.93  gc_basic_clause_elim:                   0
% 1.52/0.93  forced_gc_time:                         0
% 1.52/0.93  parsing_time:                           0.01
% 1.52/0.93  unif_index_cands_time:                  0.
% 1.52/0.93  unif_index_add_time:                    0.
% 1.52/0.93  orderings_time:                         0.
% 1.52/0.93  out_proof_time:                         0.01
% 1.52/0.93  total_time:                             0.121
% 1.52/0.93  num_of_symbols:                         47
% 1.52/0.93  num_of_terms:                           1467
% 1.52/0.93  
% 1.52/0.93  ------ Preprocessing
% 1.52/0.93  
% 1.52/0.93  num_of_splits:                          0
% 1.52/0.93  num_of_split_atoms:                     0
% 1.52/0.93  num_of_reused_defs:                     0
% 1.52/0.93  num_eq_ax_congr_red:                    8
% 1.52/0.93  num_of_sem_filtered_clauses:            1
% 1.52/0.93  num_of_subtypes:                        0
% 1.52/0.93  monotx_restored_types:                  0
% 1.52/0.93  sat_num_of_epr_types:                   0
% 1.52/0.93  sat_num_of_non_cyclic_types:            0
% 1.52/0.93  sat_guarded_non_collapsed_types:        0
% 1.52/0.93  num_pure_diseq_elim:                    0
% 1.52/0.93  simp_replaced_by:                       0
% 1.52/0.93  res_preprocessed:                       103
% 1.52/0.93  prep_upred:                             0
% 1.52/0.93  prep_unflattend:                        40
% 1.52/0.93  smt_new_axioms:                         0
% 1.52/0.93  pred_elim_cands:                        5
% 1.52/0.93  pred_elim:                              5
% 1.52/0.93  pred_elim_cl:                           6
% 1.52/0.93  pred_elim_cycles:                       8
% 1.52/0.93  merged_defs:                            10
% 1.52/0.93  merged_defs_ncl:                        0
% 1.52/0.93  bin_hyper_res:                          10
% 1.52/0.93  prep_cycles:                            4
% 1.52/0.93  pred_elim_time:                         0.015
% 1.52/0.93  splitting_time:                         0.
% 1.52/0.93  sem_filter_time:                        0.
% 1.52/0.93  monotx_time:                            0.001
% 1.52/0.93  subtype_inf_time:                       0.
% 1.52/0.93  
% 1.52/0.93  ------ Problem properties
% 1.52/0.93  
% 1.52/0.93  clauses:                                19
% 1.52/0.93  conjectures:                            2
% 1.52/0.93  epr:                                    8
% 1.52/0.93  horn:                                   14
% 1.52/0.93  ground:                                 5
% 1.52/0.93  unary:                                  7
% 1.52/0.93  binary:                                 2
% 1.52/0.93  lits:                                   51
% 1.52/0.93  lits_eq:                                6
% 1.52/0.93  fd_pure:                                0
% 1.52/0.93  fd_pseudo:                              0
% 1.52/0.93  fd_cond:                                1
% 1.52/0.93  fd_pseudo_cond:                         4
% 1.52/0.93  ac_symbols:                             0
% 1.52/0.93  
% 1.52/0.93  ------ Propositional Solver
% 1.52/0.93  
% 1.52/0.93  prop_solver_calls:                      27
% 1.52/0.93  prop_fast_solver_calls:                 923
% 1.52/0.93  smt_solver_calls:                       0
% 1.52/0.93  smt_fast_solver_calls:                  0
% 1.52/0.93  prop_num_of_clauses:                    863
% 1.52/0.93  prop_preprocess_simplified:             4025
% 1.52/0.93  prop_fo_subsumed:                       47
% 1.52/0.93  prop_solver_time:                       0.
% 1.52/0.93  smt_solver_time:                        0.
% 1.52/0.93  smt_fast_solver_time:                   0.
% 1.52/0.93  prop_fast_solver_time:                  0.
% 1.52/0.93  prop_unsat_core_time:                   0.
% 1.52/0.93  
% 1.52/0.93  ------ QBF
% 1.52/0.93  
% 1.52/0.93  qbf_q_res:                              0
% 1.52/0.93  qbf_num_tautologies:                    0
% 1.52/0.93  qbf_prep_cycles:                        0
% 1.52/0.93  
% 1.52/0.93  ------ BMC1
% 1.52/0.93  
% 1.52/0.93  bmc1_current_bound:                     -1
% 1.52/0.93  bmc1_last_solved_bound:                 -1
% 1.52/0.93  bmc1_unsat_core_size:                   -1
% 1.52/0.93  bmc1_unsat_core_parents_size:           -1
% 1.52/0.93  bmc1_merge_next_fun:                    0
% 1.52/0.93  bmc1_unsat_core_clauses_time:           0.
% 1.52/0.93  
% 1.52/0.93  ------ Instantiation
% 1.52/0.93  
% 1.52/0.93  inst_num_of_clauses:                    252
% 1.52/0.93  inst_num_in_passive:                    30
% 1.52/0.93  inst_num_in_active:                     164
% 1.52/0.93  inst_num_in_unprocessed:                58
% 1.52/0.93  inst_num_of_loops:                      172
% 1.52/0.93  inst_num_of_learning_restarts:          0
% 1.52/0.93  inst_num_moves_active_passive:          4
% 1.52/0.93  inst_lit_activity:                      0
% 1.52/0.93  inst_lit_activity_moves:                0
% 1.52/0.93  inst_num_tautologies:                   0
% 1.52/0.93  inst_num_prop_implied:                  0
% 1.52/0.93  inst_num_existing_simplified:           0
% 1.52/0.93  inst_num_eq_res_simplified:             0
% 1.52/0.93  inst_num_child_elim:                    0
% 1.52/0.93  inst_num_of_dismatching_blockings:      28
% 1.52/0.93  inst_num_of_non_proper_insts:           312
% 1.52/0.93  inst_num_of_duplicates:                 0
% 1.52/0.93  inst_inst_num_from_inst_to_res:         0
% 1.52/0.93  inst_dismatching_checking_time:         0.
% 1.52/0.93  
% 1.52/0.93  ------ Resolution
% 1.52/0.93  
% 1.52/0.93  res_num_of_clauses:                     0
% 1.52/0.93  res_num_in_passive:                     0
% 1.52/0.93  res_num_in_active:                      0
% 1.52/0.93  res_num_of_loops:                       107
% 1.52/0.93  res_forward_subset_subsumed:            80
% 1.52/0.93  res_backward_subset_subsumed:           3
% 1.52/0.93  res_forward_subsumed:                   1
% 1.52/0.93  res_backward_subsumed:                  1
% 1.52/0.93  res_forward_subsumption_resolution:     0
% 1.52/0.93  res_backward_subsumption_resolution:    2
% 1.52/0.93  res_clause_to_clause_subsumption:       307
% 1.52/0.93  res_orphan_elimination:                 0
% 1.52/0.93  res_tautology_del:                      70
% 1.52/0.93  res_num_eq_res_simplified:              0
% 1.52/0.93  res_num_sel_changes:                    0
% 1.52/0.93  res_moves_from_active_to_pass:          0
% 1.52/0.93  
% 1.52/0.93  ------ Superposition
% 1.52/0.93  
% 1.52/0.93  sup_time_total:                         0.
% 1.52/0.93  sup_time_generating:                    0.
% 1.52/0.93  sup_time_sim_full:                      0.
% 1.52/0.93  sup_time_sim_immed:                     0.
% 1.52/0.93  
% 1.52/0.93  sup_num_of_clauses:                     50
% 1.52/0.93  sup_num_in_active:                      34
% 1.52/0.93  sup_num_in_passive:                     16
% 1.52/0.93  sup_num_of_loops:                       34
% 1.52/0.93  sup_fw_superposition:                   28
% 1.52/0.93  sup_bw_superposition:                   18
% 1.52/0.93  sup_immediate_simplified:               8
% 1.52/0.93  sup_given_eliminated:                   0
% 1.52/0.93  comparisons_done:                       0
% 1.52/0.93  comparisons_avoided:                    0
% 1.52/0.93  
% 1.52/0.93  ------ Simplifications
% 1.52/0.93  
% 1.52/0.93  
% 1.52/0.93  sim_fw_subset_subsumed:                 5
% 1.52/0.93  sim_bw_subset_subsumed:                 0
% 1.52/0.93  sim_fw_subsumed:                        4
% 1.52/0.93  sim_bw_subsumed:                        0
% 1.52/0.93  sim_fw_subsumption_res:                 0
% 1.52/0.93  sim_bw_subsumption_res:                 0
% 1.52/0.93  sim_tautology_del:                      1
% 1.52/0.93  sim_eq_tautology_del:                   3
% 1.52/0.93  sim_eq_res_simp:                        0
% 1.52/0.93  sim_fw_demodulated:                     0
% 1.52/0.93  sim_bw_demodulated:                     0
% 1.52/0.93  sim_light_normalised:                   0
% 1.52/0.93  sim_joinable_taut:                      0
% 1.52/0.93  sim_joinable_simp:                      0
% 1.52/0.93  sim_ac_normalised:                      0
% 1.52/0.93  sim_smt_subsumption:                    0
% 1.52/0.93  
%------------------------------------------------------------------------------
