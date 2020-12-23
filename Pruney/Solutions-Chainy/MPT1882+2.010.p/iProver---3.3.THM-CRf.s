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
% DateTime   : Thu Dec  3 12:27:20 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :  169 (2440 expanded)
%              Number of clauses        :  110 ( 569 expanded)
%              Number of leaves         :   15 ( 542 expanded)
%              Depth                    :   25
%              Number of atoms          :  714 (19190 expanded)
%              Number of equality atoms :  179 ( 646 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

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
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

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
    inference(nnf_transformation,[],[f25])).

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
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
    inference(nnf_transformation,[],[f19])).

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

fof(f60,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

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
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(nnf_transformation,[],[f23])).

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

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK0(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f64,plain,
    ( ~ v1_zfmisc_1(sK2)
    | ~ v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK0(X0,X1) != X1
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

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
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

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1717,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1712,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | v3_tex_2(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_1708,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v2_tex_2(X0,sK1) != iProver_top
    | v3_tex_2(X0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_7,plain,
    ( v1_zfmisc_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_139,plain,
    ( v1_zfmisc_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_7])).

cnf(c_140,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_139])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_328,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_140,c_25])).

cnf(c_329,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_23,negated_conjecture,
    ( v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_333,plain,
    ( ~ v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_zfmisc_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_329,c_24,c_23,c_22])).

cnf(c_334,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_333])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_525,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | X2 != X0
    | X1 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_334,c_15])).

cnf(c_526,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ r1_tarski(X1,X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_1704,plain,
    ( X0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(X1,sK1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_526])).

cnf(c_2642,plain,
    ( sK0(sK1,X0) = X1
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(X0,sK1) != iProver_top
    | v2_tex_2(sK0(sK1,X0),sK1) != iProver_top
    | v3_tex_2(X0,sK1) = iProver_top
    | r1_tarski(X1,sK0(sK1,X0)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK0(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1708,c_1704])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_437,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_438,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | v2_tex_2(sK0(sK1,X0),sK1)
    | v3_tex_2(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_439,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(X0,sK1) != iProver_top
    | v2_tex_2(sK0(sK1,X0),sK1) = iProver_top
    | v3_tex_2(X0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_438])).

cnf(c_3283,plain,
    ( v2_tex_2(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sK0(sK1,X0) = X1
    | v3_tex_2(X0,sK1) = iProver_top
    | r1_tarski(X1,sK0(sK1,X0)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK0(sK1,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2642,c_439])).

cnf(c_3284,plain,
    ( sK0(sK1,X0) = X1
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(X0,sK1) != iProver_top
    | v3_tex_2(X0,sK1) = iProver_top
    | r1_tarski(X1,sK0(sK1,X0)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK0(sK1,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3283])).

cnf(c_3296,plain,
    ( sK0(sK1,sK2) = X0
    | v2_tex_2(sK2,sK1) != iProver_top
    | v3_tex_2(sK2,sK1) = iProver_top
    | r1_tarski(X0,sK0(sK1,sK2)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1712,c_3284])).

cnf(c_21,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_30,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_31,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_349,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_354,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_24,c_23,c_22])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_354])).

cnf(c_19,negated_conjecture,
    ( v3_tex_2(sK2,sK1)
    | v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_191,plain,
    ( v1_zfmisc_1(sK2)
    | v3_tex_2(sK2,sK1) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_192,plain,
    ( v3_tex_2(sK2,sK1)
    | v1_zfmisc_1(sK2) ),
    inference(renaming,[status(thm)],[c_191])).

cnf(c_565,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1)
    | v3_tex_2(sK2,sK1)
    | v1_xboole_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_355,c_192])).

cnf(c_566,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(sK2,sK1)
    | v3_tex_2(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_568,plain,
    ( v3_tex_2(sK2,sK1)
    | v2_tex_2(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_566,c_21,c_20])).

cnf(c_569,plain,
    ( v2_tex_2(sK2,sK1)
    | v3_tex_2(sK2,sK1) ),
    inference(renaming,[status(thm)],[c_568])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1)
    | ~ v3_tex_2(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_820,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1)
    | v2_tex_2(sK2,sK1)
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_569,c_383])).

cnf(c_821,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(sK2,sK1) ),
    inference(unflattening,[status(thm)],[c_820])).

cnf(c_822,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_821])).

cnf(c_18,negated_conjecture,
    ( ~ v3_tex_2(sK2,sK1)
    | ~ v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_189,plain,
    ( ~ v1_zfmisc_1(sK2)
    | ~ v3_tex_2(sK2,sK1) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_190,plain,
    ( ~ v3_tex_2(sK2,sK1)
    | ~ v1_zfmisc_1(sK2) ),
    inference(renaming,[status(thm)],[c_189])).

cnf(c_549,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ v3_tex_2(sK2,sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_334,c_190])).

cnf(c_550,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(sK2,sK1)
    | ~ v3_tex_2(sK2,sK1) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_552,plain,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ v3_tex_2(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_550,c_20])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | sK0(X1,X0) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_474,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | v3_tex_2(X0,sK1)
    | sK0(sK1,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_831,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ v2_tex_2(sK2,sK1)
    | sK0(sK1,X0) != X0
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_552,c_474])).

cnf(c_832,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(sK2,sK1)
    | sK0(sK1,sK2) != sK2 ),
    inference(unflattening,[status(thm)],[c_831])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | r1_tarski(X0,sK0(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | r1_tarski(X0,sK0(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | v3_tex_2(X0,sK1)
    | r1_tarski(X0,sK0(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_839,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ v2_tex_2(sK2,sK1)
    | r1_tarski(X0,sK0(sK1,X0))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_552,c_456])).

cnf(c_840,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(sK2,sK1)
    | r1_tarski(sK2,sK0(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_839])).

cnf(c_841,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(sK2,sK1) != iProver_top
    | r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_840])).

cnf(c_850,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | v2_tex_2(sK0(sK1,X0),sK1)
    | ~ v2_tex_2(sK2,sK1)
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_552,c_438])).

cnf(c_851,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(sK0(sK1,sK2),sK1)
    | ~ v2_tex_2(sK2,sK1) ),
    inference(unflattening,[status(thm)],[c_850])).

cnf(c_852,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(sK0(sK1,sK2),sK1) = iProver_top
    | v2_tex_2(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_851])).

cnf(c_861,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ v2_tex_2(sK2,sK1)
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_552,c_420])).

cnf(c_862,plain,
    ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(sK2,sK1) ),
    inference(unflattening,[status(thm)],[c_861])).

cnf(c_863,plain,
    ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_862])).

cnf(c_1374,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2190,plain,
    ( sK0(sK1,sK2) = sK0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1374])).

cnf(c_1991,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ r1_tarski(sK2,X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_526])).

cnf(c_2209,plain,
    ( ~ m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(sK0(sK1,sK2),sK1)
    | ~ r1_tarski(sK2,sK0(sK1,sK2))
    | v1_xboole_0(sK0(sK1,sK2))
    | v1_xboole_0(sK2)
    | sK2 = sK0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1991])).

cnf(c_2210,plain,
    ( sK2 = sK0(sK1,sK2)
    | m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(sK0(sK1,sK2),sK1) != iProver_top
    | r1_tarski(sK2,sK0(sK1,sK2)) != iProver_top
    | v1_xboole_0(sK0(sK1,sK2)) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2209])).

cnf(c_1375,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1948,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_2312,plain,
    ( X0 != sK0(sK1,sK2)
    | X0 = sK2
    | sK2 != sK0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1948])).

cnf(c_2746,plain,
    ( sK0(sK1,sK2) != sK0(sK1,sK2)
    | sK0(sK1,sK2) = sK2
    | sK2 != sK0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2312])).

cnf(c_3335,plain,
    ( v1_xboole_0(sK0(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3296,c_30,c_20,c_31,c_821,c_822,c_832,c_841,c_852,c_863,c_2190,c_2210,c_2746])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1713,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3340,plain,
    ( sK0(sK1,sK2) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3335,c_1713])).

cnf(c_3434,plain,
    ( sK0(sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1717,c_3340])).

cnf(c_1706,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(X0,sK1) != iProver_top
    | v3_tex_2(X0,sK1) = iProver_top
    | r1_tarski(X0,sK0(sK1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_2042,plain,
    ( v2_tex_2(sK2,sK1) != iProver_top
    | v3_tex_2(sK2,sK1) = iProver_top
    | r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1712,c_1706])).

cnf(c_2045,plain,
    ( r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2042,c_31,c_822,c_841])).

cnf(c_3652,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3434,c_2045])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1715,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1714,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2291,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1714])).

cnf(c_2866,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1715,c_2291])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1716,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3085,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2866,c_1716])).

cnf(c_3832,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3652,c_3085])).

cnf(c_1705,plain,
    ( sK0(sK1,X0) != X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(X0,sK1) != iProver_top
    | v3_tex_2(X0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_3680,plain,
    ( sK2 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(sK2,sK1) != iProver_top
    | v3_tex_2(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3434,c_1705])).

cnf(c_554,plain,
    ( v2_tex_2(sK2,sK1) != iProver_top
    | v3_tex_2(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_3847,plain,
    ( sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3680,c_31,c_554,c_822])).

cnf(c_3851,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3832,c_3847])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:12:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.73/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/0.99  
% 1.73/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.73/0.99  
% 1.73/0.99  ------  iProver source info
% 1.73/0.99  
% 1.73/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.73/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.73/0.99  git: non_committed_changes: false
% 1.73/0.99  git: last_make_outside_of_git: false
% 1.73/0.99  
% 1.73/0.99  ------ 
% 1.73/0.99  
% 1.73/0.99  ------ Input Options
% 1.73/0.99  
% 1.73/0.99  --out_options                           all
% 1.73/0.99  --tptp_safe_out                         true
% 1.73/0.99  --problem_path                          ""
% 1.73/0.99  --include_path                          ""
% 1.73/0.99  --clausifier                            res/vclausify_rel
% 1.73/0.99  --clausifier_options                    --mode clausify
% 1.73/0.99  --stdin                                 false
% 1.73/0.99  --stats_out                             all
% 1.73/0.99  
% 1.73/0.99  ------ General Options
% 1.73/0.99  
% 1.73/0.99  --fof                                   false
% 1.73/0.99  --time_out_real                         305.
% 1.73/0.99  --time_out_virtual                      -1.
% 1.73/0.99  --symbol_type_check                     false
% 1.73/0.99  --clausify_out                          false
% 1.73/0.99  --sig_cnt_out                           false
% 1.73/0.99  --trig_cnt_out                          false
% 1.73/0.99  --trig_cnt_out_tolerance                1.
% 1.73/0.99  --trig_cnt_out_sk_spl                   false
% 1.73/0.99  --abstr_cl_out                          false
% 1.73/0.99  
% 1.73/0.99  ------ Global Options
% 1.73/0.99  
% 1.73/0.99  --schedule                              default
% 1.73/0.99  --add_important_lit                     false
% 1.73/0.99  --prop_solver_per_cl                    1000
% 1.73/0.99  --min_unsat_core                        false
% 1.73/0.99  --soft_assumptions                      false
% 1.73/0.99  --soft_lemma_size                       3
% 1.73/0.99  --prop_impl_unit_size                   0
% 1.73/0.99  --prop_impl_unit                        []
% 1.73/0.99  --share_sel_clauses                     true
% 1.73/0.99  --reset_solvers                         false
% 1.73/0.99  --bc_imp_inh                            [conj_cone]
% 1.73/0.99  --conj_cone_tolerance                   3.
% 1.73/0.99  --extra_neg_conj                        none
% 1.73/0.99  --large_theory_mode                     true
% 1.73/0.99  --prolific_symb_bound                   200
% 1.73/0.99  --lt_threshold                          2000
% 1.73/0.99  --clause_weak_htbl                      true
% 1.73/0.99  --gc_record_bc_elim                     false
% 1.73/0.99  
% 1.73/0.99  ------ Preprocessing Options
% 1.73/0.99  
% 1.73/0.99  --preprocessing_flag                    true
% 1.73/0.99  --time_out_prep_mult                    0.1
% 1.73/0.99  --splitting_mode                        input
% 1.73/0.99  --splitting_grd                         true
% 1.73/0.99  --splitting_cvd                         false
% 1.73/0.99  --splitting_cvd_svl                     false
% 1.73/0.99  --splitting_nvd                         32
% 1.73/0.99  --sub_typing                            true
% 1.73/0.99  --prep_gs_sim                           true
% 1.73/0.99  --prep_unflatten                        true
% 1.73/0.99  --prep_res_sim                          true
% 1.73/0.99  --prep_upred                            true
% 1.73/0.99  --prep_sem_filter                       exhaustive
% 1.73/0.99  --prep_sem_filter_out                   false
% 1.73/0.99  --pred_elim                             true
% 1.73/0.99  --res_sim_input                         true
% 1.73/0.99  --eq_ax_congr_red                       true
% 1.73/0.99  --pure_diseq_elim                       true
% 1.73/0.99  --brand_transform                       false
% 1.73/0.99  --non_eq_to_eq                          false
% 1.73/0.99  --prep_def_merge                        true
% 1.73/0.99  --prep_def_merge_prop_impl              false
% 1.73/0.99  --prep_def_merge_mbd                    true
% 1.73/0.99  --prep_def_merge_tr_red                 false
% 1.73/0.99  --prep_def_merge_tr_cl                  false
% 1.73/0.99  --smt_preprocessing                     true
% 1.73/0.99  --smt_ac_axioms                         fast
% 1.73/0.99  --preprocessed_out                      false
% 1.73/0.99  --preprocessed_stats                    false
% 1.73/0.99  
% 1.73/0.99  ------ Abstraction refinement Options
% 1.73/0.99  
% 1.73/0.99  --abstr_ref                             []
% 1.73/0.99  --abstr_ref_prep                        false
% 1.73/0.99  --abstr_ref_until_sat                   false
% 1.73/0.99  --abstr_ref_sig_restrict                funpre
% 1.73/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.73/0.99  --abstr_ref_under                       []
% 1.73/0.99  
% 1.73/0.99  ------ SAT Options
% 1.73/0.99  
% 1.73/0.99  --sat_mode                              false
% 1.73/0.99  --sat_fm_restart_options                ""
% 1.73/0.99  --sat_gr_def                            false
% 1.73/0.99  --sat_epr_types                         true
% 1.73/0.99  --sat_non_cyclic_types                  false
% 1.73/0.99  --sat_finite_models                     false
% 1.73/0.99  --sat_fm_lemmas                         false
% 1.73/0.99  --sat_fm_prep                           false
% 1.73/0.99  --sat_fm_uc_incr                        true
% 1.73/0.99  --sat_out_model                         small
% 1.73/0.99  --sat_out_clauses                       false
% 1.73/0.99  
% 1.73/0.99  ------ QBF Options
% 1.73/0.99  
% 1.73/0.99  --qbf_mode                              false
% 1.73/0.99  --qbf_elim_univ                         false
% 1.73/0.99  --qbf_dom_inst                          none
% 1.73/0.99  --qbf_dom_pre_inst                      false
% 1.73/0.99  --qbf_sk_in                             false
% 1.73/0.99  --qbf_pred_elim                         true
% 1.73/0.99  --qbf_split                             512
% 1.73/0.99  
% 1.73/0.99  ------ BMC1 Options
% 1.73/0.99  
% 1.73/0.99  --bmc1_incremental                      false
% 1.73/0.99  --bmc1_axioms                           reachable_all
% 1.73/0.99  --bmc1_min_bound                        0
% 1.73/0.99  --bmc1_max_bound                        -1
% 1.73/0.99  --bmc1_max_bound_default                -1
% 1.73/0.99  --bmc1_symbol_reachability              true
% 1.73/0.99  --bmc1_property_lemmas                  false
% 1.73/0.99  --bmc1_k_induction                      false
% 1.73/0.99  --bmc1_non_equiv_states                 false
% 1.73/0.99  --bmc1_deadlock                         false
% 1.73/0.99  --bmc1_ucm                              false
% 1.73/0.99  --bmc1_add_unsat_core                   none
% 1.73/0.99  --bmc1_unsat_core_children              false
% 1.73/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.73/0.99  --bmc1_out_stat                         full
% 1.73/0.99  --bmc1_ground_init                      false
% 1.73/0.99  --bmc1_pre_inst_next_state              false
% 1.73/0.99  --bmc1_pre_inst_state                   false
% 1.73/0.99  --bmc1_pre_inst_reach_state             false
% 1.73/0.99  --bmc1_out_unsat_core                   false
% 1.73/0.99  --bmc1_aig_witness_out                  false
% 1.73/0.99  --bmc1_verbose                          false
% 1.73/0.99  --bmc1_dump_clauses_tptp                false
% 1.73/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.73/0.99  --bmc1_dump_file                        -
% 1.73/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.73/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.73/0.99  --bmc1_ucm_extend_mode                  1
% 1.73/0.99  --bmc1_ucm_init_mode                    2
% 1.73/0.99  --bmc1_ucm_cone_mode                    none
% 1.73/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.73/0.99  --bmc1_ucm_relax_model                  4
% 1.73/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.73/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.73/0.99  --bmc1_ucm_layered_model                none
% 1.73/0.99  --bmc1_ucm_max_lemma_size               10
% 1.73/0.99  
% 1.73/0.99  ------ AIG Options
% 1.73/0.99  
% 1.73/0.99  --aig_mode                              false
% 1.73/0.99  
% 1.73/0.99  ------ Instantiation Options
% 1.73/0.99  
% 1.73/0.99  --instantiation_flag                    true
% 1.73/0.99  --inst_sos_flag                         false
% 1.73/0.99  --inst_sos_phase                        true
% 1.73/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.73/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.73/0.99  --inst_lit_sel_side                     num_symb
% 1.73/0.99  --inst_solver_per_active                1400
% 1.73/0.99  --inst_solver_calls_frac                1.
% 1.73/0.99  --inst_passive_queue_type               priority_queues
% 1.73/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.73/0.99  --inst_passive_queues_freq              [25;2]
% 1.73/0.99  --inst_dismatching                      true
% 1.73/0.99  --inst_eager_unprocessed_to_passive     true
% 1.73/0.99  --inst_prop_sim_given                   true
% 1.73/0.99  --inst_prop_sim_new                     false
% 1.73/0.99  --inst_subs_new                         false
% 1.73/0.99  --inst_eq_res_simp                      false
% 1.73/0.99  --inst_subs_given                       false
% 1.73/0.99  --inst_orphan_elimination               true
% 1.73/0.99  --inst_learning_loop_flag               true
% 1.73/0.99  --inst_learning_start                   3000
% 1.73/0.99  --inst_learning_factor                  2
% 1.73/0.99  --inst_start_prop_sim_after_learn       3
% 1.73/0.99  --inst_sel_renew                        solver
% 1.73/0.99  --inst_lit_activity_flag                true
% 1.73/0.99  --inst_restr_to_given                   false
% 1.73/0.99  --inst_activity_threshold               500
% 1.73/0.99  --inst_out_proof                        true
% 1.73/0.99  
% 1.73/0.99  ------ Resolution Options
% 1.73/0.99  
% 1.73/0.99  --resolution_flag                       true
% 1.73/0.99  --res_lit_sel                           adaptive
% 1.73/0.99  --res_lit_sel_side                      none
% 1.73/0.99  --res_ordering                          kbo
% 1.73/0.99  --res_to_prop_solver                    active
% 1.73/0.99  --res_prop_simpl_new                    false
% 1.73/0.99  --res_prop_simpl_given                  true
% 1.73/0.99  --res_passive_queue_type                priority_queues
% 1.73/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.73/0.99  --res_passive_queues_freq               [15;5]
% 1.73/0.99  --res_forward_subs                      full
% 1.73/0.99  --res_backward_subs                     full
% 1.73/0.99  --res_forward_subs_resolution           true
% 1.73/0.99  --res_backward_subs_resolution          true
% 1.73/0.99  --res_orphan_elimination                true
% 1.73/0.99  --res_time_limit                        2.
% 1.73/0.99  --res_out_proof                         true
% 1.73/0.99  
% 1.73/0.99  ------ Superposition Options
% 1.73/0.99  
% 1.73/0.99  --superposition_flag                    true
% 1.73/0.99  --sup_passive_queue_type                priority_queues
% 1.73/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.73/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.73/0.99  --demod_completeness_check              fast
% 1.73/0.99  --demod_use_ground                      true
% 1.73/0.99  --sup_to_prop_solver                    passive
% 1.73/0.99  --sup_prop_simpl_new                    true
% 1.73/0.99  --sup_prop_simpl_given                  true
% 1.73/0.99  --sup_fun_splitting                     false
% 1.73/0.99  --sup_smt_interval                      50000
% 1.73/0.99  
% 1.73/0.99  ------ Superposition Simplification Setup
% 1.73/0.99  
% 1.73/0.99  --sup_indices_passive                   []
% 1.73/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.73/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/0.99  --sup_full_bw                           [BwDemod]
% 1.73/0.99  --sup_immed_triv                        [TrivRules]
% 1.73/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.73/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/0.99  --sup_immed_bw_main                     []
% 1.73/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.73/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/0.99  
% 1.73/0.99  ------ Combination Options
% 1.73/0.99  
% 1.73/0.99  --comb_res_mult                         3
% 1.73/0.99  --comb_sup_mult                         2
% 1.73/0.99  --comb_inst_mult                        10
% 1.73/0.99  
% 1.73/0.99  ------ Debug Options
% 1.73/0.99  
% 1.73/0.99  --dbg_backtrace                         false
% 1.73/0.99  --dbg_dump_prop_clauses                 false
% 1.73/0.99  --dbg_dump_prop_clauses_file            -
% 1.73/0.99  --dbg_out_stat                          false
% 1.73/0.99  ------ Parsing...
% 1.73/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.73/0.99  
% 1.73/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.73/0.99  
% 1.73/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.73/0.99  
% 1.73/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.73/0.99  ------ Proving...
% 1.73/0.99  ------ Problem Properties 
% 1.73/0.99  
% 1.73/0.99  
% 1.73/0.99  clauses                                 18
% 1.73/0.99  conjectures                             2
% 1.73/0.99  EPR                                     8
% 1.73/0.99  Horn                                    13
% 1.73/0.99  unary                                   7
% 1.73/0.99  binary                                  1
% 1.73/0.99  lits                                    49
% 1.73/0.99  lits eq                                 7
% 1.73/0.99  fd_pure                                 0
% 1.73/0.99  fd_pseudo                               0
% 1.73/0.99  fd_cond                                 1
% 1.73/0.99  fd_pseudo_cond                          4
% 1.73/0.99  AC symbols                              0
% 1.73/0.99  
% 1.73/0.99  ------ Schedule dynamic 5 is on 
% 1.73/0.99  
% 1.73/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.73/0.99  
% 1.73/0.99  
% 1.73/0.99  ------ 
% 1.73/0.99  Current options:
% 1.73/0.99  ------ 
% 1.73/0.99  
% 1.73/0.99  ------ Input Options
% 1.73/0.99  
% 1.73/0.99  --out_options                           all
% 1.73/0.99  --tptp_safe_out                         true
% 1.73/0.99  --problem_path                          ""
% 1.73/0.99  --include_path                          ""
% 1.73/0.99  --clausifier                            res/vclausify_rel
% 1.73/0.99  --clausifier_options                    --mode clausify
% 1.73/0.99  --stdin                                 false
% 1.73/0.99  --stats_out                             all
% 1.73/0.99  
% 1.73/0.99  ------ General Options
% 1.73/0.99  
% 1.73/0.99  --fof                                   false
% 1.73/0.99  --time_out_real                         305.
% 1.73/0.99  --time_out_virtual                      -1.
% 1.73/0.99  --symbol_type_check                     false
% 1.73/0.99  --clausify_out                          false
% 1.73/0.99  --sig_cnt_out                           false
% 1.73/0.99  --trig_cnt_out                          false
% 1.73/0.99  --trig_cnt_out_tolerance                1.
% 1.73/0.99  --trig_cnt_out_sk_spl                   false
% 1.73/0.99  --abstr_cl_out                          false
% 1.73/0.99  
% 1.73/0.99  ------ Global Options
% 1.73/0.99  
% 1.73/0.99  --schedule                              default
% 1.73/0.99  --add_important_lit                     false
% 1.73/0.99  --prop_solver_per_cl                    1000
% 1.73/0.99  --min_unsat_core                        false
% 1.73/0.99  --soft_assumptions                      false
% 1.73/0.99  --soft_lemma_size                       3
% 1.73/0.99  --prop_impl_unit_size                   0
% 1.73/0.99  --prop_impl_unit                        []
% 1.73/0.99  --share_sel_clauses                     true
% 1.73/0.99  --reset_solvers                         false
% 1.73/0.99  --bc_imp_inh                            [conj_cone]
% 1.73/0.99  --conj_cone_tolerance                   3.
% 1.73/0.99  --extra_neg_conj                        none
% 1.73/0.99  --large_theory_mode                     true
% 1.73/0.99  --prolific_symb_bound                   200
% 1.73/0.99  --lt_threshold                          2000
% 1.73/0.99  --clause_weak_htbl                      true
% 1.73/0.99  --gc_record_bc_elim                     false
% 1.73/0.99  
% 1.73/0.99  ------ Preprocessing Options
% 1.73/0.99  
% 1.73/0.99  --preprocessing_flag                    true
% 1.73/0.99  --time_out_prep_mult                    0.1
% 1.73/0.99  --splitting_mode                        input
% 1.73/0.99  --splitting_grd                         true
% 1.73/0.99  --splitting_cvd                         false
% 1.73/0.99  --splitting_cvd_svl                     false
% 1.73/0.99  --splitting_nvd                         32
% 1.73/0.99  --sub_typing                            true
% 1.73/0.99  --prep_gs_sim                           true
% 1.73/0.99  --prep_unflatten                        true
% 1.73/0.99  --prep_res_sim                          true
% 1.73/0.99  --prep_upred                            true
% 1.73/0.99  --prep_sem_filter                       exhaustive
% 1.73/0.99  --prep_sem_filter_out                   false
% 1.73/0.99  --pred_elim                             true
% 1.73/0.99  --res_sim_input                         true
% 1.73/0.99  --eq_ax_congr_red                       true
% 1.73/0.99  --pure_diseq_elim                       true
% 1.73/0.99  --brand_transform                       false
% 1.73/0.99  --non_eq_to_eq                          false
% 1.73/0.99  --prep_def_merge                        true
% 1.73/0.99  --prep_def_merge_prop_impl              false
% 1.73/0.99  --prep_def_merge_mbd                    true
% 1.73/0.99  --prep_def_merge_tr_red                 false
% 1.73/0.99  --prep_def_merge_tr_cl                  false
% 1.73/0.99  --smt_preprocessing                     true
% 1.73/0.99  --smt_ac_axioms                         fast
% 1.73/0.99  --preprocessed_out                      false
% 1.73/0.99  --preprocessed_stats                    false
% 1.73/0.99  
% 1.73/0.99  ------ Abstraction refinement Options
% 1.73/0.99  
% 1.73/0.99  --abstr_ref                             []
% 1.73/0.99  --abstr_ref_prep                        false
% 1.73/0.99  --abstr_ref_until_sat                   false
% 1.73/0.99  --abstr_ref_sig_restrict                funpre
% 1.73/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.73/0.99  --abstr_ref_under                       []
% 1.73/0.99  
% 1.73/0.99  ------ SAT Options
% 1.73/0.99  
% 1.73/0.99  --sat_mode                              false
% 1.73/0.99  --sat_fm_restart_options                ""
% 1.73/0.99  --sat_gr_def                            false
% 1.73/0.99  --sat_epr_types                         true
% 1.73/0.99  --sat_non_cyclic_types                  false
% 1.73/0.99  --sat_finite_models                     false
% 1.73/0.99  --sat_fm_lemmas                         false
% 1.73/0.99  --sat_fm_prep                           false
% 1.73/0.99  --sat_fm_uc_incr                        true
% 1.73/0.99  --sat_out_model                         small
% 1.73/0.99  --sat_out_clauses                       false
% 1.73/0.99  
% 1.73/0.99  ------ QBF Options
% 1.73/0.99  
% 1.73/0.99  --qbf_mode                              false
% 1.73/0.99  --qbf_elim_univ                         false
% 1.73/0.99  --qbf_dom_inst                          none
% 1.73/0.99  --qbf_dom_pre_inst                      false
% 1.73/0.99  --qbf_sk_in                             false
% 1.73/0.99  --qbf_pred_elim                         true
% 1.73/0.99  --qbf_split                             512
% 1.73/0.99  
% 1.73/0.99  ------ BMC1 Options
% 1.73/0.99  
% 1.73/0.99  --bmc1_incremental                      false
% 1.73/0.99  --bmc1_axioms                           reachable_all
% 1.73/0.99  --bmc1_min_bound                        0
% 1.73/0.99  --bmc1_max_bound                        -1
% 1.73/0.99  --bmc1_max_bound_default                -1
% 1.73/1.00  --bmc1_symbol_reachability              true
% 1.73/1.00  --bmc1_property_lemmas                  false
% 1.73/1.00  --bmc1_k_induction                      false
% 1.73/1.00  --bmc1_non_equiv_states                 false
% 1.73/1.00  --bmc1_deadlock                         false
% 1.73/1.00  --bmc1_ucm                              false
% 1.73/1.00  --bmc1_add_unsat_core                   none
% 1.73/1.00  --bmc1_unsat_core_children              false
% 1.73/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.73/1.00  --bmc1_out_stat                         full
% 1.73/1.00  --bmc1_ground_init                      false
% 1.73/1.00  --bmc1_pre_inst_next_state              false
% 1.73/1.00  --bmc1_pre_inst_state                   false
% 1.73/1.00  --bmc1_pre_inst_reach_state             false
% 1.73/1.00  --bmc1_out_unsat_core                   false
% 1.73/1.00  --bmc1_aig_witness_out                  false
% 1.73/1.00  --bmc1_verbose                          false
% 1.73/1.00  --bmc1_dump_clauses_tptp                false
% 1.73/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.73/1.00  --bmc1_dump_file                        -
% 1.73/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.73/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.73/1.00  --bmc1_ucm_extend_mode                  1
% 1.73/1.00  --bmc1_ucm_init_mode                    2
% 1.73/1.00  --bmc1_ucm_cone_mode                    none
% 1.73/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.73/1.00  --bmc1_ucm_relax_model                  4
% 1.73/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.73/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.73/1.00  --bmc1_ucm_layered_model                none
% 1.73/1.00  --bmc1_ucm_max_lemma_size               10
% 1.73/1.00  
% 1.73/1.00  ------ AIG Options
% 1.73/1.00  
% 1.73/1.00  --aig_mode                              false
% 1.73/1.00  
% 1.73/1.00  ------ Instantiation Options
% 1.73/1.00  
% 1.73/1.00  --instantiation_flag                    true
% 1.73/1.00  --inst_sos_flag                         false
% 1.73/1.00  --inst_sos_phase                        true
% 1.73/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.73/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.73/1.00  --inst_lit_sel_side                     none
% 1.73/1.00  --inst_solver_per_active                1400
% 1.73/1.00  --inst_solver_calls_frac                1.
% 1.73/1.00  --inst_passive_queue_type               priority_queues
% 1.73/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.73/1.00  --inst_passive_queues_freq              [25;2]
% 1.73/1.00  --inst_dismatching                      true
% 1.73/1.00  --inst_eager_unprocessed_to_passive     true
% 1.73/1.00  --inst_prop_sim_given                   true
% 1.73/1.00  --inst_prop_sim_new                     false
% 1.73/1.00  --inst_subs_new                         false
% 1.73/1.00  --inst_eq_res_simp                      false
% 1.73/1.00  --inst_subs_given                       false
% 1.73/1.00  --inst_orphan_elimination               true
% 1.73/1.00  --inst_learning_loop_flag               true
% 1.73/1.00  --inst_learning_start                   3000
% 1.73/1.00  --inst_learning_factor                  2
% 1.73/1.00  --inst_start_prop_sim_after_learn       3
% 1.73/1.00  --inst_sel_renew                        solver
% 1.73/1.00  --inst_lit_activity_flag                true
% 1.73/1.00  --inst_restr_to_given                   false
% 1.73/1.00  --inst_activity_threshold               500
% 1.73/1.00  --inst_out_proof                        true
% 1.73/1.00  
% 1.73/1.00  ------ Resolution Options
% 1.73/1.00  
% 1.73/1.00  --resolution_flag                       false
% 1.73/1.00  --res_lit_sel                           adaptive
% 1.73/1.00  --res_lit_sel_side                      none
% 1.73/1.00  --res_ordering                          kbo
% 1.73/1.00  --res_to_prop_solver                    active
% 1.73/1.00  --res_prop_simpl_new                    false
% 1.73/1.00  --res_prop_simpl_given                  true
% 1.73/1.00  --res_passive_queue_type                priority_queues
% 1.73/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.73/1.00  --res_passive_queues_freq               [15;5]
% 1.73/1.00  --res_forward_subs                      full
% 1.73/1.00  --res_backward_subs                     full
% 1.73/1.00  --res_forward_subs_resolution           true
% 1.73/1.00  --res_backward_subs_resolution          true
% 1.73/1.00  --res_orphan_elimination                true
% 1.73/1.00  --res_time_limit                        2.
% 1.73/1.00  --res_out_proof                         true
% 1.73/1.00  
% 1.73/1.00  ------ Superposition Options
% 1.73/1.00  
% 1.73/1.00  --superposition_flag                    true
% 1.73/1.00  --sup_passive_queue_type                priority_queues
% 1.73/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.73/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.73/1.00  --demod_completeness_check              fast
% 1.73/1.00  --demod_use_ground                      true
% 1.73/1.00  --sup_to_prop_solver                    passive
% 1.73/1.00  --sup_prop_simpl_new                    true
% 1.73/1.00  --sup_prop_simpl_given                  true
% 1.73/1.00  --sup_fun_splitting                     false
% 1.73/1.00  --sup_smt_interval                      50000
% 1.73/1.00  
% 1.73/1.00  ------ Superposition Simplification Setup
% 1.73/1.00  
% 1.73/1.00  --sup_indices_passive                   []
% 1.73/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.73/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.73/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.00  --sup_full_bw                           [BwDemod]
% 1.73/1.00  --sup_immed_triv                        [TrivRules]
% 1.73/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.73/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.00  --sup_immed_bw_main                     []
% 1.73/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.73/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.73/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.73/1.00  
% 1.73/1.00  ------ Combination Options
% 1.73/1.00  
% 1.73/1.00  --comb_res_mult                         3
% 1.73/1.00  --comb_sup_mult                         2
% 1.73/1.00  --comb_inst_mult                        10
% 1.73/1.00  
% 1.73/1.00  ------ Debug Options
% 1.73/1.00  
% 1.73/1.00  --dbg_backtrace                         false
% 1.73/1.00  --dbg_dump_prop_clauses                 false
% 1.73/1.00  --dbg_dump_prop_clauses_file            -
% 1.73/1.00  --dbg_out_stat                          false
% 1.73/1.00  
% 1.73/1.00  
% 1.73/1.00  
% 1.73/1.00  
% 1.73/1.00  ------ Proving...
% 1.73/1.00  
% 1.73/1.00  
% 1.73/1.00  % SZS status Theorem for theBenchmark.p
% 1.73/1.00  
% 1.73/1.00   Resolution empty clause
% 1.73/1.00  
% 1.73/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.73/1.00  
% 1.73/1.00  fof(f1,axiom,(
% 1.73/1.00    v1_xboole_0(k1_xboole_0)),
% 1.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f39,plain,(
% 1.73/1.00    v1_xboole_0(k1_xboole_0)),
% 1.73/1.00    inference(cnf_transformation,[],[f1])).
% 1.73/1.00  
% 1.73/1.00  fof(f11,conjecture,(
% 1.73/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f12,negated_conjecture,(
% 1.73/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.73/1.00    inference(negated_conjecture,[],[f11])).
% 1.73/1.00  
% 1.73/1.00  fof(f24,plain,(
% 1.73/1.00    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.73/1.00    inference(ennf_transformation,[],[f12])).
% 1.73/1.00  
% 1.73/1.00  fof(f25,plain,(
% 1.73/1.00    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.73/1.00    inference(flattening,[],[f24])).
% 1.73/1.00  
% 1.73/1.00  fof(f34,plain,(
% 1.73/1.00    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.73/1.00    inference(nnf_transformation,[],[f25])).
% 1.73/1.00  
% 1.73/1.00  fof(f35,plain,(
% 1.73/1.00    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.73/1.00    inference(flattening,[],[f34])).
% 1.73/1.00  
% 1.73/1.00  fof(f37,plain,(
% 1.73/1.00    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK2) | ~v3_tex_2(sK2,X0)) & (v1_zfmisc_1(sK2) | v3_tex_2(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK2))) )),
% 1.73/1.00    introduced(choice_axiom,[])).
% 1.73/1.00  
% 1.73/1.00  fof(f36,plain,(
% 1.73/1.00    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK1)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK1) & v2_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.73/1.00    introduced(choice_axiom,[])).
% 1.73/1.00  
% 1.73/1.00  fof(f38,plain,(
% 1.73/1.00    ((~v1_zfmisc_1(sK2) | ~v3_tex_2(sK2,sK1)) & (v1_zfmisc_1(sK2) | v3_tex_2(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(sK2)) & l1_pre_topc(sK1) & v2_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f35,f37,f36])).
% 1.73/1.00  
% 1.73/1.00  fof(f62,plain,(
% 1.73/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.73/1.00    inference(cnf_transformation,[],[f38])).
% 1.73/1.00  
% 1.73/1.00  fof(f8,axiom,(
% 1.73/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f18,plain,(
% 1.73/1.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.73/1.00    inference(ennf_transformation,[],[f8])).
% 1.73/1.00  
% 1.73/1.00  fof(f19,plain,(
% 1.73/1.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.73/1.00    inference(flattening,[],[f18])).
% 1.73/1.00  
% 1.73/1.00  fof(f28,plain,(
% 1.73/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.73/1.00    inference(nnf_transformation,[],[f19])).
% 1.73/1.00  
% 1.73/1.00  fof(f29,plain,(
% 1.73/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.73/1.00    inference(flattening,[],[f28])).
% 1.73/1.00  
% 1.73/1.00  fof(f30,plain,(
% 1.73/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.73/1.00    inference(rectify,[],[f29])).
% 1.73/1.00  
% 1.73/1.00  fof(f31,plain,(
% 1.73/1.00    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.73/1.00    introduced(choice_axiom,[])).
% 1.73/1.00  
% 1.73/1.00  fof(f32,plain,(
% 1.73/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 1.73/1.00  
% 1.73/1.00  fof(f50,plain,(
% 1.73/1.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f32])).
% 1.73/1.00  
% 1.73/1.00  fof(f60,plain,(
% 1.73/1.00    l1_pre_topc(sK1)),
% 1.73/1.00    inference(cnf_transformation,[],[f38])).
% 1.73/1.00  
% 1.73/1.00  fof(f10,axiom,(
% 1.73/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f22,plain,(
% 1.73/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.73/1.00    inference(ennf_transformation,[],[f10])).
% 1.73/1.00  
% 1.73/1.00  fof(f23,plain,(
% 1.73/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/1.00    inference(flattening,[],[f22])).
% 1.73/1.00  
% 1.73/1.00  fof(f33,plain,(
% 1.73/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/1.00    inference(nnf_transformation,[],[f23])).
% 1.73/1.00  
% 1.73/1.00  fof(f55,plain,(
% 1.73/1.00    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  fof(f6,axiom,(
% 1.73/1.00    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 1.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f15,plain,(
% 1.73/1.00    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 1.73/1.00    inference(ennf_transformation,[],[f6])).
% 1.73/1.00  
% 1.73/1.00  fof(f46,plain,(
% 1.73/1.00    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f15])).
% 1.73/1.00  
% 1.73/1.00  fof(f57,plain,(
% 1.73/1.00    ~v2_struct_0(sK1)),
% 1.73/1.00    inference(cnf_transformation,[],[f38])).
% 1.73/1.00  
% 1.73/1.00  fof(f58,plain,(
% 1.73/1.00    v2_pre_topc(sK1)),
% 1.73/1.00    inference(cnf_transformation,[],[f38])).
% 1.73/1.00  
% 1.73/1.00  fof(f59,plain,(
% 1.73/1.00    v2_tdlat_3(sK1)),
% 1.73/1.00    inference(cnf_transformation,[],[f38])).
% 1.73/1.00  
% 1.73/1.00  fof(f9,axiom,(
% 1.73/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f20,plain,(
% 1.73/1.00    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.73/1.00    inference(ennf_transformation,[],[f9])).
% 1.73/1.00  
% 1.73/1.00  fof(f21,plain,(
% 1.73/1.00    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.73/1.00    inference(flattening,[],[f20])).
% 1.73/1.00  
% 1.73/1.00  fof(f54,plain,(
% 1.73/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f21])).
% 1.73/1.00  
% 1.73/1.00  fof(f51,plain,(
% 1.73/1.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | v2_tex_2(sK0(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f32])).
% 1.73/1.00  
% 1.73/1.00  fof(f61,plain,(
% 1.73/1.00    ~v1_xboole_0(sK2)),
% 1.73/1.00    inference(cnf_transformation,[],[f38])).
% 1.73/1.00  
% 1.73/1.00  fof(f56,plain,(
% 1.73/1.00    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f33])).
% 1.73/1.00  
% 1.73/1.00  fof(f63,plain,(
% 1.73/1.00    v1_zfmisc_1(sK2) | v3_tex_2(sK2,sK1)),
% 1.73/1.00    inference(cnf_transformation,[],[f38])).
% 1.73/1.00  
% 1.73/1.00  fof(f48,plain,(
% 1.73/1.00    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f32])).
% 1.73/1.00  
% 1.73/1.00  fof(f64,plain,(
% 1.73/1.00    ~v1_zfmisc_1(sK2) | ~v3_tex_2(sK2,sK1)),
% 1.73/1.00    inference(cnf_transformation,[],[f38])).
% 1.73/1.00  
% 1.73/1.00  fof(f53,plain,(
% 1.73/1.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK0(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f32])).
% 1.73/1.00  
% 1.73/1.00  fof(f52,plain,(
% 1.73/1.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK0(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f32])).
% 1.73/1.00  
% 1.73/1.00  fof(f5,axiom,(
% 1.73/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f14,plain,(
% 1.73/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.73/1.00    inference(ennf_transformation,[],[f5])).
% 1.73/1.00  
% 1.73/1.00  fof(f45,plain,(
% 1.73/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f14])).
% 1.73/1.00  
% 1.73/1.00  fof(f2,axiom,(
% 1.73/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f26,plain,(
% 1.73/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.73/1.00    inference(nnf_transformation,[],[f2])).
% 1.73/1.00  
% 1.73/1.00  fof(f27,plain,(
% 1.73/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.73/1.00    inference(flattening,[],[f26])).
% 1.73/1.00  
% 1.73/1.00  fof(f40,plain,(
% 1.73/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.73/1.00    inference(cnf_transformation,[],[f27])).
% 1.73/1.00  
% 1.73/1.00  fof(f66,plain,(
% 1.73/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.73/1.00    inference(equality_resolution,[],[f40])).
% 1.73/1.00  
% 1.73/1.00  fof(f4,axiom,(
% 1.73/1.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f44,plain,(
% 1.73/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.73/1.00    inference(cnf_transformation,[],[f4])).
% 1.73/1.00  
% 1.73/1.00  fof(f3,axiom,(
% 1.73/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.73/1.00  
% 1.73/1.00  fof(f13,plain,(
% 1.73/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.73/1.00    inference(ennf_transformation,[],[f3])).
% 1.73/1.00  
% 1.73/1.00  fof(f43,plain,(
% 1.73/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f13])).
% 1.73/1.00  
% 1.73/1.00  fof(f42,plain,(
% 1.73/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.73/1.00    inference(cnf_transformation,[],[f27])).
% 1.73/1.00  
% 1.73/1.00  cnf(c_0,plain,
% 1.73/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 1.73/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1717,plain,
% 1.73/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_20,negated_conjecture,
% 1.73/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.73/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1712,plain,
% 1.73/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_12,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | ~ v2_tex_2(X0,X1)
% 1.73/1.00      | v3_tex_2(X0,X1)
% 1.73/1.00      | ~ l1_pre_topc(X1) ),
% 1.73/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_22,negated_conjecture,
% 1.73/1.00      ( l1_pre_topc(sK1) ),
% 1.73/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_419,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | ~ v2_tex_2(X0,X1)
% 1.73/1.00      | v3_tex_2(X0,X1)
% 1.73/1.00      | sK1 != X1 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_420,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ v2_tex_2(X0,sK1)
% 1.73/1.00      | v3_tex_2(X0,sK1) ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_419]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1708,plain,
% 1.73/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.73/1.00      | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.73/1.00      | v2_tex_2(X0,sK1) != iProver_top
% 1.73/1.00      | v3_tex_2(X0,sK1) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_420]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_17,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | ~ v2_tex_2(X0,X1)
% 1.73/1.00      | v2_struct_0(X1)
% 1.73/1.00      | ~ l1_pre_topc(X1)
% 1.73/1.00      | ~ v2_tdlat_3(X1)
% 1.73/1.00      | ~ v2_pre_topc(X1)
% 1.73/1.00      | v1_zfmisc_1(X0)
% 1.73/1.00      | v1_xboole_0(X0) ),
% 1.73/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_7,plain,
% 1.73/1.00      ( v1_zfmisc_1(X0) | ~ v1_xboole_0(X0) ),
% 1.73/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_139,plain,
% 1.73/1.00      ( v1_zfmisc_1(X0)
% 1.73/1.00      | ~ v2_pre_topc(X1)
% 1.73/1.00      | ~ v2_tdlat_3(X1)
% 1.73/1.00      | ~ l1_pre_topc(X1)
% 1.73/1.00      | v2_struct_0(X1)
% 1.73/1.00      | ~ v2_tex_2(X0,X1)
% 1.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ),
% 1.73/1.00      inference(global_propositional_subsumption,[status(thm)],[c_17,c_7]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_140,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | ~ v2_tex_2(X0,X1)
% 1.73/1.00      | v2_struct_0(X1)
% 1.73/1.00      | ~ l1_pre_topc(X1)
% 1.73/1.00      | ~ v2_tdlat_3(X1)
% 1.73/1.00      | ~ v2_pre_topc(X1)
% 1.73/1.00      | v1_zfmisc_1(X0) ),
% 1.73/1.00      inference(renaming,[status(thm)],[c_139]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_25,negated_conjecture,
% 1.73/1.00      ( ~ v2_struct_0(sK1) ),
% 1.73/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_328,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | ~ v2_tex_2(X0,X1)
% 1.73/1.00      | ~ l1_pre_topc(X1)
% 1.73/1.00      | ~ v2_tdlat_3(X1)
% 1.73/1.00      | ~ v2_pre_topc(X1)
% 1.73/1.00      | v1_zfmisc_1(X0)
% 1.73/1.00      | sK1 != X1 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_140,c_25]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_329,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ v2_tex_2(X0,sK1)
% 1.73/1.00      | ~ l1_pre_topc(sK1)
% 1.73/1.00      | ~ v2_tdlat_3(sK1)
% 1.73/1.00      | ~ v2_pre_topc(sK1)
% 1.73/1.00      | v1_zfmisc_1(X0) ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_328]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_24,negated_conjecture,
% 1.73/1.00      ( v2_pre_topc(sK1) ),
% 1.73/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_23,negated_conjecture,
% 1.73/1.00      ( v2_tdlat_3(sK1) ),
% 1.73/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_333,plain,
% 1.73/1.00      ( ~ v2_tex_2(X0,sK1)
% 1.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | v1_zfmisc_1(X0) ),
% 1.73/1.00      inference(global_propositional_subsumption,
% 1.73/1.00                [status(thm)],
% 1.73/1.00                [c_329,c_24,c_23,c_22]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_334,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ v2_tex_2(X0,sK1)
% 1.73/1.00      | v1_zfmisc_1(X0) ),
% 1.73/1.00      inference(renaming,[status(thm)],[c_333]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_15,plain,
% 1.73/1.00      ( ~ r1_tarski(X0,X1)
% 1.73/1.00      | ~ v1_zfmisc_1(X1)
% 1.73/1.00      | v1_xboole_0(X1)
% 1.73/1.00      | v1_xboole_0(X0)
% 1.73/1.00      | X1 = X0 ),
% 1.73/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_525,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ v2_tex_2(X0,sK1)
% 1.73/1.00      | ~ r1_tarski(X1,X2)
% 1.73/1.00      | v1_xboole_0(X2)
% 1.73/1.00      | v1_xboole_0(X1)
% 1.73/1.00      | X2 != X0
% 1.73/1.00      | X1 = X2 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_334,c_15]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_526,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ v2_tex_2(X0,sK1)
% 1.73/1.00      | ~ r1_tarski(X1,X0)
% 1.73/1.00      | v1_xboole_0(X1)
% 1.73/1.00      | v1_xboole_0(X0)
% 1.73/1.00      | X1 = X0 ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_525]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1704,plain,
% 1.73/1.00      ( X0 = X1
% 1.73/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.73/1.00      | v2_tex_2(X1,sK1) != iProver_top
% 1.73/1.00      | r1_tarski(X0,X1) != iProver_top
% 1.73/1.00      | v1_xboole_0(X1) = iProver_top
% 1.73/1.00      | v1_xboole_0(X0) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_526]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2642,plain,
% 1.73/1.00      ( sK0(sK1,X0) = X1
% 1.73/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.73/1.00      | v2_tex_2(X0,sK1) != iProver_top
% 1.73/1.00      | v2_tex_2(sK0(sK1,X0),sK1) != iProver_top
% 1.73/1.00      | v3_tex_2(X0,sK1) = iProver_top
% 1.73/1.00      | r1_tarski(X1,sK0(sK1,X0)) != iProver_top
% 1.73/1.00      | v1_xboole_0(X1) = iProver_top
% 1.73/1.00      | v1_xboole_0(sK0(sK1,X0)) = iProver_top ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_1708,c_1704]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_11,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | ~ v2_tex_2(X0,X1)
% 1.73/1.00      | v2_tex_2(sK0(X1,X0),X1)
% 1.73/1.00      | v3_tex_2(X0,X1)
% 1.73/1.00      | ~ l1_pre_topc(X1) ),
% 1.73/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_437,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | ~ v2_tex_2(X0,X1)
% 1.73/1.00      | v2_tex_2(sK0(X1,X0),X1)
% 1.73/1.00      | v3_tex_2(X0,X1)
% 1.73/1.00      | sK1 != X1 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_438,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ v2_tex_2(X0,sK1)
% 1.73/1.00      | v2_tex_2(sK0(sK1,X0),sK1)
% 1.73/1.00      | v3_tex_2(X0,sK1) ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_437]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_439,plain,
% 1.73/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.73/1.00      | v2_tex_2(X0,sK1) != iProver_top
% 1.73/1.00      | v2_tex_2(sK0(sK1,X0),sK1) = iProver_top
% 1.73/1.00      | v3_tex_2(X0,sK1) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_438]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_3283,plain,
% 1.73/1.00      ( v2_tex_2(X0,sK1) != iProver_top
% 1.73/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.73/1.00      | sK0(sK1,X0) = X1
% 1.73/1.00      | v3_tex_2(X0,sK1) = iProver_top
% 1.73/1.00      | r1_tarski(X1,sK0(sK1,X0)) != iProver_top
% 1.73/1.00      | v1_xboole_0(X1) = iProver_top
% 1.73/1.00      | v1_xboole_0(sK0(sK1,X0)) = iProver_top ),
% 1.73/1.00      inference(global_propositional_subsumption,[status(thm)],[c_2642,c_439]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_3284,plain,
% 1.73/1.00      ( sK0(sK1,X0) = X1
% 1.73/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.73/1.00      | v2_tex_2(X0,sK1) != iProver_top
% 1.73/1.00      | v3_tex_2(X0,sK1) = iProver_top
% 1.73/1.00      | r1_tarski(X1,sK0(sK1,X0)) != iProver_top
% 1.73/1.00      | v1_xboole_0(X1) = iProver_top
% 1.73/1.00      | v1_xboole_0(sK0(sK1,X0)) = iProver_top ),
% 1.73/1.00      inference(renaming,[status(thm)],[c_3283]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_3296,plain,
% 1.73/1.00      ( sK0(sK1,sK2) = X0
% 1.73/1.00      | v2_tex_2(sK2,sK1) != iProver_top
% 1.73/1.00      | v3_tex_2(sK2,sK1) = iProver_top
% 1.73/1.00      | r1_tarski(X0,sK0(sK1,sK2)) != iProver_top
% 1.73/1.00      | v1_xboole_0(X0) = iProver_top
% 1.73/1.00      | v1_xboole_0(sK0(sK1,sK2)) = iProver_top ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_1712,c_3284]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_21,negated_conjecture,
% 1.73/1.00      ( ~ v1_xboole_0(sK2) ),
% 1.73/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_30,plain,
% 1.73/1.00      ( v1_xboole_0(sK2) != iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_31,plain,
% 1.73/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_16,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | v2_tex_2(X0,X1)
% 1.73/1.00      | v2_struct_0(X1)
% 1.73/1.00      | ~ l1_pre_topc(X1)
% 1.73/1.00      | ~ v2_tdlat_3(X1)
% 1.73/1.00      | ~ v2_pre_topc(X1)
% 1.73/1.00      | ~ v1_zfmisc_1(X0)
% 1.73/1.00      | v1_xboole_0(X0) ),
% 1.73/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_349,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | v2_tex_2(X0,X1)
% 1.73/1.00      | ~ l1_pre_topc(X1)
% 1.73/1.00      | ~ v2_tdlat_3(X1)
% 1.73/1.00      | ~ v2_pre_topc(X1)
% 1.73/1.00      | ~ v1_zfmisc_1(X0)
% 1.73/1.00      | v1_xboole_0(X0)
% 1.73/1.00      | sK1 != X1 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_350,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | v2_tex_2(X0,sK1)
% 1.73/1.00      | ~ l1_pre_topc(sK1)
% 1.73/1.00      | ~ v2_tdlat_3(sK1)
% 1.73/1.00      | ~ v2_pre_topc(sK1)
% 1.73/1.00      | ~ v1_zfmisc_1(X0)
% 1.73/1.00      | v1_xboole_0(X0) ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_349]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_354,plain,
% 1.73/1.00      ( v2_tex_2(X0,sK1)
% 1.73/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ v1_zfmisc_1(X0)
% 1.73/1.00      | v1_xboole_0(X0) ),
% 1.73/1.00      inference(global_propositional_subsumption,
% 1.73/1.00                [status(thm)],
% 1.73/1.00                [c_350,c_24,c_23,c_22]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_355,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | v2_tex_2(X0,sK1)
% 1.73/1.00      | ~ v1_zfmisc_1(X0)
% 1.73/1.00      | v1_xboole_0(X0) ),
% 1.73/1.00      inference(renaming,[status(thm)],[c_354]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_19,negated_conjecture,
% 1.73/1.00      ( v3_tex_2(sK2,sK1) | v1_zfmisc_1(sK2) ),
% 1.73/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_191,plain,
% 1.73/1.00      ( v1_zfmisc_1(sK2) | v3_tex_2(sK2,sK1) ),
% 1.73/1.00      inference(prop_impl,[status(thm)],[c_19]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_192,plain,
% 1.73/1.00      ( v3_tex_2(sK2,sK1) | v1_zfmisc_1(sK2) ),
% 1.73/1.00      inference(renaming,[status(thm)],[c_191]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_565,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | v2_tex_2(X0,sK1)
% 1.73/1.00      | v3_tex_2(sK2,sK1)
% 1.73/1.00      | v1_xboole_0(X0)
% 1.73/1.00      | sK2 != X0 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_355,c_192]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_566,plain,
% 1.73/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | v2_tex_2(sK2,sK1)
% 1.73/1.00      | v3_tex_2(sK2,sK1)
% 1.73/1.00      | v1_xboole_0(sK2) ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_565]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_568,plain,
% 1.73/1.00      ( v3_tex_2(sK2,sK1) | v2_tex_2(sK2,sK1) ),
% 1.73/1.00      inference(global_propositional_subsumption,
% 1.73/1.00                [status(thm)],
% 1.73/1.00                [c_566,c_21,c_20]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_569,plain,
% 1.73/1.00      ( v2_tex_2(sK2,sK1) | v3_tex_2(sK2,sK1) ),
% 1.73/1.00      inference(renaming,[status(thm)],[c_568]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_14,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | v2_tex_2(X0,X1)
% 1.73/1.00      | ~ v3_tex_2(X0,X1)
% 1.73/1.00      | ~ l1_pre_topc(X1) ),
% 1.73/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_382,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | v2_tex_2(X0,X1)
% 1.73/1.00      | ~ v3_tex_2(X0,X1)
% 1.73/1.00      | sK1 != X1 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_383,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | v2_tex_2(X0,sK1)
% 1.73/1.00      | ~ v3_tex_2(X0,sK1) ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_382]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_820,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | v2_tex_2(X0,sK1)
% 1.73/1.00      | v2_tex_2(sK2,sK1)
% 1.73/1.00      | sK1 != sK1
% 1.73/1.00      | sK2 != X0 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_569,c_383]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_821,plain,
% 1.73/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | v2_tex_2(sK2,sK1) ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_820]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_822,plain,
% 1.73/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.73/1.00      | v2_tex_2(sK2,sK1) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_821]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_18,negated_conjecture,
% 1.73/1.00      ( ~ v3_tex_2(sK2,sK1) | ~ v1_zfmisc_1(sK2) ),
% 1.73/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_189,plain,
% 1.73/1.00      ( ~ v1_zfmisc_1(sK2) | ~ v3_tex_2(sK2,sK1) ),
% 1.73/1.00      inference(prop_impl,[status(thm)],[c_18]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_190,plain,
% 1.73/1.00      ( ~ v3_tex_2(sK2,sK1) | ~ v1_zfmisc_1(sK2) ),
% 1.73/1.00      inference(renaming,[status(thm)],[c_189]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_549,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ v2_tex_2(X0,sK1)
% 1.73/1.00      | ~ v3_tex_2(sK2,sK1)
% 1.73/1.00      | sK2 != X0 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_334,c_190]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_550,plain,
% 1.73/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ v2_tex_2(sK2,sK1)
% 1.73/1.00      | ~ v3_tex_2(sK2,sK1) ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_549]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_552,plain,
% 1.73/1.00      ( ~ v2_tex_2(sK2,sK1) | ~ v3_tex_2(sK2,sK1) ),
% 1.73/1.00      inference(global_propositional_subsumption,[status(thm)],[c_550,c_20]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_9,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | ~ v2_tex_2(X0,X1)
% 1.73/1.00      | v3_tex_2(X0,X1)
% 1.73/1.00      | ~ l1_pre_topc(X1)
% 1.73/1.00      | sK0(X1,X0) != X0 ),
% 1.73/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_473,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | ~ v2_tex_2(X0,X1)
% 1.73/1.00      | v3_tex_2(X0,X1)
% 1.73/1.00      | sK0(X1,X0) != X0
% 1.73/1.00      | sK1 != X1 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_474,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ v2_tex_2(X0,sK1)
% 1.73/1.00      | v3_tex_2(X0,sK1)
% 1.73/1.00      | sK0(sK1,X0) != X0 ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_473]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_831,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ v2_tex_2(X0,sK1)
% 1.73/1.00      | ~ v2_tex_2(sK2,sK1)
% 1.73/1.00      | sK0(sK1,X0) != X0
% 1.73/1.00      | sK1 != sK1
% 1.73/1.00      | sK2 != X0 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_552,c_474]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_832,plain,
% 1.73/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ v2_tex_2(sK2,sK1)
% 1.73/1.00      | sK0(sK1,sK2) != sK2 ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_831]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_10,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | ~ v2_tex_2(X0,X1)
% 1.73/1.00      | v3_tex_2(X0,X1)
% 1.73/1.00      | r1_tarski(X0,sK0(X1,X0))
% 1.73/1.00      | ~ l1_pre_topc(X1) ),
% 1.73/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_455,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.73/1.00      | ~ v2_tex_2(X0,X1)
% 1.73/1.00      | v3_tex_2(X0,X1)
% 1.73/1.00      | r1_tarski(X0,sK0(X1,X0))
% 1.73/1.00      | sK1 != X1 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_456,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ v2_tex_2(X0,sK1)
% 1.73/1.00      | v3_tex_2(X0,sK1)
% 1.73/1.00      | r1_tarski(X0,sK0(sK1,X0)) ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_455]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_839,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ v2_tex_2(X0,sK1)
% 1.73/1.00      | ~ v2_tex_2(sK2,sK1)
% 1.73/1.00      | r1_tarski(X0,sK0(sK1,X0))
% 1.73/1.00      | sK1 != sK1
% 1.73/1.00      | sK2 != X0 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_552,c_456]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_840,plain,
% 1.73/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ v2_tex_2(sK2,sK1)
% 1.73/1.00      | r1_tarski(sK2,sK0(sK1,sK2)) ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_839]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_841,plain,
% 1.73/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.73/1.00      | v2_tex_2(sK2,sK1) != iProver_top
% 1.73/1.00      | r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_840]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_850,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ v2_tex_2(X0,sK1)
% 1.73/1.00      | v2_tex_2(sK0(sK1,X0),sK1)
% 1.73/1.00      | ~ v2_tex_2(sK2,sK1)
% 1.73/1.00      | sK1 != sK1
% 1.73/1.00      | sK2 != X0 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_552,c_438]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_851,plain,
% 1.73/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | v2_tex_2(sK0(sK1,sK2),sK1)
% 1.73/1.00      | ~ v2_tex_2(sK2,sK1) ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_850]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_852,plain,
% 1.73/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.73/1.00      | v2_tex_2(sK0(sK1,sK2),sK1) = iProver_top
% 1.73/1.00      | v2_tex_2(sK2,sK1) != iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_851]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_861,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ v2_tex_2(X0,sK1)
% 1.73/1.00      | ~ v2_tex_2(sK2,sK1)
% 1.73/1.00      | sK1 != sK1
% 1.73/1.00      | sK2 != X0 ),
% 1.73/1.00      inference(resolution_lifted,[status(thm)],[c_552,c_420]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_862,plain,
% 1.73/1.00      ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ v2_tex_2(sK2,sK1) ),
% 1.73/1.00      inference(unflattening,[status(thm)],[c_861]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_863,plain,
% 1.73/1.00      ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.73/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.73/1.00      | v2_tex_2(sK2,sK1) != iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_862]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1374,plain,( X0 = X0 ),theory(equality) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2190,plain,
% 1.73/1.00      ( sK0(sK1,sK2) = sK0(sK1,sK2) ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_1374]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1991,plain,
% 1.73/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ v2_tex_2(X0,sK1)
% 1.73/1.00      | ~ r1_tarski(sK2,X0)
% 1.73/1.00      | v1_xboole_0(X0)
% 1.73/1.00      | v1_xboole_0(sK2)
% 1.73/1.00      | sK2 = X0 ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_526]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2209,plain,
% 1.73/1.00      ( ~ m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.73/1.00      | ~ v2_tex_2(sK0(sK1,sK2),sK1)
% 1.73/1.00      | ~ r1_tarski(sK2,sK0(sK1,sK2))
% 1.73/1.00      | v1_xboole_0(sK0(sK1,sK2))
% 1.73/1.00      | v1_xboole_0(sK2)
% 1.73/1.00      | sK2 = sK0(sK1,sK2) ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_1991]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2210,plain,
% 1.73/1.00      ( sK2 = sK0(sK1,sK2)
% 1.73/1.00      | m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.73/1.00      | v2_tex_2(sK0(sK1,sK2),sK1) != iProver_top
% 1.73/1.00      | r1_tarski(sK2,sK0(sK1,sK2)) != iProver_top
% 1.73/1.00      | v1_xboole_0(sK0(sK1,sK2)) = iProver_top
% 1.73/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_2209]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1375,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1948,plain,
% 1.73/1.00      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_1375]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2312,plain,
% 1.73/1.00      ( X0 != sK0(sK1,sK2) | X0 = sK2 | sK2 != sK0(sK1,sK2) ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_1948]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2746,plain,
% 1.73/1.00      ( sK0(sK1,sK2) != sK0(sK1,sK2)
% 1.73/1.00      | sK0(sK1,sK2) = sK2
% 1.73/1.00      | sK2 != sK0(sK1,sK2) ),
% 1.73/1.00      inference(instantiation,[status(thm)],[c_2312]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_3335,plain,
% 1.73/1.00      ( v1_xboole_0(sK0(sK1,sK2)) = iProver_top ),
% 1.73/1.00      inference(global_propositional_subsumption,
% 1.73/1.00                [status(thm)],
% 1.73/1.00                [c_3296,c_30,c_20,c_31,c_821,c_822,c_832,c_841,c_852,c_863,
% 1.73/1.00                 c_2190,c_2210,c_2746]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_6,plain,
% 1.73/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 1.73/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1713,plain,
% 1.73/1.00      ( X0 = X1
% 1.73/1.00      | v1_xboole_0(X0) != iProver_top
% 1.73/1.00      | v1_xboole_0(X1) != iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_3340,plain,
% 1.73/1.00      ( sK0(sK1,sK2) = X0 | v1_xboole_0(X0) != iProver_top ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_3335,c_1713]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_3434,plain,
% 1.73/1.00      ( sK0(sK1,sK2) = k1_xboole_0 ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_1717,c_3340]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1706,plain,
% 1.73/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.73/1.00      | v2_tex_2(X0,sK1) != iProver_top
% 1.73/1.00      | v3_tex_2(X0,sK1) = iProver_top
% 1.73/1.00      | r1_tarski(X0,sK0(sK1,X0)) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_456]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2042,plain,
% 1.73/1.00      ( v2_tex_2(sK2,sK1) != iProver_top
% 1.73/1.00      | v3_tex_2(sK2,sK1) = iProver_top
% 1.73/1.00      | r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_1712,c_1706]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2045,plain,
% 1.73/1.00      ( r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
% 1.73/1.00      inference(global_propositional_subsumption,
% 1.73/1.00                [status(thm)],
% 1.73/1.00                [c_2042,c_31,c_822,c_841]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_3652,plain,
% 1.73/1.00      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 1.73/1.00      inference(demodulation,[status(thm)],[c_3434,c_2045]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f66]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1715,plain,
% 1.73/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_5,plain,
% 1.73/1.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.73/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_4,plain,
% 1.73/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 1.73/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1714,plain,
% 1.73/1.00      ( r1_tarski(X0,X1) != iProver_top
% 1.73/1.00      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2291,plain,
% 1.73/1.00      ( r1_tarski(X0,X1) = iProver_top
% 1.73/1.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_5,c_1714]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_2866,plain,
% 1.73/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_1715,c_2291]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1,plain,
% 1.73/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.73/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1716,plain,
% 1.73/1.00      ( X0 = X1
% 1.73/1.00      | r1_tarski(X0,X1) != iProver_top
% 1.73/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_3085,plain,
% 1.73/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_2866,c_1716]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_3832,plain,
% 1.73/1.00      ( sK2 = k1_xboole_0 ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_3652,c_3085]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_1705,plain,
% 1.73/1.00      ( sK0(sK1,X0) != X0
% 1.73/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.73/1.00      | v2_tex_2(X0,sK1) != iProver_top
% 1.73/1.00      | v3_tex_2(X0,sK1) = iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_474]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_3680,plain,
% 1.73/1.00      ( sK2 != k1_xboole_0
% 1.73/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.73/1.00      | v2_tex_2(sK2,sK1) != iProver_top
% 1.73/1.00      | v3_tex_2(sK2,sK1) = iProver_top ),
% 1.73/1.00      inference(superposition,[status(thm)],[c_3434,c_1705]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_554,plain,
% 1.73/1.00      ( v2_tex_2(sK2,sK1) != iProver_top | v3_tex_2(sK2,sK1) != iProver_top ),
% 1.73/1.00      inference(predicate_to_equality,[status(thm)],[c_552]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_3847,plain,
% 1.73/1.00      ( sK2 != k1_xboole_0 ),
% 1.73/1.00      inference(global_propositional_subsumption,
% 1.73/1.00                [status(thm)],
% 1.73/1.00                [c_3680,c_31,c_554,c_822]) ).
% 1.73/1.00  
% 1.73/1.00  cnf(c_3851,plain,
% 1.73/1.00      ( $false ),
% 1.73/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3832,c_3847]) ).
% 1.73/1.00  
% 1.73/1.00  
% 1.73/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.73/1.00  
% 1.73/1.00  ------                               Statistics
% 1.73/1.00  
% 1.73/1.00  ------ General
% 1.73/1.00  
% 1.73/1.00  abstr_ref_over_cycles:                  0
% 1.73/1.00  abstr_ref_under_cycles:                 0
% 1.73/1.00  gc_basic_clause_elim:                   0
% 1.73/1.00  forced_gc_time:                         0
% 1.73/1.00  parsing_time:                           0.009
% 1.73/1.00  unif_index_cands_time:                  0.
% 1.73/1.00  unif_index_add_time:                    0.
% 1.73/1.00  orderings_time:                         0.
% 1.73/1.00  out_proof_time:                         0.012
% 1.73/1.00  total_time:                             0.148
% 1.73/1.00  num_of_symbols:                         48
% 1.73/1.00  num_of_terms:                           1647
% 1.73/1.00  
% 1.73/1.00  ------ Preprocessing
% 1.73/1.00  
% 1.73/1.00  num_of_splits:                          0
% 1.73/1.00  num_of_split_atoms:                     0
% 1.73/1.00  num_of_reused_defs:                     0
% 1.73/1.00  num_eq_ax_congr_red:                    11
% 1.73/1.00  num_of_sem_filtered_clauses:            1
% 1.73/1.00  num_of_subtypes:                        0
% 1.73/1.00  monotx_restored_types:                  0
% 1.73/1.00  sat_num_of_epr_types:                   0
% 1.73/1.00  sat_num_of_non_cyclic_types:            0
% 1.73/1.00  sat_guarded_non_collapsed_types:        0
% 1.73/1.00  num_pure_diseq_elim:                    0
% 1.73/1.00  simp_replaced_by:                       0
% 1.73/1.00  res_preprocessed:                       102
% 1.73/1.00  prep_upred:                             0
% 1.73/1.00  prep_unflattend:                        30
% 1.73/1.00  smt_new_axioms:                         0
% 1.73/1.00  pred_elim_cands:                        5
% 1.73/1.00  pred_elim:                              5
% 1.73/1.00  pred_elim_cl:                           7
% 1.73/1.00  pred_elim_cycles:                       8
% 1.73/1.00  merged_defs:                            2
% 1.73/1.00  merged_defs_ncl:                        0
% 1.73/1.00  bin_hyper_res:                          2
% 1.73/1.00  prep_cycles:                            4
% 1.73/1.00  pred_elim_time:                         0.028
% 1.73/1.00  splitting_time:                         0.
% 1.73/1.00  sem_filter_time:                        0.
% 1.73/1.00  monotx_time:                            0.
% 1.73/1.00  subtype_inf_time:                       0.
% 1.73/1.00  
% 1.73/1.00  ------ Problem properties
% 1.73/1.00  
% 1.73/1.00  clauses:                                18
% 1.73/1.00  conjectures:                            2
% 1.73/1.00  epr:                                    8
% 1.73/1.00  horn:                                   13
% 1.73/1.00  ground:                                 5
% 1.73/1.00  unary:                                  7
% 1.73/1.00  binary:                                 1
% 1.73/1.00  lits:                                   49
% 1.73/1.00  lits_eq:                                7
% 1.73/1.00  fd_pure:                                0
% 1.73/1.00  fd_pseudo:                              0
% 1.73/1.00  fd_cond:                                1
% 1.73/1.00  fd_pseudo_cond:                         4
% 1.73/1.00  ac_symbols:                             0
% 1.73/1.00  
% 1.73/1.00  ------ Propositional Solver
% 1.73/1.00  
% 1.73/1.00  prop_solver_calls:                      27
% 1.73/1.00  prop_fast_solver_calls:                 1012
% 1.73/1.00  smt_solver_calls:                       0
% 1.73/1.00  smt_fast_solver_calls:                  0
% 1.73/1.00  prop_num_of_clauses:                    980
% 1.73/1.00  prop_preprocess_simplified:             3984
% 1.73/1.00  prop_fo_subsumed:                       66
% 1.73/1.00  prop_solver_time:                       0.
% 1.73/1.00  smt_solver_time:                        0.
% 1.73/1.00  smt_fast_solver_time:                   0.
% 1.73/1.00  prop_fast_solver_time:                  0.
% 1.73/1.00  prop_unsat_core_time:                   0.
% 1.73/1.00  
% 1.73/1.00  ------ QBF
% 1.73/1.00  
% 1.73/1.00  qbf_q_res:                              0
% 1.73/1.00  qbf_num_tautologies:                    0
% 1.73/1.00  qbf_prep_cycles:                        0
% 1.73/1.00  
% 1.73/1.00  ------ BMC1
% 1.73/1.00  
% 1.73/1.00  bmc1_current_bound:                     -1
% 1.73/1.00  bmc1_last_solved_bound:                 -1
% 1.73/1.00  bmc1_unsat_core_size:                   -1
% 1.73/1.00  bmc1_unsat_core_parents_size:           -1
% 1.73/1.00  bmc1_merge_next_fun:                    0
% 1.73/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.73/1.00  
% 1.73/1.00  ------ Instantiation
% 1.73/1.00  
% 1.73/1.00  inst_num_of_clauses:                    282
% 1.73/1.00  inst_num_in_passive:                    81
% 1.73/1.00  inst_num_in_active:                     180
% 1.73/1.00  inst_num_in_unprocessed:                21
% 1.73/1.00  inst_num_of_loops:                      200
% 1.73/1.00  inst_num_of_learning_restarts:          0
% 1.73/1.00  inst_num_moves_active_passive:          17
% 1.73/1.00  inst_lit_activity:                      0
% 1.73/1.00  inst_lit_activity_moves:                0
% 1.73/1.00  inst_num_tautologies:                   0
% 1.73/1.00  inst_num_prop_implied:                  0
% 1.73/1.00  inst_num_existing_simplified:           0
% 1.73/1.00  inst_num_eq_res_simplified:             0
% 1.73/1.00  inst_num_child_elim:                    0
% 1.73/1.00  inst_num_of_dismatching_blockings:      33
% 1.73/1.00  inst_num_of_non_proper_insts:           270
% 1.73/1.00  inst_num_of_duplicates:                 0
% 1.73/1.00  inst_inst_num_from_inst_to_res:         0
% 1.73/1.00  inst_dismatching_checking_time:         0.
% 1.73/1.00  
% 1.73/1.00  ------ Resolution
% 1.73/1.00  
% 1.73/1.00  res_num_of_clauses:                     0
% 1.73/1.00  res_num_in_passive:                     0
% 1.73/1.00  res_num_in_active:                      0
% 1.73/1.00  res_num_of_loops:                       106
% 1.73/1.00  res_forward_subset_subsumed:            66
% 1.73/1.00  res_backward_subset_subsumed:           1
% 1.73/1.00  res_forward_subsumed:                   0
% 1.73/1.00  res_backward_subsumed:                  4
% 1.73/1.00  res_forward_subsumption_resolution:     0
% 1.73/1.00  res_backward_subsumption_resolution:    1
% 1.73/1.00  res_clause_to_clause_subsumption:       279
% 1.73/1.00  res_orphan_elimination:                 0
% 1.73/1.00  res_tautology_del:                      42
% 1.73/1.00  res_num_eq_res_simplified:              0
% 1.73/1.00  res_num_sel_changes:                    0
% 1.73/1.00  res_moves_from_active_to_pass:          0
% 1.73/1.00  
% 1.73/1.00  ------ Superposition
% 1.73/1.00  
% 1.73/1.00  sup_time_total:                         0.
% 1.73/1.00  sup_time_generating:                    0.
% 1.73/1.00  sup_time_sim_full:                      0.
% 1.73/1.00  sup_time_sim_immed:                     0.
% 1.73/1.00  
% 1.73/1.00  sup_num_of_clauses:                     44
% 1.73/1.00  sup_num_in_active:                      32
% 1.73/1.00  sup_num_in_passive:                     12
% 1.73/1.00  sup_num_of_loops:                       39
% 1.73/1.00  sup_fw_superposition:                   27
% 1.73/1.00  sup_bw_superposition:                   19
% 1.73/1.00  sup_immediate_simplified:               10
% 1.73/1.00  sup_given_eliminated:                   2
% 1.73/1.00  comparisons_done:                       0
% 1.73/1.00  comparisons_avoided:                    0
% 1.73/1.00  
% 1.73/1.00  ------ Simplifications
% 1.73/1.00  
% 1.73/1.00  
% 1.73/1.00  sim_fw_subset_subsumed:                 5
% 1.73/1.00  sim_bw_subset_subsumed:                 0
% 1.73/1.00  sim_fw_subsumed:                        2
% 1.73/1.00  sim_bw_subsumed:                        2
% 1.73/1.00  sim_fw_subsumption_res:                 1
% 1.73/1.00  sim_bw_subsumption_res:                 0
% 1.73/1.00  sim_tautology_del:                      0
% 1.73/1.00  sim_eq_tautology_del:                   5
% 1.73/1.00  sim_eq_res_simp:                        0
% 1.73/1.00  sim_fw_demodulated:                     0
% 1.73/1.00  sim_bw_demodulated:                     7
% 1.73/1.00  sim_light_normalised:                   3
% 1.73/1.00  sim_joinable_taut:                      0
% 1.73/1.00  sim_joinable_simp:                      0
% 1.73/1.00  sim_ac_normalised:                      0
% 1.73/1.00  sim_smt_subsumption:                    0
% 1.73/1.00  
%------------------------------------------------------------------------------
