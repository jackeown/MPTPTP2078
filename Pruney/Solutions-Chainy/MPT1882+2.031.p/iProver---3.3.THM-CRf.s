%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:24 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  158 (1431 expanded)
%              Number of clauses        :  102 ( 316 expanded)
%              Number of leaves         :   11 ( 322 expanded)
%              Depth                    :   28
%              Number of atoms          :  682 (11346 expanded)
%              Number of equality atoms :  111 ( 272 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f19])).

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
    inference(flattening,[],[f33])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ( ~ v1_zfmisc_1(sK3)
          | ~ v3_tex_2(sK3,X0) )
        & ( v1_zfmisc_1(sK3)
          | v3_tex_2(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
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
            | ~ v3_tex_2(X1,sK2) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK2)
      & v2_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( ~ v1_zfmisc_1(sK3)
      | ~ v3_tex_2(sK3,sK2) )
    & ( v1_zfmisc_1(sK3)
      | v3_tex_2(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & ~ v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f34,f36,f35])).

fof(f60,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
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

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f13])).

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
    inference(flattening,[],[f27])).

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
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK1(X0,X1) != X1
        & r1_tarski(X1,sK1(X0,X1))
        & v2_tex_2(sK1(X0,X1),X0)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK1(X0,X1) != X1
                & r1_tarski(X1,sK1(X0,X1))
                & v2_tex_2(sK1(X0,X1),X0)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK1(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,
    ( v1_zfmisc_1(sK3)
    | v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,
    ( ~ v1_zfmisc_1(sK3)
    | ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f39,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK1(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK1(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1690,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | r1_tarski(X0,sK1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | r1_tarski(X0,sK1(X1,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_495,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | r1_tarski(X0,sK1(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_1682,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | r1_tarski(X0,sK1(sK2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_495])).

cnf(c_2022,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top
    | r1_tarski(sK3,sK1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1690,c_1682])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ v1_zfmisc_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_387,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | ~ v1_zfmisc_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_388,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(X0,sK2)
    | ~ v1_zfmisc_1(X0)
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_22,negated_conjecture,
    ( v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_392,plain,
    ( ~ v1_zfmisc_1(X0)
    | v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_388,c_23,c_22,c_21])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(X0,sK2)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_392])).

cnf(c_18,negated_conjecture,
    ( v3_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_191,plain,
    ( v1_zfmisc_1(sK3)
    | v3_tex_2(sK3,sK2) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_192,plain,
    ( v3_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(renaming,[status(thm)],[c_191])).

cnf(c_623,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(X0,sK2)
    | v3_tex_2(sK3,sK2)
    | v1_xboole_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_393,c_192])).

cnf(c_624,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(sK3,sK2)
    | v3_tex_2(sK3,sK2)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_623])).

cnf(c_20,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_626,plain,
    ( v3_tex_2(sK3,sK2)
    | v2_tex_2(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_624,c_20,c_19])).

cnf(c_627,plain,
    ( v2_tex_2(sK3,sK2)
    | v3_tex_2(sK3,sK2) ),
    inference(renaming,[status(thm)],[c_626])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_421,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_422,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(X0,sK2)
    | ~ v3_tex_2(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_800,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(X0,sK2)
    | v2_tex_2(sK3,sK2)
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_627,c_422])).

cnf(c_801,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_800])).

cnf(c_802,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_tex_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_801])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_struct_0(X1)
    | v1_zfmisc_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v1_zfmisc_1(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v1_zfmisc_1(X0)
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_368,plain,
    ( v1_zfmisc_1(X0)
    | ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_364,c_23,c_22,c_21])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_368])).

cnf(c_17,negated_conjecture,
    ( ~ v3_tex_2(sK3,sK2)
    | ~ v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_189,plain,
    ( ~ v1_zfmisc_1(sK3)
    | ~ v3_tex_2(sK3,sK2) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_190,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | ~ v1_zfmisc_1(sK3) ),
    inference(renaming,[status(thm)],[c_189])).

cnf(c_609,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(sK3,sK2)
    | v1_xboole_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_369,c_190])).

cnf(c_610,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(sK3,sK2)
    | ~ v3_tex_2(sK3,sK2)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_609])).

cnf(c_612,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_610,c_20,c_19])).

cnf(c_613,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ v3_tex_2(sK3,sK2) ),
    inference(renaming,[status(thm)],[c_612])).

cnf(c_832,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | r1_tarski(X0,sK1(sK2,X0))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_613,c_495])).

cnf(c_833,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(sK3,sK2)
    | r1_tarski(sK3,sK1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_832])).

cnf(c_834,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top
    | r1_tarski(sK3,sK1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_833])).

cnf(c_2025,plain,
    ( r1_tarski(sK3,sK1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2022,c_30,c_802,c_834])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_187,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_188,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_187])).

cnf(c_343,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | v1_xboole_0(X2)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_188])).

cnf(c_344,plain,
    ( r1_tarski(k1_tarski(sK0(X0)),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_1687,plain,
    ( r1_tarski(k1_tarski(sK0(X0)),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_803,plain,
    ( v2_tex_2(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_801,c_19])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_585,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_192])).

cnf(c_586,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ r1_tarski(X0,sK3)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 = X0 ),
    inference(unflattening,[status(thm)],[c_585])).

cnf(c_590,plain,
    ( v1_xboole_0(X0)
    | ~ r1_tarski(X0,sK3)
    | v3_tex_2(sK3,sK2)
    | sK3 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_586,c_20])).

cnf(c_591,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ r1_tarski(X0,sK3)
    | v1_xboole_0(X0)
    | sK3 = X0 ),
    inference(renaming,[status(thm)],[c_590])).

cnf(c_656,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ r1_tarski(X0,sK3)
    | v1_xboole_0(X0)
    | sK3 = X0 ),
    inference(resolution,[status(thm)],[c_591,c_613])).

cnf(c_811,plain,
    ( ~ r1_tarski(X0,sK3)
    | v1_xboole_0(X0)
    | sK3 = X0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_803,c_656])).

cnf(c_1678,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_2690,plain,
    ( k1_tarski(sK0(sK3)) = sK3
    | v1_xboole_0(k1_tarski(sK0(sK3))) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1687,c_1678])).

cnf(c_29,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2794,plain,
    ( v1_xboole_0(k1_tarski(sK0(sK3))) = iProver_top
    | k1_tarski(sK0(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2690,c_29])).

cnf(c_2795,plain,
    ( k1_tarski(sK0(sK3)) = sK3
    | v1_xboole_0(k1_tarski(sK0(sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2794])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1691,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_185,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_tarski(X0),X1) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_186,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_185])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_332,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | ~ v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_186,c_1])).

cnf(c_1688,plain,
    ( r1_tarski(k1_tarski(X0),X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_2184,plain,
    ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1691,c_1688])).

cnf(c_2800,plain,
    ( k1_tarski(sK0(sK3)) = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2795,c_2184])).

cnf(c_2802,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2800,c_1688])).

cnf(c_3326,plain,
    ( v1_xboole_0(sK1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2025,c_2802])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | X0 != X2
    | X2 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_369])).

cnf(c_564,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | ~ r1_tarski(X1,X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_563])).

cnf(c_1834,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | ~ r1_tarski(sK3,X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | X0 = sK3 ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_2450,plain,
    ( ~ m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(sK1(sK2,sK3),sK2)
    | ~ r1_tarski(sK3,sK1(sK2,sK3))
    | v1_xboole_0(sK1(sK2,sK3))
    | v1_xboole_0(sK3)
    | sK1(sK2,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_1834])).

cnf(c_2457,plain,
    ( sK1(sK2,sK3) = sK3
    | m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_tex_2(sK1(sK2,sK3),sK2) != iProver_top
    | r1_tarski(sK3,sK1(sK2,sK3)) != iProver_top
    | v1_xboole_0(sK1(sK2,sK3)) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2450])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_459,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_854,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_613,c_459])).

cnf(c_855,plain,
    ( m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_854])).

cnf(c_856,plain,
    ( m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_855])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK1(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_476,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK1(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_477,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v2_tex_2(sK1(sK2,X0),sK2)
    | v3_tex_2(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_843,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v2_tex_2(sK1(sK2,X0),sK2)
    | ~ v2_tex_2(sK3,sK2)
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_613,c_477])).

cnf(c_844,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(sK1(sK2,sK3),sK2)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_843])).

cnf(c_845,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_tex_2(sK1(sK2,sK3),sK2) = iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_844])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | sK1(X1,X0) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | sK1(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_824,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | sK1(sK2,X0) != X0
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_613,c_513])).

cnf(c_825,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(sK3,sK2)
    | sK1(sK2,sK3) != sK3 ),
    inference(unflattening,[status(thm)],[c_824])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3326,c_2457,c_856,c_845,c_834,c_825,c_802,c_801,c_30,c_19,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:51:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.65/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.00  
% 1.65/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.65/1.00  
% 1.65/1.00  ------  iProver source info
% 1.65/1.00  
% 1.65/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.65/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.65/1.00  git: non_committed_changes: false
% 1.65/1.00  git: last_make_outside_of_git: false
% 1.65/1.00  
% 1.65/1.00  ------ 
% 1.65/1.00  
% 1.65/1.00  ------ Input Options
% 1.65/1.00  
% 1.65/1.00  --out_options                           all
% 1.65/1.00  --tptp_safe_out                         true
% 1.65/1.00  --problem_path                          ""
% 1.65/1.00  --include_path                          ""
% 1.65/1.00  --clausifier                            res/vclausify_rel
% 1.65/1.00  --clausifier_options                    --mode clausify
% 1.65/1.00  --stdin                                 false
% 1.65/1.00  --stats_out                             all
% 1.65/1.00  
% 1.65/1.00  ------ General Options
% 1.65/1.00  
% 1.65/1.00  --fof                                   false
% 1.65/1.00  --time_out_real                         305.
% 1.65/1.00  --time_out_virtual                      -1.
% 1.65/1.00  --symbol_type_check                     false
% 1.65/1.00  --clausify_out                          false
% 1.65/1.00  --sig_cnt_out                           false
% 1.65/1.00  --trig_cnt_out                          false
% 1.65/1.00  --trig_cnt_out_tolerance                1.
% 1.65/1.00  --trig_cnt_out_sk_spl                   false
% 1.65/1.00  --abstr_cl_out                          false
% 1.65/1.00  
% 1.65/1.00  ------ Global Options
% 1.65/1.00  
% 1.65/1.00  --schedule                              default
% 1.65/1.00  --add_important_lit                     false
% 1.65/1.00  --prop_solver_per_cl                    1000
% 1.65/1.00  --min_unsat_core                        false
% 1.65/1.00  --soft_assumptions                      false
% 1.65/1.00  --soft_lemma_size                       3
% 1.65/1.00  --prop_impl_unit_size                   0
% 1.65/1.00  --prop_impl_unit                        []
% 1.65/1.00  --share_sel_clauses                     true
% 1.65/1.00  --reset_solvers                         false
% 1.65/1.00  --bc_imp_inh                            [conj_cone]
% 1.65/1.00  --conj_cone_tolerance                   3.
% 1.65/1.00  --extra_neg_conj                        none
% 1.65/1.00  --large_theory_mode                     true
% 1.65/1.00  --prolific_symb_bound                   200
% 1.65/1.00  --lt_threshold                          2000
% 1.65/1.00  --clause_weak_htbl                      true
% 1.65/1.00  --gc_record_bc_elim                     false
% 1.65/1.00  
% 1.65/1.00  ------ Preprocessing Options
% 1.65/1.00  
% 1.65/1.00  --preprocessing_flag                    true
% 1.65/1.00  --time_out_prep_mult                    0.1
% 1.65/1.00  --splitting_mode                        input
% 1.65/1.00  --splitting_grd                         true
% 1.65/1.00  --splitting_cvd                         false
% 1.65/1.00  --splitting_cvd_svl                     false
% 1.65/1.00  --splitting_nvd                         32
% 1.65/1.00  --sub_typing                            true
% 1.65/1.00  --prep_gs_sim                           true
% 1.65/1.00  --prep_unflatten                        true
% 1.65/1.00  --prep_res_sim                          true
% 1.65/1.00  --prep_upred                            true
% 1.65/1.00  --prep_sem_filter                       exhaustive
% 1.65/1.00  --prep_sem_filter_out                   false
% 1.65/1.00  --pred_elim                             true
% 1.65/1.00  --res_sim_input                         true
% 1.65/1.00  --eq_ax_congr_red                       true
% 1.65/1.00  --pure_diseq_elim                       true
% 1.65/1.00  --brand_transform                       false
% 1.65/1.00  --non_eq_to_eq                          false
% 1.65/1.00  --prep_def_merge                        true
% 1.65/1.00  --prep_def_merge_prop_impl              false
% 1.65/1.00  --prep_def_merge_mbd                    true
% 1.65/1.00  --prep_def_merge_tr_red                 false
% 1.65/1.00  --prep_def_merge_tr_cl                  false
% 1.65/1.00  --smt_preprocessing                     true
% 1.65/1.00  --smt_ac_axioms                         fast
% 1.65/1.00  --preprocessed_out                      false
% 1.65/1.00  --preprocessed_stats                    false
% 1.65/1.00  
% 1.65/1.00  ------ Abstraction refinement Options
% 1.65/1.00  
% 1.65/1.00  --abstr_ref                             []
% 1.65/1.00  --abstr_ref_prep                        false
% 1.65/1.00  --abstr_ref_until_sat                   false
% 1.65/1.00  --abstr_ref_sig_restrict                funpre
% 1.65/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.65/1.00  --abstr_ref_under                       []
% 1.65/1.00  
% 1.65/1.00  ------ SAT Options
% 1.65/1.00  
% 1.65/1.00  --sat_mode                              false
% 1.65/1.00  --sat_fm_restart_options                ""
% 1.65/1.00  --sat_gr_def                            false
% 1.65/1.00  --sat_epr_types                         true
% 1.65/1.00  --sat_non_cyclic_types                  false
% 1.65/1.00  --sat_finite_models                     false
% 1.65/1.00  --sat_fm_lemmas                         false
% 1.65/1.00  --sat_fm_prep                           false
% 1.65/1.00  --sat_fm_uc_incr                        true
% 1.65/1.00  --sat_out_model                         small
% 1.65/1.00  --sat_out_clauses                       false
% 1.65/1.00  
% 1.65/1.00  ------ QBF Options
% 1.65/1.00  
% 1.65/1.00  --qbf_mode                              false
% 1.65/1.00  --qbf_elim_univ                         false
% 1.65/1.00  --qbf_dom_inst                          none
% 1.65/1.00  --qbf_dom_pre_inst                      false
% 1.65/1.00  --qbf_sk_in                             false
% 1.65/1.00  --qbf_pred_elim                         true
% 1.65/1.00  --qbf_split                             512
% 1.65/1.00  
% 1.65/1.00  ------ BMC1 Options
% 1.65/1.00  
% 1.65/1.00  --bmc1_incremental                      false
% 1.65/1.00  --bmc1_axioms                           reachable_all
% 1.65/1.00  --bmc1_min_bound                        0
% 1.65/1.00  --bmc1_max_bound                        -1
% 1.65/1.00  --bmc1_max_bound_default                -1
% 1.65/1.00  --bmc1_symbol_reachability              true
% 1.65/1.00  --bmc1_property_lemmas                  false
% 1.65/1.00  --bmc1_k_induction                      false
% 1.65/1.00  --bmc1_non_equiv_states                 false
% 1.65/1.00  --bmc1_deadlock                         false
% 1.65/1.00  --bmc1_ucm                              false
% 1.65/1.00  --bmc1_add_unsat_core                   none
% 1.65/1.00  --bmc1_unsat_core_children              false
% 1.65/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.65/1.00  --bmc1_out_stat                         full
% 1.65/1.00  --bmc1_ground_init                      false
% 1.65/1.00  --bmc1_pre_inst_next_state              false
% 1.65/1.00  --bmc1_pre_inst_state                   false
% 1.65/1.00  --bmc1_pre_inst_reach_state             false
% 1.65/1.00  --bmc1_out_unsat_core                   false
% 1.65/1.00  --bmc1_aig_witness_out                  false
% 1.65/1.00  --bmc1_verbose                          false
% 1.65/1.00  --bmc1_dump_clauses_tptp                false
% 1.65/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.65/1.00  --bmc1_dump_file                        -
% 1.65/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.65/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.65/1.00  --bmc1_ucm_extend_mode                  1
% 1.65/1.00  --bmc1_ucm_init_mode                    2
% 1.65/1.00  --bmc1_ucm_cone_mode                    none
% 1.65/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.65/1.00  --bmc1_ucm_relax_model                  4
% 1.65/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.65/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.65/1.00  --bmc1_ucm_layered_model                none
% 1.65/1.00  --bmc1_ucm_max_lemma_size               10
% 1.65/1.00  
% 1.65/1.00  ------ AIG Options
% 1.65/1.00  
% 1.65/1.00  --aig_mode                              false
% 1.65/1.00  
% 1.65/1.00  ------ Instantiation Options
% 1.65/1.00  
% 1.65/1.00  --instantiation_flag                    true
% 1.65/1.00  --inst_sos_flag                         false
% 1.65/1.00  --inst_sos_phase                        true
% 1.65/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.65/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.65/1.00  --inst_lit_sel_side                     num_symb
% 1.65/1.00  --inst_solver_per_active                1400
% 1.65/1.00  --inst_solver_calls_frac                1.
% 1.65/1.00  --inst_passive_queue_type               priority_queues
% 1.65/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.65/1.00  --inst_passive_queues_freq              [25;2]
% 1.65/1.00  --inst_dismatching                      true
% 1.65/1.00  --inst_eager_unprocessed_to_passive     true
% 1.65/1.00  --inst_prop_sim_given                   true
% 1.65/1.00  --inst_prop_sim_new                     false
% 1.65/1.00  --inst_subs_new                         false
% 1.65/1.00  --inst_eq_res_simp                      false
% 1.65/1.00  --inst_subs_given                       false
% 1.65/1.00  --inst_orphan_elimination               true
% 1.65/1.00  --inst_learning_loop_flag               true
% 1.65/1.00  --inst_learning_start                   3000
% 1.65/1.00  --inst_learning_factor                  2
% 1.65/1.00  --inst_start_prop_sim_after_learn       3
% 1.65/1.00  --inst_sel_renew                        solver
% 1.65/1.00  --inst_lit_activity_flag                true
% 1.65/1.00  --inst_restr_to_given                   false
% 1.65/1.00  --inst_activity_threshold               500
% 1.65/1.00  --inst_out_proof                        true
% 1.65/1.00  
% 1.65/1.00  ------ Resolution Options
% 1.65/1.00  
% 1.65/1.00  --resolution_flag                       true
% 1.65/1.00  --res_lit_sel                           adaptive
% 1.65/1.00  --res_lit_sel_side                      none
% 1.65/1.00  --res_ordering                          kbo
% 1.65/1.00  --res_to_prop_solver                    active
% 1.65/1.00  --res_prop_simpl_new                    false
% 1.65/1.00  --res_prop_simpl_given                  true
% 1.65/1.00  --res_passive_queue_type                priority_queues
% 1.65/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.65/1.00  --res_passive_queues_freq               [15;5]
% 1.65/1.00  --res_forward_subs                      full
% 1.65/1.00  --res_backward_subs                     full
% 1.65/1.00  --res_forward_subs_resolution           true
% 1.65/1.00  --res_backward_subs_resolution          true
% 1.65/1.00  --res_orphan_elimination                true
% 1.65/1.00  --res_time_limit                        2.
% 1.65/1.00  --res_out_proof                         true
% 1.65/1.00  
% 1.65/1.00  ------ Superposition Options
% 1.65/1.00  
% 1.65/1.00  --superposition_flag                    true
% 1.65/1.00  --sup_passive_queue_type                priority_queues
% 1.65/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.65/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.65/1.00  --demod_completeness_check              fast
% 1.65/1.00  --demod_use_ground                      true
% 1.65/1.00  --sup_to_prop_solver                    passive
% 1.65/1.00  --sup_prop_simpl_new                    true
% 1.65/1.00  --sup_prop_simpl_given                  true
% 1.65/1.00  --sup_fun_splitting                     false
% 1.65/1.00  --sup_smt_interval                      50000
% 1.65/1.00  
% 1.65/1.00  ------ Superposition Simplification Setup
% 1.65/1.00  
% 1.65/1.00  --sup_indices_passive                   []
% 1.65/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.65/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.00  --sup_full_bw                           [BwDemod]
% 1.65/1.00  --sup_immed_triv                        [TrivRules]
% 1.65/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.65/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.00  --sup_immed_bw_main                     []
% 1.65/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.65/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/1.00  
% 1.65/1.00  ------ Combination Options
% 1.65/1.00  
% 1.65/1.00  --comb_res_mult                         3
% 1.65/1.00  --comb_sup_mult                         2
% 1.65/1.00  --comb_inst_mult                        10
% 1.65/1.00  
% 1.65/1.00  ------ Debug Options
% 1.65/1.00  
% 1.65/1.00  --dbg_backtrace                         false
% 1.65/1.00  --dbg_dump_prop_clauses                 false
% 1.65/1.00  --dbg_dump_prop_clauses_file            -
% 1.65/1.00  --dbg_out_stat                          false
% 1.65/1.00  ------ Parsing...
% 1.65/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.65/1.00  
% 1.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.65/1.00  
% 1.65/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.65/1.00  
% 1.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.65/1.00  ------ Proving...
% 1.65/1.00  ------ Problem Properties 
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  clauses                                 16
% 1.65/1.00  conjectures                             2
% 1.65/1.00  EPR                                     6
% 1.65/1.00  Horn                                    10
% 1.65/1.00  unary                                   5
% 1.65/1.00  binary                                  2
% 1.65/1.00  lits                                    46
% 1.65/1.00  lits eq                                 5
% 1.65/1.00  fd_pure                                 0
% 1.65/1.00  fd_pseudo                               0
% 1.65/1.00  fd_cond                                 1
% 1.65/1.00  fd_pseudo_cond                          3
% 1.65/1.00  AC symbols                              0
% 1.65/1.00  
% 1.65/1.00  ------ Schedule dynamic 5 is on 
% 1.65/1.00  
% 1.65/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  ------ 
% 1.65/1.00  Current options:
% 1.65/1.00  ------ 
% 1.65/1.00  
% 1.65/1.00  ------ Input Options
% 1.65/1.00  
% 1.65/1.00  --out_options                           all
% 1.65/1.00  --tptp_safe_out                         true
% 1.65/1.00  --problem_path                          ""
% 1.65/1.00  --include_path                          ""
% 1.65/1.00  --clausifier                            res/vclausify_rel
% 1.65/1.00  --clausifier_options                    --mode clausify
% 1.65/1.00  --stdin                                 false
% 1.65/1.00  --stats_out                             all
% 1.65/1.00  
% 1.65/1.00  ------ General Options
% 1.65/1.00  
% 1.65/1.00  --fof                                   false
% 1.65/1.00  --time_out_real                         305.
% 1.65/1.00  --time_out_virtual                      -1.
% 1.65/1.00  --symbol_type_check                     false
% 1.65/1.00  --clausify_out                          false
% 1.65/1.00  --sig_cnt_out                           false
% 1.65/1.00  --trig_cnt_out                          false
% 1.65/1.00  --trig_cnt_out_tolerance                1.
% 1.65/1.00  --trig_cnt_out_sk_spl                   false
% 1.65/1.00  --abstr_cl_out                          false
% 1.65/1.00  
% 1.65/1.00  ------ Global Options
% 1.65/1.00  
% 1.65/1.00  --schedule                              default
% 1.65/1.00  --add_important_lit                     false
% 1.65/1.00  --prop_solver_per_cl                    1000
% 1.65/1.00  --min_unsat_core                        false
% 1.65/1.00  --soft_assumptions                      false
% 1.65/1.00  --soft_lemma_size                       3
% 1.65/1.00  --prop_impl_unit_size                   0
% 1.65/1.00  --prop_impl_unit                        []
% 1.65/1.00  --share_sel_clauses                     true
% 1.65/1.00  --reset_solvers                         false
% 1.65/1.00  --bc_imp_inh                            [conj_cone]
% 1.65/1.00  --conj_cone_tolerance                   3.
% 1.65/1.00  --extra_neg_conj                        none
% 1.65/1.00  --large_theory_mode                     true
% 1.65/1.00  --prolific_symb_bound                   200
% 1.65/1.00  --lt_threshold                          2000
% 1.65/1.00  --clause_weak_htbl                      true
% 1.65/1.00  --gc_record_bc_elim                     false
% 1.65/1.00  
% 1.65/1.00  ------ Preprocessing Options
% 1.65/1.00  
% 1.65/1.00  --preprocessing_flag                    true
% 1.65/1.00  --time_out_prep_mult                    0.1
% 1.65/1.00  --splitting_mode                        input
% 1.65/1.00  --splitting_grd                         true
% 1.65/1.00  --splitting_cvd                         false
% 1.65/1.00  --splitting_cvd_svl                     false
% 1.65/1.00  --splitting_nvd                         32
% 1.65/1.00  --sub_typing                            true
% 1.65/1.00  --prep_gs_sim                           true
% 1.65/1.00  --prep_unflatten                        true
% 1.65/1.00  --prep_res_sim                          true
% 1.65/1.00  --prep_upred                            true
% 1.65/1.00  --prep_sem_filter                       exhaustive
% 1.65/1.00  --prep_sem_filter_out                   false
% 1.65/1.00  --pred_elim                             true
% 1.65/1.00  --res_sim_input                         true
% 1.65/1.00  --eq_ax_congr_red                       true
% 1.65/1.00  --pure_diseq_elim                       true
% 1.65/1.00  --brand_transform                       false
% 1.65/1.00  --non_eq_to_eq                          false
% 1.65/1.00  --prep_def_merge                        true
% 1.65/1.00  --prep_def_merge_prop_impl              false
% 1.65/1.00  --prep_def_merge_mbd                    true
% 1.65/1.00  --prep_def_merge_tr_red                 false
% 1.65/1.00  --prep_def_merge_tr_cl                  false
% 1.65/1.00  --smt_preprocessing                     true
% 1.65/1.00  --smt_ac_axioms                         fast
% 1.65/1.00  --preprocessed_out                      false
% 1.65/1.00  --preprocessed_stats                    false
% 1.65/1.00  
% 1.65/1.00  ------ Abstraction refinement Options
% 1.65/1.00  
% 1.65/1.00  --abstr_ref                             []
% 1.65/1.00  --abstr_ref_prep                        false
% 1.65/1.00  --abstr_ref_until_sat                   false
% 1.65/1.00  --abstr_ref_sig_restrict                funpre
% 1.65/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.65/1.00  --abstr_ref_under                       []
% 1.65/1.00  
% 1.65/1.00  ------ SAT Options
% 1.65/1.00  
% 1.65/1.00  --sat_mode                              false
% 1.65/1.00  --sat_fm_restart_options                ""
% 1.65/1.00  --sat_gr_def                            false
% 1.65/1.00  --sat_epr_types                         true
% 1.65/1.00  --sat_non_cyclic_types                  false
% 1.65/1.00  --sat_finite_models                     false
% 1.65/1.00  --sat_fm_lemmas                         false
% 1.65/1.00  --sat_fm_prep                           false
% 1.65/1.00  --sat_fm_uc_incr                        true
% 1.65/1.00  --sat_out_model                         small
% 1.65/1.00  --sat_out_clauses                       false
% 1.65/1.00  
% 1.65/1.00  ------ QBF Options
% 1.65/1.00  
% 1.65/1.00  --qbf_mode                              false
% 1.65/1.00  --qbf_elim_univ                         false
% 1.65/1.00  --qbf_dom_inst                          none
% 1.65/1.00  --qbf_dom_pre_inst                      false
% 1.65/1.00  --qbf_sk_in                             false
% 1.65/1.00  --qbf_pred_elim                         true
% 1.65/1.00  --qbf_split                             512
% 1.65/1.00  
% 1.65/1.00  ------ BMC1 Options
% 1.65/1.00  
% 1.65/1.00  --bmc1_incremental                      false
% 1.65/1.00  --bmc1_axioms                           reachable_all
% 1.65/1.00  --bmc1_min_bound                        0
% 1.65/1.00  --bmc1_max_bound                        -1
% 1.65/1.00  --bmc1_max_bound_default                -1
% 1.65/1.00  --bmc1_symbol_reachability              true
% 1.65/1.00  --bmc1_property_lemmas                  false
% 1.65/1.00  --bmc1_k_induction                      false
% 1.65/1.00  --bmc1_non_equiv_states                 false
% 1.65/1.00  --bmc1_deadlock                         false
% 1.65/1.00  --bmc1_ucm                              false
% 1.65/1.00  --bmc1_add_unsat_core                   none
% 1.65/1.00  --bmc1_unsat_core_children              false
% 1.65/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.65/1.00  --bmc1_out_stat                         full
% 1.65/1.00  --bmc1_ground_init                      false
% 1.65/1.00  --bmc1_pre_inst_next_state              false
% 1.65/1.00  --bmc1_pre_inst_state                   false
% 1.65/1.00  --bmc1_pre_inst_reach_state             false
% 1.65/1.00  --bmc1_out_unsat_core                   false
% 1.65/1.00  --bmc1_aig_witness_out                  false
% 1.65/1.00  --bmc1_verbose                          false
% 1.65/1.00  --bmc1_dump_clauses_tptp                false
% 1.65/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.65/1.00  --bmc1_dump_file                        -
% 1.65/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.65/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.65/1.00  --bmc1_ucm_extend_mode                  1
% 1.65/1.00  --bmc1_ucm_init_mode                    2
% 1.65/1.00  --bmc1_ucm_cone_mode                    none
% 1.65/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.65/1.00  --bmc1_ucm_relax_model                  4
% 1.65/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.65/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.65/1.00  --bmc1_ucm_layered_model                none
% 1.65/1.00  --bmc1_ucm_max_lemma_size               10
% 1.65/1.00  
% 1.65/1.00  ------ AIG Options
% 1.65/1.00  
% 1.65/1.00  --aig_mode                              false
% 1.65/1.00  
% 1.65/1.00  ------ Instantiation Options
% 1.65/1.00  
% 1.65/1.00  --instantiation_flag                    true
% 1.65/1.00  --inst_sos_flag                         false
% 1.65/1.00  --inst_sos_phase                        true
% 1.65/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.65/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.65/1.00  --inst_lit_sel_side                     none
% 1.65/1.00  --inst_solver_per_active                1400
% 1.65/1.00  --inst_solver_calls_frac                1.
% 1.65/1.00  --inst_passive_queue_type               priority_queues
% 1.65/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.65/1.00  --inst_passive_queues_freq              [25;2]
% 1.65/1.00  --inst_dismatching                      true
% 1.65/1.00  --inst_eager_unprocessed_to_passive     true
% 1.65/1.00  --inst_prop_sim_given                   true
% 1.65/1.00  --inst_prop_sim_new                     false
% 1.65/1.00  --inst_subs_new                         false
% 1.65/1.00  --inst_eq_res_simp                      false
% 1.65/1.00  --inst_subs_given                       false
% 1.65/1.00  --inst_orphan_elimination               true
% 1.65/1.00  --inst_learning_loop_flag               true
% 1.65/1.00  --inst_learning_start                   3000
% 1.65/1.00  --inst_learning_factor                  2
% 1.65/1.00  --inst_start_prop_sim_after_learn       3
% 1.65/1.00  --inst_sel_renew                        solver
% 1.65/1.00  --inst_lit_activity_flag                true
% 1.65/1.00  --inst_restr_to_given                   false
% 1.65/1.00  --inst_activity_threshold               500
% 1.65/1.00  --inst_out_proof                        true
% 1.65/1.00  
% 1.65/1.00  ------ Resolution Options
% 1.65/1.00  
% 1.65/1.00  --resolution_flag                       false
% 1.65/1.00  --res_lit_sel                           adaptive
% 1.65/1.00  --res_lit_sel_side                      none
% 1.65/1.00  --res_ordering                          kbo
% 1.65/1.00  --res_to_prop_solver                    active
% 1.65/1.00  --res_prop_simpl_new                    false
% 1.65/1.00  --res_prop_simpl_given                  true
% 1.65/1.00  --res_passive_queue_type                priority_queues
% 1.65/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.65/1.00  --res_passive_queues_freq               [15;5]
% 1.65/1.00  --res_forward_subs                      full
% 1.65/1.00  --res_backward_subs                     full
% 1.65/1.00  --res_forward_subs_resolution           true
% 1.65/1.00  --res_backward_subs_resolution          true
% 1.65/1.00  --res_orphan_elimination                true
% 1.65/1.00  --res_time_limit                        2.
% 1.65/1.00  --res_out_proof                         true
% 1.65/1.00  
% 1.65/1.00  ------ Superposition Options
% 1.65/1.00  
% 1.65/1.00  --superposition_flag                    true
% 1.65/1.00  --sup_passive_queue_type                priority_queues
% 1.65/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.65/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.65/1.00  --demod_completeness_check              fast
% 1.65/1.00  --demod_use_ground                      true
% 1.65/1.00  --sup_to_prop_solver                    passive
% 1.65/1.00  --sup_prop_simpl_new                    true
% 1.65/1.00  --sup_prop_simpl_given                  true
% 1.65/1.00  --sup_fun_splitting                     false
% 1.65/1.00  --sup_smt_interval                      50000
% 1.65/1.00  
% 1.65/1.00  ------ Superposition Simplification Setup
% 1.65/1.00  
% 1.65/1.00  --sup_indices_passive                   []
% 1.65/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.65/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.65/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.00  --sup_full_bw                           [BwDemod]
% 1.65/1.00  --sup_immed_triv                        [TrivRules]
% 1.65/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.65/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.00  --sup_immed_bw_main                     []
% 1.65/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.65/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.65/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.65/1.00  
% 1.65/1.00  ------ Combination Options
% 1.65/1.00  
% 1.65/1.00  --comb_res_mult                         3
% 1.65/1.00  --comb_sup_mult                         2
% 1.65/1.00  --comb_inst_mult                        10
% 1.65/1.00  
% 1.65/1.00  ------ Debug Options
% 1.65/1.00  
% 1.65/1.00  --dbg_backtrace                         false
% 1.65/1.00  --dbg_dump_prop_clauses                 false
% 1.65/1.00  --dbg_dump_prop_clauses_file            -
% 1.65/1.00  --dbg_out_stat                          false
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  ------ Proving...
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  % SZS status Theorem for theBenchmark.p
% 1.65/1.00  
% 1.65/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.65/1.00  
% 1.65/1.00  fof(f8,conjecture,(
% 1.65/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f9,negated_conjecture,(
% 1.65/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.65/1.00    inference(negated_conjecture,[],[f8])).
% 1.65/1.00  
% 1.65/1.00  fof(f18,plain,(
% 1.65/1.00    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.65/1.00    inference(ennf_transformation,[],[f9])).
% 1.65/1.00  
% 1.65/1.00  fof(f19,plain,(
% 1.65/1.00    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.65/1.00    inference(flattening,[],[f18])).
% 1.65/1.00  
% 1.65/1.00  fof(f33,plain,(
% 1.65/1.00    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.65/1.00    inference(nnf_transformation,[],[f19])).
% 1.65/1.00  
% 1.65/1.00  fof(f34,plain,(
% 1.65/1.00    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.65/1.00    inference(flattening,[],[f33])).
% 1.65/1.00  
% 1.65/1.00  fof(f36,plain,(
% 1.65/1.00    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,X0)) & (v1_zfmisc_1(sK3) | v3_tex_2(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK3))) )),
% 1.65/1.00    introduced(choice_axiom,[])).
% 1.65/1.00  
% 1.65/1.00  fof(f35,plain,(
% 1.65/1.00    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK2)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.65/1.00    introduced(choice_axiom,[])).
% 1.65/1.00  
% 1.65/1.00  fof(f37,plain,(
% 1.65/1.00    ((~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,sK2)) & (v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f34,f36,f35])).
% 1.65/1.00  
% 1.65/1.00  fof(f60,plain,(
% 1.65/1.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.65/1.00    inference(cnf_transformation,[],[f37])).
% 1.65/1.00  
% 1.65/1.00  fof(f5,axiom,(
% 1.65/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f12,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/1.00    inference(ennf_transformation,[],[f5])).
% 1.65/1.00  
% 1.65/1.00  fof(f13,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/1.00    inference(flattening,[],[f12])).
% 1.65/1.00  
% 1.65/1.00  fof(f27,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/1.00    inference(nnf_transformation,[],[f13])).
% 1.65/1.00  
% 1.65/1.00  fof(f28,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/1.00    inference(flattening,[],[f27])).
% 1.65/1.00  
% 1.65/1.00  fof(f29,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/1.00    inference(rectify,[],[f28])).
% 1.65/1.00  
% 1.65/1.00  fof(f30,plain,(
% 1.65/1.00    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.65/1.00    introduced(choice_axiom,[])).
% 1.65/1.00  
% 1.65/1.00  fof(f31,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 1.65/1.00  
% 1.65/1.00  fof(f50,plain,(
% 1.65/1.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK1(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f31])).
% 1.65/1.00  
% 1.65/1.00  fof(f58,plain,(
% 1.65/1.00    l1_pre_topc(sK2)),
% 1.65/1.00    inference(cnf_transformation,[],[f37])).
% 1.65/1.00  
% 1.65/1.00  fof(f7,axiom,(
% 1.65/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f16,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.65/1.00    inference(ennf_transformation,[],[f7])).
% 1.65/1.00  
% 1.65/1.00  fof(f17,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.65/1.00    inference(flattening,[],[f16])).
% 1.65/1.00  
% 1.65/1.00  fof(f32,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.65/1.00    inference(nnf_transformation,[],[f17])).
% 1.65/1.00  
% 1.65/1.00  fof(f54,plain,(
% 1.65/1.00    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f32])).
% 1.65/1.00  
% 1.65/1.00  fof(f55,plain,(
% 1.65/1.00    ~v2_struct_0(sK2)),
% 1.65/1.00    inference(cnf_transformation,[],[f37])).
% 1.65/1.00  
% 1.65/1.00  fof(f56,plain,(
% 1.65/1.00    v2_pre_topc(sK2)),
% 1.65/1.00    inference(cnf_transformation,[],[f37])).
% 1.65/1.00  
% 1.65/1.00  fof(f57,plain,(
% 1.65/1.00    v2_tdlat_3(sK2)),
% 1.65/1.00    inference(cnf_transformation,[],[f37])).
% 1.65/1.00  
% 1.65/1.00  fof(f61,plain,(
% 1.65/1.00    v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2)),
% 1.65/1.00    inference(cnf_transformation,[],[f37])).
% 1.65/1.00  
% 1.65/1.00  fof(f59,plain,(
% 1.65/1.00    ~v1_xboole_0(sK3)),
% 1.65/1.00    inference(cnf_transformation,[],[f37])).
% 1.65/1.00  
% 1.65/1.00  fof(f46,plain,(
% 1.65/1.00    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f31])).
% 1.65/1.00  
% 1.65/1.00  fof(f53,plain,(
% 1.65/1.00    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f32])).
% 1.65/1.00  
% 1.65/1.00  fof(f62,plain,(
% 1.65/1.00    ~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,sK2)),
% 1.65/1.00    inference(cnf_transformation,[],[f37])).
% 1.65/1.00  
% 1.65/1.00  fof(f1,axiom,(
% 1.65/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f20,plain,(
% 1.65/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.65/1.00    inference(nnf_transformation,[],[f1])).
% 1.65/1.00  
% 1.65/1.00  fof(f21,plain,(
% 1.65/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.65/1.00    inference(rectify,[],[f20])).
% 1.65/1.00  
% 1.65/1.00  fof(f22,plain,(
% 1.65/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.65/1.00    introduced(choice_axiom,[])).
% 1.65/1.00  
% 1.65/1.00  fof(f23,plain,(
% 1.65/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 1.65/1.00  
% 1.65/1.00  fof(f39,plain,(
% 1.65/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f23])).
% 1.65/1.00  
% 1.65/1.00  fof(f3,axiom,(
% 1.65/1.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f26,plain,(
% 1.65/1.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.65/1.00    inference(nnf_transformation,[],[f3])).
% 1.65/1.00  
% 1.65/1.00  fof(f44,plain,(
% 1.65/1.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f26])).
% 1.65/1.00  
% 1.65/1.00  fof(f6,axiom,(
% 1.65/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f14,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.65/1.00    inference(ennf_transformation,[],[f6])).
% 1.65/1.00  
% 1.65/1.00  fof(f15,plain,(
% 1.65/1.00    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.65/1.00    inference(flattening,[],[f14])).
% 1.65/1.00  
% 1.65/1.00  fof(f52,plain,(
% 1.65/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f15])).
% 1.65/1.00  
% 1.65/1.00  fof(f2,axiom,(
% 1.65/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.65/1.00  
% 1.65/1.00  fof(f24,plain,(
% 1.65/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.65/1.00    inference(nnf_transformation,[],[f2])).
% 1.65/1.00  
% 1.65/1.00  fof(f25,plain,(
% 1.65/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.65/1.00    inference(flattening,[],[f24])).
% 1.65/1.00  
% 1.65/1.00  fof(f40,plain,(
% 1.65/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.65/1.00    inference(cnf_transformation,[],[f25])).
% 1.65/1.00  
% 1.65/1.00  fof(f64,plain,(
% 1.65/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.65/1.00    inference(equality_resolution,[],[f40])).
% 1.65/1.00  
% 1.65/1.00  fof(f43,plain,(
% 1.65/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f26])).
% 1.65/1.00  
% 1.65/1.00  fof(f38,plain,(
% 1.65/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f23])).
% 1.65/1.00  
% 1.65/1.00  fof(f48,plain,(
% 1.65/1.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f31])).
% 1.65/1.00  
% 1.65/1.00  fof(f49,plain,(
% 1.65/1.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | v2_tex_2(sK1(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f31])).
% 1.65/1.00  
% 1.65/1.00  fof(f51,plain,(
% 1.65/1.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK1(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.65/1.00    inference(cnf_transformation,[],[f31])).
% 1.65/1.00  
% 1.65/1.00  cnf(c_19,negated_conjecture,
% 1.65/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.65/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1690,plain,
% 1.65/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_9,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | ~ v2_tex_2(X0,X1)
% 1.65/1.00      | v3_tex_2(X0,X1)
% 1.65/1.00      | r1_tarski(X0,sK1(X1,X0))
% 1.65/1.00      | ~ l1_pre_topc(X1) ),
% 1.65/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_21,negated_conjecture,
% 1.65/1.00      ( l1_pre_topc(sK2) ),
% 1.65/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_494,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | ~ v2_tex_2(X0,X1)
% 1.65/1.00      | v3_tex_2(X0,X1)
% 1.65/1.00      | r1_tarski(X0,sK1(X1,X0))
% 1.65/1.00      | sK2 != X1 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_495,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ v2_tex_2(X0,sK2)
% 1.65/1.00      | v3_tex_2(X0,sK2)
% 1.65/1.00      | r1_tarski(X0,sK1(sK2,X0)) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_494]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1682,plain,
% 1.65/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.65/1.00      | v2_tex_2(X0,sK2) != iProver_top
% 1.65/1.00      | v3_tex_2(X0,sK2) = iProver_top
% 1.65/1.00      | r1_tarski(X0,sK1(sK2,X0)) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_495]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2022,plain,
% 1.65/1.00      ( v2_tex_2(sK3,sK2) != iProver_top
% 1.65/1.00      | v3_tex_2(sK3,sK2) = iProver_top
% 1.65/1.00      | r1_tarski(sK3,sK1(sK2,sK3)) = iProver_top ),
% 1.65/1.00      inference(superposition,[status(thm)],[c_1690,c_1682]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_30,plain,
% 1.65/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_15,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | v2_tex_2(X0,X1)
% 1.65/1.00      | v2_struct_0(X1)
% 1.65/1.00      | ~ v1_zfmisc_1(X0)
% 1.65/1.00      | ~ l1_pre_topc(X1)
% 1.65/1.00      | ~ v2_tdlat_3(X1)
% 1.65/1.00      | ~ v2_pre_topc(X1)
% 1.65/1.00      | v1_xboole_0(X0) ),
% 1.65/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_24,negated_conjecture,
% 1.65/1.00      ( ~ v2_struct_0(sK2) ),
% 1.65/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_387,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | v2_tex_2(X0,X1)
% 1.65/1.00      | ~ v1_zfmisc_1(X0)
% 1.65/1.00      | ~ l1_pre_topc(X1)
% 1.65/1.00      | ~ v2_tdlat_3(X1)
% 1.65/1.00      | ~ v2_pre_topc(X1)
% 1.65/1.00      | v1_xboole_0(X0)
% 1.65/1.00      | sK2 != X1 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_388,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | v2_tex_2(X0,sK2)
% 1.65/1.00      | ~ v1_zfmisc_1(X0)
% 1.65/1.00      | ~ l1_pre_topc(sK2)
% 1.65/1.00      | ~ v2_tdlat_3(sK2)
% 1.65/1.00      | ~ v2_pre_topc(sK2)
% 1.65/1.00      | v1_xboole_0(X0) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_387]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_23,negated_conjecture,
% 1.65/1.00      ( v2_pre_topc(sK2) ),
% 1.65/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_22,negated_conjecture,
% 1.65/1.00      ( v2_tdlat_3(sK2) ),
% 1.65/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_392,plain,
% 1.65/1.00      ( ~ v1_zfmisc_1(X0)
% 1.65/1.00      | v2_tex_2(X0,sK2)
% 1.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | v1_xboole_0(X0) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_388,c_23,c_22,c_21]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_393,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | v2_tex_2(X0,sK2)
% 1.65/1.00      | ~ v1_zfmisc_1(X0)
% 1.65/1.00      | v1_xboole_0(X0) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_392]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_18,negated_conjecture,
% 1.65/1.00      ( v3_tex_2(sK3,sK2) | v1_zfmisc_1(sK3) ),
% 1.65/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_191,plain,
% 1.65/1.00      ( v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2) ),
% 1.65/1.00      inference(prop_impl,[status(thm)],[c_18]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_192,plain,
% 1.65/1.00      ( v3_tex_2(sK3,sK2) | v1_zfmisc_1(sK3) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_191]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_623,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | v2_tex_2(X0,sK2)
% 1.65/1.00      | v3_tex_2(sK3,sK2)
% 1.65/1.00      | v1_xboole_0(X0)
% 1.65/1.00      | sK3 != X0 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_393,c_192]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_624,plain,
% 1.65/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | v2_tex_2(sK3,sK2)
% 1.65/1.00      | v3_tex_2(sK3,sK2)
% 1.65/1.00      | v1_xboole_0(sK3) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_623]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_20,negated_conjecture,
% 1.65/1.00      ( ~ v1_xboole_0(sK3) ),
% 1.65/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_626,plain,
% 1.65/1.00      ( v3_tex_2(sK3,sK2) | v2_tex_2(sK3,sK2) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_624,c_20,c_19]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_627,plain,
% 1.65/1.00      ( v2_tex_2(sK3,sK2) | v3_tex_2(sK3,sK2) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_626]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_13,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | v2_tex_2(X0,X1)
% 1.65/1.00      | ~ v3_tex_2(X0,X1)
% 1.65/1.00      | ~ l1_pre_topc(X1) ),
% 1.65/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_421,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | v2_tex_2(X0,X1)
% 1.65/1.00      | ~ v3_tex_2(X0,X1)
% 1.65/1.00      | sK2 != X1 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_422,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | v2_tex_2(X0,sK2)
% 1.65/1.00      | ~ v3_tex_2(X0,sK2) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_421]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_800,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | v2_tex_2(X0,sK2)
% 1.65/1.00      | v2_tex_2(sK3,sK2)
% 1.65/1.00      | sK2 != sK2
% 1.65/1.00      | sK3 != X0 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_627,c_422]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_801,plain,
% 1.65/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | v2_tex_2(sK3,sK2) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_800]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_802,plain,
% 1.65/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.65/1.00      | v2_tex_2(sK3,sK2) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_801]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_16,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | ~ v2_tex_2(X0,X1)
% 1.65/1.00      | v2_struct_0(X1)
% 1.65/1.00      | v1_zfmisc_1(X0)
% 1.65/1.00      | ~ l1_pre_topc(X1)
% 1.65/1.00      | ~ v2_tdlat_3(X1)
% 1.65/1.00      | ~ v2_pre_topc(X1)
% 1.65/1.00      | v1_xboole_0(X0) ),
% 1.65/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_363,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | ~ v2_tex_2(X0,X1)
% 1.65/1.00      | v1_zfmisc_1(X0)
% 1.65/1.00      | ~ l1_pre_topc(X1)
% 1.65/1.00      | ~ v2_tdlat_3(X1)
% 1.65/1.00      | ~ v2_pre_topc(X1)
% 1.65/1.00      | v1_xboole_0(X0)
% 1.65/1.00      | sK2 != X1 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_364,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ v2_tex_2(X0,sK2)
% 1.65/1.00      | v1_zfmisc_1(X0)
% 1.65/1.00      | ~ l1_pre_topc(sK2)
% 1.65/1.00      | ~ v2_tdlat_3(sK2)
% 1.65/1.00      | ~ v2_pre_topc(sK2)
% 1.65/1.00      | v1_xboole_0(X0) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_363]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_368,plain,
% 1.65/1.00      ( v1_zfmisc_1(X0)
% 1.65/1.00      | ~ v2_tex_2(X0,sK2)
% 1.65/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | v1_xboole_0(X0) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_364,c_23,c_22,c_21]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_369,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ v2_tex_2(X0,sK2)
% 1.65/1.00      | v1_zfmisc_1(X0)
% 1.65/1.00      | v1_xboole_0(X0) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_368]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_17,negated_conjecture,
% 1.65/1.00      ( ~ v3_tex_2(sK3,sK2) | ~ v1_zfmisc_1(sK3) ),
% 1.65/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_189,plain,
% 1.65/1.00      ( ~ v1_zfmisc_1(sK3) | ~ v3_tex_2(sK3,sK2) ),
% 1.65/1.00      inference(prop_impl,[status(thm)],[c_17]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_190,plain,
% 1.65/1.00      ( ~ v3_tex_2(sK3,sK2) | ~ v1_zfmisc_1(sK3) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_189]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_609,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ v2_tex_2(X0,sK2)
% 1.65/1.00      | ~ v3_tex_2(sK3,sK2)
% 1.65/1.00      | v1_xboole_0(X0)
% 1.65/1.00      | sK3 != X0 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_369,c_190]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_610,plain,
% 1.65/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ v2_tex_2(sK3,sK2)
% 1.65/1.00      | ~ v3_tex_2(sK3,sK2)
% 1.65/1.00      | v1_xboole_0(sK3) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_609]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_612,plain,
% 1.65/1.00      ( ~ v3_tex_2(sK3,sK2) | ~ v2_tex_2(sK3,sK2) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_610,c_20,c_19]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_613,plain,
% 1.65/1.00      ( ~ v2_tex_2(sK3,sK2) | ~ v3_tex_2(sK3,sK2) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_612]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_832,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ v2_tex_2(X0,sK2)
% 1.65/1.00      | ~ v2_tex_2(sK3,sK2)
% 1.65/1.00      | r1_tarski(X0,sK1(sK2,X0))
% 1.65/1.00      | sK2 != sK2
% 1.65/1.00      | sK3 != X0 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_613,c_495]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_833,plain,
% 1.65/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ v2_tex_2(sK3,sK2)
% 1.65/1.00      | r1_tarski(sK3,sK1(sK2,sK3)) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_832]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_834,plain,
% 1.65/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.65/1.00      | v2_tex_2(sK3,sK2) != iProver_top
% 1.65/1.00      | r1_tarski(sK3,sK1(sK2,sK3)) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_833]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2025,plain,
% 1.65/1.00      ( r1_tarski(sK3,sK1(sK2,sK3)) = iProver_top ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_2022,c_30,c_802,c_834]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_0,plain,
% 1.65/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.65/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_5,plain,
% 1.65/1.00      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 1.65/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_187,plain,
% 1.65/1.00      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 1.65/1.00      inference(prop_impl,[status(thm)],[c_5]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_188,plain,
% 1.65/1.00      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_187]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_343,plain,
% 1.65/1.00      ( r1_tarski(k1_tarski(X0),X1)
% 1.65/1.00      | v1_xboole_0(X2)
% 1.65/1.00      | X1 != X2
% 1.65/1.00      | sK0(X2) != X0 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_188]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_344,plain,
% 1.65/1.00      ( r1_tarski(k1_tarski(sK0(X0)),X0) | v1_xboole_0(X0) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_343]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1687,plain,
% 1.65/1.00      ( r1_tarski(k1_tarski(sK0(X0)),X0) = iProver_top
% 1.65/1.00      | v1_xboole_0(X0) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_803,plain,
% 1.65/1.00      ( v2_tex_2(sK3,sK2) ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_801,c_19]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_14,plain,
% 1.65/1.00      ( ~ r1_tarski(X0,X1)
% 1.65/1.00      | ~ v1_zfmisc_1(X1)
% 1.65/1.00      | v1_xboole_0(X0)
% 1.65/1.00      | v1_xboole_0(X1)
% 1.65/1.00      | X1 = X0 ),
% 1.65/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_585,plain,
% 1.65/1.00      ( v3_tex_2(sK3,sK2)
% 1.65/1.00      | ~ r1_tarski(X0,X1)
% 1.65/1.00      | v1_xboole_0(X0)
% 1.65/1.00      | v1_xboole_0(X1)
% 1.65/1.00      | X1 = X0
% 1.65/1.00      | sK3 != X1 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_192]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_586,plain,
% 1.65/1.00      ( v3_tex_2(sK3,sK2)
% 1.65/1.00      | ~ r1_tarski(X0,sK3)
% 1.65/1.00      | v1_xboole_0(X0)
% 1.65/1.00      | v1_xboole_0(sK3)
% 1.65/1.00      | sK3 = X0 ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_585]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_590,plain,
% 1.65/1.00      ( v1_xboole_0(X0)
% 1.65/1.00      | ~ r1_tarski(X0,sK3)
% 1.65/1.00      | v3_tex_2(sK3,sK2)
% 1.65/1.00      | sK3 = X0 ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_586,c_20]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_591,plain,
% 1.65/1.00      ( v3_tex_2(sK3,sK2)
% 1.65/1.00      | ~ r1_tarski(X0,sK3)
% 1.65/1.00      | v1_xboole_0(X0)
% 1.65/1.00      | sK3 = X0 ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_590]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_656,plain,
% 1.65/1.00      ( ~ v2_tex_2(sK3,sK2)
% 1.65/1.00      | ~ r1_tarski(X0,sK3)
% 1.65/1.00      | v1_xboole_0(X0)
% 1.65/1.00      | sK3 = X0 ),
% 1.65/1.00      inference(resolution,[status(thm)],[c_591,c_613]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_811,plain,
% 1.65/1.00      ( ~ r1_tarski(X0,sK3) | v1_xboole_0(X0) | sK3 = X0 ),
% 1.65/1.00      inference(backward_subsumption_resolution,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_803,c_656]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1678,plain,
% 1.65/1.00      ( sK3 = X0
% 1.65/1.00      | r1_tarski(X0,sK3) != iProver_top
% 1.65/1.00      | v1_xboole_0(X0) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_811]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2690,plain,
% 1.65/1.00      ( k1_tarski(sK0(sK3)) = sK3
% 1.65/1.00      | v1_xboole_0(k1_tarski(sK0(sK3))) = iProver_top
% 1.65/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 1.65/1.00      inference(superposition,[status(thm)],[c_1687,c_1678]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_29,plain,
% 1.65/1.00      ( v1_xboole_0(sK3) != iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2794,plain,
% 1.65/1.00      ( v1_xboole_0(k1_tarski(sK0(sK3))) = iProver_top
% 1.65/1.00      | k1_tarski(sK0(sK3)) = sK3 ),
% 1.65/1.00      inference(global_propositional_subsumption,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_2690,c_29]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2795,plain,
% 1.65/1.00      ( k1_tarski(sK0(sK3)) = sK3
% 1.65/1.00      | v1_xboole_0(k1_tarski(sK0(sK3))) = iProver_top ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_2794]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_4,plain,
% 1.65/1.00      ( r1_tarski(X0,X0) ),
% 1.65/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1691,plain,
% 1.65/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_6,plain,
% 1.65/1.00      ( ~ r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1) ),
% 1.65/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_185,plain,
% 1.65/1.00      ( r2_hidden(X0,X1) | ~ r1_tarski(k1_tarski(X0),X1) ),
% 1.65/1.00      inference(prop_impl,[status(thm)],[c_6]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_186,plain,
% 1.65/1.00      ( ~ r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1) ),
% 1.65/1.00      inference(renaming,[status(thm)],[c_185]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1,plain,
% 1.65/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.65/1.00      inference(cnf_transformation,[],[f38]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_332,plain,
% 1.65/1.00      ( ~ r1_tarski(k1_tarski(X0),X1) | ~ v1_xboole_0(X1) ),
% 1.65/1.00      inference(resolution,[status(thm)],[c_186,c_1]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1688,plain,
% 1.65/1.00      ( r1_tarski(k1_tarski(X0),X1) != iProver_top
% 1.65/1.00      | v1_xboole_0(X1) != iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2184,plain,
% 1.65/1.00      ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
% 1.65/1.00      inference(superposition,[status(thm)],[c_1691,c_1688]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2800,plain,
% 1.65/1.00      ( k1_tarski(sK0(sK3)) = sK3 ),
% 1.65/1.00      inference(forward_subsumption_resolution,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_2795,c_2184]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2802,plain,
% 1.65/1.00      ( r1_tarski(sK3,X0) != iProver_top
% 1.65/1.00      | v1_xboole_0(X0) != iProver_top ),
% 1.65/1.00      inference(superposition,[status(thm)],[c_2800,c_1688]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_3326,plain,
% 1.65/1.00      ( v1_xboole_0(sK1(sK2,sK3)) != iProver_top ),
% 1.65/1.00      inference(superposition,[status(thm)],[c_2025,c_2802]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_563,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ v2_tex_2(X0,sK2)
% 1.65/1.00      | ~ r1_tarski(X1,X2)
% 1.65/1.00      | v1_xboole_0(X1)
% 1.65/1.00      | v1_xboole_0(X2)
% 1.65/1.00      | v1_xboole_0(X0)
% 1.65/1.00      | X0 != X2
% 1.65/1.00      | X2 = X1 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_369]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_564,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ v2_tex_2(X0,sK2)
% 1.65/1.00      | ~ r1_tarski(X1,X0)
% 1.65/1.00      | v1_xboole_0(X1)
% 1.65/1.00      | v1_xboole_0(X0)
% 1.65/1.00      | X0 = X1 ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_563]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_1834,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ v2_tex_2(X0,sK2)
% 1.65/1.00      | ~ r1_tarski(sK3,X0)
% 1.65/1.00      | v1_xboole_0(X0)
% 1.65/1.00      | v1_xboole_0(sK3)
% 1.65/1.00      | X0 = sK3 ),
% 1.65/1.00      inference(instantiation,[status(thm)],[c_564]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2450,plain,
% 1.65/1.00      ( ~ m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ v2_tex_2(sK1(sK2,sK3),sK2)
% 1.65/1.00      | ~ r1_tarski(sK3,sK1(sK2,sK3))
% 1.65/1.00      | v1_xboole_0(sK1(sK2,sK3))
% 1.65/1.00      | v1_xboole_0(sK3)
% 1.65/1.00      | sK1(sK2,sK3) = sK3 ),
% 1.65/1.00      inference(instantiation,[status(thm)],[c_1834]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_2457,plain,
% 1.65/1.00      ( sK1(sK2,sK3) = sK3
% 1.65/1.00      | m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.65/1.00      | v2_tex_2(sK1(sK2,sK3),sK2) != iProver_top
% 1.65/1.00      | r1_tarski(sK3,sK1(sK2,sK3)) != iProver_top
% 1.65/1.00      | v1_xboole_0(sK1(sK2,sK3)) = iProver_top
% 1.65/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_2450]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_11,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | ~ v2_tex_2(X0,X1)
% 1.65/1.00      | v3_tex_2(X0,X1)
% 1.65/1.00      | ~ l1_pre_topc(X1) ),
% 1.65/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_458,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | ~ v2_tex_2(X0,X1)
% 1.65/1.00      | v3_tex_2(X0,X1)
% 1.65/1.00      | sK2 != X1 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_459,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ v2_tex_2(X0,sK2)
% 1.65/1.00      | v3_tex_2(X0,sK2) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_458]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_854,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ v2_tex_2(X0,sK2)
% 1.65/1.00      | ~ v2_tex_2(sK3,sK2)
% 1.65/1.00      | sK2 != sK2
% 1.65/1.00      | sK3 != X0 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_613,c_459]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_855,plain,
% 1.65/1.00      ( m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ v2_tex_2(sK3,sK2) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_854]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_856,plain,
% 1.65/1.00      ( m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.65/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.65/1.00      | v2_tex_2(sK3,sK2) != iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_855]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_10,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | ~ v2_tex_2(X0,X1)
% 1.65/1.00      | v2_tex_2(sK1(X1,X0),X1)
% 1.65/1.00      | v3_tex_2(X0,X1)
% 1.65/1.00      | ~ l1_pre_topc(X1) ),
% 1.65/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_476,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | ~ v2_tex_2(X0,X1)
% 1.65/1.00      | v2_tex_2(sK1(X1,X0),X1)
% 1.65/1.00      | v3_tex_2(X0,X1)
% 1.65/1.00      | sK2 != X1 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_477,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ v2_tex_2(X0,sK2)
% 1.65/1.00      | v2_tex_2(sK1(sK2,X0),sK2)
% 1.65/1.00      | v3_tex_2(X0,sK2) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_476]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_843,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ v2_tex_2(X0,sK2)
% 1.65/1.00      | v2_tex_2(sK1(sK2,X0),sK2)
% 1.65/1.00      | ~ v2_tex_2(sK3,sK2)
% 1.65/1.00      | sK2 != sK2
% 1.65/1.00      | sK3 != X0 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_613,c_477]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_844,plain,
% 1.65/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | v2_tex_2(sK1(sK2,sK3),sK2)
% 1.65/1.00      | ~ v2_tex_2(sK3,sK2) ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_843]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_845,plain,
% 1.65/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.65/1.00      | v2_tex_2(sK1(sK2,sK3),sK2) = iProver_top
% 1.65/1.00      | v2_tex_2(sK3,sK2) != iProver_top ),
% 1.65/1.00      inference(predicate_to_equality,[status(thm)],[c_844]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_8,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | ~ v2_tex_2(X0,X1)
% 1.65/1.00      | v3_tex_2(X0,X1)
% 1.65/1.00      | ~ l1_pre_topc(X1)
% 1.65/1.00      | sK1(X1,X0) != X0 ),
% 1.65/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_512,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.65/1.00      | ~ v2_tex_2(X0,X1)
% 1.65/1.00      | v3_tex_2(X0,X1)
% 1.65/1.00      | sK1(X1,X0) != X0
% 1.65/1.00      | sK2 != X1 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_513,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ v2_tex_2(X0,sK2)
% 1.65/1.00      | v3_tex_2(X0,sK2)
% 1.65/1.00      | sK1(sK2,X0) != X0 ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_512]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_824,plain,
% 1.65/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ v2_tex_2(X0,sK2)
% 1.65/1.00      | ~ v2_tex_2(sK3,sK2)
% 1.65/1.00      | sK1(sK2,X0) != X0
% 1.65/1.00      | sK2 != sK2
% 1.65/1.00      | sK3 != X0 ),
% 1.65/1.00      inference(resolution_lifted,[status(thm)],[c_613,c_513]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(c_825,plain,
% 1.65/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.65/1.00      | ~ v2_tex_2(sK3,sK2)
% 1.65/1.00      | sK1(sK2,sK3) != sK3 ),
% 1.65/1.00      inference(unflattening,[status(thm)],[c_824]) ).
% 1.65/1.00  
% 1.65/1.00  cnf(contradiction,plain,
% 1.65/1.00      ( $false ),
% 1.65/1.00      inference(minisat,
% 1.65/1.00                [status(thm)],
% 1.65/1.00                [c_3326,c_2457,c_856,c_845,c_834,c_825,c_802,c_801,c_30,
% 1.65/1.00                 c_19,c_29]) ).
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.65/1.00  
% 1.65/1.00  ------                               Statistics
% 1.65/1.00  
% 1.65/1.00  ------ General
% 1.65/1.00  
% 1.65/1.00  abstr_ref_over_cycles:                  0
% 1.65/1.00  abstr_ref_under_cycles:                 0
% 1.65/1.00  gc_basic_clause_elim:                   0
% 1.65/1.00  forced_gc_time:                         0
% 1.65/1.00  parsing_time:                           0.011
% 1.65/1.00  unif_index_cands_time:                  0.
% 1.65/1.00  unif_index_add_time:                    0.
% 1.65/1.00  orderings_time:                         0.
% 1.65/1.00  out_proof_time:                         0.011
% 1.65/1.00  total_time:                             0.124
% 1.65/1.00  num_of_symbols:                         49
% 1.65/1.00  num_of_terms:                           1577
% 1.65/1.00  
% 1.65/1.00  ------ Preprocessing
% 1.65/1.00  
% 1.65/1.00  num_of_splits:                          0
% 1.65/1.00  num_of_split_atoms:                     0
% 1.65/1.00  num_of_reused_defs:                     0
% 1.65/1.00  num_eq_ax_congr_red:                    10
% 1.65/1.00  num_of_sem_filtered_clauses:            1
% 1.65/1.00  num_of_subtypes:                        0
% 1.65/1.00  monotx_restored_types:                  0
% 1.65/1.00  sat_num_of_epr_types:                   0
% 1.65/1.00  sat_num_of_non_cyclic_types:            0
% 1.65/1.00  sat_guarded_non_collapsed_types:        0
% 1.65/1.00  num_pure_diseq_elim:                    0
% 1.65/1.00  simp_replaced_by:                       0
% 1.65/1.00  res_preprocessed:                       95
% 1.65/1.00  prep_upred:                             0
% 1.65/1.00  prep_unflattend:                        32
% 1.65/1.00  smt_new_axioms:                         0
% 1.65/1.00  pred_elim_cands:                        5
% 1.65/1.00  pred_elim:                              6
% 1.65/1.00  pred_elim_cl:                           8
% 1.65/1.00  pred_elim_cycles:                       9
% 1.65/1.00  merged_defs:                            4
% 1.65/1.00  merged_defs_ncl:                        0
% 1.65/1.00  bin_hyper_res:                          4
% 1.65/1.00  prep_cycles:                            4
% 1.65/1.00  pred_elim_time:                         0.016
% 1.65/1.00  splitting_time:                         0.
% 1.65/1.00  sem_filter_time:                        0.
% 1.65/1.00  monotx_time:                            0.
% 1.65/1.00  subtype_inf_time:                       0.
% 1.65/1.00  
% 1.65/1.00  ------ Problem properties
% 1.65/1.00  
% 1.65/1.00  clauses:                                16
% 1.65/1.00  conjectures:                            2
% 1.65/1.00  epr:                                    6
% 1.65/1.00  horn:                                   10
% 1.65/1.00  ground:                                 4
% 1.65/1.00  unary:                                  5
% 1.65/1.00  binary:                                 2
% 1.65/1.00  lits:                                   46
% 1.65/1.00  lits_eq:                                5
% 1.65/1.00  fd_pure:                                0
% 1.65/1.00  fd_pseudo:                              0
% 1.65/1.00  fd_cond:                                1
% 1.65/1.00  fd_pseudo_cond:                         3
% 1.65/1.00  ac_symbols:                             0
% 1.65/1.00  
% 1.65/1.00  ------ Propositional Solver
% 1.65/1.00  
% 1.65/1.00  prop_solver_calls:                      27
% 1.65/1.00  prop_fast_solver_calls:                 982
% 1.65/1.00  smt_solver_calls:                       0
% 1.65/1.00  smt_fast_solver_calls:                  0
% 1.65/1.00  prop_num_of_clauses:                    785
% 1.65/1.00  prop_preprocess_simplified:             3693
% 1.65/1.00  prop_fo_subsumed:                       59
% 1.65/1.00  prop_solver_time:                       0.
% 1.65/1.00  smt_solver_time:                        0.
% 1.65/1.00  smt_fast_solver_time:                   0.
% 1.65/1.00  prop_fast_solver_time:                  0.
% 1.65/1.00  prop_unsat_core_time:                   0.
% 1.65/1.00  
% 1.65/1.00  ------ QBF
% 1.65/1.00  
% 1.65/1.00  qbf_q_res:                              0
% 1.65/1.00  qbf_num_tautologies:                    0
% 1.65/1.00  qbf_prep_cycles:                        0
% 1.65/1.00  
% 1.65/1.00  ------ BMC1
% 1.65/1.00  
% 1.65/1.00  bmc1_current_bound:                     -1
% 1.65/1.00  bmc1_last_solved_bound:                 -1
% 1.65/1.00  bmc1_unsat_core_size:                   -1
% 1.65/1.00  bmc1_unsat_core_parents_size:           -1
% 1.65/1.00  bmc1_merge_next_fun:                    0
% 1.65/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.65/1.00  
% 1.65/1.00  ------ Instantiation
% 1.65/1.00  
% 1.65/1.00  inst_num_of_clauses:                    213
% 1.65/1.00  inst_num_in_passive:                    17
% 1.65/1.00  inst_num_in_active:                     160
% 1.65/1.00  inst_num_in_unprocessed:                36
% 1.65/1.00  inst_num_of_loops:                      170
% 1.65/1.00  inst_num_of_learning_restarts:          0
% 1.65/1.00  inst_num_moves_active_passive:          6
% 1.65/1.00  inst_lit_activity:                      0
% 1.65/1.00  inst_lit_activity_moves:                0
% 1.65/1.00  inst_num_tautologies:                   0
% 1.65/1.00  inst_num_prop_implied:                  0
% 1.65/1.00  inst_num_existing_simplified:           0
% 1.65/1.00  inst_num_eq_res_simplified:             0
% 1.65/1.00  inst_num_child_elim:                    0
% 1.65/1.00  inst_num_of_dismatching_blockings:      59
% 1.65/1.00  inst_num_of_non_proper_insts:           294
% 1.65/1.00  inst_num_of_duplicates:                 0
% 1.65/1.00  inst_inst_num_from_inst_to_res:         0
% 1.65/1.00  inst_dismatching_checking_time:         0.
% 1.65/1.00  
% 1.65/1.00  ------ Resolution
% 1.65/1.00  
% 1.65/1.00  res_num_of_clauses:                     0
% 1.65/1.00  res_num_in_passive:                     0
% 1.65/1.00  res_num_in_active:                      0
% 1.65/1.00  res_num_of_loops:                       99
% 1.65/1.00  res_forward_subset_subsumed:            45
% 1.65/1.00  res_backward_subset_subsumed:           3
% 1.65/1.00  res_forward_subsumed:                   1
% 1.65/1.00  res_backward_subsumed:                  2
% 1.65/1.00  res_forward_subsumption_resolution:     0
% 1.65/1.00  res_backward_subsumption_resolution:    2
% 1.65/1.00  res_clause_to_clause_subsumption:       241
% 1.65/1.00  res_orphan_elimination:                 0
% 1.65/1.00  res_tautology_del:                      56
% 1.65/1.00  res_num_eq_res_simplified:              0
% 1.65/1.00  res_num_sel_changes:                    0
% 1.65/1.00  res_moves_from_active_to_pass:          0
% 1.65/1.00  
% 1.65/1.00  ------ Superposition
% 1.65/1.00  
% 1.65/1.00  sup_time_total:                         0.
% 1.65/1.00  sup_time_generating:                    0.
% 1.65/1.00  sup_time_sim_full:                      0.
% 1.65/1.00  sup_time_sim_immed:                     0.
% 1.65/1.00  
% 1.65/1.00  sup_num_of_clauses:                     39
% 1.65/1.00  sup_num_in_active:                      33
% 1.65/1.00  sup_num_in_passive:                     6
% 1.65/1.00  sup_num_of_loops:                       32
% 1.65/1.00  sup_fw_superposition:                   22
% 1.65/1.00  sup_bw_superposition:                   13
% 1.65/1.00  sup_immediate_simplified:               7
% 1.65/1.00  sup_given_eliminated:                   0
% 1.65/1.00  comparisons_done:                       0
% 1.65/1.00  comparisons_avoided:                    0
% 1.65/1.00  
% 1.65/1.00  ------ Simplifications
% 1.65/1.00  
% 1.65/1.00  
% 1.65/1.00  sim_fw_subset_subsumed:                 6
% 1.65/1.00  sim_bw_subset_subsumed:                 0
% 1.65/1.00  sim_fw_subsumed:                        1
% 1.65/1.00  sim_bw_subsumed:                        0
% 1.65/1.00  sim_fw_subsumption_res:                 1
% 1.65/1.00  sim_bw_subsumption_res:                 0
% 1.65/1.00  sim_tautology_del:                      1
% 1.65/1.00  sim_eq_tautology_del:                   2
% 1.65/1.00  sim_eq_res_simp:                        0
% 1.65/1.00  sim_fw_demodulated:                     0
% 1.65/1.00  sim_bw_demodulated:                     0
% 1.65/1.00  sim_light_normalised:                   0
% 1.65/1.00  sim_joinable_taut:                      0
% 1.65/1.00  sim_joinable_simp:                      0
% 1.65/1.00  sim_ac_normalised:                      0
% 1.65/1.00  sim_smt_subsumption:                    0
% 1.65/1.00  
%------------------------------------------------------------------------------
