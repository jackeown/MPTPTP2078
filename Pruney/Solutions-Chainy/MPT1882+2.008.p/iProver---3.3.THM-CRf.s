%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:20 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  169 (2440 expanded)
%              Number of clauses        :  110 ( 569 expanded)
%              Number of leaves         :   15 ( 542 expanded)
%              Depth                    :   25
%              Number of atoms          :  715 (19191 expanded)
%              Number of equality atoms :  180 ( 647 expanded)
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

fof(f63,plain,(
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

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
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

fof(f56,plain,(
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

fof(f14,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
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

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK0(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
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

fof(f64,plain,
    ( v1_zfmisc_1(sK2)
    | v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,
    ( ~ v1_zfmisc_1(sK2)
    | ~ v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK0(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
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

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

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

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1933,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1926,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_447,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | v3_tex_2(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_1922,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v2_tex_2(X0,sK1) != iProver_top
    | v3_tex_2(X0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_8,plain,
    ( v1_zfmisc_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_149,plain,
    ( v1_zfmisc_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_8])).

cnf(c_150,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_149])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_150,c_26])).

cnf(c_357,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_24,negated_conjecture,
    ( v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_361,plain,
    ( ~ v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_zfmisc_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_357,c_25,c_24,c_23])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_361])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_553,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | X2 != X0
    | X1 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_362,c_16])).

cnf(c_554,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ r1_tarski(X1,X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_1918,plain,
    ( X0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(X1,sK1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_554])).

cnf(c_2992,plain,
    ( sK0(sK1,X0) = X1
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(X0,sK1) != iProver_top
    | v2_tex_2(sK0(sK1,X0),sK1) != iProver_top
    | v3_tex_2(X0,sK1) = iProver_top
    | r1_tarski(X1,sK0(sK1,X0)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK0(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1922,c_1918])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_465,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_466,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | v2_tex_2(sK0(sK1,X0),sK1)
    | v3_tex_2(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_467,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(X0,sK1) != iProver_top
    | v2_tex_2(sK0(sK1,X0),sK1) = iProver_top
    | v3_tex_2(X0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_3724,plain,
    ( v2_tex_2(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sK0(sK1,X0) = X1
    | v3_tex_2(X0,sK1) = iProver_top
    | r1_tarski(X1,sK0(sK1,X0)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK0(sK1,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2992,c_467])).

cnf(c_3725,plain,
    ( sK0(sK1,X0) = X1
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(X0,sK1) != iProver_top
    | v3_tex_2(X0,sK1) = iProver_top
    | r1_tarski(X1,sK0(sK1,X0)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK0(sK1,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3724])).

cnf(c_3737,plain,
    ( sK0(sK1,sK2) = X0
    | v2_tex_2(sK2,sK1) != iProver_top
    | v3_tex_2(sK2,sK1) = iProver_top
    | r1_tarski(X0,sK0(sK1,sK2)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1926,c_3725])).

cnf(c_22,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_31,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_32,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_378,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_382,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_378,c_25,c_24,c_23])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_382])).

cnf(c_20,negated_conjecture,
    ( v3_tex_2(sK2,sK1)
    | v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_210,plain,
    ( v1_zfmisc_1(sK2)
    | v3_tex_2(sK2,sK1) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_211,plain,
    ( v3_tex_2(sK2,sK1)
    | v1_zfmisc_1(sK2) ),
    inference(renaming,[status(thm)],[c_210])).

cnf(c_593,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1)
    | v3_tex_2(sK2,sK1)
    | v1_xboole_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_383,c_211])).

cnf(c_594,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(sK2,sK1)
    | v3_tex_2(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_596,plain,
    ( v3_tex_2(sK2,sK1)
    | v2_tex_2(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_594,c_22,c_21])).

cnf(c_597,plain,
    ( v2_tex_2(sK2,sK1)
    | v3_tex_2(sK2,sK1) ),
    inference(renaming,[status(thm)],[c_596])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_411,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1)
    | ~ v3_tex_2(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_848,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1)
    | v2_tex_2(sK2,sK1)
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_597,c_411])).

cnf(c_849,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(sK2,sK1) ),
    inference(unflattening,[status(thm)],[c_848])).

cnf(c_850,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_849])).

cnf(c_19,negated_conjecture,
    ( ~ v3_tex_2(sK2,sK1)
    | ~ v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_208,plain,
    ( ~ v1_zfmisc_1(sK2)
    | ~ v3_tex_2(sK2,sK1) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_209,plain,
    ( ~ v3_tex_2(sK2,sK1)
    | ~ v1_zfmisc_1(sK2) ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_577,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ v3_tex_2(sK2,sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_362,c_209])).

cnf(c_578,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(sK2,sK1)
    | ~ v3_tex_2(sK2,sK1) ),
    inference(unflattening,[status(thm)],[c_577])).

cnf(c_580,plain,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ v3_tex_2(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_578,c_21])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_501,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | sK0(X1,X0) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | v3_tex_2(X0,sK1)
    | sK0(sK1,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_859,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ v2_tex_2(sK2,sK1)
    | sK0(sK1,X0) != X0
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_580,c_502])).

cnf(c_860,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(sK2,sK1)
    | sK0(sK1,sK2) != sK2 ),
    inference(unflattening,[status(thm)],[c_859])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | r1_tarski(X0,sK0(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_483,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | r1_tarski(X0,sK0(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_484,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | v3_tex_2(X0,sK1)
    | r1_tarski(X0,sK0(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_867,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ v2_tex_2(sK2,sK1)
    | r1_tarski(X0,sK0(sK1,X0))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_580,c_484])).

cnf(c_868,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(sK2,sK1)
    | r1_tarski(sK2,sK0(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_867])).

cnf(c_869,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(sK2,sK1) != iProver_top
    | r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_868])).

cnf(c_878,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | v2_tex_2(sK0(sK1,X0),sK1)
    | ~ v2_tex_2(sK2,sK1)
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_580,c_466])).

cnf(c_879,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(sK0(sK1,sK2),sK1)
    | ~ v2_tex_2(sK2,sK1) ),
    inference(unflattening,[status(thm)],[c_878])).

cnf(c_880,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(sK0(sK1,sK2),sK1) = iProver_top
    | v2_tex_2(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_879])).

cnf(c_889,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ v2_tex_2(sK2,sK1)
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_580,c_448])).

cnf(c_890,plain,
    ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(sK2,sK1) ),
    inference(unflattening,[status(thm)],[c_889])).

cnf(c_891,plain,
    ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_890])).

cnf(c_1451,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2455,plain,
    ( sK0(sK1,sK2) = sK0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1451])).

cnf(c_2271,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ r1_tarski(sK2,X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_2472,plain,
    ( ~ m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(sK0(sK1,sK2),sK1)
    | ~ r1_tarski(sK2,sK0(sK1,sK2))
    | v1_xboole_0(sK0(sK1,sK2))
    | v1_xboole_0(sK2)
    | sK2 = sK0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2271])).

cnf(c_2473,plain,
    ( sK2 = sK0(sK1,sK2)
    | m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(sK0(sK1,sK2),sK1) != iProver_top
    | r1_tarski(sK2,sK0(sK1,sK2)) != iProver_top
    | v1_xboole_0(sK0(sK1,sK2)) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2472])).

cnf(c_1452,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2181,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_1452])).

cnf(c_2612,plain,
    ( X0 != sK0(sK1,sK2)
    | X0 = sK2
    | sK2 != sK0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2181])).

cnf(c_2971,plain,
    ( sK0(sK1,sK2) != sK0(sK1,sK2)
    | sK0(sK1,sK2) = sK2
    | sK2 != sK0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2612])).

cnf(c_3776,plain,
    ( v1_xboole_0(sK0(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3737,c_31,c_21,c_32,c_849,c_850,c_860,c_869,c_880,c_891,c_2455,c_2473,c_2971])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1927,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3781,plain,
    ( sK0(sK1,sK2) = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3776,c_1927])).

cnf(c_3823,plain,
    ( sK0(sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1933,c_3781])).

cnf(c_1920,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(X0,sK1) != iProver_top
    | v3_tex_2(X0,sK1) = iProver_top
    | r1_tarski(X0,sK0(sK1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_484])).

cnf(c_2247,plain,
    ( v2_tex_2(sK2,sK1) != iProver_top
    | v3_tex_2(sK2,sK1) = iProver_top
    | r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1926,c_1920])).

cnf(c_2250,plain,
    ( r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2247,c_32,c_850,c_869])).

cnf(c_4046,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3823,c_2250])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1931,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1930,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3259,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1931,c_1930])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1928,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3355,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3259,c_1928])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1932,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3363,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3355,c_1932])).

cnf(c_4695,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4046,c_3363])).

cnf(c_1919,plain,
    ( sK0(sK1,X0) != X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(X0,sK1) != iProver_top
    | v3_tex_2(X0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_502])).

cnf(c_4066,plain,
    ( sK2 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(sK2,sK1) != iProver_top
    | v3_tex_2(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3823,c_1919])).

cnf(c_582,plain,
    ( v2_tex_2(sK2,sK1) != iProver_top
    | v3_tex_2(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_580])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4695,c_4066,c_850,c_582,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.03/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/0.99  
% 2.03/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.03/0.99  
% 2.03/0.99  ------  iProver source info
% 2.03/0.99  
% 2.03/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.03/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.03/0.99  git: non_committed_changes: false
% 2.03/0.99  git: last_make_outside_of_git: false
% 2.03/0.99  
% 2.03/0.99  ------ 
% 2.03/0.99  
% 2.03/0.99  ------ Input Options
% 2.03/0.99  
% 2.03/0.99  --out_options                           all
% 2.03/0.99  --tptp_safe_out                         true
% 2.03/0.99  --problem_path                          ""
% 2.03/0.99  --include_path                          ""
% 2.03/0.99  --clausifier                            res/vclausify_rel
% 2.03/0.99  --clausifier_options                    --mode clausify
% 2.03/0.99  --stdin                                 false
% 2.03/0.99  --stats_out                             all
% 2.03/0.99  
% 2.03/0.99  ------ General Options
% 2.03/0.99  
% 2.03/0.99  --fof                                   false
% 2.03/0.99  --time_out_real                         305.
% 2.03/0.99  --time_out_virtual                      -1.
% 2.03/0.99  --symbol_type_check                     false
% 2.03/0.99  --clausify_out                          false
% 2.03/0.99  --sig_cnt_out                           false
% 2.03/0.99  --trig_cnt_out                          false
% 2.03/0.99  --trig_cnt_out_tolerance                1.
% 2.03/0.99  --trig_cnt_out_sk_spl                   false
% 2.03/0.99  --abstr_cl_out                          false
% 2.03/0.99  
% 2.03/0.99  ------ Global Options
% 2.03/0.99  
% 2.03/0.99  --schedule                              default
% 2.03/0.99  --add_important_lit                     false
% 2.03/0.99  --prop_solver_per_cl                    1000
% 2.03/0.99  --min_unsat_core                        false
% 2.03/0.99  --soft_assumptions                      false
% 2.03/0.99  --soft_lemma_size                       3
% 2.03/0.99  --prop_impl_unit_size                   0
% 2.03/0.99  --prop_impl_unit                        []
% 2.03/0.99  --share_sel_clauses                     true
% 2.03/0.99  --reset_solvers                         false
% 2.03/0.99  --bc_imp_inh                            [conj_cone]
% 2.03/0.99  --conj_cone_tolerance                   3.
% 2.03/0.99  --extra_neg_conj                        none
% 2.03/0.99  --large_theory_mode                     true
% 2.03/0.99  --prolific_symb_bound                   200
% 2.03/0.99  --lt_threshold                          2000
% 2.03/0.99  --clause_weak_htbl                      true
% 2.03/0.99  --gc_record_bc_elim                     false
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing Options
% 2.03/0.99  
% 2.03/0.99  --preprocessing_flag                    true
% 2.03/0.99  --time_out_prep_mult                    0.1
% 2.03/0.99  --splitting_mode                        input
% 2.03/0.99  --splitting_grd                         true
% 2.03/0.99  --splitting_cvd                         false
% 2.03/0.99  --splitting_cvd_svl                     false
% 2.03/0.99  --splitting_nvd                         32
% 2.03/0.99  --sub_typing                            true
% 2.03/0.99  --prep_gs_sim                           true
% 2.03/0.99  --prep_unflatten                        true
% 2.03/0.99  --prep_res_sim                          true
% 2.03/0.99  --prep_upred                            true
% 2.03/0.99  --prep_sem_filter                       exhaustive
% 2.03/0.99  --prep_sem_filter_out                   false
% 2.03/0.99  --pred_elim                             true
% 2.03/0.99  --res_sim_input                         true
% 2.03/0.99  --eq_ax_congr_red                       true
% 2.03/0.99  --pure_diseq_elim                       true
% 2.03/0.99  --brand_transform                       false
% 2.03/0.99  --non_eq_to_eq                          false
% 2.03/0.99  --prep_def_merge                        true
% 2.03/0.99  --prep_def_merge_prop_impl              false
% 2.03/0.99  --prep_def_merge_mbd                    true
% 2.03/0.99  --prep_def_merge_tr_red                 false
% 2.03/0.99  --prep_def_merge_tr_cl                  false
% 2.03/0.99  --smt_preprocessing                     true
% 2.03/0.99  --smt_ac_axioms                         fast
% 2.03/0.99  --preprocessed_out                      false
% 2.03/0.99  --preprocessed_stats                    false
% 2.03/0.99  
% 2.03/0.99  ------ Abstraction refinement Options
% 2.03/0.99  
% 2.03/0.99  --abstr_ref                             []
% 2.03/0.99  --abstr_ref_prep                        false
% 2.03/0.99  --abstr_ref_until_sat                   false
% 2.03/0.99  --abstr_ref_sig_restrict                funpre
% 2.03/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.03/0.99  --abstr_ref_under                       []
% 2.03/0.99  
% 2.03/0.99  ------ SAT Options
% 2.03/0.99  
% 2.03/0.99  --sat_mode                              false
% 2.03/0.99  --sat_fm_restart_options                ""
% 2.03/0.99  --sat_gr_def                            false
% 2.03/0.99  --sat_epr_types                         true
% 2.03/0.99  --sat_non_cyclic_types                  false
% 2.03/0.99  --sat_finite_models                     false
% 2.03/0.99  --sat_fm_lemmas                         false
% 2.03/0.99  --sat_fm_prep                           false
% 2.03/0.99  --sat_fm_uc_incr                        true
% 2.03/0.99  --sat_out_model                         small
% 2.03/0.99  --sat_out_clauses                       false
% 2.03/0.99  
% 2.03/0.99  ------ QBF Options
% 2.03/0.99  
% 2.03/0.99  --qbf_mode                              false
% 2.03/0.99  --qbf_elim_univ                         false
% 2.03/0.99  --qbf_dom_inst                          none
% 2.03/0.99  --qbf_dom_pre_inst                      false
% 2.03/0.99  --qbf_sk_in                             false
% 2.03/0.99  --qbf_pred_elim                         true
% 2.03/0.99  --qbf_split                             512
% 2.03/0.99  
% 2.03/0.99  ------ BMC1 Options
% 2.03/0.99  
% 2.03/0.99  --bmc1_incremental                      false
% 2.03/0.99  --bmc1_axioms                           reachable_all
% 2.03/0.99  --bmc1_min_bound                        0
% 2.03/0.99  --bmc1_max_bound                        -1
% 2.03/0.99  --bmc1_max_bound_default                -1
% 2.03/0.99  --bmc1_symbol_reachability              true
% 2.03/0.99  --bmc1_property_lemmas                  false
% 2.03/0.99  --bmc1_k_induction                      false
% 2.03/0.99  --bmc1_non_equiv_states                 false
% 2.03/0.99  --bmc1_deadlock                         false
% 2.03/0.99  --bmc1_ucm                              false
% 2.03/0.99  --bmc1_add_unsat_core                   none
% 2.03/0.99  --bmc1_unsat_core_children              false
% 2.03/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.03/0.99  --bmc1_out_stat                         full
% 2.03/0.99  --bmc1_ground_init                      false
% 2.03/0.99  --bmc1_pre_inst_next_state              false
% 2.03/0.99  --bmc1_pre_inst_state                   false
% 2.03/0.99  --bmc1_pre_inst_reach_state             false
% 2.03/0.99  --bmc1_out_unsat_core                   false
% 2.03/0.99  --bmc1_aig_witness_out                  false
% 2.03/0.99  --bmc1_verbose                          false
% 2.03/0.99  --bmc1_dump_clauses_tptp                false
% 2.03/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.03/0.99  --bmc1_dump_file                        -
% 2.03/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.03/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.03/0.99  --bmc1_ucm_extend_mode                  1
% 2.03/0.99  --bmc1_ucm_init_mode                    2
% 2.03/0.99  --bmc1_ucm_cone_mode                    none
% 2.03/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.03/0.99  --bmc1_ucm_relax_model                  4
% 2.03/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.03/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.03/0.99  --bmc1_ucm_layered_model                none
% 2.03/0.99  --bmc1_ucm_max_lemma_size               10
% 2.03/0.99  
% 2.03/0.99  ------ AIG Options
% 2.03/0.99  
% 2.03/0.99  --aig_mode                              false
% 2.03/0.99  
% 2.03/0.99  ------ Instantiation Options
% 2.03/0.99  
% 2.03/0.99  --instantiation_flag                    true
% 2.03/0.99  --inst_sos_flag                         false
% 2.03/0.99  --inst_sos_phase                        true
% 2.03/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel_side                     num_symb
% 2.03/0.99  --inst_solver_per_active                1400
% 2.03/0.99  --inst_solver_calls_frac                1.
% 2.03/0.99  --inst_passive_queue_type               priority_queues
% 2.03/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.03/0.99  --inst_passive_queues_freq              [25;2]
% 2.03/0.99  --inst_dismatching                      true
% 2.03/0.99  --inst_eager_unprocessed_to_passive     true
% 2.03/0.99  --inst_prop_sim_given                   true
% 2.03/0.99  --inst_prop_sim_new                     false
% 2.03/0.99  --inst_subs_new                         false
% 2.03/0.99  --inst_eq_res_simp                      false
% 2.03/0.99  --inst_subs_given                       false
% 2.03/0.99  --inst_orphan_elimination               true
% 2.03/0.99  --inst_learning_loop_flag               true
% 2.03/0.99  --inst_learning_start                   3000
% 2.03/0.99  --inst_learning_factor                  2
% 2.03/0.99  --inst_start_prop_sim_after_learn       3
% 2.03/0.99  --inst_sel_renew                        solver
% 2.03/0.99  --inst_lit_activity_flag                true
% 2.03/0.99  --inst_restr_to_given                   false
% 2.03/0.99  --inst_activity_threshold               500
% 2.03/0.99  --inst_out_proof                        true
% 2.03/0.99  
% 2.03/0.99  ------ Resolution Options
% 2.03/0.99  
% 2.03/0.99  --resolution_flag                       true
% 2.03/0.99  --res_lit_sel                           adaptive
% 2.03/0.99  --res_lit_sel_side                      none
% 2.03/0.99  --res_ordering                          kbo
% 2.03/0.99  --res_to_prop_solver                    active
% 2.03/0.99  --res_prop_simpl_new                    false
% 2.03/0.99  --res_prop_simpl_given                  true
% 2.03/0.99  --res_passive_queue_type                priority_queues
% 2.03/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.03/0.99  --res_passive_queues_freq               [15;5]
% 2.03/0.99  --res_forward_subs                      full
% 2.03/0.99  --res_backward_subs                     full
% 2.03/0.99  --res_forward_subs_resolution           true
% 2.03/0.99  --res_backward_subs_resolution          true
% 2.03/0.99  --res_orphan_elimination                true
% 2.03/0.99  --res_time_limit                        2.
% 2.03/0.99  --res_out_proof                         true
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Options
% 2.03/0.99  
% 2.03/0.99  --superposition_flag                    true
% 2.03/0.99  --sup_passive_queue_type                priority_queues
% 2.03/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.03/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.03/0.99  --demod_completeness_check              fast
% 2.03/0.99  --demod_use_ground                      true
% 2.03/0.99  --sup_to_prop_solver                    passive
% 2.03/0.99  --sup_prop_simpl_new                    true
% 2.03/0.99  --sup_prop_simpl_given                  true
% 2.03/0.99  --sup_fun_splitting                     false
% 2.03/0.99  --sup_smt_interval                      50000
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Simplification Setup
% 2.03/0.99  
% 2.03/0.99  --sup_indices_passive                   []
% 2.03/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.03/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_full_bw                           [BwDemod]
% 2.03/0.99  --sup_immed_triv                        [TrivRules]
% 2.03/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.03/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_immed_bw_main                     []
% 2.03/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.03/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  
% 2.03/0.99  ------ Combination Options
% 2.03/0.99  
% 2.03/0.99  --comb_res_mult                         3
% 2.03/0.99  --comb_sup_mult                         2
% 2.03/0.99  --comb_inst_mult                        10
% 2.03/0.99  
% 2.03/0.99  ------ Debug Options
% 2.03/0.99  
% 2.03/0.99  --dbg_backtrace                         false
% 2.03/0.99  --dbg_dump_prop_clauses                 false
% 2.03/0.99  --dbg_dump_prop_clauses_file            -
% 2.03/0.99  --dbg_out_stat                          false
% 2.03/0.99  ------ Parsing...
% 2.03/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.03/0.99  ------ Proving...
% 2.03/0.99  ------ Problem Properties 
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  clauses                                 19
% 2.03/0.99  conjectures                             2
% 2.03/0.99  EPR                                     8
% 2.03/0.99  Horn                                    14
% 2.03/0.99  unary                                   7
% 2.03/0.99  binary                                  2
% 2.03/0.99  lits                                    51
% 2.03/0.99  lits eq                                 8
% 2.03/0.99  fd_pure                                 0
% 2.03/0.99  fd_pseudo                               0
% 2.03/0.99  fd_cond                                 1
% 2.03/0.99  fd_pseudo_cond                          4
% 2.03/0.99  AC symbols                              0
% 2.03/0.99  
% 2.03/0.99  ------ Schedule dynamic 5 is on 
% 2.03/0.99  
% 2.03/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  ------ 
% 2.03/0.99  Current options:
% 2.03/0.99  ------ 
% 2.03/0.99  
% 2.03/0.99  ------ Input Options
% 2.03/0.99  
% 2.03/0.99  --out_options                           all
% 2.03/0.99  --tptp_safe_out                         true
% 2.03/0.99  --problem_path                          ""
% 2.03/0.99  --include_path                          ""
% 2.03/0.99  --clausifier                            res/vclausify_rel
% 2.03/0.99  --clausifier_options                    --mode clausify
% 2.03/0.99  --stdin                                 false
% 2.03/0.99  --stats_out                             all
% 2.03/0.99  
% 2.03/0.99  ------ General Options
% 2.03/0.99  
% 2.03/0.99  --fof                                   false
% 2.03/0.99  --time_out_real                         305.
% 2.03/0.99  --time_out_virtual                      -1.
% 2.03/0.99  --symbol_type_check                     false
% 2.03/0.99  --clausify_out                          false
% 2.03/0.99  --sig_cnt_out                           false
% 2.03/0.99  --trig_cnt_out                          false
% 2.03/0.99  --trig_cnt_out_tolerance                1.
% 2.03/0.99  --trig_cnt_out_sk_spl                   false
% 2.03/0.99  --abstr_cl_out                          false
% 2.03/0.99  
% 2.03/0.99  ------ Global Options
% 2.03/0.99  
% 2.03/0.99  --schedule                              default
% 2.03/0.99  --add_important_lit                     false
% 2.03/0.99  --prop_solver_per_cl                    1000
% 2.03/0.99  --min_unsat_core                        false
% 2.03/0.99  --soft_assumptions                      false
% 2.03/0.99  --soft_lemma_size                       3
% 2.03/0.99  --prop_impl_unit_size                   0
% 2.03/0.99  --prop_impl_unit                        []
% 2.03/0.99  --share_sel_clauses                     true
% 2.03/0.99  --reset_solvers                         false
% 2.03/0.99  --bc_imp_inh                            [conj_cone]
% 2.03/0.99  --conj_cone_tolerance                   3.
% 2.03/0.99  --extra_neg_conj                        none
% 2.03/0.99  --large_theory_mode                     true
% 2.03/0.99  --prolific_symb_bound                   200
% 2.03/0.99  --lt_threshold                          2000
% 2.03/0.99  --clause_weak_htbl                      true
% 2.03/0.99  --gc_record_bc_elim                     false
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing Options
% 2.03/0.99  
% 2.03/0.99  --preprocessing_flag                    true
% 2.03/0.99  --time_out_prep_mult                    0.1
% 2.03/0.99  --splitting_mode                        input
% 2.03/0.99  --splitting_grd                         true
% 2.03/0.99  --splitting_cvd                         false
% 2.03/0.99  --splitting_cvd_svl                     false
% 2.03/0.99  --splitting_nvd                         32
% 2.03/0.99  --sub_typing                            true
% 2.03/0.99  --prep_gs_sim                           true
% 2.03/0.99  --prep_unflatten                        true
% 2.03/0.99  --prep_res_sim                          true
% 2.03/0.99  --prep_upred                            true
% 2.03/0.99  --prep_sem_filter                       exhaustive
% 2.03/0.99  --prep_sem_filter_out                   false
% 2.03/0.99  --pred_elim                             true
% 2.03/0.99  --res_sim_input                         true
% 2.03/0.99  --eq_ax_congr_red                       true
% 2.03/0.99  --pure_diseq_elim                       true
% 2.03/0.99  --brand_transform                       false
% 2.03/0.99  --non_eq_to_eq                          false
% 2.03/0.99  --prep_def_merge                        true
% 2.03/0.99  --prep_def_merge_prop_impl              false
% 2.03/0.99  --prep_def_merge_mbd                    true
% 2.03/0.99  --prep_def_merge_tr_red                 false
% 2.03/0.99  --prep_def_merge_tr_cl                  false
% 2.03/0.99  --smt_preprocessing                     true
% 2.03/0.99  --smt_ac_axioms                         fast
% 2.03/0.99  --preprocessed_out                      false
% 2.03/0.99  --preprocessed_stats                    false
% 2.03/0.99  
% 2.03/0.99  ------ Abstraction refinement Options
% 2.03/0.99  
% 2.03/0.99  --abstr_ref                             []
% 2.03/0.99  --abstr_ref_prep                        false
% 2.03/0.99  --abstr_ref_until_sat                   false
% 2.03/0.99  --abstr_ref_sig_restrict                funpre
% 2.03/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.03/0.99  --abstr_ref_under                       []
% 2.03/0.99  
% 2.03/0.99  ------ SAT Options
% 2.03/0.99  
% 2.03/0.99  --sat_mode                              false
% 2.03/0.99  --sat_fm_restart_options                ""
% 2.03/0.99  --sat_gr_def                            false
% 2.03/0.99  --sat_epr_types                         true
% 2.03/0.99  --sat_non_cyclic_types                  false
% 2.03/0.99  --sat_finite_models                     false
% 2.03/0.99  --sat_fm_lemmas                         false
% 2.03/0.99  --sat_fm_prep                           false
% 2.03/0.99  --sat_fm_uc_incr                        true
% 2.03/0.99  --sat_out_model                         small
% 2.03/0.99  --sat_out_clauses                       false
% 2.03/0.99  
% 2.03/0.99  ------ QBF Options
% 2.03/0.99  
% 2.03/0.99  --qbf_mode                              false
% 2.03/0.99  --qbf_elim_univ                         false
% 2.03/0.99  --qbf_dom_inst                          none
% 2.03/0.99  --qbf_dom_pre_inst                      false
% 2.03/0.99  --qbf_sk_in                             false
% 2.03/0.99  --qbf_pred_elim                         true
% 2.03/0.99  --qbf_split                             512
% 2.03/0.99  
% 2.03/0.99  ------ BMC1 Options
% 2.03/0.99  
% 2.03/0.99  --bmc1_incremental                      false
% 2.03/0.99  --bmc1_axioms                           reachable_all
% 2.03/0.99  --bmc1_min_bound                        0
% 2.03/0.99  --bmc1_max_bound                        -1
% 2.03/0.99  --bmc1_max_bound_default                -1
% 2.03/0.99  --bmc1_symbol_reachability              true
% 2.03/0.99  --bmc1_property_lemmas                  false
% 2.03/0.99  --bmc1_k_induction                      false
% 2.03/0.99  --bmc1_non_equiv_states                 false
% 2.03/0.99  --bmc1_deadlock                         false
% 2.03/0.99  --bmc1_ucm                              false
% 2.03/0.99  --bmc1_add_unsat_core                   none
% 2.03/0.99  --bmc1_unsat_core_children              false
% 2.03/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.03/0.99  --bmc1_out_stat                         full
% 2.03/0.99  --bmc1_ground_init                      false
% 2.03/0.99  --bmc1_pre_inst_next_state              false
% 2.03/0.99  --bmc1_pre_inst_state                   false
% 2.03/0.99  --bmc1_pre_inst_reach_state             false
% 2.03/0.99  --bmc1_out_unsat_core                   false
% 2.03/0.99  --bmc1_aig_witness_out                  false
% 2.03/0.99  --bmc1_verbose                          false
% 2.03/0.99  --bmc1_dump_clauses_tptp                false
% 2.03/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.03/0.99  --bmc1_dump_file                        -
% 2.03/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.03/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.03/0.99  --bmc1_ucm_extend_mode                  1
% 2.03/0.99  --bmc1_ucm_init_mode                    2
% 2.03/0.99  --bmc1_ucm_cone_mode                    none
% 2.03/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.03/0.99  --bmc1_ucm_relax_model                  4
% 2.03/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.03/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.03/0.99  --bmc1_ucm_layered_model                none
% 2.03/0.99  --bmc1_ucm_max_lemma_size               10
% 2.03/0.99  
% 2.03/0.99  ------ AIG Options
% 2.03/0.99  
% 2.03/0.99  --aig_mode                              false
% 2.03/0.99  
% 2.03/0.99  ------ Instantiation Options
% 2.03/0.99  
% 2.03/0.99  --instantiation_flag                    true
% 2.03/0.99  --inst_sos_flag                         false
% 2.03/0.99  --inst_sos_phase                        true
% 2.03/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel_side                     none
% 2.03/0.99  --inst_solver_per_active                1400
% 2.03/0.99  --inst_solver_calls_frac                1.
% 2.03/0.99  --inst_passive_queue_type               priority_queues
% 2.03/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.03/0.99  --inst_passive_queues_freq              [25;2]
% 2.03/0.99  --inst_dismatching                      true
% 2.03/0.99  --inst_eager_unprocessed_to_passive     true
% 2.03/0.99  --inst_prop_sim_given                   true
% 2.03/0.99  --inst_prop_sim_new                     false
% 2.03/0.99  --inst_subs_new                         false
% 2.03/0.99  --inst_eq_res_simp                      false
% 2.03/0.99  --inst_subs_given                       false
% 2.03/0.99  --inst_orphan_elimination               true
% 2.03/0.99  --inst_learning_loop_flag               true
% 2.03/0.99  --inst_learning_start                   3000
% 2.03/0.99  --inst_learning_factor                  2
% 2.03/0.99  --inst_start_prop_sim_after_learn       3
% 2.03/0.99  --inst_sel_renew                        solver
% 2.03/0.99  --inst_lit_activity_flag                true
% 2.03/0.99  --inst_restr_to_given                   false
% 2.03/0.99  --inst_activity_threshold               500
% 2.03/0.99  --inst_out_proof                        true
% 2.03/0.99  
% 2.03/0.99  ------ Resolution Options
% 2.03/0.99  
% 2.03/0.99  --resolution_flag                       false
% 2.03/0.99  --res_lit_sel                           adaptive
% 2.03/0.99  --res_lit_sel_side                      none
% 2.03/0.99  --res_ordering                          kbo
% 2.03/0.99  --res_to_prop_solver                    active
% 2.03/0.99  --res_prop_simpl_new                    false
% 2.03/0.99  --res_prop_simpl_given                  true
% 2.03/0.99  --res_passive_queue_type                priority_queues
% 2.03/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.03/0.99  --res_passive_queues_freq               [15;5]
% 2.03/0.99  --res_forward_subs                      full
% 2.03/0.99  --res_backward_subs                     full
% 2.03/0.99  --res_forward_subs_resolution           true
% 2.03/0.99  --res_backward_subs_resolution          true
% 2.03/0.99  --res_orphan_elimination                true
% 2.03/0.99  --res_time_limit                        2.
% 2.03/0.99  --res_out_proof                         true
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Options
% 2.03/0.99  
% 2.03/0.99  --superposition_flag                    true
% 2.03/0.99  --sup_passive_queue_type                priority_queues
% 2.03/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.03/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.03/0.99  --demod_completeness_check              fast
% 2.03/0.99  --demod_use_ground                      true
% 2.03/0.99  --sup_to_prop_solver                    passive
% 2.03/0.99  --sup_prop_simpl_new                    true
% 2.03/0.99  --sup_prop_simpl_given                  true
% 2.03/0.99  --sup_fun_splitting                     false
% 2.03/0.99  --sup_smt_interval                      50000
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Simplification Setup
% 2.03/0.99  
% 2.03/0.99  --sup_indices_passive                   []
% 2.03/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.03/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_full_bw                           [BwDemod]
% 2.03/0.99  --sup_immed_triv                        [TrivRules]
% 2.03/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.03/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_immed_bw_main                     []
% 2.03/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.03/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  
% 2.03/0.99  ------ Combination Options
% 2.03/0.99  
% 2.03/0.99  --comb_res_mult                         3
% 2.03/0.99  --comb_sup_mult                         2
% 2.03/0.99  --comb_inst_mult                        10
% 2.03/0.99  
% 2.03/0.99  ------ Debug Options
% 2.03/0.99  
% 2.03/0.99  --dbg_backtrace                         false
% 2.03/0.99  --dbg_dump_prop_clauses                 false
% 2.03/0.99  --dbg_dump_prop_clauses_file            -
% 2.03/0.99  --dbg_out_stat                          false
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  ------ Proving...
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  % SZS status Theorem for theBenchmark.p
% 2.03/0.99  
% 2.03/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.03/0.99  
% 2.03/0.99  fof(f1,axiom,(
% 2.03/0.99    v1_xboole_0(k1_xboole_0)),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f39,plain,(
% 2.03/0.99    v1_xboole_0(k1_xboole_0)),
% 2.03/0.99    inference(cnf_transformation,[],[f1])).
% 2.03/0.99  
% 2.03/0.99  fof(f11,conjecture,(
% 2.03/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f12,negated_conjecture,(
% 2.03/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.03/0.99    inference(negated_conjecture,[],[f11])).
% 2.03/0.99  
% 2.03/0.99  fof(f23,plain,(
% 2.03/0.99    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.03/0.99    inference(ennf_transformation,[],[f12])).
% 2.03/0.99  
% 2.03/0.99  fof(f24,plain,(
% 2.03/0.99    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.03/0.99    inference(flattening,[],[f23])).
% 2.03/0.99  
% 2.03/0.99  fof(f34,plain,(
% 2.03/0.99    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.03/0.99    inference(nnf_transformation,[],[f24])).
% 2.03/0.99  
% 2.03/0.99  fof(f35,plain,(
% 2.03/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.03/0.99    inference(flattening,[],[f34])).
% 2.03/0.99  
% 2.03/0.99  fof(f37,plain,(
% 2.03/0.99    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK2) | ~v3_tex_2(sK2,X0)) & (v1_zfmisc_1(sK2) | v3_tex_2(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK2))) )),
% 2.03/0.99    introduced(choice_axiom,[])).
% 2.03/0.99  
% 2.03/0.99  fof(f36,plain,(
% 2.03/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK1)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK1) & v2_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.03/0.99    introduced(choice_axiom,[])).
% 2.03/0.99  
% 2.03/0.99  fof(f38,plain,(
% 2.03/0.99    ((~v1_zfmisc_1(sK2) | ~v3_tex_2(sK2,sK1)) & (v1_zfmisc_1(sK2) | v3_tex_2(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(sK2)) & l1_pre_topc(sK1) & v2_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f35,f37,f36])).
% 2.03/0.99  
% 2.03/0.99  fof(f63,plain,(
% 2.03/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.03/0.99    inference(cnf_transformation,[],[f38])).
% 2.03/0.99  
% 2.03/0.99  fof(f8,axiom,(
% 2.03/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f17,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.99    inference(ennf_transformation,[],[f8])).
% 2.03/0.99  
% 2.03/0.99  fof(f18,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.99    inference(flattening,[],[f17])).
% 2.03/0.99  
% 2.03/0.99  fof(f28,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.99    inference(nnf_transformation,[],[f18])).
% 2.03/0.99  
% 2.03/0.99  fof(f29,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.99    inference(flattening,[],[f28])).
% 2.03/0.99  
% 2.03/0.99  fof(f30,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.99    inference(rectify,[],[f29])).
% 2.03/0.99  
% 2.03/0.99  fof(f31,plain,(
% 2.03/0.99    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.03/0.99    introduced(choice_axiom,[])).
% 2.03/0.99  
% 2.03/0.99  fof(f32,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 2.03/0.99  
% 2.03/0.99  fof(f51,plain,(
% 2.03/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f32])).
% 2.03/0.99  
% 2.03/0.99  fof(f61,plain,(
% 2.03/0.99    l1_pre_topc(sK1)),
% 2.03/0.99    inference(cnf_transformation,[],[f38])).
% 2.03/0.99  
% 2.03/0.99  fof(f10,axiom,(
% 2.03/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f21,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.03/0.99    inference(ennf_transformation,[],[f10])).
% 2.03/0.99  
% 2.03/0.99  fof(f22,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.03/0.99    inference(flattening,[],[f21])).
% 2.03/0.99  
% 2.03/0.99  fof(f33,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.03/0.99    inference(nnf_transformation,[],[f22])).
% 2.03/0.99  
% 2.03/0.99  fof(f56,plain,(
% 2.03/0.99    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f33])).
% 2.03/0.99  
% 2.03/0.99  fof(f6,axiom,(
% 2.03/0.99    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f14,plain,(
% 2.03/0.99    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 2.03/0.99    inference(ennf_transformation,[],[f6])).
% 2.03/0.99  
% 2.03/0.99  fof(f47,plain,(
% 2.03/0.99    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f14])).
% 2.03/0.99  
% 2.03/0.99  fof(f58,plain,(
% 2.03/0.99    ~v2_struct_0(sK1)),
% 2.03/0.99    inference(cnf_transformation,[],[f38])).
% 2.03/0.99  
% 2.03/0.99  fof(f59,plain,(
% 2.03/0.99    v2_pre_topc(sK1)),
% 2.03/0.99    inference(cnf_transformation,[],[f38])).
% 2.03/0.99  
% 2.03/0.99  fof(f60,plain,(
% 2.03/0.99    v2_tdlat_3(sK1)),
% 2.03/0.99    inference(cnf_transformation,[],[f38])).
% 2.03/0.99  
% 2.03/0.99  fof(f9,axiom,(
% 2.03/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f19,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.03/0.99    inference(ennf_transformation,[],[f9])).
% 2.03/0.99  
% 2.03/0.99  fof(f20,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.03/0.99    inference(flattening,[],[f19])).
% 2.03/0.99  
% 2.03/0.99  fof(f55,plain,(
% 2.03/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f20])).
% 2.03/0.99  
% 2.03/0.99  fof(f52,plain,(
% 2.03/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | v2_tex_2(sK0(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f32])).
% 2.03/0.99  
% 2.03/0.99  fof(f62,plain,(
% 2.03/0.99    ~v1_xboole_0(sK2)),
% 2.03/0.99    inference(cnf_transformation,[],[f38])).
% 2.03/0.99  
% 2.03/0.99  fof(f57,plain,(
% 2.03/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f33])).
% 2.03/0.99  
% 2.03/0.99  fof(f64,plain,(
% 2.03/0.99    v1_zfmisc_1(sK2) | v3_tex_2(sK2,sK1)),
% 2.03/0.99    inference(cnf_transformation,[],[f38])).
% 2.03/0.99  
% 2.03/0.99  fof(f49,plain,(
% 2.03/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f32])).
% 2.03/0.99  
% 2.03/0.99  fof(f65,plain,(
% 2.03/0.99    ~v1_zfmisc_1(sK2) | ~v3_tex_2(sK2,sK1)),
% 2.03/0.99    inference(cnf_transformation,[],[f38])).
% 2.03/0.99  
% 2.03/0.99  fof(f54,plain,(
% 2.03/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK0(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f32])).
% 2.03/0.99  
% 2.03/0.99  fof(f53,plain,(
% 2.03/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK0(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f32])).
% 2.03/0.99  
% 2.03/0.99  fof(f5,axiom,(
% 2.03/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f13,plain,(
% 2.03/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.03/0.99    inference(ennf_transformation,[],[f5])).
% 2.03/0.99  
% 2.03/0.99  fof(f46,plain,(
% 2.03/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f13])).
% 2.03/0.99  
% 2.03/0.99  fof(f2,axiom,(
% 2.03/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f25,plain,(
% 2.03/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.03/0.99    inference(nnf_transformation,[],[f2])).
% 2.03/0.99  
% 2.03/0.99  fof(f26,plain,(
% 2.03/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.03/0.99    inference(flattening,[],[f25])).
% 2.03/0.99  
% 2.03/0.99  fof(f40,plain,(
% 2.03/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.03/0.99    inference(cnf_transformation,[],[f26])).
% 2.03/0.99  
% 2.03/0.99  fof(f67,plain,(
% 2.03/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.03/0.99    inference(equality_resolution,[],[f40])).
% 2.03/0.99  
% 2.03/0.99  fof(f3,axiom,(
% 2.03/0.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f27,plain,(
% 2.03/0.99    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.03/0.99    inference(nnf_transformation,[],[f3])).
% 2.03/0.99  
% 2.03/0.99  fof(f44,plain,(
% 2.03/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f27])).
% 2.03/0.99  
% 2.03/0.99  fof(f4,axiom,(
% 2.03/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f45,plain,(
% 2.03/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f4])).
% 2.03/0.99  
% 2.03/0.99  fof(f42,plain,(
% 2.03/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f26])).
% 2.03/0.99  
% 2.03/0.99  cnf(c_0,plain,
% 2.03/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.03/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1933,plain,
% 2.03/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_21,negated_conjecture,
% 2.03/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.03/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1926,plain,
% 2.03/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_13,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.99      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.99      | ~ v2_tex_2(X0,X1)
% 2.03/0.99      | v3_tex_2(X0,X1)
% 2.03/0.99      | ~ l1_pre_topc(X1) ),
% 2.03/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_23,negated_conjecture,
% 2.03/0.99      ( l1_pre_topc(sK1) ),
% 2.03/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_447,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.99      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.99      | ~ v2_tex_2(X0,X1)
% 2.03/0.99      | v3_tex_2(X0,X1)
% 2.03/0.99      | sK1 != X1 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_448,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | ~ v2_tex_2(X0,sK1)
% 2.03/0.99      | v3_tex_2(X0,sK1) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_447]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1922,plain,
% 2.03/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.03/0.99      | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.03/0.99      | v2_tex_2(X0,sK1) != iProver_top
% 2.03/0.99      | v3_tex_2(X0,sK1) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_18,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.99      | ~ v2_tex_2(X0,X1)
% 2.03/0.99      | v2_struct_0(X1)
% 2.03/0.99      | ~ l1_pre_topc(X1)
% 2.03/0.99      | ~ v2_tdlat_3(X1)
% 2.03/0.99      | ~ v2_pre_topc(X1)
% 2.03/0.99      | v1_zfmisc_1(X0)
% 2.03/0.99      | v1_xboole_0(X0) ),
% 2.03/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_8,plain,
% 2.03/0.99      ( v1_zfmisc_1(X0) | ~ v1_xboole_0(X0) ),
% 2.03/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_149,plain,
% 2.03/0.99      ( v1_zfmisc_1(X0)
% 2.03/0.99      | ~ v2_pre_topc(X1)
% 2.03/0.99      | ~ v2_tdlat_3(X1)
% 2.03/0.99      | ~ l1_pre_topc(X1)
% 2.03/0.99      | v2_struct_0(X1)
% 2.03/0.99      | ~ v2_tex_2(X0,X1)
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ),
% 2.03/0.99      inference(global_propositional_subsumption,
% 2.03/0.99                [status(thm)],
% 2.03/0.99                [c_18,c_8]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_150,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.99      | ~ v2_tex_2(X0,X1)
% 2.03/0.99      | v2_struct_0(X1)
% 2.03/0.99      | ~ l1_pre_topc(X1)
% 2.03/0.99      | ~ v2_tdlat_3(X1)
% 2.03/0.99      | ~ v2_pre_topc(X1)
% 2.03/0.99      | v1_zfmisc_1(X0) ),
% 2.03/0.99      inference(renaming,[status(thm)],[c_149]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_26,negated_conjecture,
% 2.03/0.99      ( ~ v2_struct_0(sK1) ),
% 2.03/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_356,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.99      | ~ v2_tex_2(X0,X1)
% 2.03/0.99      | ~ l1_pre_topc(X1)
% 2.03/0.99      | ~ v2_tdlat_3(X1)
% 2.03/0.99      | ~ v2_pre_topc(X1)
% 2.03/0.99      | v1_zfmisc_1(X0)
% 2.03/0.99      | sK1 != X1 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_150,c_26]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_357,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | ~ v2_tex_2(X0,sK1)
% 2.03/0.99      | ~ l1_pre_topc(sK1)
% 2.03/0.99      | ~ v2_tdlat_3(sK1)
% 2.03/0.99      | ~ v2_pre_topc(sK1)
% 2.03/0.99      | v1_zfmisc_1(X0) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_356]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_25,negated_conjecture,
% 2.03/0.99      ( v2_pre_topc(sK1) ),
% 2.03/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_24,negated_conjecture,
% 2.03/0.99      ( v2_tdlat_3(sK1) ),
% 2.03/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_361,plain,
% 2.03/0.99      ( ~ v2_tex_2(X0,sK1)
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | v1_zfmisc_1(X0) ),
% 2.03/0.99      inference(global_propositional_subsumption,
% 2.03/0.99                [status(thm)],
% 2.03/0.99                [c_357,c_25,c_24,c_23]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_362,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | ~ v2_tex_2(X0,sK1)
% 2.03/0.99      | v1_zfmisc_1(X0) ),
% 2.03/0.99      inference(renaming,[status(thm)],[c_361]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_16,plain,
% 2.03/0.99      ( ~ r1_tarski(X0,X1)
% 2.03/0.99      | ~ v1_zfmisc_1(X1)
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | X1 = X0 ),
% 2.03/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_553,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | ~ v2_tex_2(X0,sK1)
% 2.03/0.99      | ~ r1_tarski(X1,X2)
% 2.03/0.99      | v1_xboole_0(X2)
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | X2 != X0
% 2.03/0.99      | X1 = X2 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_362,c_16]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_554,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | ~ v2_tex_2(X0,sK1)
% 2.03/0.99      | ~ r1_tarski(X1,X0)
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | X1 = X0 ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_553]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1918,plain,
% 2.03/0.99      ( X0 = X1
% 2.03/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.03/0.99      | v2_tex_2(X1,sK1) != iProver_top
% 2.03/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.03/0.99      | v1_xboole_0(X1) = iProver_top
% 2.03/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_554]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2992,plain,
% 2.03/0.99      ( sK0(sK1,X0) = X1
% 2.03/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.03/0.99      | v2_tex_2(X0,sK1) != iProver_top
% 2.03/0.99      | v2_tex_2(sK0(sK1,X0),sK1) != iProver_top
% 2.03/0.99      | v3_tex_2(X0,sK1) = iProver_top
% 2.03/0.99      | r1_tarski(X1,sK0(sK1,X0)) != iProver_top
% 2.03/0.99      | v1_xboole_0(X1) = iProver_top
% 2.03/0.99      | v1_xboole_0(sK0(sK1,X0)) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1922,c_1918]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_12,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.99      | ~ v2_tex_2(X0,X1)
% 2.03/0.99      | v2_tex_2(sK0(X1,X0),X1)
% 2.03/0.99      | v3_tex_2(X0,X1)
% 2.03/0.99      | ~ l1_pre_topc(X1) ),
% 2.03/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_465,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.99      | ~ v2_tex_2(X0,X1)
% 2.03/0.99      | v2_tex_2(sK0(X1,X0),X1)
% 2.03/0.99      | v3_tex_2(X0,X1)
% 2.03/0.99      | sK1 != X1 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_466,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | ~ v2_tex_2(X0,sK1)
% 2.03/0.99      | v2_tex_2(sK0(sK1,X0),sK1)
% 2.03/0.99      | v3_tex_2(X0,sK1) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_465]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_467,plain,
% 2.03/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.03/0.99      | v2_tex_2(X0,sK1) != iProver_top
% 2.03/0.99      | v2_tex_2(sK0(sK1,X0),sK1) = iProver_top
% 2.03/0.99      | v3_tex_2(X0,sK1) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_466]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3724,plain,
% 2.03/0.99      ( v2_tex_2(X0,sK1) != iProver_top
% 2.03/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.03/0.99      | sK0(sK1,X0) = X1
% 2.03/0.99      | v3_tex_2(X0,sK1) = iProver_top
% 2.03/0.99      | r1_tarski(X1,sK0(sK1,X0)) != iProver_top
% 2.03/0.99      | v1_xboole_0(X1) = iProver_top
% 2.03/0.99      | v1_xboole_0(sK0(sK1,X0)) = iProver_top ),
% 2.03/0.99      inference(global_propositional_subsumption,
% 2.03/0.99                [status(thm)],
% 2.03/0.99                [c_2992,c_467]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3725,plain,
% 2.03/0.99      ( sK0(sK1,X0) = X1
% 2.03/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.03/0.99      | v2_tex_2(X0,sK1) != iProver_top
% 2.03/0.99      | v3_tex_2(X0,sK1) = iProver_top
% 2.03/0.99      | r1_tarski(X1,sK0(sK1,X0)) != iProver_top
% 2.03/0.99      | v1_xboole_0(X1) = iProver_top
% 2.03/0.99      | v1_xboole_0(sK0(sK1,X0)) = iProver_top ),
% 2.03/0.99      inference(renaming,[status(thm)],[c_3724]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3737,plain,
% 2.03/0.99      ( sK0(sK1,sK2) = X0
% 2.03/0.99      | v2_tex_2(sK2,sK1) != iProver_top
% 2.03/0.99      | v3_tex_2(sK2,sK1) = iProver_top
% 2.03/0.99      | r1_tarski(X0,sK0(sK1,sK2)) != iProver_top
% 2.03/0.99      | v1_xboole_0(X0) = iProver_top
% 2.03/0.99      | v1_xboole_0(sK0(sK1,sK2)) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1926,c_3725]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_22,negated_conjecture,
% 2.03/0.99      ( ~ v1_xboole_0(sK2) ),
% 2.03/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_31,plain,
% 2.03/0.99      ( v1_xboole_0(sK2) != iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_32,plain,
% 2.03/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_17,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.99      | v2_tex_2(X0,X1)
% 2.03/0.99      | v2_struct_0(X1)
% 2.03/0.99      | ~ l1_pre_topc(X1)
% 2.03/0.99      | ~ v2_tdlat_3(X1)
% 2.03/0.99      | ~ v2_pre_topc(X1)
% 2.03/0.99      | ~ v1_zfmisc_1(X0)
% 2.03/0.99      | v1_xboole_0(X0) ),
% 2.03/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_377,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.99      | v2_tex_2(X0,X1)
% 2.03/0.99      | ~ l1_pre_topc(X1)
% 2.03/0.99      | ~ v2_tdlat_3(X1)
% 2.03/0.99      | ~ v2_pre_topc(X1)
% 2.03/0.99      | ~ v1_zfmisc_1(X0)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | sK1 != X1 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_378,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | v2_tex_2(X0,sK1)
% 2.03/0.99      | ~ l1_pre_topc(sK1)
% 2.03/0.99      | ~ v2_tdlat_3(sK1)
% 2.03/0.99      | ~ v2_pre_topc(sK1)
% 2.03/0.99      | ~ v1_zfmisc_1(X0)
% 2.03/0.99      | v1_xboole_0(X0) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_377]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_382,plain,
% 2.03/0.99      ( v2_tex_2(X0,sK1)
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | ~ v1_zfmisc_1(X0)
% 2.03/0.99      | v1_xboole_0(X0) ),
% 2.03/0.99      inference(global_propositional_subsumption,
% 2.03/0.99                [status(thm)],
% 2.03/0.99                [c_378,c_25,c_24,c_23]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_383,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | v2_tex_2(X0,sK1)
% 2.03/0.99      | ~ v1_zfmisc_1(X0)
% 2.03/0.99      | v1_xboole_0(X0) ),
% 2.03/0.99      inference(renaming,[status(thm)],[c_382]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_20,negated_conjecture,
% 2.03/0.99      ( v3_tex_2(sK2,sK1) | v1_zfmisc_1(sK2) ),
% 2.03/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_210,plain,
% 2.03/0.99      ( v1_zfmisc_1(sK2) | v3_tex_2(sK2,sK1) ),
% 2.03/0.99      inference(prop_impl,[status(thm)],[c_20]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_211,plain,
% 2.03/0.99      ( v3_tex_2(sK2,sK1) | v1_zfmisc_1(sK2) ),
% 2.03/0.99      inference(renaming,[status(thm)],[c_210]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_593,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | v2_tex_2(X0,sK1)
% 2.03/0.99      | v3_tex_2(sK2,sK1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | sK2 != X0 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_383,c_211]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_594,plain,
% 2.03/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | v2_tex_2(sK2,sK1)
% 2.03/0.99      | v3_tex_2(sK2,sK1)
% 2.03/0.99      | v1_xboole_0(sK2) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_593]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_596,plain,
% 2.03/0.99      ( v3_tex_2(sK2,sK1) | v2_tex_2(sK2,sK1) ),
% 2.03/0.99      inference(global_propositional_subsumption,
% 2.03/0.99                [status(thm)],
% 2.03/0.99                [c_594,c_22,c_21]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_597,plain,
% 2.03/0.99      ( v2_tex_2(sK2,sK1) | v3_tex_2(sK2,sK1) ),
% 2.03/0.99      inference(renaming,[status(thm)],[c_596]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_15,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.99      | v2_tex_2(X0,X1)
% 2.03/0.99      | ~ v3_tex_2(X0,X1)
% 2.03/0.99      | ~ l1_pre_topc(X1) ),
% 2.03/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_410,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.99      | v2_tex_2(X0,X1)
% 2.03/0.99      | ~ v3_tex_2(X0,X1)
% 2.03/0.99      | sK1 != X1 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_411,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | v2_tex_2(X0,sK1)
% 2.03/0.99      | ~ v3_tex_2(X0,sK1) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_410]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_848,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | v2_tex_2(X0,sK1)
% 2.03/0.99      | v2_tex_2(sK2,sK1)
% 2.03/0.99      | sK1 != sK1
% 2.03/0.99      | sK2 != X0 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_597,c_411]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_849,plain,
% 2.03/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | v2_tex_2(sK2,sK1) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_848]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_850,plain,
% 2.03/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.03/0.99      | v2_tex_2(sK2,sK1) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_849]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_19,negated_conjecture,
% 2.03/0.99      ( ~ v3_tex_2(sK2,sK1) | ~ v1_zfmisc_1(sK2) ),
% 2.03/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_208,plain,
% 2.03/0.99      ( ~ v1_zfmisc_1(sK2) | ~ v3_tex_2(sK2,sK1) ),
% 2.03/0.99      inference(prop_impl,[status(thm)],[c_19]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_209,plain,
% 2.03/0.99      ( ~ v3_tex_2(sK2,sK1) | ~ v1_zfmisc_1(sK2) ),
% 2.03/0.99      inference(renaming,[status(thm)],[c_208]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_577,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | ~ v2_tex_2(X0,sK1)
% 2.03/0.99      | ~ v3_tex_2(sK2,sK1)
% 2.03/0.99      | sK2 != X0 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_362,c_209]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_578,plain,
% 2.03/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | ~ v2_tex_2(sK2,sK1)
% 2.03/0.99      | ~ v3_tex_2(sK2,sK1) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_577]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_580,plain,
% 2.03/0.99      ( ~ v2_tex_2(sK2,sK1) | ~ v3_tex_2(sK2,sK1) ),
% 2.03/0.99      inference(global_propositional_subsumption,
% 2.03/0.99                [status(thm)],
% 2.03/0.99                [c_578,c_21]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_10,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.99      | ~ v2_tex_2(X0,X1)
% 2.03/0.99      | v3_tex_2(X0,X1)
% 2.03/0.99      | ~ l1_pre_topc(X1)
% 2.03/0.99      | sK0(X1,X0) != X0 ),
% 2.03/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_501,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.99      | ~ v2_tex_2(X0,X1)
% 2.03/0.99      | v3_tex_2(X0,X1)
% 2.03/0.99      | sK0(X1,X0) != X0
% 2.03/0.99      | sK1 != X1 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_502,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | ~ v2_tex_2(X0,sK1)
% 2.03/0.99      | v3_tex_2(X0,sK1)
% 2.03/0.99      | sK0(sK1,X0) != X0 ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_501]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_859,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | ~ v2_tex_2(X0,sK1)
% 2.03/0.99      | ~ v2_tex_2(sK2,sK1)
% 2.03/0.99      | sK0(sK1,X0) != X0
% 2.03/0.99      | sK1 != sK1
% 2.03/0.99      | sK2 != X0 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_580,c_502]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_860,plain,
% 2.03/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | ~ v2_tex_2(sK2,sK1)
% 2.03/0.99      | sK0(sK1,sK2) != sK2 ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_859]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_11,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.99      | ~ v2_tex_2(X0,X1)
% 2.03/0.99      | v3_tex_2(X0,X1)
% 2.03/0.99      | r1_tarski(X0,sK0(X1,X0))
% 2.03/0.99      | ~ l1_pre_topc(X1) ),
% 2.03/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_483,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.99      | ~ v2_tex_2(X0,X1)
% 2.03/0.99      | v3_tex_2(X0,X1)
% 2.03/0.99      | r1_tarski(X0,sK0(X1,X0))
% 2.03/0.99      | sK1 != X1 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_484,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | ~ v2_tex_2(X0,sK1)
% 2.03/0.99      | v3_tex_2(X0,sK1)
% 2.03/0.99      | r1_tarski(X0,sK0(sK1,X0)) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_483]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_867,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | ~ v2_tex_2(X0,sK1)
% 2.03/0.99      | ~ v2_tex_2(sK2,sK1)
% 2.03/0.99      | r1_tarski(X0,sK0(sK1,X0))
% 2.03/0.99      | sK1 != sK1
% 2.03/0.99      | sK2 != X0 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_580,c_484]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_868,plain,
% 2.03/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | ~ v2_tex_2(sK2,sK1)
% 2.03/0.99      | r1_tarski(sK2,sK0(sK1,sK2)) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_867]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_869,plain,
% 2.03/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.03/0.99      | v2_tex_2(sK2,sK1) != iProver_top
% 2.03/0.99      | r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_868]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_878,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | ~ v2_tex_2(X0,sK1)
% 2.03/0.99      | v2_tex_2(sK0(sK1,X0),sK1)
% 2.03/0.99      | ~ v2_tex_2(sK2,sK1)
% 2.03/0.99      | sK1 != sK1
% 2.03/0.99      | sK2 != X0 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_580,c_466]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_879,plain,
% 2.03/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | v2_tex_2(sK0(sK1,sK2),sK1)
% 2.03/0.99      | ~ v2_tex_2(sK2,sK1) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_878]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_880,plain,
% 2.03/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.03/0.99      | v2_tex_2(sK0(sK1,sK2),sK1) = iProver_top
% 2.03/0.99      | v2_tex_2(sK2,sK1) != iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_879]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_889,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | ~ v2_tex_2(X0,sK1)
% 2.03/0.99      | ~ v2_tex_2(sK2,sK1)
% 2.03/0.99      | sK1 != sK1
% 2.03/0.99      | sK2 != X0 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_580,c_448]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_890,plain,
% 2.03/0.99      ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | ~ v2_tex_2(sK2,sK1) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_889]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_891,plain,
% 2.03/0.99      ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.03/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.03/0.99      | v2_tex_2(sK2,sK1) != iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_890]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1451,plain,( X0 = X0 ),theory(equality) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2455,plain,
% 2.03/0.99      ( sK0(sK1,sK2) = sK0(sK1,sK2) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_1451]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2271,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | ~ v2_tex_2(X0,sK1)
% 2.03/0.99      | ~ r1_tarski(sK2,X0)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | v1_xboole_0(sK2)
% 2.03/0.99      | sK2 = X0 ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_554]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2472,plain,
% 2.03/0.99      ( ~ m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.03/0.99      | ~ v2_tex_2(sK0(sK1,sK2),sK1)
% 2.03/0.99      | ~ r1_tarski(sK2,sK0(sK1,sK2))
% 2.03/0.99      | v1_xboole_0(sK0(sK1,sK2))
% 2.03/0.99      | v1_xboole_0(sK2)
% 2.03/0.99      | sK2 = sK0(sK1,sK2) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_2271]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2473,plain,
% 2.03/0.99      ( sK2 = sK0(sK1,sK2)
% 2.03/0.99      | m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.03/0.99      | v2_tex_2(sK0(sK1,sK2),sK1) != iProver_top
% 2.03/0.99      | r1_tarski(sK2,sK0(sK1,sK2)) != iProver_top
% 2.03/0.99      | v1_xboole_0(sK0(sK1,sK2)) = iProver_top
% 2.03/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_2472]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1452,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2181,plain,
% 2.03/0.99      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_1452]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2612,plain,
% 2.03/0.99      ( X0 != sK0(sK1,sK2) | X0 = sK2 | sK2 != sK0(sK1,sK2) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_2181]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2971,plain,
% 2.03/0.99      ( sK0(sK1,sK2) != sK0(sK1,sK2)
% 2.03/0.99      | sK0(sK1,sK2) = sK2
% 2.03/0.99      | sK2 != sK0(sK1,sK2) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_2612]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3776,plain,
% 2.03/0.99      ( v1_xboole_0(sK0(sK1,sK2)) = iProver_top ),
% 2.03/0.99      inference(global_propositional_subsumption,
% 2.03/0.99                [status(thm)],
% 2.03/0.99                [c_3737,c_31,c_21,c_32,c_849,c_850,c_860,c_869,c_880,
% 2.03/0.99                 c_891,c_2455,c_2473,c_2971]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_7,plain,
% 2.03/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 2.03/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1927,plain,
% 2.03/0.99      ( X0 = X1
% 2.03/0.99      | v1_xboole_0(X0) != iProver_top
% 2.03/0.99      | v1_xboole_0(X1) != iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3781,plain,
% 2.03/0.99      ( sK0(sK1,sK2) = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_3776,c_1927]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3823,plain,
% 2.03/0.99      ( sK0(sK1,sK2) = k1_xboole_0 ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1933,c_3781]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1920,plain,
% 2.03/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.03/0.99      | v2_tex_2(X0,sK1) != iProver_top
% 2.03/0.99      | v3_tex_2(X0,sK1) = iProver_top
% 2.03/0.99      | r1_tarski(X0,sK0(sK1,X0)) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_484]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2247,plain,
% 2.03/0.99      ( v2_tex_2(sK2,sK1) != iProver_top
% 2.03/0.99      | v3_tex_2(sK2,sK1) = iProver_top
% 2.03/0.99      | r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1926,c_1920]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2250,plain,
% 2.03/0.99      ( r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
% 2.03/0.99      inference(global_propositional_subsumption,
% 2.03/0.99                [status(thm)],
% 2.03/0.99                [c_2247,c_32,c_850,c_869]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_4046,plain,
% 2.03/0.99      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 2.03/0.99      inference(demodulation,[status(thm)],[c_3823,c_2250]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3,plain,
% 2.03/0.99      ( r1_tarski(X0,X0) ),
% 2.03/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1931,plain,
% 2.03/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_4,plain,
% 2.03/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.03/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1930,plain,
% 2.03/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 2.03/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3259,plain,
% 2.03/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_1931,c_1930]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_6,plain,
% 2.03/0.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 2.03/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1928,plain,
% 2.03/0.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3355,plain,
% 2.03/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_3259,c_1928]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1,plain,
% 2.03/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.03/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1932,plain,
% 2.03/0.99      ( X0 = X1
% 2.03/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.03/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3363,plain,
% 2.03/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_3355,c_1932]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_4695,plain,
% 2.03/0.99      ( sK2 = k1_xboole_0 ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_4046,c_3363]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1919,plain,
% 2.03/0.99      ( sK0(sK1,X0) != X0
% 2.03/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.03/0.99      | v2_tex_2(X0,sK1) != iProver_top
% 2.03/0.99      | v3_tex_2(X0,sK1) = iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_502]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_4066,plain,
% 2.03/0.99      ( sK2 != k1_xboole_0
% 2.03/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.03/0.99      | v2_tex_2(sK2,sK1) != iProver_top
% 2.03/0.99      | v3_tex_2(sK2,sK1) = iProver_top ),
% 2.03/0.99      inference(superposition,[status(thm)],[c_3823,c_1919]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_582,plain,
% 2.03/0.99      ( v2_tex_2(sK2,sK1) != iProver_top
% 2.03/0.99      | v3_tex_2(sK2,sK1) != iProver_top ),
% 2.03/0.99      inference(predicate_to_equality,[status(thm)],[c_580]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(contradiction,plain,
% 2.03/0.99      ( $false ),
% 2.03/0.99      inference(minisat,[status(thm)],[c_4695,c_4066,c_850,c_582,c_32]) ).
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.03/0.99  
% 2.03/0.99  ------                               Statistics
% 2.03/0.99  
% 2.03/0.99  ------ General
% 2.03/0.99  
% 2.03/0.99  abstr_ref_over_cycles:                  0
% 2.03/0.99  abstr_ref_under_cycles:                 0
% 2.03/0.99  gc_basic_clause_elim:                   0
% 2.03/0.99  forced_gc_time:                         0
% 2.03/0.99  parsing_time:                           0.009
% 2.03/0.99  unif_index_cands_time:                  0.
% 2.03/0.99  unif_index_add_time:                    0.
% 2.03/0.99  orderings_time:                         0.
% 2.03/0.99  out_proof_time:                         0.009
% 2.03/0.99  total_time:                             0.158
% 2.03/0.99  num_of_symbols:                         48
% 2.03/0.99  num_of_terms:                           2274
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing
% 2.03/0.99  
% 2.03/0.99  num_of_splits:                          0
% 2.03/0.99  num_of_split_atoms:                     0
% 2.03/0.99  num_of_reused_defs:                     0
% 2.03/0.99  num_eq_ax_congr_red:                    11
% 2.03/0.99  num_of_sem_filtered_clauses:            1
% 2.03/0.99  num_of_subtypes:                        0
% 2.03/0.99  monotx_restored_types:                  0
% 2.03/0.99  sat_num_of_epr_types:                   0
% 2.03/0.99  sat_num_of_non_cyclic_types:            0
% 2.03/0.99  sat_guarded_non_collapsed_types:        0
% 2.03/0.99  num_pure_diseq_elim:                    0
% 2.03/0.99  simp_replaced_by:                       0
% 2.03/0.99  res_preprocessed:                       104
% 2.03/0.99  prep_upred:                             0
% 2.03/0.99  prep_unflattend:                        30
% 2.03/0.99  smt_new_axioms:                         0
% 2.03/0.99  pred_elim_cands:                        5
% 2.03/0.99  pred_elim:                              5
% 2.03/0.99  pred_elim_cl:                           7
% 2.03/0.99  pred_elim_cycles:                       8
% 2.03/0.99  merged_defs:                            10
% 2.03/0.99  merged_defs_ncl:                        0
% 2.03/0.99  bin_hyper_res:                          10
% 2.03/0.99  prep_cycles:                            4
% 2.03/0.99  pred_elim_time:                         0.016
% 2.03/0.99  splitting_time:                         0.
% 2.03/0.99  sem_filter_time:                        0.
% 2.03/0.99  monotx_time:                            0.
% 2.03/0.99  subtype_inf_time:                       0.
% 2.03/0.99  
% 2.03/0.99  ------ Problem properties
% 2.03/0.99  
% 2.03/0.99  clauses:                                19
% 2.03/0.99  conjectures:                            2
% 2.03/0.99  epr:                                    8
% 2.03/0.99  horn:                                   14
% 2.03/0.99  ground:                                 5
% 2.03/0.99  unary:                                  7
% 2.03/0.99  binary:                                 2
% 2.03/0.99  lits:                                   51
% 2.03/0.99  lits_eq:                                8
% 2.03/0.99  fd_pure:                                0
% 2.03/0.99  fd_pseudo:                              0
% 2.03/0.99  fd_cond:                                1
% 2.03/0.99  fd_pseudo_cond:                         4
% 2.03/0.99  ac_symbols:                             0
% 2.03/0.99  
% 2.03/0.99  ------ Propositional Solver
% 2.03/0.99  
% 2.03/0.99  prop_solver_calls:                      28
% 2.03/0.99  prop_fast_solver_calls:                 1053
% 2.03/0.99  smt_solver_calls:                       0
% 2.03/0.99  smt_fast_solver_calls:                  0
% 2.03/0.99  prop_num_of_clauses:                    1292
% 2.03/0.99  prop_preprocess_simplified:             4583
% 2.03/0.99  prop_fo_subsumed:                       73
% 2.03/0.99  prop_solver_time:                       0.
% 2.03/0.99  smt_solver_time:                        0.
% 2.03/0.99  smt_fast_solver_time:                   0.
% 2.03/0.99  prop_fast_solver_time:                  0.
% 2.03/0.99  prop_unsat_core_time:                   0.
% 2.03/0.99  
% 2.03/0.99  ------ QBF
% 2.03/0.99  
% 2.03/0.99  qbf_q_res:                              0
% 2.03/0.99  qbf_num_tautologies:                    0
% 2.03/0.99  qbf_prep_cycles:                        0
% 2.03/0.99  
% 2.03/0.99  ------ BMC1
% 2.03/0.99  
% 2.03/0.99  bmc1_current_bound:                     -1
% 2.03/0.99  bmc1_last_solved_bound:                 -1
% 2.03/0.99  bmc1_unsat_core_size:                   -1
% 2.03/0.99  bmc1_unsat_core_parents_size:           -1
% 2.03/0.99  bmc1_merge_next_fun:                    0
% 2.03/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.03/0.99  
% 2.03/0.99  ------ Instantiation
% 2.03/0.99  
% 2.03/0.99  inst_num_of_clauses:                    352
% 2.03/0.99  inst_num_in_passive:                    43
% 2.03/0.99  inst_num_in_active:                     222
% 2.03/0.99  inst_num_in_unprocessed:                87
% 2.03/0.99  inst_num_of_loops:                      240
% 2.03/0.99  inst_num_of_learning_restarts:          0
% 2.03/0.99  inst_num_moves_active_passive:          15
% 2.03/0.99  inst_lit_activity:                      0
% 2.03/0.99  inst_lit_activity_moves:                0
% 2.03/0.99  inst_num_tautologies:                   0
% 2.03/0.99  inst_num_prop_implied:                  0
% 2.03/0.99  inst_num_existing_simplified:           0
% 2.03/0.99  inst_num_eq_res_simplified:             0
% 2.03/0.99  inst_num_child_elim:                    0
% 2.03/0.99  inst_num_of_dismatching_blockings:      67
% 2.03/0.99  inst_num_of_non_proper_insts:           400
% 2.03/0.99  inst_num_of_duplicates:                 0
% 2.03/0.99  inst_inst_num_from_inst_to_res:         0
% 2.03/0.99  inst_dismatching_checking_time:         0.
% 2.03/0.99  
% 2.03/0.99  ------ Resolution
% 2.03/0.99  
% 2.03/0.99  res_num_of_clauses:                     0
% 2.03/0.99  res_num_in_passive:                     0
% 2.03/0.99  res_num_in_active:                      0
% 2.03/0.99  res_num_of_loops:                       108
% 2.03/0.99  res_forward_subset_subsumed:            100
% 2.03/0.99  res_backward_subset_subsumed:           3
% 2.03/0.99  res_forward_subsumed:                   0
% 2.03/0.99  res_backward_subsumed:                  4
% 2.03/0.99  res_forward_subsumption_resolution:     0
% 2.03/0.99  res_backward_subsumption_resolution:    1
% 2.03/0.99  res_clause_to_clause_subsumption:       314
% 2.03/0.99  res_orphan_elimination:                 0
% 2.03/0.99  res_tautology_del:                      67
% 2.03/0.99  res_num_eq_res_simplified:              0
% 2.03/0.99  res_num_sel_changes:                    0
% 2.03/0.99  res_moves_from_active_to_pass:          0
% 2.03/0.99  
% 2.03/0.99  ------ Superposition
% 2.03/0.99  
% 2.03/0.99  sup_time_total:                         0.
% 2.03/0.99  sup_time_generating:                    0.
% 2.03/0.99  sup_time_sim_full:                      0.
% 2.03/0.99  sup_time_sim_immed:                     0.
% 2.03/0.99  
% 2.03/0.99  sup_num_of_clauses:                     55
% 2.03/0.99  sup_num_in_active:                      40
% 2.03/0.99  sup_num_in_passive:                     15
% 2.03/0.99  sup_num_of_loops:                       46
% 2.03/0.99  sup_fw_superposition:                   38
% 2.03/0.99  sup_bw_superposition:                   37
% 2.03/0.99  sup_immediate_simplified:               22
% 2.03/0.99  sup_given_eliminated:                   1
% 2.03/0.99  comparisons_done:                       0
% 2.03/0.99  comparisons_avoided:                    0
% 2.03/0.99  
% 2.03/0.99  ------ Simplifications
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  sim_fw_subset_subsumed:                 10
% 2.03/0.99  sim_bw_subset_subsumed:                 0
% 2.03/0.99  sim_fw_subsumed:                        8
% 2.03/0.99  sim_bw_subsumed:                        1
% 2.03/0.99  sim_fw_subsumption_res:                 0
% 2.03/0.99  sim_bw_subsumption_res:                 0
% 2.03/0.99  sim_tautology_del:                      0
% 2.03/0.99  sim_eq_tautology_del:                   7
% 2.03/0.99  sim_eq_res_simp:                        0
% 2.03/0.99  sim_fw_demodulated:                     1
% 2.03/0.99  sim_bw_demodulated:                     7
% 2.03/0.99  sim_light_normalised:                   5
% 2.03/0.99  sim_joinable_taut:                      0
% 2.03/0.99  sim_joinable_simp:                      0
% 2.03/0.99  sim_ac_normalised:                      0
% 2.03/0.99  sim_smt_subsumption:                    0
% 2.03/0.99  
%------------------------------------------------------------------------------
