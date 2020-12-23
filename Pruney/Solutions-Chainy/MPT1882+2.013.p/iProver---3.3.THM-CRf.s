%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:21 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  164 (2430 expanded)
%              Number of clauses        :  107 ( 563 expanded)
%              Number of leaves         :   14 ( 540 expanded)
%              Depth                    :   24
%              Number of atoms          :  704 (19169 expanded)
%              Number of equality atoms :  176 ( 639 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f22])).

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
    inference(nnf_transformation,[],[f23])).

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
     => ( ( ~ v1_zfmisc_1(sK2)
          | ~ v3_tex_2(sK2,X0) )
        & ( v1_zfmisc_1(sK2)
          | v3_tex_2(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK2) ) ) ),
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

fof(f37,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f36,f35])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f7])).

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
    inference(flattening,[],[f16])).

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
    inference(nnf_transformation,[],[f17])).

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
     => ( sK0(X0,X1) != X1
        & r1_tarski(X1,sK0(X0,X1))
        & v2_tex_2(sK0(X0,X1),X0)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f20])).

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
    inference(nnf_transformation,[],[f21])).

fof(f54,plain,(
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

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK0(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
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

fof(f62,plain,
    ( v1_zfmisc_1(sK2)
    | v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,
    ( ~ v1_zfmisc_1(sK2)
    | ~ v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK0(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK0(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

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

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1897,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_438,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_439,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | v3_tex_2(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_1893,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v2_tex_2(X0,sK1) != iProver_top
    | v3_tex_2(X0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_7,plain,
    ( v1_zfmisc_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_145,plain,
    ( v1_zfmisc_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_7])).

cnf(c_146,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_145])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_146,c_25])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,negated_conjecture,
    ( v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_352,plain,
    ( ~ v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_zfmisc_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_348,c_24,c_23,c_22])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_352])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_544,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | X2 != X0
    | X1 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_353,c_15])).

cnf(c_545,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ r1_tarski(X1,X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_544])).

cnf(c_1889,plain,
    ( X0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(X1,sK1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_545])).

cnf(c_2911,plain,
    ( sK0(sK1,X0) = X1
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(X0,sK1) != iProver_top
    | v2_tex_2(sK0(sK1,X0),sK1) != iProver_top
    | v3_tex_2(X0,sK1) = iProver_top
    | r1_tarski(X1,sK0(sK1,X0)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK0(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1893,c_1889])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | v2_tex_2(sK0(sK1,X0),sK1)
    | v3_tex_2(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_458,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(X0,sK1) != iProver_top
    | v2_tex_2(sK0(sK1,X0),sK1) = iProver_top
    | v3_tex_2(X0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_3564,plain,
    ( v2_tex_2(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sK0(sK1,X0) = X1
    | v3_tex_2(X0,sK1) = iProver_top
    | r1_tarski(X1,sK0(sK1,X0)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK0(sK1,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2911,c_458])).

cnf(c_3565,plain,
    ( sK0(sK1,X0) = X1
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(X0,sK1) != iProver_top
    | v3_tex_2(X0,sK1) = iProver_top
    | r1_tarski(X1,sK0(sK1,X0)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK0(sK1,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3564])).

cnf(c_3577,plain,
    ( sK0(sK1,sK2) = X0
    | v2_tex_2(sK2,sK1) != iProver_top
    | v3_tex_2(sK2,sK1) = iProver_top
    | r1_tarski(X0,sK0(sK1,sK2)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1897,c_3565])).

cnf(c_21,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f60])).

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
    inference(cnf_transformation,[],[f55])).

cnf(c_368,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_373,plain,
    ( v2_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_369,c_24,c_23,c_22])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_373])).

cnf(c_19,negated_conjecture,
    ( v3_tex_2(sK2,sK1)
    | v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_205,plain,
    ( v1_zfmisc_1(sK2)
    | v3_tex_2(sK2,sK1) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_206,plain,
    ( v3_tex_2(sK2,sK1)
    | v1_zfmisc_1(sK2) ),
    inference(renaming,[status(thm)],[c_205])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1)
    | v3_tex_2(sK2,sK1)
    | v1_xboole_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_374,c_206])).

cnf(c_585,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(sK2,sK1)
    | v3_tex_2(sK2,sK1)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_587,plain,
    ( v3_tex_2(sK2,sK1)
    | v2_tex_2(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_585,c_21,c_20])).

cnf(c_588,plain,
    ( v2_tex_2(sK2,sK1)
    | v3_tex_2(sK2,sK1) ),
    inference(renaming,[status(thm)],[c_587])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_401,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_402,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1)
    | ~ v3_tex_2(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_839,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(X0,sK1)
    | v2_tex_2(sK2,sK1)
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_588,c_402])).

cnf(c_840,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(sK2,sK1) ),
    inference(unflattening,[status(thm)],[c_839])).

cnf(c_841,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_840])).

cnf(c_18,negated_conjecture,
    ( ~ v3_tex_2(sK2,sK1)
    | ~ v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_203,plain,
    ( ~ v1_zfmisc_1(sK2)
    | ~ v3_tex_2(sK2,sK1) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_204,plain,
    ( ~ v3_tex_2(sK2,sK1)
    | ~ v1_zfmisc_1(sK2) ),
    inference(renaming,[status(thm)],[c_203])).

cnf(c_568,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ v3_tex_2(sK2,sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_353,c_204])).

cnf(c_569,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(sK2,sK1)
    | ~ v3_tex_2(sK2,sK1) ),
    inference(unflattening,[status(thm)],[c_568])).

cnf(c_571,plain,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ v3_tex_2(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_569,c_20])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_492,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | sK0(X1,X0) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_493,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | v3_tex_2(X0,sK1)
    | sK0(sK1,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_850,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ v2_tex_2(sK2,sK1)
    | sK0(sK1,X0) != X0
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_571,c_493])).

cnf(c_851,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(sK2,sK1)
    | sK0(sK1,sK2) != sK2 ),
    inference(unflattening,[status(thm)],[c_850])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | r1_tarski(X0,sK0(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_474,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | r1_tarski(X0,sK0(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_475,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | v3_tex_2(X0,sK1)
    | r1_tarski(X0,sK0(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_858,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ v2_tex_2(sK2,sK1)
    | r1_tarski(X0,sK0(sK1,X0))
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_571,c_475])).

cnf(c_859,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(sK2,sK1)
    | r1_tarski(sK2,sK0(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_858])).

cnf(c_860,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(sK2,sK1) != iProver_top
    | r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_859])).

cnf(c_869,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | v2_tex_2(sK0(sK1,X0),sK1)
    | ~ v2_tex_2(sK2,sK1)
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_571,c_457])).

cnf(c_870,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_tex_2(sK0(sK1,sK2),sK1)
    | ~ v2_tex_2(sK2,sK1) ),
    inference(unflattening,[status(thm)],[c_869])).

cnf(c_871,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(sK0(sK1,sK2),sK1) = iProver_top
    | v2_tex_2(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_870])).

cnf(c_880,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ v2_tex_2(sK2,sK1)
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_571,c_439])).

cnf(c_881,plain,
    ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(sK2,sK1) ),
    inference(unflattening,[status(thm)],[c_880])).

cnf(c_882,plain,
    ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_881])).

cnf(c_1436,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2385,plain,
    ( sK0(sK1,sK2) = sK0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1436])).

cnf(c_2225,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(X0,sK1)
    | ~ r1_tarski(sK2,X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_2401,plain,
    ( ~ m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tex_2(sK0(sK1,sK2),sK1)
    | ~ r1_tarski(sK2,sK0(sK1,sK2))
    | v1_xboole_0(sK0(sK1,sK2))
    | v1_xboole_0(sK2)
    | sK2 = sK0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2225])).

cnf(c_2402,plain,
    ( sK2 = sK0(sK1,sK2)
    | m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(sK0(sK1,sK2),sK1) != iProver_top
    | r1_tarski(sK2,sK0(sK1,sK2)) != iProver_top
    | v1_xboole_0(sK0(sK1,sK2)) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2401])).

cnf(c_1437,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2116,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_1437])).

cnf(c_2519,plain,
    ( X0 != sK0(sK1,sK2)
    | X0 = sK2
    | sK2 != sK0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2116])).

cnf(c_2818,plain,
    ( sK0(sK1,sK2) != sK0(sK1,sK2)
    | sK0(sK1,sK2) = sK2
    | sK2 != sK0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2519])).

cnf(c_3616,plain,
    ( v1_xboole_0(sK0(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3577,c_30,c_20,c_31,c_840,c_841,c_851,c_860,c_871,c_882,c_2385,c_2402,c_2818])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1903,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3621,plain,
    ( sK0(sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3616,c_1903])).

cnf(c_1891,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(X0,sK1) != iProver_top
    | v3_tex_2(X0,sK1) = iProver_top
    | r1_tarski(X0,sK0(sK1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_475])).

cnf(c_2212,plain,
    ( v2_tex_2(sK2,sK1) != iProver_top
    | v3_tex_2(sK2,sK1) = iProver_top
    | r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1897,c_1891])).

cnf(c_2215,plain,
    ( r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2212,c_31,c_841,c_860])).

cnf(c_3694,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3621,c_2215])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1901,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1900,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3217,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1901,c_1900])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1898,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3356,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3217,c_1898])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1902,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3364,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3356,c_1902])).

cnf(c_4022,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3694,c_3364])).

cnf(c_1890,plain,
    ( sK0(sK1,X0) != X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(X0,sK1) != iProver_top
    | v3_tex_2(X0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_493])).

cnf(c_3713,plain,
    ( sK2 != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(sK2,sK1) != iProver_top
    | v3_tex_2(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3621,c_1890])).

cnf(c_573,plain,
    ( v2_tex_2(sK2,sK1) != iProver_top
    | v3_tex_2(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4022,c_3713,c_841,c_573,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:23:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.05/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/0.98  
% 2.05/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.05/0.98  
% 2.05/0.98  ------  iProver source info
% 2.05/0.98  
% 2.05/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.05/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.05/0.98  git: non_committed_changes: false
% 2.05/0.98  git: last_make_outside_of_git: false
% 2.05/0.98  
% 2.05/0.98  ------ 
% 2.05/0.98  
% 2.05/0.98  ------ Input Options
% 2.05/0.98  
% 2.05/0.98  --out_options                           all
% 2.05/0.98  --tptp_safe_out                         true
% 2.05/0.98  --problem_path                          ""
% 2.05/0.98  --include_path                          ""
% 2.05/0.98  --clausifier                            res/vclausify_rel
% 2.05/0.98  --clausifier_options                    --mode clausify
% 2.05/0.98  --stdin                                 false
% 2.05/0.98  --stats_out                             all
% 2.05/0.98  
% 2.05/0.98  ------ General Options
% 2.05/0.98  
% 2.05/0.98  --fof                                   false
% 2.05/0.98  --time_out_real                         305.
% 2.05/0.98  --time_out_virtual                      -1.
% 2.05/0.98  --symbol_type_check                     false
% 2.05/0.98  --clausify_out                          false
% 2.05/0.98  --sig_cnt_out                           false
% 2.05/0.98  --trig_cnt_out                          false
% 2.05/0.98  --trig_cnt_out_tolerance                1.
% 2.05/0.98  --trig_cnt_out_sk_spl                   false
% 2.05/0.98  --abstr_cl_out                          false
% 2.05/0.98  
% 2.05/0.98  ------ Global Options
% 2.05/0.98  
% 2.05/0.98  --schedule                              default
% 2.05/0.98  --add_important_lit                     false
% 2.05/0.98  --prop_solver_per_cl                    1000
% 2.05/0.98  --min_unsat_core                        false
% 2.05/0.98  --soft_assumptions                      false
% 2.05/0.98  --soft_lemma_size                       3
% 2.05/0.98  --prop_impl_unit_size                   0
% 2.05/0.98  --prop_impl_unit                        []
% 2.05/0.98  --share_sel_clauses                     true
% 2.05/0.98  --reset_solvers                         false
% 2.05/0.98  --bc_imp_inh                            [conj_cone]
% 2.05/0.98  --conj_cone_tolerance                   3.
% 2.05/0.98  --extra_neg_conj                        none
% 2.05/0.98  --large_theory_mode                     true
% 2.05/0.98  --prolific_symb_bound                   200
% 2.05/0.98  --lt_threshold                          2000
% 2.05/0.98  --clause_weak_htbl                      true
% 2.05/0.98  --gc_record_bc_elim                     false
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing Options
% 2.05/0.98  
% 2.05/0.98  --preprocessing_flag                    true
% 2.05/0.98  --time_out_prep_mult                    0.1
% 2.05/0.98  --splitting_mode                        input
% 2.05/0.98  --splitting_grd                         true
% 2.05/0.98  --splitting_cvd                         false
% 2.05/0.98  --splitting_cvd_svl                     false
% 2.05/0.98  --splitting_nvd                         32
% 2.05/0.98  --sub_typing                            true
% 2.05/0.98  --prep_gs_sim                           true
% 2.05/0.98  --prep_unflatten                        true
% 2.05/0.98  --prep_res_sim                          true
% 2.05/0.98  --prep_upred                            true
% 2.05/0.98  --prep_sem_filter                       exhaustive
% 2.05/0.98  --prep_sem_filter_out                   false
% 2.05/0.98  --pred_elim                             true
% 2.05/0.98  --res_sim_input                         true
% 2.05/0.98  --eq_ax_congr_red                       true
% 2.05/0.98  --pure_diseq_elim                       true
% 2.05/0.98  --brand_transform                       false
% 2.05/0.98  --non_eq_to_eq                          false
% 2.05/0.98  --prep_def_merge                        true
% 2.05/0.98  --prep_def_merge_prop_impl              false
% 2.05/0.98  --prep_def_merge_mbd                    true
% 2.05/0.98  --prep_def_merge_tr_red                 false
% 2.05/0.98  --prep_def_merge_tr_cl                  false
% 2.05/0.98  --smt_preprocessing                     true
% 2.05/0.98  --smt_ac_axioms                         fast
% 2.05/0.98  --preprocessed_out                      false
% 2.05/0.98  --preprocessed_stats                    false
% 2.05/0.98  
% 2.05/0.98  ------ Abstraction refinement Options
% 2.05/0.98  
% 2.05/0.98  --abstr_ref                             []
% 2.05/0.98  --abstr_ref_prep                        false
% 2.05/0.98  --abstr_ref_until_sat                   false
% 2.05/0.98  --abstr_ref_sig_restrict                funpre
% 2.05/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/0.98  --abstr_ref_under                       []
% 2.05/0.98  
% 2.05/0.98  ------ SAT Options
% 2.05/0.98  
% 2.05/0.98  --sat_mode                              false
% 2.05/0.98  --sat_fm_restart_options                ""
% 2.05/0.98  --sat_gr_def                            false
% 2.05/0.98  --sat_epr_types                         true
% 2.05/0.98  --sat_non_cyclic_types                  false
% 2.05/0.98  --sat_finite_models                     false
% 2.05/0.98  --sat_fm_lemmas                         false
% 2.05/0.98  --sat_fm_prep                           false
% 2.05/0.98  --sat_fm_uc_incr                        true
% 2.05/0.98  --sat_out_model                         small
% 2.05/0.98  --sat_out_clauses                       false
% 2.05/0.98  
% 2.05/0.98  ------ QBF Options
% 2.05/0.98  
% 2.05/0.98  --qbf_mode                              false
% 2.05/0.98  --qbf_elim_univ                         false
% 2.05/0.98  --qbf_dom_inst                          none
% 2.05/0.98  --qbf_dom_pre_inst                      false
% 2.05/0.98  --qbf_sk_in                             false
% 2.05/0.98  --qbf_pred_elim                         true
% 2.05/0.98  --qbf_split                             512
% 2.05/0.98  
% 2.05/0.98  ------ BMC1 Options
% 2.05/0.98  
% 2.05/0.98  --bmc1_incremental                      false
% 2.05/0.98  --bmc1_axioms                           reachable_all
% 2.05/0.98  --bmc1_min_bound                        0
% 2.05/0.98  --bmc1_max_bound                        -1
% 2.05/0.98  --bmc1_max_bound_default                -1
% 2.05/0.98  --bmc1_symbol_reachability              true
% 2.05/0.98  --bmc1_property_lemmas                  false
% 2.05/0.98  --bmc1_k_induction                      false
% 2.05/0.98  --bmc1_non_equiv_states                 false
% 2.05/0.98  --bmc1_deadlock                         false
% 2.05/0.98  --bmc1_ucm                              false
% 2.05/0.98  --bmc1_add_unsat_core                   none
% 2.05/0.98  --bmc1_unsat_core_children              false
% 2.05/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/0.98  --bmc1_out_stat                         full
% 2.05/0.98  --bmc1_ground_init                      false
% 2.05/0.98  --bmc1_pre_inst_next_state              false
% 2.05/0.98  --bmc1_pre_inst_state                   false
% 2.05/0.98  --bmc1_pre_inst_reach_state             false
% 2.05/0.98  --bmc1_out_unsat_core                   false
% 2.05/0.98  --bmc1_aig_witness_out                  false
% 2.05/0.98  --bmc1_verbose                          false
% 2.05/0.98  --bmc1_dump_clauses_tptp                false
% 2.05/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.05/0.98  --bmc1_dump_file                        -
% 2.05/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.05/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.05/0.98  --bmc1_ucm_extend_mode                  1
% 2.05/0.98  --bmc1_ucm_init_mode                    2
% 2.05/0.98  --bmc1_ucm_cone_mode                    none
% 2.05/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.05/0.98  --bmc1_ucm_relax_model                  4
% 2.05/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.05/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/0.98  --bmc1_ucm_layered_model                none
% 2.05/0.98  --bmc1_ucm_max_lemma_size               10
% 2.05/0.98  
% 2.05/0.98  ------ AIG Options
% 2.05/0.98  
% 2.05/0.98  --aig_mode                              false
% 2.05/0.98  
% 2.05/0.98  ------ Instantiation Options
% 2.05/0.98  
% 2.05/0.98  --instantiation_flag                    true
% 2.05/0.98  --inst_sos_flag                         false
% 2.05/0.98  --inst_sos_phase                        true
% 2.05/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/0.98  --inst_lit_sel_side                     num_symb
% 2.05/0.98  --inst_solver_per_active                1400
% 2.05/0.98  --inst_solver_calls_frac                1.
% 2.05/0.98  --inst_passive_queue_type               priority_queues
% 2.05/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/0.98  --inst_passive_queues_freq              [25;2]
% 2.05/0.98  --inst_dismatching                      true
% 2.05/0.98  --inst_eager_unprocessed_to_passive     true
% 2.05/0.98  --inst_prop_sim_given                   true
% 2.05/0.98  --inst_prop_sim_new                     false
% 2.05/0.98  --inst_subs_new                         false
% 2.05/0.98  --inst_eq_res_simp                      false
% 2.05/0.98  --inst_subs_given                       false
% 2.05/0.98  --inst_orphan_elimination               true
% 2.05/0.98  --inst_learning_loop_flag               true
% 2.05/0.98  --inst_learning_start                   3000
% 2.05/0.98  --inst_learning_factor                  2
% 2.05/0.98  --inst_start_prop_sim_after_learn       3
% 2.05/0.98  --inst_sel_renew                        solver
% 2.05/0.98  --inst_lit_activity_flag                true
% 2.05/0.98  --inst_restr_to_given                   false
% 2.05/0.98  --inst_activity_threshold               500
% 2.05/0.98  --inst_out_proof                        true
% 2.05/0.98  
% 2.05/0.98  ------ Resolution Options
% 2.05/0.98  
% 2.05/0.98  --resolution_flag                       true
% 2.05/0.98  --res_lit_sel                           adaptive
% 2.05/0.98  --res_lit_sel_side                      none
% 2.05/0.98  --res_ordering                          kbo
% 2.05/0.98  --res_to_prop_solver                    active
% 2.05/0.98  --res_prop_simpl_new                    false
% 2.05/0.98  --res_prop_simpl_given                  true
% 2.05/0.98  --res_passive_queue_type                priority_queues
% 2.05/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/0.98  --res_passive_queues_freq               [15;5]
% 2.05/0.98  --res_forward_subs                      full
% 2.05/0.98  --res_backward_subs                     full
% 2.05/0.98  --res_forward_subs_resolution           true
% 2.05/0.98  --res_backward_subs_resolution          true
% 2.05/0.98  --res_orphan_elimination                true
% 2.05/0.98  --res_time_limit                        2.
% 2.05/0.98  --res_out_proof                         true
% 2.05/0.98  
% 2.05/0.98  ------ Superposition Options
% 2.05/0.98  
% 2.05/0.98  --superposition_flag                    true
% 2.05/0.98  --sup_passive_queue_type                priority_queues
% 2.05/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.05/0.98  --demod_completeness_check              fast
% 2.05/0.98  --demod_use_ground                      true
% 2.05/0.98  --sup_to_prop_solver                    passive
% 2.05/0.98  --sup_prop_simpl_new                    true
% 2.05/0.98  --sup_prop_simpl_given                  true
% 2.05/0.98  --sup_fun_splitting                     false
% 2.05/0.98  --sup_smt_interval                      50000
% 2.05/0.98  
% 2.05/0.98  ------ Superposition Simplification Setup
% 2.05/0.98  
% 2.05/0.98  --sup_indices_passive                   []
% 2.05/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_full_bw                           [BwDemod]
% 2.05/0.98  --sup_immed_triv                        [TrivRules]
% 2.05/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_immed_bw_main                     []
% 2.05/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.98  
% 2.05/0.98  ------ Combination Options
% 2.05/0.98  
% 2.05/0.98  --comb_res_mult                         3
% 2.05/0.98  --comb_sup_mult                         2
% 2.05/0.98  --comb_inst_mult                        10
% 2.05/0.98  
% 2.05/0.98  ------ Debug Options
% 2.05/0.98  
% 2.05/0.98  --dbg_backtrace                         false
% 2.05/0.98  --dbg_dump_prop_clauses                 false
% 2.05/0.98  --dbg_dump_prop_clauses_file            -
% 2.05/0.98  --dbg_out_stat                          false
% 2.05/0.98  ------ Parsing...
% 2.05/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.05/0.98  ------ Proving...
% 2.05/0.98  ------ Problem Properties 
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  clauses                                 18
% 2.05/0.98  conjectures                             2
% 2.05/0.98  EPR                                     7
% 2.05/0.98  Horn                                    13
% 2.05/0.98  unary                                   6
% 2.05/0.98  binary                                  3
% 2.05/0.98  lits                                    49
% 2.05/0.98  lits eq                                 8
% 2.05/0.98  fd_pure                                 0
% 2.05/0.98  fd_pseudo                               0
% 2.05/0.98  fd_cond                                 2
% 2.05/0.98  fd_pseudo_cond                          3
% 2.05/0.98  AC symbols                              0
% 2.05/0.98  
% 2.05/0.98  ------ Schedule dynamic 5 is on 
% 2.05/0.98  
% 2.05/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  ------ 
% 2.05/0.98  Current options:
% 2.05/0.98  ------ 
% 2.05/0.98  
% 2.05/0.98  ------ Input Options
% 2.05/0.98  
% 2.05/0.98  --out_options                           all
% 2.05/0.98  --tptp_safe_out                         true
% 2.05/0.98  --problem_path                          ""
% 2.05/0.98  --include_path                          ""
% 2.05/0.98  --clausifier                            res/vclausify_rel
% 2.05/0.98  --clausifier_options                    --mode clausify
% 2.05/0.98  --stdin                                 false
% 2.05/0.98  --stats_out                             all
% 2.05/0.98  
% 2.05/0.98  ------ General Options
% 2.05/0.98  
% 2.05/0.98  --fof                                   false
% 2.05/0.98  --time_out_real                         305.
% 2.05/0.98  --time_out_virtual                      -1.
% 2.05/0.98  --symbol_type_check                     false
% 2.05/0.98  --clausify_out                          false
% 2.05/0.98  --sig_cnt_out                           false
% 2.05/0.98  --trig_cnt_out                          false
% 2.05/0.98  --trig_cnt_out_tolerance                1.
% 2.05/0.98  --trig_cnt_out_sk_spl                   false
% 2.05/0.98  --abstr_cl_out                          false
% 2.05/0.98  
% 2.05/0.98  ------ Global Options
% 2.05/0.98  
% 2.05/0.98  --schedule                              default
% 2.05/0.98  --add_important_lit                     false
% 2.05/0.98  --prop_solver_per_cl                    1000
% 2.05/0.98  --min_unsat_core                        false
% 2.05/0.98  --soft_assumptions                      false
% 2.05/0.98  --soft_lemma_size                       3
% 2.05/0.98  --prop_impl_unit_size                   0
% 2.05/0.98  --prop_impl_unit                        []
% 2.05/0.98  --share_sel_clauses                     true
% 2.05/0.98  --reset_solvers                         false
% 2.05/0.98  --bc_imp_inh                            [conj_cone]
% 2.05/0.98  --conj_cone_tolerance                   3.
% 2.05/0.98  --extra_neg_conj                        none
% 2.05/0.98  --large_theory_mode                     true
% 2.05/0.98  --prolific_symb_bound                   200
% 2.05/0.98  --lt_threshold                          2000
% 2.05/0.98  --clause_weak_htbl                      true
% 2.05/0.98  --gc_record_bc_elim                     false
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing Options
% 2.05/0.98  
% 2.05/0.98  --preprocessing_flag                    true
% 2.05/0.98  --time_out_prep_mult                    0.1
% 2.05/0.98  --splitting_mode                        input
% 2.05/0.98  --splitting_grd                         true
% 2.05/0.98  --splitting_cvd                         false
% 2.05/0.98  --splitting_cvd_svl                     false
% 2.05/0.98  --splitting_nvd                         32
% 2.05/0.98  --sub_typing                            true
% 2.05/0.98  --prep_gs_sim                           true
% 2.05/0.98  --prep_unflatten                        true
% 2.05/0.98  --prep_res_sim                          true
% 2.05/0.98  --prep_upred                            true
% 2.05/0.98  --prep_sem_filter                       exhaustive
% 2.05/0.98  --prep_sem_filter_out                   false
% 2.05/0.98  --pred_elim                             true
% 2.05/0.98  --res_sim_input                         true
% 2.05/0.98  --eq_ax_congr_red                       true
% 2.05/0.98  --pure_diseq_elim                       true
% 2.05/0.98  --brand_transform                       false
% 2.05/0.98  --non_eq_to_eq                          false
% 2.05/0.98  --prep_def_merge                        true
% 2.05/0.98  --prep_def_merge_prop_impl              false
% 2.05/0.98  --prep_def_merge_mbd                    true
% 2.05/0.98  --prep_def_merge_tr_red                 false
% 2.05/0.98  --prep_def_merge_tr_cl                  false
% 2.05/0.98  --smt_preprocessing                     true
% 2.05/0.98  --smt_ac_axioms                         fast
% 2.05/0.98  --preprocessed_out                      false
% 2.05/0.98  --preprocessed_stats                    false
% 2.05/0.98  
% 2.05/0.98  ------ Abstraction refinement Options
% 2.05/0.98  
% 2.05/0.98  --abstr_ref                             []
% 2.05/0.98  --abstr_ref_prep                        false
% 2.05/0.98  --abstr_ref_until_sat                   false
% 2.05/0.98  --abstr_ref_sig_restrict                funpre
% 2.05/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/0.98  --abstr_ref_under                       []
% 2.05/0.98  
% 2.05/0.98  ------ SAT Options
% 2.05/0.98  
% 2.05/0.98  --sat_mode                              false
% 2.05/0.98  --sat_fm_restart_options                ""
% 2.05/0.98  --sat_gr_def                            false
% 2.05/0.98  --sat_epr_types                         true
% 2.05/0.98  --sat_non_cyclic_types                  false
% 2.05/0.98  --sat_finite_models                     false
% 2.05/0.98  --sat_fm_lemmas                         false
% 2.05/0.98  --sat_fm_prep                           false
% 2.05/0.98  --sat_fm_uc_incr                        true
% 2.05/0.98  --sat_out_model                         small
% 2.05/0.98  --sat_out_clauses                       false
% 2.05/0.98  
% 2.05/0.98  ------ QBF Options
% 2.05/0.98  
% 2.05/0.98  --qbf_mode                              false
% 2.05/0.98  --qbf_elim_univ                         false
% 2.05/0.98  --qbf_dom_inst                          none
% 2.05/0.98  --qbf_dom_pre_inst                      false
% 2.05/0.98  --qbf_sk_in                             false
% 2.05/0.98  --qbf_pred_elim                         true
% 2.05/0.98  --qbf_split                             512
% 2.05/0.98  
% 2.05/0.98  ------ BMC1 Options
% 2.05/0.98  
% 2.05/0.98  --bmc1_incremental                      false
% 2.05/0.98  --bmc1_axioms                           reachable_all
% 2.05/0.98  --bmc1_min_bound                        0
% 2.05/0.98  --bmc1_max_bound                        -1
% 2.05/0.98  --bmc1_max_bound_default                -1
% 2.05/0.98  --bmc1_symbol_reachability              true
% 2.05/0.98  --bmc1_property_lemmas                  false
% 2.05/0.98  --bmc1_k_induction                      false
% 2.05/0.98  --bmc1_non_equiv_states                 false
% 2.05/0.98  --bmc1_deadlock                         false
% 2.05/0.98  --bmc1_ucm                              false
% 2.05/0.98  --bmc1_add_unsat_core                   none
% 2.05/0.98  --bmc1_unsat_core_children              false
% 2.05/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/0.98  --bmc1_out_stat                         full
% 2.05/0.98  --bmc1_ground_init                      false
% 2.05/0.98  --bmc1_pre_inst_next_state              false
% 2.05/0.98  --bmc1_pre_inst_state                   false
% 2.05/0.98  --bmc1_pre_inst_reach_state             false
% 2.05/0.98  --bmc1_out_unsat_core                   false
% 2.05/0.98  --bmc1_aig_witness_out                  false
% 2.05/0.98  --bmc1_verbose                          false
% 2.05/0.98  --bmc1_dump_clauses_tptp                false
% 2.05/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.05/0.98  --bmc1_dump_file                        -
% 2.05/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.05/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.05/0.98  --bmc1_ucm_extend_mode                  1
% 2.05/0.98  --bmc1_ucm_init_mode                    2
% 2.05/0.98  --bmc1_ucm_cone_mode                    none
% 2.05/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.05/0.98  --bmc1_ucm_relax_model                  4
% 2.05/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.05/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/0.98  --bmc1_ucm_layered_model                none
% 2.05/0.98  --bmc1_ucm_max_lemma_size               10
% 2.05/0.98  
% 2.05/0.98  ------ AIG Options
% 2.05/0.98  
% 2.05/0.98  --aig_mode                              false
% 2.05/0.98  
% 2.05/0.98  ------ Instantiation Options
% 2.05/0.98  
% 2.05/0.98  --instantiation_flag                    true
% 2.05/0.98  --inst_sos_flag                         false
% 2.05/0.98  --inst_sos_phase                        true
% 2.05/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/0.98  --inst_lit_sel_side                     none
% 2.05/0.98  --inst_solver_per_active                1400
% 2.05/0.98  --inst_solver_calls_frac                1.
% 2.05/0.98  --inst_passive_queue_type               priority_queues
% 2.05/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/0.98  --inst_passive_queues_freq              [25;2]
% 2.05/0.98  --inst_dismatching                      true
% 2.05/0.98  --inst_eager_unprocessed_to_passive     true
% 2.05/0.98  --inst_prop_sim_given                   true
% 2.05/0.98  --inst_prop_sim_new                     false
% 2.05/0.98  --inst_subs_new                         false
% 2.05/0.98  --inst_eq_res_simp                      false
% 2.05/0.98  --inst_subs_given                       false
% 2.05/0.98  --inst_orphan_elimination               true
% 2.05/0.98  --inst_learning_loop_flag               true
% 2.05/0.98  --inst_learning_start                   3000
% 2.05/0.98  --inst_learning_factor                  2
% 2.05/0.98  --inst_start_prop_sim_after_learn       3
% 2.05/0.98  --inst_sel_renew                        solver
% 2.05/0.98  --inst_lit_activity_flag                true
% 2.05/0.98  --inst_restr_to_given                   false
% 2.05/0.98  --inst_activity_threshold               500
% 2.05/0.98  --inst_out_proof                        true
% 2.05/0.98  
% 2.05/0.98  ------ Resolution Options
% 2.05/0.98  
% 2.05/0.98  --resolution_flag                       false
% 2.05/0.98  --res_lit_sel                           adaptive
% 2.05/0.98  --res_lit_sel_side                      none
% 2.05/0.98  --res_ordering                          kbo
% 2.05/0.98  --res_to_prop_solver                    active
% 2.05/0.98  --res_prop_simpl_new                    false
% 2.05/0.98  --res_prop_simpl_given                  true
% 2.05/0.98  --res_passive_queue_type                priority_queues
% 2.05/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/0.98  --res_passive_queues_freq               [15;5]
% 2.05/0.98  --res_forward_subs                      full
% 2.05/0.98  --res_backward_subs                     full
% 2.05/0.98  --res_forward_subs_resolution           true
% 2.05/0.98  --res_backward_subs_resolution          true
% 2.05/0.98  --res_orphan_elimination                true
% 2.05/0.98  --res_time_limit                        2.
% 2.05/0.98  --res_out_proof                         true
% 2.05/0.98  
% 2.05/0.98  ------ Superposition Options
% 2.05/0.98  
% 2.05/0.98  --superposition_flag                    true
% 2.05/0.98  --sup_passive_queue_type                priority_queues
% 2.05/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.05/0.98  --demod_completeness_check              fast
% 2.05/0.98  --demod_use_ground                      true
% 2.05/0.98  --sup_to_prop_solver                    passive
% 2.05/0.98  --sup_prop_simpl_new                    true
% 2.05/0.98  --sup_prop_simpl_given                  true
% 2.05/0.98  --sup_fun_splitting                     false
% 2.05/0.98  --sup_smt_interval                      50000
% 2.05/0.98  
% 2.05/0.98  ------ Superposition Simplification Setup
% 2.05/0.98  
% 2.05/0.98  --sup_indices_passive                   []
% 2.05/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_full_bw                           [BwDemod]
% 2.05/0.98  --sup_immed_triv                        [TrivRules]
% 2.05/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_immed_bw_main                     []
% 2.05/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.98  
% 2.05/0.98  ------ Combination Options
% 2.05/0.98  
% 2.05/0.98  --comb_res_mult                         3
% 2.05/0.98  --comb_sup_mult                         2
% 2.05/0.98  --comb_inst_mult                        10
% 2.05/0.98  
% 2.05/0.98  ------ Debug Options
% 2.05/0.98  
% 2.05/0.98  --dbg_backtrace                         false
% 2.05/0.98  --dbg_dump_prop_clauses                 false
% 2.05/0.98  --dbg_dump_prop_clauses_file            -
% 2.05/0.98  --dbg_out_stat                          false
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  ------ Proving...
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  % SZS status Theorem for theBenchmark.p
% 2.05/0.98  
% 2.05/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.05/0.98  
% 2.05/0.98  fof(f10,conjecture,(
% 2.05/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f11,negated_conjecture,(
% 2.05/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.05/0.98    inference(negated_conjecture,[],[f10])).
% 2.05/0.98  
% 2.05/0.98  fof(f22,plain,(
% 2.05/0.98    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f11])).
% 2.05/0.98  
% 2.05/0.98  fof(f23,plain,(
% 2.05/0.98    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.05/0.98    inference(flattening,[],[f22])).
% 2.05/0.98  
% 2.05/0.98  fof(f33,plain,(
% 2.05/0.98    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.05/0.98    inference(nnf_transformation,[],[f23])).
% 2.05/0.98  
% 2.05/0.98  fof(f34,plain,(
% 2.05/0.98    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.05/0.98    inference(flattening,[],[f33])).
% 2.05/0.98  
% 2.05/0.98  fof(f36,plain,(
% 2.05/0.98    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK2) | ~v3_tex_2(sK2,X0)) & (v1_zfmisc_1(sK2) | v3_tex_2(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK2))) )),
% 2.05/0.98    introduced(choice_axiom,[])).
% 2.05/0.98  
% 2.05/0.98  fof(f35,plain,(
% 2.05/0.98    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK1)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK1) & v2_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.05/0.98    introduced(choice_axiom,[])).
% 2.05/0.98  
% 2.05/0.98  fof(f37,plain,(
% 2.05/0.98    ((~v1_zfmisc_1(sK2) | ~v3_tex_2(sK2,sK1)) & (v1_zfmisc_1(sK2) | v3_tex_2(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(sK2)) & l1_pre_topc(sK1) & v2_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.05/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f34,f36,f35])).
% 2.05/0.98  
% 2.05/0.98  fof(f61,plain,(
% 2.05/0.98    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.05/0.98    inference(cnf_transformation,[],[f37])).
% 2.05/0.98  
% 2.05/0.98  fof(f7,axiom,(
% 2.05/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 2.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f16,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.98    inference(ennf_transformation,[],[f7])).
% 2.05/0.98  
% 2.05/0.98  fof(f17,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.98    inference(flattening,[],[f16])).
% 2.05/0.98  
% 2.05/0.98  fof(f27,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.98    inference(nnf_transformation,[],[f17])).
% 2.05/0.98  
% 2.05/0.98  fof(f28,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.98    inference(flattening,[],[f27])).
% 2.05/0.98  
% 2.05/0.98  fof(f29,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.98    inference(rectify,[],[f28])).
% 2.05/0.98  
% 2.05/0.98  fof(f30,plain,(
% 2.05/0.98    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.05/0.98    introduced(choice_axiom,[])).
% 2.05/0.98  
% 2.05/0.98  fof(f31,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 2.05/0.98  
% 2.05/0.98  fof(f49,plain,(
% 2.05/0.98    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f31])).
% 2.05/0.98  
% 2.05/0.98  fof(f59,plain,(
% 2.05/0.98    l1_pre_topc(sK1)),
% 2.05/0.98    inference(cnf_transformation,[],[f37])).
% 2.05/0.98  
% 2.05/0.98  fof(f9,axiom,(
% 2.05/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f20,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f9])).
% 2.05/0.98  
% 2.05/0.98  fof(f21,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.98    inference(flattening,[],[f20])).
% 2.05/0.98  
% 2.05/0.98  fof(f32,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.98    inference(nnf_transformation,[],[f21])).
% 2.05/0.98  
% 2.05/0.98  fof(f54,plain,(
% 2.05/0.98    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f32])).
% 2.05/0.98  
% 2.05/0.98  fof(f5,axiom,(
% 2.05/0.98    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 2.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f13,plain,(
% 2.05/0.98    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 2.05/0.98    inference(ennf_transformation,[],[f5])).
% 2.05/0.98  
% 2.05/0.98  fof(f45,plain,(
% 2.05/0.98    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f13])).
% 2.05/0.98  
% 2.05/0.98  fof(f56,plain,(
% 2.05/0.98    ~v2_struct_0(sK1)),
% 2.05/0.98    inference(cnf_transformation,[],[f37])).
% 2.05/0.98  
% 2.05/0.98  fof(f57,plain,(
% 2.05/0.98    v2_pre_topc(sK1)),
% 2.05/0.98    inference(cnf_transformation,[],[f37])).
% 2.05/0.98  
% 2.05/0.98  fof(f58,plain,(
% 2.05/0.98    v2_tdlat_3(sK1)),
% 2.05/0.98    inference(cnf_transformation,[],[f37])).
% 2.05/0.98  
% 2.05/0.98  fof(f8,axiom,(
% 2.05/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f18,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.05/0.98    inference(ennf_transformation,[],[f8])).
% 2.05/0.98  
% 2.05/0.98  fof(f19,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.05/0.98    inference(flattening,[],[f18])).
% 2.05/0.98  
% 2.05/0.98  fof(f53,plain,(
% 2.05/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f19])).
% 2.05/0.98  
% 2.05/0.98  fof(f50,plain,(
% 2.05/0.98    ( ! [X0,X1] : (v3_tex_2(X1,X0) | v2_tex_2(sK0(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f31])).
% 2.05/0.98  
% 2.05/0.98  fof(f60,plain,(
% 2.05/0.98    ~v1_xboole_0(sK2)),
% 2.05/0.98    inference(cnf_transformation,[],[f37])).
% 2.05/0.98  
% 2.05/0.98  fof(f55,plain,(
% 2.05/0.98    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f32])).
% 2.05/0.98  
% 2.05/0.98  fof(f62,plain,(
% 2.05/0.98    v1_zfmisc_1(sK2) | v3_tex_2(sK2,sK1)),
% 2.05/0.98    inference(cnf_transformation,[],[f37])).
% 2.05/0.98  
% 2.05/0.98  fof(f47,plain,(
% 2.05/0.98    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f31])).
% 2.05/0.98  
% 2.05/0.98  fof(f63,plain,(
% 2.05/0.98    ~v1_zfmisc_1(sK2) | ~v3_tex_2(sK2,sK1)),
% 2.05/0.98    inference(cnf_transformation,[],[f37])).
% 2.05/0.98  
% 2.05/0.98  fof(f52,plain,(
% 2.05/0.98    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK0(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f31])).
% 2.05/0.98  
% 2.05/0.98  fof(f51,plain,(
% 2.05/0.98    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK0(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f31])).
% 2.05/0.98  
% 2.05/0.98  fof(f1,axiom,(
% 2.05/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f12,plain,(
% 2.05/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.05/0.98    inference(ennf_transformation,[],[f1])).
% 2.05/0.98  
% 2.05/0.98  fof(f38,plain,(
% 2.05/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f12])).
% 2.05/0.98  
% 2.05/0.98  fof(f2,axiom,(
% 2.05/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f24,plain,(
% 2.05/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.05/0.98    inference(nnf_transformation,[],[f2])).
% 2.05/0.98  
% 2.05/0.98  fof(f25,plain,(
% 2.05/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.05/0.98    inference(flattening,[],[f24])).
% 2.05/0.98  
% 2.05/0.98  fof(f39,plain,(
% 2.05/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.05/0.98    inference(cnf_transformation,[],[f25])).
% 2.05/0.98  
% 2.05/0.98  fof(f65,plain,(
% 2.05/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.05/0.98    inference(equality_resolution,[],[f39])).
% 2.05/0.98  
% 2.05/0.98  fof(f3,axiom,(
% 2.05/0.98    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f26,plain,(
% 2.05/0.98    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.05/0.98    inference(nnf_transformation,[],[f3])).
% 2.05/0.98  
% 2.05/0.98  fof(f43,plain,(
% 2.05/0.98    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f26])).
% 2.05/0.98  
% 2.05/0.98  fof(f4,axiom,(
% 2.05/0.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f44,plain,(
% 2.05/0.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f4])).
% 2.05/0.98  
% 2.05/0.98  fof(f41,plain,(
% 2.05/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f25])).
% 2.05/0.98  
% 2.05/0.98  cnf(c_20,negated_conjecture,
% 2.05/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.05/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1897,plain,
% 2.05/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_12,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | ~ v2_tex_2(X0,X1)
% 2.05/0.98      | v3_tex_2(X0,X1)
% 2.05/0.98      | ~ l1_pre_topc(X1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_22,negated_conjecture,
% 2.05/0.98      ( l1_pre_topc(sK1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_438,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | ~ v2_tex_2(X0,X1)
% 2.05/0.98      | v3_tex_2(X0,X1)
% 2.05/0.98      | sK1 != X1 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_439,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | ~ v2_tex_2(X0,sK1)
% 2.05/0.98      | v3_tex_2(X0,sK1) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_438]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1893,plain,
% 2.05/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.98      | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.05/0.98      | v2_tex_2(X0,sK1) != iProver_top
% 2.05/0.98      | v3_tex_2(X0,sK1) = iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_439]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_17,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | ~ v2_tex_2(X0,X1)
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_tdlat_3(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | v1_zfmisc_1(X0)
% 2.05/0.98      | v1_xboole_0(X0) ),
% 2.05/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_7,plain,
% 2.05/0.98      ( v1_zfmisc_1(X0) | ~ v1_xboole_0(X0) ),
% 2.05/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_145,plain,
% 2.05/0.98      ( v1_zfmisc_1(X0)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | ~ v2_tdlat_3(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ v2_tex_2(X0,X1)
% 2.05/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_17,c_7]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_146,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | ~ v2_tex_2(X0,X1)
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_tdlat_3(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | v1_zfmisc_1(X0) ),
% 2.05/0.98      inference(renaming,[status(thm)],[c_145]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_25,negated_conjecture,
% 2.05/0.98      ( ~ v2_struct_0(sK1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_347,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | ~ v2_tex_2(X0,X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_tdlat_3(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | v1_zfmisc_1(X0)
% 2.05/0.98      | sK1 != X1 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_146,c_25]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_348,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | ~ v2_tex_2(X0,sK1)
% 2.05/0.98      | ~ l1_pre_topc(sK1)
% 2.05/0.98      | ~ v2_tdlat_3(sK1)
% 2.05/0.98      | ~ v2_pre_topc(sK1)
% 2.05/0.98      | v1_zfmisc_1(X0) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_347]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_24,negated_conjecture,
% 2.05/0.98      ( v2_pre_topc(sK1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_23,negated_conjecture,
% 2.05/0.98      ( v2_tdlat_3(sK1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_352,plain,
% 2.05/0.98      ( ~ v2_tex_2(X0,sK1)
% 2.05/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | v1_zfmisc_1(X0) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_348,c_24,c_23,c_22]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_353,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | ~ v2_tex_2(X0,sK1)
% 2.05/0.98      | v1_zfmisc_1(X0) ),
% 2.05/0.98      inference(renaming,[status(thm)],[c_352]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_15,plain,
% 2.05/0.98      ( ~ r1_tarski(X0,X1)
% 2.05/0.98      | ~ v1_zfmisc_1(X1)
% 2.05/0.98      | v1_xboole_0(X0)
% 2.05/0.98      | v1_xboole_0(X1)
% 2.05/0.98      | X1 = X0 ),
% 2.05/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_544,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | ~ v2_tex_2(X0,sK1)
% 2.05/0.98      | ~ r1_tarski(X1,X2)
% 2.05/0.98      | v1_xboole_0(X2)
% 2.05/0.98      | v1_xboole_0(X1)
% 2.05/0.98      | X2 != X0
% 2.05/0.98      | X1 = X2 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_353,c_15]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_545,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | ~ v2_tex_2(X0,sK1)
% 2.05/0.98      | ~ r1_tarski(X1,X0)
% 2.05/0.98      | v1_xboole_0(X0)
% 2.05/0.98      | v1_xboole_0(X1)
% 2.05/0.98      | X1 = X0 ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_544]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1889,plain,
% 2.05/0.98      ( X0 = X1
% 2.05/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.98      | v2_tex_2(X1,sK1) != iProver_top
% 2.05/0.98      | r1_tarski(X0,X1) != iProver_top
% 2.05/0.98      | v1_xboole_0(X1) = iProver_top
% 2.05/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_545]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2911,plain,
% 2.05/0.98      ( sK0(sK1,X0) = X1
% 2.05/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.98      | v2_tex_2(X0,sK1) != iProver_top
% 2.05/0.98      | v2_tex_2(sK0(sK1,X0),sK1) != iProver_top
% 2.05/0.98      | v3_tex_2(X0,sK1) = iProver_top
% 2.05/0.98      | r1_tarski(X1,sK0(sK1,X0)) != iProver_top
% 2.05/0.98      | v1_xboole_0(X1) = iProver_top
% 2.05/0.98      | v1_xboole_0(sK0(sK1,X0)) = iProver_top ),
% 2.05/0.98      inference(superposition,[status(thm)],[c_1893,c_1889]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_11,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | ~ v2_tex_2(X0,X1)
% 2.05/0.98      | v2_tex_2(sK0(X1,X0),X1)
% 2.05/0.98      | v3_tex_2(X0,X1)
% 2.05/0.98      | ~ l1_pre_topc(X1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_456,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | ~ v2_tex_2(X0,X1)
% 2.05/0.98      | v2_tex_2(sK0(X1,X0),X1)
% 2.05/0.98      | v3_tex_2(X0,X1)
% 2.05/0.98      | sK1 != X1 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_457,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | ~ v2_tex_2(X0,sK1)
% 2.05/0.98      | v2_tex_2(sK0(sK1,X0),sK1)
% 2.05/0.98      | v3_tex_2(X0,sK1) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_456]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_458,plain,
% 2.05/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.98      | v2_tex_2(X0,sK1) != iProver_top
% 2.05/0.98      | v2_tex_2(sK0(sK1,X0),sK1) = iProver_top
% 2.05/0.98      | v3_tex_2(X0,sK1) = iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_3564,plain,
% 2.05/0.98      ( v2_tex_2(X0,sK1) != iProver_top
% 2.05/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.98      | sK0(sK1,X0) = X1
% 2.05/0.98      | v3_tex_2(X0,sK1) = iProver_top
% 2.05/0.98      | r1_tarski(X1,sK0(sK1,X0)) != iProver_top
% 2.05/0.98      | v1_xboole_0(X1) = iProver_top
% 2.05/0.98      | v1_xboole_0(sK0(sK1,X0)) = iProver_top ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_2911,c_458]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_3565,plain,
% 2.05/0.98      ( sK0(sK1,X0) = X1
% 2.05/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.98      | v2_tex_2(X0,sK1) != iProver_top
% 2.05/0.98      | v3_tex_2(X0,sK1) = iProver_top
% 2.05/0.98      | r1_tarski(X1,sK0(sK1,X0)) != iProver_top
% 2.05/0.98      | v1_xboole_0(X1) = iProver_top
% 2.05/0.98      | v1_xboole_0(sK0(sK1,X0)) = iProver_top ),
% 2.05/0.98      inference(renaming,[status(thm)],[c_3564]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_3577,plain,
% 2.05/0.98      ( sK0(sK1,sK2) = X0
% 2.05/0.98      | v2_tex_2(sK2,sK1) != iProver_top
% 2.05/0.98      | v3_tex_2(sK2,sK1) = iProver_top
% 2.05/0.98      | r1_tarski(X0,sK0(sK1,sK2)) != iProver_top
% 2.05/0.98      | v1_xboole_0(X0) = iProver_top
% 2.05/0.98      | v1_xboole_0(sK0(sK1,sK2)) = iProver_top ),
% 2.05/0.98      inference(superposition,[status(thm)],[c_1897,c_3565]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_21,negated_conjecture,
% 2.05/0.98      ( ~ v1_xboole_0(sK2) ),
% 2.05/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_30,plain,
% 2.05/0.98      ( v1_xboole_0(sK2) != iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_31,plain,
% 2.05/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_16,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | v2_tex_2(X0,X1)
% 2.05/0.98      | v2_struct_0(X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_tdlat_3(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | ~ v1_zfmisc_1(X0)
% 2.05/0.98      | v1_xboole_0(X0) ),
% 2.05/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_368,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | v2_tex_2(X0,X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | ~ v2_tdlat_3(X1)
% 2.05/0.98      | ~ v2_pre_topc(X1)
% 2.05/0.98      | ~ v1_zfmisc_1(X0)
% 2.05/0.98      | v1_xboole_0(X0)
% 2.05/0.98      | sK1 != X1 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_369,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | v2_tex_2(X0,sK1)
% 2.05/0.98      | ~ l1_pre_topc(sK1)
% 2.05/0.98      | ~ v2_tdlat_3(sK1)
% 2.05/0.98      | ~ v2_pre_topc(sK1)
% 2.05/0.98      | ~ v1_zfmisc_1(X0)
% 2.05/0.98      | v1_xboole_0(X0) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_368]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_373,plain,
% 2.05/0.98      ( v2_tex_2(X0,sK1)
% 2.05/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | ~ v1_zfmisc_1(X0)
% 2.05/0.98      | v1_xboole_0(X0) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_369,c_24,c_23,c_22]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_374,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | v2_tex_2(X0,sK1)
% 2.05/0.98      | ~ v1_zfmisc_1(X0)
% 2.05/0.98      | v1_xboole_0(X0) ),
% 2.05/0.98      inference(renaming,[status(thm)],[c_373]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_19,negated_conjecture,
% 2.05/0.98      ( v3_tex_2(sK2,sK1) | v1_zfmisc_1(sK2) ),
% 2.05/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_205,plain,
% 2.05/0.98      ( v1_zfmisc_1(sK2) | v3_tex_2(sK2,sK1) ),
% 2.05/0.98      inference(prop_impl,[status(thm)],[c_19]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_206,plain,
% 2.05/0.98      ( v3_tex_2(sK2,sK1) | v1_zfmisc_1(sK2) ),
% 2.05/0.98      inference(renaming,[status(thm)],[c_205]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_584,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | v2_tex_2(X0,sK1)
% 2.05/0.98      | v3_tex_2(sK2,sK1)
% 2.05/0.98      | v1_xboole_0(X0)
% 2.05/0.98      | sK2 != X0 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_374,c_206]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_585,plain,
% 2.05/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | v2_tex_2(sK2,sK1)
% 2.05/0.98      | v3_tex_2(sK2,sK1)
% 2.05/0.98      | v1_xboole_0(sK2) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_584]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_587,plain,
% 2.05/0.98      ( v3_tex_2(sK2,sK1) | v2_tex_2(sK2,sK1) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_585,c_21,c_20]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_588,plain,
% 2.05/0.98      ( v2_tex_2(sK2,sK1) | v3_tex_2(sK2,sK1) ),
% 2.05/0.98      inference(renaming,[status(thm)],[c_587]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_14,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | v2_tex_2(X0,X1)
% 2.05/0.98      | ~ v3_tex_2(X0,X1)
% 2.05/0.98      | ~ l1_pre_topc(X1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_401,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | v2_tex_2(X0,X1)
% 2.05/0.98      | ~ v3_tex_2(X0,X1)
% 2.05/0.98      | sK1 != X1 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_402,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | v2_tex_2(X0,sK1)
% 2.05/0.98      | ~ v3_tex_2(X0,sK1) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_401]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_839,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | v2_tex_2(X0,sK1)
% 2.05/0.98      | v2_tex_2(sK2,sK1)
% 2.05/0.98      | sK1 != sK1
% 2.05/0.98      | sK2 != X0 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_588,c_402]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_840,plain,
% 2.05/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | v2_tex_2(sK2,sK1) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_839]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_841,plain,
% 2.05/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.98      | v2_tex_2(sK2,sK1) = iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_840]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_18,negated_conjecture,
% 2.05/0.98      ( ~ v3_tex_2(sK2,sK1) | ~ v1_zfmisc_1(sK2) ),
% 2.05/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_203,plain,
% 2.05/0.98      ( ~ v1_zfmisc_1(sK2) | ~ v3_tex_2(sK2,sK1) ),
% 2.05/0.98      inference(prop_impl,[status(thm)],[c_18]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_204,plain,
% 2.05/0.98      ( ~ v3_tex_2(sK2,sK1) | ~ v1_zfmisc_1(sK2) ),
% 2.05/0.98      inference(renaming,[status(thm)],[c_203]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_568,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | ~ v2_tex_2(X0,sK1)
% 2.05/0.98      | ~ v3_tex_2(sK2,sK1)
% 2.05/0.98      | sK2 != X0 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_353,c_204]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_569,plain,
% 2.05/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | ~ v2_tex_2(sK2,sK1)
% 2.05/0.98      | ~ v3_tex_2(sK2,sK1) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_568]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_571,plain,
% 2.05/0.98      ( ~ v2_tex_2(sK2,sK1) | ~ v3_tex_2(sK2,sK1) ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_569,c_20]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_9,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | ~ v2_tex_2(X0,X1)
% 2.05/0.98      | v3_tex_2(X0,X1)
% 2.05/0.98      | ~ l1_pre_topc(X1)
% 2.05/0.98      | sK0(X1,X0) != X0 ),
% 2.05/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_492,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | ~ v2_tex_2(X0,X1)
% 2.05/0.98      | v3_tex_2(X0,X1)
% 2.05/0.98      | sK0(X1,X0) != X0
% 2.05/0.98      | sK1 != X1 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_493,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | ~ v2_tex_2(X0,sK1)
% 2.05/0.98      | v3_tex_2(X0,sK1)
% 2.05/0.98      | sK0(sK1,X0) != X0 ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_492]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_850,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | ~ v2_tex_2(X0,sK1)
% 2.05/0.98      | ~ v2_tex_2(sK2,sK1)
% 2.05/0.98      | sK0(sK1,X0) != X0
% 2.05/0.98      | sK1 != sK1
% 2.05/0.98      | sK2 != X0 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_571,c_493]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_851,plain,
% 2.05/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | ~ v2_tex_2(sK2,sK1)
% 2.05/0.98      | sK0(sK1,sK2) != sK2 ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_850]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_10,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | ~ v2_tex_2(X0,X1)
% 2.05/0.98      | v3_tex_2(X0,X1)
% 2.05/0.98      | r1_tarski(X0,sK0(X1,X0))
% 2.05/0.98      | ~ l1_pre_topc(X1) ),
% 2.05/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_474,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.05/0.98      | ~ v2_tex_2(X0,X1)
% 2.05/0.98      | v3_tex_2(X0,X1)
% 2.05/0.98      | r1_tarski(X0,sK0(X1,X0))
% 2.05/0.98      | sK1 != X1 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_475,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | ~ v2_tex_2(X0,sK1)
% 2.05/0.98      | v3_tex_2(X0,sK1)
% 2.05/0.98      | r1_tarski(X0,sK0(sK1,X0)) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_474]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_858,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | ~ v2_tex_2(X0,sK1)
% 2.05/0.98      | ~ v2_tex_2(sK2,sK1)
% 2.05/0.98      | r1_tarski(X0,sK0(sK1,X0))
% 2.05/0.98      | sK1 != sK1
% 2.05/0.98      | sK2 != X0 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_571,c_475]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_859,plain,
% 2.05/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | ~ v2_tex_2(sK2,sK1)
% 2.05/0.98      | r1_tarski(sK2,sK0(sK1,sK2)) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_858]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_860,plain,
% 2.05/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.98      | v2_tex_2(sK2,sK1) != iProver_top
% 2.05/0.98      | r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_859]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_869,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | ~ v2_tex_2(X0,sK1)
% 2.05/0.98      | v2_tex_2(sK0(sK1,X0),sK1)
% 2.05/0.98      | ~ v2_tex_2(sK2,sK1)
% 2.05/0.98      | sK1 != sK1
% 2.05/0.98      | sK2 != X0 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_571,c_457]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_870,plain,
% 2.05/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | v2_tex_2(sK0(sK1,sK2),sK1)
% 2.05/0.98      | ~ v2_tex_2(sK2,sK1) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_869]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_871,plain,
% 2.05/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.98      | v2_tex_2(sK0(sK1,sK2),sK1) = iProver_top
% 2.05/0.98      | v2_tex_2(sK2,sK1) != iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_870]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_880,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | m1_subset_1(sK0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | ~ v2_tex_2(X0,sK1)
% 2.05/0.98      | ~ v2_tex_2(sK2,sK1)
% 2.05/0.98      | sK1 != sK1
% 2.05/0.98      | sK2 != X0 ),
% 2.05/0.98      inference(resolution_lifted,[status(thm)],[c_571,c_439]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_881,plain,
% 2.05/0.98      ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | ~ v2_tex_2(sK2,sK1) ),
% 2.05/0.98      inference(unflattening,[status(thm)],[c_880]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_882,plain,
% 2.05/0.98      ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.05/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.98      | v2_tex_2(sK2,sK1) != iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_881]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1436,plain,( X0 = X0 ),theory(equality) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2385,plain,
% 2.05/0.98      ( sK0(sK1,sK2) = sK0(sK1,sK2) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_1436]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2225,plain,
% 2.05/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | ~ v2_tex_2(X0,sK1)
% 2.05/0.98      | ~ r1_tarski(sK2,X0)
% 2.05/0.98      | v1_xboole_0(X0)
% 2.05/0.98      | v1_xboole_0(sK2)
% 2.05/0.98      | sK2 = X0 ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_545]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2401,plain,
% 2.05/0.98      ( ~ m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.98      | ~ v2_tex_2(sK0(sK1,sK2),sK1)
% 2.05/0.98      | ~ r1_tarski(sK2,sK0(sK1,sK2))
% 2.05/0.98      | v1_xboole_0(sK0(sK1,sK2))
% 2.05/0.98      | v1_xboole_0(sK2)
% 2.05/0.98      | sK2 = sK0(sK1,sK2) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2225]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2402,plain,
% 2.05/0.98      ( sK2 = sK0(sK1,sK2)
% 2.05/0.98      | m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.98      | v2_tex_2(sK0(sK1,sK2),sK1) != iProver_top
% 2.05/0.98      | r1_tarski(sK2,sK0(sK1,sK2)) != iProver_top
% 2.05/0.98      | v1_xboole_0(sK0(sK1,sK2)) = iProver_top
% 2.05/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_2401]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1437,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2116,plain,
% 2.05/0.98      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_1437]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2519,plain,
% 2.05/0.98      ( X0 != sK0(sK1,sK2) | X0 = sK2 | sK2 != sK0(sK1,sK2) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2116]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2818,plain,
% 2.05/0.98      ( sK0(sK1,sK2) != sK0(sK1,sK2)
% 2.05/0.98      | sK0(sK1,sK2) = sK2
% 2.05/0.98      | sK2 != sK0(sK1,sK2) ),
% 2.05/0.98      inference(instantiation,[status(thm)],[c_2519]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_3616,plain,
% 2.05/0.98      ( v1_xboole_0(sK0(sK1,sK2)) = iProver_top ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_3577,c_30,c_20,c_31,c_840,c_841,c_851,c_860,c_871,
% 2.05/0.98                 c_882,c_2385,c_2402,c_2818]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_0,plain,
% 2.05/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.05/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1903,plain,
% 2.05/0.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_3621,plain,
% 2.05/0.98      ( sK0(sK1,sK2) = k1_xboole_0 ),
% 2.05/0.98      inference(superposition,[status(thm)],[c_3616,c_1903]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1891,plain,
% 2.05/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.98      | v2_tex_2(X0,sK1) != iProver_top
% 2.05/0.98      | v3_tex_2(X0,sK1) = iProver_top
% 2.05/0.98      | r1_tarski(X0,sK0(sK1,X0)) = iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_475]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2212,plain,
% 2.05/0.98      ( v2_tex_2(sK2,sK1) != iProver_top
% 2.05/0.98      | v3_tex_2(sK2,sK1) = iProver_top
% 2.05/0.98      | r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
% 2.05/0.98      inference(superposition,[status(thm)],[c_1897,c_1891]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_2215,plain,
% 2.05/0.98      ( r1_tarski(sK2,sK0(sK1,sK2)) = iProver_top ),
% 2.05/0.98      inference(global_propositional_subsumption,
% 2.05/0.98                [status(thm)],
% 2.05/0.98                [c_2212,c_31,c_841,c_860]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_3694,plain,
% 2.05/0.98      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 2.05/0.98      inference(demodulation,[status(thm)],[c_3621,c_2215]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_3,plain,
% 2.05/0.98      ( r1_tarski(X0,X0) ),
% 2.05/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1901,plain,
% 2.05/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4,plain,
% 2.05/0.98      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.05/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1900,plain,
% 2.05/0.98      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 2.05/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_3217,plain,
% 2.05/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.05/0.98      inference(superposition,[status(thm)],[c_1901,c_1900]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_6,plain,
% 2.05/0.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 2.05/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1898,plain,
% 2.05/0.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_3356,plain,
% 2.05/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.05/0.98      inference(superposition,[status(thm)],[c_3217,c_1898]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1,plain,
% 2.05/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.05/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1902,plain,
% 2.05/0.98      ( X0 = X1
% 2.05/0.98      | r1_tarski(X0,X1) != iProver_top
% 2.05/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_3364,plain,
% 2.05/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.05/0.98      inference(superposition,[status(thm)],[c_3356,c_1902]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_4022,plain,
% 2.05/0.98      ( sK2 = k1_xboole_0 ),
% 2.05/0.98      inference(superposition,[status(thm)],[c_3694,c_3364]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_1890,plain,
% 2.05/0.98      ( sK0(sK1,X0) != X0
% 2.05/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.98      | v2_tex_2(X0,sK1) != iProver_top
% 2.05/0.98      | v3_tex_2(X0,sK1) = iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_493]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_3713,plain,
% 2.05/0.98      ( sK2 != k1_xboole_0
% 2.05/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.98      | v2_tex_2(sK2,sK1) != iProver_top
% 2.05/0.98      | v3_tex_2(sK2,sK1) = iProver_top ),
% 2.05/0.98      inference(superposition,[status(thm)],[c_3621,c_1890]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(c_573,plain,
% 2.05/0.98      ( v2_tex_2(sK2,sK1) != iProver_top
% 2.05/0.98      | v3_tex_2(sK2,sK1) != iProver_top ),
% 2.05/0.98      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 2.05/0.98  
% 2.05/0.98  cnf(contradiction,plain,
% 2.05/0.98      ( $false ),
% 2.05/0.98      inference(minisat,[status(thm)],[c_4022,c_3713,c_841,c_573,c_31]) ).
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.05/0.98  
% 2.05/0.98  ------                               Statistics
% 2.05/0.98  
% 2.05/0.98  ------ General
% 2.05/0.98  
% 2.05/0.98  abstr_ref_over_cycles:                  0
% 2.05/0.98  abstr_ref_under_cycles:                 0
% 2.05/0.98  gc_basic_clause_elim:                   0
% 2.05/0.98  forced_gc_time:                         0
% 2.05/0.98  parsing_time:                           0.011
% 2.05/0.98  unif_index_cands_time:                  0.
% 2.05/0.98  unif_index_add_time:                    0.
% 2.05/0.98  orderings_time:                         0.
% 2.05/0.98  out_proof_time:                         0.01
% 2.05/0.98  total_time:                             0.141
% 2.05/0.98  num_of_symbols:                         48
% 2.05/0.98  num_of_terms:                           2243
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing
% 2.05/0.98  
% 2.05/0.98  num_of_splits:                          0
% 2.05/0.98  num_of_split_atoms:                     0
% 2.05/0.98  num_of_reused_defs:                     0
% 2.05/0.98  num_eq_ax_congr_red:                    11
% 2.05/0.98  num_of_sem_filtered_clauses:            1
% 2.05/0.98  num_of_subtypes:                        0
% 2.05/0.98  monotx_restored_types:                  0
% 2.05/0.98  sat_num_of_epr_types:                   0
% 2.05/0.98  sat_num_of_non_cyclic_types:            0
% 2.05/0.98  sat_guarded_non_collapsed_types:        0
% 2.05/0.98  num_pure_diseq_elim:                    0
% 2.05/0.98  simp_replaced_by:                       0
% 2.05/0.98  res_preprocessed:                       100
% 2.05/0.98  prep_upred:                             0
% 2.05/0.98  prep_unflattend:                        30
% 2.05/0.98  smt_new_axioms:                         0
% 2.05/0.98  pred_elim_cands:                        5
% 2.05/0.98  pred_elim:                              5
% 2.05/0.98  pred_elim_cl:                           7
% 2.05/0.98  pred_elim_cycles:                       8
% 2.05/0.98  merged_defs:                            10
% 2.05/0.98  merged_defs_ncl:                        0
% 2.05/0.98  bin_hyper_res:                          10
% 2.05/0.98  prep_cycles:                            4
% 2.05/0.98  pred_elim_time:                         0.015
% 2.05/0.98  splitting_time:                         0.
% 2.05/0.98  sem_filter_time:                        0.
% 2.05/0.98  monotx_time:                            0.001
% 2.05/0.98  subtype_inf_time:                       0.
% 2.05/0.98  
% 2.05/0.98  ------ Problem properties
% 2.05/0.98  
% 2.05/0.98  clauses:                                18
% 2.05/0.98  conjectures:                            2
% 2.05/0.98  epr:                                    7
% 2.05/0.98  horn:                                   13
% 2.05/0.98  ground:                                 4
% 2.05/0.98  unary:                                  6
% 2.05/0.98  binary:                                 3
% 2.05/0.98  lits:                                   49
% 2.05/0.98  lits_eq:                                8
% 2.05/0.98  fd_pure:                                0
% 2.05/0.98  fd_pseudo:                              0
% 2.05/0.98  fd_cond:                                2
% 2.05/0.98  fd_pseudo_cond:                         3
% 2.05/0.98  ac_symbols:                             0
% 2.05/0.98  
% 2.05/0.98  ------ Propositional Solver
% 2.05/0.98  
% 2.05/0.98  prop_solver_calls:                      27
% 2.05/0.98  prop_fast_solver_calls:                 967
% 2.05/0.98  smt_solver_calls:                       0
% 2.05/0.98  smt_fast_solver_calls:                  0
% 2.05/0.98  prop_num_of_clauses:                    1117
% 2.05/0.98  prop_preprocess_simplified:             4259
% 2.05/0.98  prop_fo_subsumed:                       58
% 2.05/0.98  prop_solver_time:                       0.
% 2.05/0.98  smt_solver_time:                        0.
% 2.05/0.98  smt_fast_solver_time:                   0.
% 2.05/0.98  prop_fast_solver_time:                  0.
% 2.05/0.98  prop_unsat_core_time:                   0.
% 2.05/0.98  
% 2.05/0.98  ------ QBF
% 2.05/0.98  
% 2.05/0.98  qbf_q_res:                              0
% 2.05/0.98  qbf_num_tautologies:                    0
% 2.05/0.98  qbf_prep_cycles:                        0
% 2.05/0.98  
% 2.05/0.98  ------ BMC1
% 2.05/0.98  
% 2.05/0.98  bmc1_current_bound:                     -1
% 2.05/0.98  bmc1_last_solved_bound:                 -1
% 2.05/0.98  bmc1_unsat_core_size:                   -1
% 2.05/0.98  bmc1_unsat_core_parents_size:           -1
% 2.05/0.98  bmc1_merge_next_fun:                    0
% 2.05/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.05/0.98  
% 2.05/0.98  ------ Instantiation
% 2.05/0.98  
% 2.05/0.98  inst_num_of_clauses:                    305
% 2.05/0.98  inst_num_in_passive:                    87
% 2.05/0.98  inst_num_in_active:                     172
% 2.05/0.98  inst_num_in_unprocessed:                47
% 2.05/0.98  inst_num_of_loops:                      190
% 2.05/0.98  inst_num_of_learning_restarts:          0
% 2.05/0.98  inst_num_moves_active_passive:          15
% 2.05/0.98  inst_lit_activity:                      0
% 2.05/0.98  inst_lit_activity_moves:                0
% 2.05/0.98  inst_num_tautologies:                   0
% 2.05/0.98  inst_num_prop_implied:                  0
% 2.05/0.98  inst_num_existing_simplified:           0
% 2.05/0.98  inst_num_eq_res_simplified:             0
% 2.05/0.98  inst_num_child_elim:                    0
% 2.05/0.98  inst_num_of_dismatching_blockings:      20
% 2.05/0.98  inst_num_of_non_proper_insts:           298
% 2.05/0.98  inst_num_of_duplicates:                 0
% 2.05/0.98  inst_inst_num_from_inst_to_res:         0
% 2.05/0.98  inst_dismatching_checking_time:         0.
% 2.05/0.98  
% 2.05/0.98  ------ Resolution
% 2.05/0.98  
% 2.05/0.98  res_num_of_clauses:                     0
% 2.05/0.98  res_num_in_passive:                     0
% 2.05/0.98  res_num_in_active:                      0
% 2.05/0.98  res_num_of_loops:                       104
% 2.05/0.98  res_forward_subset_subsumed:            53
% 2.05/0.98  res_backward_subset_subsumed:           3
% 2.05/0.98  res_forward_subsumed:                   0
% 2.05/0.98  res_backward_subsumed:                  4
% 2.05/0.98  res_forward_subsumption_resolution:     0
% 2.05/0.98  res_backward_subsumption_resolution:    1
% 2.05/0.98  res_clause_to_clause_subsumption:       259
% 2.05/0.98  res_orphan_elimination:                 0
% 2.05/0.98  res_tautology_del:                      51
% 2.05/0.98  res_num_eq_res_simplified:              0
% 2.05/0.98  res_num_sel_changes:                    0
% 2.05/0.98  res_moves_from_active_to_pass:          0
% 2.05/0.98  
% 2.05/0.98  ------ Superposition
% 2.05/0.98  
% 2.05/0.98  sup_time_total:                         0.
% 2.05/0.98  sup_time_generating:                    0.
% 2.05/0.98  sup_time_sim_full:                      0.
% 2.05/0.98  sup_time_sim_immed:                     0.
% 2.05/0.98  
% 2.05/0.98  sup_num_of_clauses:                     48
% 2.05/0.98  sup_num_in_active:                      33
% 2.05/0.98  sup_num_in_passive:                     15
% 2.05/0.98  sup_num_of_loops:                       37
% 2.05/0.98  sup_fw_superposition:                   28
% 2.05/0.98  sup_bw_superposition:                   28
% 2.05/0.98  sup_immediate_simplified:               14
% 2.05/0.98  sup_given_eliminated:                   0
% 2.05/0.98  comparisons_done:                       0
% 2.05/0.98  comparisons_avoided:                    0
% 2.05/0.98  
% 2.05/0.98  ------ Simplifications
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  sim_fw_subset_subsumed:                 5
% 2.05/0.98  sim_bw_subset_subsumed:                 1
% 2.05/0.98  sim_fw_subsumed:                        7
% 2.05/0.98  sim_bw_subsumed:                        0
% 2.05/0.98  sim_fw_subsumption_res:                 0
% 2.05/0.98  sim_bw_subsumption_res:                 0
% 2.05/0.98  sim_tautology_del:                      0
% 2.05/0.98  sim_eq_tautology_del:                   3
% 2.05/0.98  sim_eq_res_simp:                        0
% 2.05/0.98  sim_fw_demodulated:                     1
% 2.05/0.98  sim_bw_demodulated:                     5
% 2.05/0.98  sim_light_normalised:                   3
% 2.05/0.98  sim_joinable_taut:                      0
% 2.05/0.98  sim_joinable_simp:                      0
% 2.05/0.98  sim_ac_normalised:                      0
% 2.05/0.98  sim_smt_subsumption:                    0
% 2.05/0.98  
%------------------------------------------------------------------------------
