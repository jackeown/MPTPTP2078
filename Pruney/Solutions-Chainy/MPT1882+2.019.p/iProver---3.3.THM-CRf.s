%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:22 EST 2020

% Result     : Theorem 1.27s
% Output     : CNFRefutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 696 expanded)
%              Number of clauses        :   86 ( 163 expanded)
%              Number of leaves         :   15 ( 156 expanded)
%              Depth                    :   28
%              Number of atoms          :  668 (5494 expanded)
%              Number of equality atoms :   98 ( 204 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f26])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

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
    inference(ennf_transformation,[],[f9])).

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
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

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
    inference(ennf_transformation,[],[f11])).

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
     => ( ( ~ v1_zfmisc_1(sK3)
          | ~ v3_tex_2(sK3,X0) )
        & ( v1_zfmisc_1(sK3)
          | v3_tex_2(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK3) ) ) ),
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

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f35,f37,f36])).

fof(f56,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,
    ( ~ v1_zfmisc_1(sK3)
    | ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

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
     => ( sK1(X0,X1) != X1
        & r1_tarski(X1,sK1(X0,X1))
        & v2_tex_2(sK1(X0,X1),X0)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK1(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK1(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK1(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

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
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,
    ( v1_zfmisc_1(sK3)
    | v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( k6_subset_1(X1,X0) = k1_xboole_0
        & X0 != X1
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X1,X0) != k1_xboole_0
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X1,X0) != k1_xboole_0
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_1,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | X2 != X0
    | sK0(X2) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_5])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_16,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0)
    | v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_139,plain,
    ( ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v1_zfmisc_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_0])).

cnf(c_140,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_139])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_377,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_140,c_24])).

cnf(c_378,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_22,negated_conjecture,
    ( v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v1_zfmisc_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_378,c_23,c_22,c_21])).

cnf(c_383,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_382])).

cnf(c_17,negated_conjecture,
    ( ~ v3_tex_2(sK3,sK2)
    | ~ v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_190,plain,
    ( ~ v1_zfmisc_1(sK3)
    | ~ v3_tex_2(sK3,sK2) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_191,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | ~ v1_zfmisc_1(sK3) ),
    inference(renaming,[status(thm)],[c_190])).

cnf(c_760,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_383,c_191])).

cnf(c_761,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_760])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_763,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_761,c_19])).

cnf(c_764,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ v3_tex_2(sK3,sK2) ),
    inference(renaming,[status(thm)],[c_763])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_8,plain,
    ( r1_tarski(X0,sK1(X1,X0))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_598,plain,
    ( r1_tarski(X0,sK1(X1,X0))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_599,plain,
    ( r1_tarski(X0,sK1(sK2,X0))
    | ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_598])).

cnf(c_691,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_zfmisc_1(X2)
    | X0 != X1
    | X2 = X1
    | sK1(sK2,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_599])).

cnf(c_692,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK2,X0))
    | ~ v1_zfmisc_1(sK1(sK2,X0))
    | sK1(sK2,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_691])).

cnf(c_7,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_616,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK1(X1,X0) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_617,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_616])).

cnf(c_696,plain,
    ( ~ v1_zfmisc_1(sK1(sK2,X0))
    | v1_xboole_0(sK1(sK2,X0))
    | v1_xboole_0(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_tex_2(X0,sK2)
    | ~ v2_tex_2(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_692,c_617])).

cnf(c_697,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK2,X0))
    | ~ v1_zfmisc_1(sK1(sK2,X0)) ),
    inference(renaming,[status(thm)],[c_696])).

cnf(c_790,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(X1,sK2)
    | v3_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(sK1(sK2,X1))
    | sK1(sK2,X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_383,c_697])).

cnf(c_791,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(sK1(sK2,X0),sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_790])).

cnf(c_10,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_562,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_563,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_9,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK1(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_580,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK1(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_581,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(sK1(sK2,X0),sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_580])).

cnf(c_795,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_tex_2(X0,sK2)
    | ~ v2_tex_2(X0,sK2)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_791,c_563,c_581])).

cnf(c_796,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK2,X0)) ),
    inference(renaming,[status(thm)],[c_795])).

cnf(c_854,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK2,X0))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_764,c_796])).

cnf(c_855,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK1(sK2,sK3))
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_854])).

cnf(c_20,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_15,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_398,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_399,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(X0,sK2)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_399,c_23,c_22,c_21])).

cnf(c_404,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_403])).

cnf(c_18,negated_conjecture,
    ( v3_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_192,plain,
    ( v1_zfmisc_1(sK3)
    | v3_tex_2(sK3,sK2) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_193,plain,
    ( v3_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(renaming,[status(thm)],[c_192])).

cnf(c_776,plain,
    ( v2_tex_2(X0,sK2)
    | v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_404,c_193])).

cnf(c_777,plain,
    ( v2_tex_2(sK3,sK2)
    | v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_776])).

cnf(c_779,plain,
    ( v2_tex_2(sK3,sK2)
    | v3_tex_2(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_777,c_20,c_19])).

cnf(c_12,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_547,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_548,plain,
    ( v2_tex_2(X0,sK2)
    | ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_843,plain,
    ( v2_tex_2(X0,sK2)
    | v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_779,c_548])).

cnf(c_844,plain,
    ( v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_843])).

cnf(c_857,plain,
    ( v1_xboole_0(sK1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_855,c_20,c_19,c_844])).

cnf(c_913,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | sK1(sK2,sK3) != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_355,c_857])).

cnf(c_914,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK2,sK3)))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_913])).

cnf(c_929,plain,
    ( k6_subset_1(X0,X1) != X2
    | k1_zfmisc_1(sK1(sK2,sK3)) != k1_zfmisc_1(X0)
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_914])).

cnf(c_930,plain,
    ( k1_zfmisc_1(sK1(sK2,sK3)) != k1_zfmisc_1(X0)
    | k1_xboole_0 = k6_subset_1(X0,X1) ),
    inference(unflattening,[status(thm)],[c_929])).

cnf(c_1004,plain,
    ( k1_zfmisc_1(sK1(sK2,sK3)) != k1_zfmisc_1(sK1(sK2,sK3))
    | k1_xboole_0 = k6_subset_1(sK1(sK2,sK3),X0) ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(c_1052,plain,
    ( k1_zfmisc_1(sK1(sK2,sK3)) != k1_zfmisc_1(sK1(sK2,sK3))
    | k1_xboole_0 = k6_subset_1(sK1(sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_1004])).

cnf(c_967,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1028,plain,
    ( k6_subset_1(sK1(sK2,sK3),sK3) = k6_subset_1(sK1(sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_968,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1013,plain,
    ( k6_subset_1(sK1(sK2,sK3),sK3) != X0
    | k6_subset_1(sK1(sK2,sK3),sK3) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_1027,plain,
    ( k6_subset_1(sK1(sK2,sK3),sK3) != k6_subset_1(sK1(sK2,sK3),sK3)
    | k6_subset_1(sK1(sK2,sK3),sK3) = k1_xboole_0
    | k1_xboole_0 != k6_subset_1(sK1(sK2,sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_1013])).

cnf(c_1005,plain,
    ( k1_zfmisc_1(sK1(sK2,sK3)) = k1_zfmisc_1(sK1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | X1 = X0
    | k6_subset_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_721,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 != X1
    | X2 = X1
    | sK1(sK2,X0) != X2
    | k6_subset_1(X2,X1) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_599])).

cnf(c_722,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(sK2,X0) = X0
    | k6_subset_1(sK1(sK2,X0),X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_721])).

cnf(c_726,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_tex_2(X0,sK2)
    | ~ v2_tex_2(X0,sK2)
    | k6_subset_1(sK1(sK2,X0),X0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_722,c_617])).

cnf(c_727,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k6_subset_1(sK1(sK2,X0),X0) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_726])).

cnf(c_865,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k6_subset_1(sK1(sK2,X0),X0) != k1_xboole_0
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_764,c_727])).

cnf(c_866,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k6_subset_1(sK1(sK2,sK3),sK3) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_865])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1052,c_1028,c_1027,c_1005,c_866,c_844,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.27/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.27/1.01  
% 1.27/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.27/1.01  
% 1.27/1.01  ------  iProver source info
% 1.27/1.01  
% 1.27/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.27/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.27/1.01  git: non_committed_changes: false
% 1.27/1.01  git: last_make_outside_of_git: false
% 1.27/1.01  
% 1.27/1.01  ------ 
% 1.27/1.01  
% 1.27/1.01  ------ Input Options
% 1.27/1.01  
% 1.27/1.01  --out_options                           all
% 1.27/1.01  --tptp_safe_out                         true
% 1.27/1.01  --problem_path                          ""
% 1.27/1.01  --include_path                          ""
% 1.27/1.01  --clausifier                            res/vclausify_rel
% 1.27/1.01  --clausifier_options                    --mode clausify
% 1.27/1.01  --stdin                                 false
% 1.27/1.01  --stats_out                             all
% 1.27/1.01  
% 1.27/1.01  ------ General Options
% 1.27/1.01  
% 1.27/1.01  --fof                                   false
% 1.27/1.01  --time_out_real                         305.
% 1.27/1.01  --time_out_virtual                      -1.
% 1.27/1.01  --symbol_type_check                     false
% 1.27/1.01  --clausify_out                          false
% 1.27/1.01  --sig_cnt_out                           false
% 1.27/1.01  --trig_cnt_out                          false
% 1.27/1.01  --trig_cnt_out_tolerance                1.
% 1.27/1.01  --trig_cnt_out_sk_spl                   false
% 1.27/1.01  --abstr_cl_out                          false
% 1.27/1.01  
% 1.27/1.01  ------ Global Options
% 1.27/1.01  
% 1.27/1.01  --schedule                              default
% 1.27/1.01  --add_important_lit                     false
% 1.27/1.01  --prop_solver_per_cl                    1000
% 1.27/1.01  --min_unsat_core                        false
% 1.27/1.01  --soft_assumptions                      false
% 1.27/1.01  --soft_lemma_size                       3
% 1.27/1.01  --prop_impl_unit_size                   0
% 1.27/1.01  --prop_impl_unit                        []
% 1.27/1.01  --share_sel_clauses                     true
% 1.27/1.01  --reset_solvers                         false
% 1.27/1.01  --bc_imp_inh                            [conj_cone]
% 1.27/1.01  --conj_cone_tolerance                   3.
% 1.27/1.01  --extra_neg_conj                        none
% 1.27/1.01  --large_theory_mode                     true
% 1.27/1.01  --prolific_symb_bound                   200
% 1.27/1.01  --lt_threshold                          2000
% 1.27/1.01  --clause_weak_htbl                      true
% 1.27/1.01  --gc_record_bc_elim                     false
% 1.27/1.01  
% 1.27/1.01  ------ Preprocessing Options
% 1.27/1.01  
% 1.27/1.01  --preprocessing_flag                    true
% 1.27/1.01  --time_out_prep_mult                    0.1
% 1.27/1.01  --splitting_mode                        input
% 1.27/1.01  --splitting_grd                         true
% 1.27/1.01  --splitting_cvd                         false
% 1.27/1.01  --splitting_cvd_svl                     false
% 1.27/1.01  --splitting_nvd                         32
% 1.27/1.01  --sub_typing                            true
% 1.27/1.01  --prep_gs_sim                           true
% 1.27/1.01  --prep_unflatten                        true
% 1.27/1.01  --prep_res_sim                          true
% 1.27/1.01  --prep_upred                            true
% 1.27/1.01  --prep_sem_filter                       exhaustive
% 1.27/1.01  --prep_sem_filter_out                   false
% 1.27/1.01  --pred_elim                             true
% 1.27/1.01  --res_sim_input                         true
% 1.27/1.01  --eq_ax_congr_red                       true
% 1.27/1.01  --pure_diseq_elim                       true
% 1.27/1.01  --brand_transform                       false
% 1.27/1.01  --non_eq_to_eq                          false
% 1.27/1.01  --prep_def_merge                        true
% 1.27/1.01  --prep_def_merge_prop_impl              false
% 1.27/1.01  --prep_def_merge_mbd                    true
% 1.27/1.01  --prep_def_merge_tr_red                 false
% 1.27/1.01  --prep_def_merge_tr_cl                  false
% 1.27/1.01  --smt_preprocessing                     true
% 1.27/1.01  --smt_ac_axioms                         fast
% 1.27/1.01  --preprocessed_out                      false
% 1.27/1.01  --preprocessed_stats                    false
% 1.27/1.01  
% 1.27/1.01  ------ Abstraction refinement Options
% 1.27/1.01  
% 1.27/1.01  --abstr_ref                             []
% 1.27/1.01  --abstr_ref_prep                        false
% 1.27/1.01  --abstr_ref_until_sat                   false
% 1.27/1.01  --abstr_ref_sig_restrict                funpre
% 1.27/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.27/1.01  --abstr_ref_under                       []
% 1.27/1.01  
% 1.27/1.01  ------ SAT Options
% 1.27/1.01  
% 1.27/1.01  --sat_mode                              false
% 1.27/1.01  --sat_fm_restart_options                ""
% 1.27/1.01  --sat_gr_def                            false
% 1.27/1.01  --sat_epr_types                         true
% 1.27/1.01  --sat_non_cyclic_types                  false
% 1.27/1.01  --sat_finite_models                     false
% 1.27/1.01  --sat_fm_lemmas                         false
% 1.27/1.01  --sat_fm_prep                           false
% 1.27/1.01  --sat_fm_uc_incr                        true
% 1.27/1.01  --sat_out_model                         small
% 1.27/1.01  --sat_out_clauses                       false
% 1.27/1.01  
% 1.27/1.01  ------ QBF Options
% 1.27/1.01  
% 1.27/1.01  --qbf_mode                              false
% 1.27/1.01  --qbf_elim_univ                         false
% 1.27/1.01  --qbf_dom_inst                          none
% 1.27/1.01  --qbf_dom_pre_inst                      false
% 1.27/1.01  --qbf_sk_in                             false
% 1.27/1.01  --qbf_pred_elim                         true
% 1.27/1.01  --qbf_split                             512
% 1.27/1.01  
% 1.27/1.01  ------ BMC1 Options
% 1.27/1.01  
% 1.27/1.01  --bmc1_incremental                      false
% 1.27/1.01  --bmc1_axioms                           reachable_all
% 1.27/1.01  --bmc1_min_bound                        0
% 1.27/1.01  --bmc1_max_bound                        -1
% 1.27/1.01  --bmc1_max_bound_default                -1
% 1.27/1.01  --bmc1_symbol_reachability              true
% 1.27/1.01  --bmc1_property_lemmas                  false
% 1.27/1.01  --bmc1_k_induction                      false
% 1.27/1.01  --bmc1_non_equiv_states                 false
% 1.27/1.01  --bmc1_deadlock                         false
% 1.27/1.01  --bmc1_ucm                              false
% 1.27/1.01  --bmc1_add_unsat_core                   none
% 1.27/1.01  --bmc1_unsat_core_children              false
% 1.27/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.27/1.01  --bmc1_out_stat                         full
% 1.27/1.01  --bmc1_ground_init                      false
% 1.27/1.01  --bmc1_pre_inst_next_state              false
% 1.27/1.01  --bmc1_pre_inst_state                   false
% 1.27/1.01  --bmc1_pre_inst_reach_state             false
% 1.27/1.01  --bmc1_out_unsat_core                   false
% 1.27/1.01  --bmc1_aig_witness_out                  false
% 1.27/1.01  --bmc1_verbose                          false
% 1.27/1.01  --bmc1_dump_clauses_tptp                false
% 1.27/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.27/1.01  --bmc1_dump_file                        -
% 1.27/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.27/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.27/1.01  --bmc1_ucm_extend_mode                  1
% 1.27/1.01  --bmc1_ucm_init_mode                    2
% 1.27/1.01  --bmc1_ucm_cone_mode                    none
% 1.27/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.27/1.01  --bmc1_ucm_relax_model                  4
% 1.27/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.27/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.27/1.01  --bmc1_ucm_layered_model                none
% 1.27/1.01  --bmc1_ucm_max_lemma_size               10
% 1.27/1.01  
% 1.27/1.01  ------ AIG Options
% 1.27/1.01  
% 1.27/1.01  --aig_mode                              false
% 1.27/1.01  
% 1.27/1.01  ------ Instantiation Options
% 1.27/1.01  
% 1.27/1.01  --instantiation_flag                    true
% 1.27/1.01  --inst_sos_flag                         false
% 1.27/1.01  --inst_sos_phase                        true
% 1.27/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.27/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.27/1.01  --inst_lit_sel_side                     num_symb
% 1.27/1.01  --inst_solver_per_active                1400
% 1.27/1.01  --inst_solver_calls_frac                1.
% 1.27/1.01  --inst_passive_queue_type               priority_queues
% 1.27/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.27/1.01  --inst_passive_queues_freq              [25;2]
% 1.27/1.01  --inst_dismatching                      true
% 1.27/1.01  --inst_eager_unprocessed_to_passive     true
% 1.27/1.01  --inst_prop_sim_given                   true
% 1.27/1.01  --inst_prop_sim_new                     false
% 1.27/1.01  --inst_subs_new                         false
% 1.27/1.01  --inst_eq_res_simp                      false
% 1.27/1.01  --inst_subs_given                       false
% 1.27/1.01  --inst_orphan_elimination               true
% 1.27/1.01  --inst_learning_loop_flag               true
% 1.27/1.01  --inst_learning_start                   3000
% 1.27/1.01  --inst_learning_factor                  2
% 1.27/1.01  --inst_start_prop_sim_after_learn       3
% 1.27/1.01  --inst_sel_renew                        solver
% 1.27/1.01  --inst_lit_activity_flag                true
% 1.27/1.01  --inst_restr_to_given                   false
% 1.27/1.01  --inst_activity_threshold               500
% 1.27/1.01  --inst_out_proof                        true
% 1.27/1.01  
% 1.27/1.01  ------ Resolution Options
% 1.27/1.01  
% 1.27/1.01  --resolution_flag                       true
% 1.27/1.01  --res_lit_sel                           adaptive
% 1.27/1.01  --res_lit_sel_side                      none
% 1.27/1.01  --res_ordering                          kbo
% 1.27/1.01  --res_to_prop_solver                    active
% 1.27/1.01  --res_prop_simpl_new                    false
% 1.27/1.01  --res_prop_simpl_given                  true
% 1.27/1.01  --res_passive_queue_type                priority_queues
% 1.27/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.27/1.01  --res_passive_queues_freq               [15;5]
% 1.27/1.01  --res_forward_subs                      full
% 1.27/1.01  --res_backward_subs                     full
% 1.27/1.01  --res_forward_subs_resolution           true
% 1.27/1.01  --res_backward_subs_resolution          true
% 1.27/1.01  --res_orphan_elimination                true
% 1.27/1.01  --res_time_limit                        2.
% 1.27/1.01  --res_out_proof                         true
% 1.27/1.01  
% 1.27/1.01  ------ Superposition Options
% 1.27/1.01  
% 1.27/1.01  --superposition_flag                    true
% 1.27/1.01  --sup_passive_queue_type                priority_queues
% 1.27/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.27/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.27/1.01  --demod_completeness_check              fast
% 1.27/1.01  --demod_use_ground                      true
% 1.27/1.01  --sup_to_prop_solver                    passive
% 1.27/1.01  --sup_prop_simpl_new                    true
% 1.27/1.01  --sup_prop_simpl_given                  true
% 1.27/1.01  --sup_fun_splitting                     false
% 1.27/1.01  --sup_smt_interval                      50000
% 1.27/1.01  
% 1.27/1.01  ------ Superposition Simplification Setup
% 1.27/1.01  
% 1.27/1.01  --sup_indices_passive                   []
% 1.27/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.27/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.27/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.27/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.27/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.27/1.01  --sup_full_bw                           [BwDemod]
% 1.27/1.01  --sup_immed_triv                        [TrivRules]
% 1.27/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.27/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.27/1.01  --sup_immed_bw_main                     []
% 1.27/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.27/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.27/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.27/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.27/1.01  
% 1.27/1.01  ------ Combination Options
% 1.27/1.01  
% 1.27/1.01  --comb_res_mult                         3
% 1.27/1.01  --comb_sup_mult                         2
% 1.27/1.01  --comb_inst_mult                        10
% 1.27/1.01  
% 1.27/1.01  ------ Debug Options
% 1.27/1.01  
% 1.27/1.01  --dbg_backtrace                         false
% 1.27/1.01  --dbg_dump_prop_clauses                 false
% 1.27/1.01  --dbg_dump_prop_clauses_file            -
% 1.27/1.01  --dbg_out_stat                          false
% 1.27/1.01  ------ Parsing...
% 1.27/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.27/1.01  
% 1.27/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 12 0s  sf_e  pe_s  pe_e 
% 1.27/1.01  
% 1.27/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.27/1.01  
% 1.27/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 1.27/1.01  ------ Proving...
% 1.27/1.01  ------ Problem Properties 
% 1.27/1.01  
% 1.27/1.01  
% 1.27/1.01  clauses                                 7
% 1.27/1.01  conjectures                             0
% 1.27/1.01  EPR                                     0
% 1.27/1.01  Horn                                    7
% 1.27/1.01  unary                                   2
% 1.27/1.01  binary                                  5
% 1.27/1.01  lits                                    12
% 1.27/1.01  lits eq                                 12
% 1.27/1.01  fd_pure                                 0
% 1.27/1.01  fd_pseudo                               0
% 1.27/1.01  fd_cond                                 2
% 1.27/1.01  fd_pseudo_cond                          0
% 1.27/1.01  AC symbols                              0
% 1.27/1.01  
% 1.27/1.01  ------ Schedule dynamic 5 is on 
% 1.27/1.01  
% 1.27/1.01  ------ no conjectures: strip conj schedule 
% 1.27/1.01  
% 1.27/1.01  ------ pure equality problem: resolution off 
% 1.27/1.01  
% 1.27/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.27/1.01  
% 1.27/1.01  
% 1.27/1.01  ------ 
% 1.27/1.01  Current options:
% 1.27/1.01  ------ 
% 1.27/1.01  
% 1.27/1.01  ------ Input Options
% 1.27/1.01  
% 1.27/1.01  --out_options                           all
% 1.27/1.01  --tptp_safe_out                         true
% 1.27/1.01  --problem_path                          ""
% 1.27/1.01  --include_path                          ""
% 1.27/1.01  --clausifier                            res/vclausify_rel
% 1.27/1.01  --clausifier_options                    --mode clausify
% 1.27/1.01  --stdin                                 false
% 1.27/1.01  --stats_out                             all
% 1.27/1.01  
% 1.27/1.01  ------ General Options
% 1.27/1.01  
% 1.27/1.01  --fof                                   false
% 1.27/1.01  --time_out_real                         305.
% 1.27/1.01  --time_out_virtual                      -1.
% 1.27/1.01  --symbol_type_check                     false
% 1.27/1.01  --clausify_out                          false
% 1.27/1.01  --sig_cnt_out                           false
% 1.27/1.01  --trig_cnt_out                          false
% 1.27/1.01  --trig_cnt_out_tolerance                1.
% 1.27/1.01  --trig_cnt_out_sk_spl                   false
% 1.27/1.01  --abstr_cl_out                          false
% 1.27/1.01  
% 1.27/1.01  ------ Global Options
% 1.27/1.01  
% 1.27/1.01  --schedule                              default
% 1.27/1.01  --add_important_lit                     false
% 1.27/1.01  --prop_solver_per_cl                    1000
% 1.27/1.01  --min_unsat_core                        false
% 1.27/1.01  --soft_assumptions                      false
% 1.27/1.01  --soft_lemma_size                       3
% 1.27/1.01  --prop_impl_unit_size                   0
% 1.27/1.01  --prop_impl_unit                        []
% 1.27/1.01  --share_sel_clauses                     true
% 1.27/1.01  --reset_solvers                         false
% 1.27/1.01  --bc_imp_inh                            [conj_cone]
% 1.27/1.01  --conj_cone_tolerance                   3.
% 1.27/1.01  --extra_neg_conj                        none
% 1.27/1.01  --large_theory_mode                     true
% 1.27/1.01  --prolific_symb_bound                   200
% 1.27/1.01  --lt_threshold                          2000
% 1.27/1.01  --clause_weak_htbl                      true
% 1.27/1.01  --gc_record_bc_elim                     false
% 1.27/1.01  
% 1.27/1.01  ------ Preprocessing Options
% 1.27/1.01  
% 1.27/1.01  --preprocessing_flag                    true
% 1.27/1.01  --time_out_prep_mult                    0.1
% 1.27/1.01  --splitting_mode                        input
% 1.27/1.01  --splitting_grd                         true
% 1.27/1.01  --splitting_cvd                         false
% 1.27/1.01  --splitting_cvd_svl                     false
% 1.27/1.01  --splitting_nvd                         32
% 1.27/1.01  --sub_typing                            true
% 1.27/1.01  --prep_gs_sim                           true
% 1.27/1.01  --prep_unflatten                        true
% 1.27/1.01  --prep_res_sim                          true
% 1.27/1.01  --prep_upred                            true
% 1.27/1.01  --prep_sem_filter                       exhaustive
% 1.27/1.01  --prep_sem_filter_out                   false
% 1.27/1.01  --pred_elim                             true
% 1.27/1.01  --res_sim_input                         true
% 1.27/1.01  --eq_ax_congr_red                       true
% 1.27/1.01  --pure_diseq_elim                       true
% 1.27/1.01  --brand_transform                       false
% 1.27/1.01  --non_eq_to_eq                          false
% 1.27/1.01  --prep_def_merge                        true
% 1.27/1.01  --prep_def_merge_prop_impl              false
% 1.27/1.01  --prep_def_merge_mbd                    true
% 1.27/1.01  --prep_def_merge_tr_red                 false
% 1.27/1.01  --prep_def_merge_tr_cl                  false
% 1.27/1.01  --smt_preprocessing                     true
% 1.27/1.01  --smt_ac_axioms                         fast
% 1.27/1.01  --preprocessed_out                      false
% 1.27/1.01  --preprocessed_stats                    false
% 1.27/1.01  
% 1.27/1.01  ------ Abstraction refinement Options
% 1.27/1.01  
% 1.27/1.01  --abstr_ref                             []
% 1.27/1.01  --abstr_ref_prep                        false
% 1.27/1.01  --abstr_ref_until_sat                   false
% 1.27/1.01  --abstr_ref_sig_restrict                funpre
% 1.27/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.27/1.01  --abstr_ref_under                       []
% 1.27/1.01  
% 1.27/1.01  ------ SAT Options
% 1.27/1.01  
% 1.27/1.01  --sat_mode                              false
% 1.27/1.01  --sat_fm_restart_options                ""
% 1.27/1.01  --sat_gr_def                            false
% 1.27/1.01  --sat_epr_types                         true
% 1.27/1.01  --sat_non_cyclic_types                  false
% 1.27/1.01  --sat_finite_models                     false
% 1.27/1.01  --sat_fm_lemmas                         false
% 1.27/1.01  --sat_fm_prep                           false
% 1.27/1.01  --sat_fm_uc_incr                        true
% 1.27/1.01  --sat_out_model                         small
% 1.27/1.01  --sat_out_clauses                       false
% 1.27/1.01  
% 1.27/1.01  ------ QBF Options
% 1.27/1.01  
% 1.27/1.01  --qbf_mode                              false
% 1.27/1.01  --qbf_elim_univ                         false
% 1.27/1.01  --qbf_dom_inst                          none
% 1.27/1.01  --qbf_dom_pre_inst                      false
% 1.27/1.01  --qbf_sk_in                             false
% 1.27/1.01  --qbf_pred_elim                         true
% 1.27/1.01  --qbf_split                             512
% 1.27/1.01  
% 1.27/1.01  ------ BMC1 Options
% 1.27/1.01  
% 1.27/1.01  --bmc1_incremental                      false
% 1.27/1.01  --bmc1_axioms                           reachable_all
% 1.27/1.01  --bmc1_min_bound                        0
% 1.27/1.01  --bmc1_max_bound                        -1
% 1.27/1.01  --bmc1_max_bound_default                -1
% 1.27/1.01  --bmc1_symbol_reachability              true
% 1.27/1.01  --bmc1_property_lemmas                  false
% 1.27/1.01  --bmc1_k_induction                      false
% 1.27/1.01  --bmc1_non_equiv_states                 false
% 1.27/1.01  --bmc1_deadlock                         false
% 1.27/1.01  --bmc1_ucm                              false
% 1.27/1.01  --bmc1_add_unsat_core                   none
% 1.27/1.01  --bmc1_unsat_core_children              false
% 1.27/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.27/1.01  --bmc1_out_stat                         full
% 1.27/1.01  --bmc1_ground_init                      false
% 1.27/1.01  --bmc1_pre_inst_next_state              false
% 1.27/1.01  --bmc1_pre_inst_state                   false
% 1.27/1.01  --bmc1_pre_inst_reach_state             false
% 1.27/1.01  --bmc1_out_unsat_core                   false
% 1.27/1.01  --bmc1_aig_witness_out                  false
% 1.27/1.01  --bmc1_verbose                          false
% 1.27/1.01  --bmc1_dump_clauses_tptp                false
% 1.27/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.27/1.01  --bmc1_dump_file                        -
% 1.27/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.27/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.27/1.01  --bmc1_ucm_extend_mode                  1
% 1.27/1.01  --bmc1_ucm_init_mode                    2
% 1.27/1.01  --bmc1_ucm_cone_mode                    none
% 1.27/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.27/1.01  --bmc1_ucm_relax_model                  4
% 1.27/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.27/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.27/1.01  --bmc1_ucm_layered_model                none
% 1.27/1.01  --bmc1_ucm_max_lemma_size               10
% 1.27/1.01  
% 1.27/1.01  ------ AIG Options
% 1.27/1.01  
% 1.27/1.01  --aig_mode                              false
% 1.27/1.01  
% 1.27/1.01  ------ Instantiation Options
% 1.27/1.01  
% 1.27/1.01  --instantiation_flag                    true
% 1.27/1.01  --inst_sos_flag                         false
% 1.27/1.01  --inst_sos_phase                        true
% 1.27/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.27/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.27/1.01  --inst_lit_sel_side                     none
% 1.27/1.01  --inst_solver_per_active                1400
% 1.27/1.01  --inst_solver_calls_frac                1.
% 1.27/1.01  --inst_passive_queue_type               priority_queues
% 1.27/1.01  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.27/1.01  --inst_passive_queues_freq              [25;2]
% 1.27/1.01  --inst_dismatching                      true
% 1.27/1.01  --inst_eager_unprocessed_to_passive     true
% 1.27/1.01  --inst_prop_sim_given                   true
% 1.27/1.01  --inst_prop_sim_new                     false
% 1.27/1.01  --inst_subs_new                         false
% 1.27/1.01  --inst_eq_res_simp                      false
% 1.27/1.01  --inst_subs_given                       false
% 1.27/1.01  --inst_orphan_elimination               true
% 1.27/1.01  --inst_learning_loop_flag               true
% 1.27/1.01  --inst_learning_start                   3000
% 1.27/1.01  --inst_learning_factor                  2
% 1.27/1.01  --inst_start_prop_sim_after_learn       3
% 1.27/1.01  --inst_sel_renew                        solver
% 1.27/1.01  --inst_lit_activity_flag                true
% 1.27/1.01  --inst_restr_to_given                   false
% 1.27/1.01  --inst_activity_threshold               500
% 1.27/1.01  --inst_out_proof                        true
% 1.27/1.01  
% 1.27/1.01  ------ Resolution Options
% 1.27/1.01  
% 1.27/1.01  --resolution_flag                       false
% 1.27/1.01  --res_lit_sel                           adaptive
% 1.27/1.01  --res_lit_sel_side                      none
% 1.27/1.01  --res_ordering                          kbo
% 1.27/1.01  --res_to_prop_solver                    active
% 1.27/1.01  --res_prop_simpl_new                    false
% 1.27/1.01  --res_prop_simpl_given                  true
% 1.27/1.01  --res_passive_queue_type                priority_queues
% 1.27/1.01  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.27/1.01  --res_passive_queues_freq               [15;5]
% 1.27/1.01  --res_forward_subs                      full
% 1.27/1.01  --res_backward_subs                     full
% 1.27/1.01  --res_forward_subs_resolution           true
% 1.27/1.01  --res_backward_subs_resolution          true
% 1.27/1.01  --res_orphan_elimination                true
% 1.27/1.01  --res_time_limit                        2.
% 1.27/1.01  --res_out_proof                         true
% 1.27/1.01  
% 1.27/1.01  ------ Superposition Options
% 1.27/1.01  
% 1.27/1.01  --superposition_flag                    true
% 1.27/1.01  --sup_passive_queue_type                priority_queues
% 1.27/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.27/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.27/1.01  --demod_completeness_check              fast
% 1.27/1.01  --demod_use_ground                      true
% 1.27/1.01  --sup_to_prop_solver                    passive
% 1.27/1.01  --sup_prop_simpl_new                    true
% 1.27/1.01  --sup_prop_simpl_given                  true
% 1.27/1.01  --sup_fun_splitting                     false
% 1.27/1.01  --sup_smt_interval                      50000
% 1.27/1.01  
% 1.27/1.01  ------ Superposition Simplification Setup
% 1.27/1.01  
% 1.27/1.01  --sup_indices_passive                   []
% 1.27/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.27/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.27/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.27/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.27/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.27/1.01  --sup_full_bw                           [BwDemod]
% 1.27/1.01  --sup_immed_triv                        [TrivRules]
% 1.27/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.27/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.27/1.01  --sup_immed_bw_main                     []
% 1.27/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.27/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.27/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.27/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.27/1.01  
% 1.27/1.01  ------ Combination Options
% 1.27/1.01  
% 1.27/1.01  --comb_res_mult                         3
% 1.27/1.01  --comb_sup_mult                         2
% 1.27/1.01  --comb_inst_mult                        10
% 1.27/1.01  
% 1.27/1.01  ------ Debug Options
% 1.27/1.01  
% 1.27/1.01  --dbg_backtrace                         false
% 1.27/1.01  --dbg_dump_prop_clauses                 false
% 1.27/1.01  --dbg_dump_prop_clauses_file            -
% 1.27/1.01  --dbg_out_stat                          false
% 1.27/1.01  
% 1.27/1.01  
% 1.27/1.01  
% 1.27/1.01  
% 1.27/1.01  ------ Proving...
% 1.27/1.01  
% 1.27/1.01  
% 1.27/1.01  % SZS status Theorem for theBenchmark.p
% 1.27/1.01  
% 1.27/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.27/1.01  
% 1.27/1.01  fof(f2,axiom,(
% 1.27/1.01    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 1.27/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.27/1.01  
% 1.27/1.01  fof(f40,plain,(
% 1.27/1.01    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.27/1.01    inference(cnf_transformation,[],[f2])).
% 1.27/1.01  
% 1.27/1.01  fof(f3,axiom,(
% 1.27/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.27/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.27/1.01  
% 1.27/1.01  fof(f13,plain,(
% 1.27/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.27/1.01    inference(ennf_transformation,[],[f3])).
% 1.27/1.01  
% 1.27/1.01  fof(f41,plain,(
% 1.27/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.27/1.01    inference(cnf_transformation,[],[f13])).
% 1.27/1.01  
% 1.27/1.01  fof(f4,axiom,(
% 1.27/1.01    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.27/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.27/1.01  
% 1.27/1.01  fof(f14,plain,(
% 1.27/1.01    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.27/1.01    inference(ennf_transformation,[],[f4])).
% 1.27/1.01  
% 1.27/1.01  fof(f26,plain,(
% 1.27/1.01    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 1.27/1.01    introduced(choice_axiom,[])).
% 1.27/1.01  
% 1.27/1.01  fof(f27,plain,(
% 1.27/1.01    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 1.27/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f26])).
% 1.27/1.01  
% 1.27/1.01  fof(f42,plain,(
% 1.27/1.01    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 1.27/1.01    inference(cnf_transformation,[],[f27])).
% 1.27/1.01  
% 1.27/1.01  fof(f9,axiom,(
% 1.27/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.27/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.27/1.01  
% 1.27/1.01  fof(f22,plain,(
% 1.27/1.01    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.27/1.01    inference(ennf_transformation,[],[f9])).
% 1.27/1.01  
% 1.27/1.01  fof(f23,plain,(
% 1.27/1.01    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.27/1.01    inference(flattening,[],[f22])).
% 1.27/1.01  
% 1.27/1.01  fof(f33,plain,(
% 1.27/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.27/1.01    inference(nnf_transformation,[],[f23])).
% 1.27/1.01  
% 1.27/1.01  fof(f54,plain,(
% 1.27/1.01    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.27/1.01    inference(cnf_transformation,[],[f33])).
% 1.27/1.01  
% 1.27/1.01  fof(f1,axiom,(
% 1.27/1.01    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 1.27/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.27/1.01  
% 1.27/1.01  fof(f12,plain,(
% 1.27/1.01    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 1.27/1.01    inference(ennf_transformation,[],[f1])).
% 1.27/1.01  
% 1.27/1.01  fof(f39,plain,(
% 1.27/1.01    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 1.27/1.01    inference(cnf_transformation,[],[f12])).
% 1.27/1.01  
% 1.27/1.01  fof(f10,conjecture,(
% 1.27/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.27/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.27/1.01  
% 1.27/1.01  fof(f11,negated_conjecture,(
% 1.27/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.27/1.01    inference(negated_conjecture,[],[f10])).
% 1.27/1.01  
% 1.27/1.01  fof(f24,plain,(
% 1.27/1.01    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.27/1.01    inference(ennf_transformation,[],[f11])).
% 1.27/1.01  
% 1.27/1.01  fof(f25,plain,(
% 1.27/1.01    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.27/1.01    inference(flattening,[],[f24])).
% 1.27/1.01  
% 1.27/1.01  fof(f34,plain,(
% 1.27/1.01    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.27/1.01    inference(nnf_transformation,[],[f25])).
% 1.27/1.01  
% 1.27/1.01  fof(f35,plain,(
% 1.27/1.01    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.27/1.01    inference(flattening,[],[f34])).
% 1.27/1.01  
% 1.27/1.01  fof(f37,plain,(
% 1.27/1.01    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,X0)) & (v1_zfmisc_1(sK3) | v3_tex_2(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK3))) )),
% 1.27/1.01    introduced(choice_axiom,[])).
% 1.27/1.01  
% 1.27/1.01  fof(f36,plain,(
% 1.27/1.01    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK2)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.27/1.01    introduced(choice_axiom,[])).
% 1.27/1.01  
% 1.27/1.01  fof(f38,plain,(
% 1.27/1.01    ((~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,sK2)) & (v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.27/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f35,f37,f36])).
% 1.27/1.01  
% 1.27/1.01  fof(f56,plain,(
% 1.27/1.01    ~v2_struct_0(sK2)),
% 1.27/1.01    inference(cnf_transformation,[],[f38])).
% 1.27/1.01  
% 1.27/1.01  fof(f57,plain,(
% 1.27/1.01    v2_pre_topc(sK2)),
% 1.27/1.01    inference(cnf_transformation,[],[f38])).
% 1.27/1.01  
% 1.27/1.01  fof(f58,plain,(
% 1.27/1.01    v2_tdlat_3(sK2)),
% 1.27/1.01    inference(cnf_transformation,[],[f38])).
% 1.27/1.01  
% 1.27/1.01  fof(f59,plain,(
% 1.27/1.01    l1_pre_topc(sK2)),
% 1.27/1.01    inference(cnf_transformation,[],[f38])).
% 1.27/1.01  
% 1.27/1.01  fof(f63,plain,(
% 1.27/1.01    ~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,sK2)),
% 1.27/1.01    inference(cnf_transformation,[],[f38])).
% 1.27/1.01  
% 1.27/1.01  fof(f61,plain,(
% 1.27/1.01    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.27/1.01    inference(cnf_transformation,[],[f38])).
% 1.27/1.01  
% 1.27/1.01  fof(f8,axiom,(
% 1.27/1.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.27/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.27/1.01  
% 1.27/1.01  fof(f20,plain,(
% 1.27/1.01    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.27/1.01    inference(ennf_transformation,[],[f8])).
% 1.27/1.01  
% 1.27/1.01  fof(f21,plain,(
% 1.27/1.01    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.27/1.01    inference(flattening,[],[f20])).
% 1.27/1.01  
% 1.27/1.01  fof(f53,plain,(
% 1.27/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.27/1.01    inference(cnf_transformation,[],[f21])).
% 1.27/1.01  
% 1.27/1.01  fof(f6,axiom,(
% 1.27/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.27/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.27/1.01  
% 1.27/1.01  fof(f17,plain,(
% 1.27/1.01    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.27/1.01    inference(ennf_transformation,[],[f6])).
% 1.27/1.01  
% 1.27/1.01  fof(f18,plain,(
% 1.27/1.01    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.27/1.01    inference(flattening,[],[f17])).
% 1.27/1.01  
% 1.27/1.01  fof(f28,plain,(
% 1.27/1.01    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.27/1.01    inference(nnf_transformation,[],[f18])).
% 1.27/1.01  
% 1.27/1.01  fof(f29,plain,(
% 1.27/1.01    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.27/1.01    inference(flattening,[],[f28])).
% 1.27/1.01  
% 1.27/1.01  fof(f30,plain,(
% 1.27/1.01    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.27/1.01    inference(rectify,[],[f29])).
% 1.27/1.01  
% 1.27/1.01  fof(f31,plain,(
% 1.27/1.01    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.27/1.01    introduced(choice_axiom,[])).
% 1.27/1.01  
% 1.27/1.01  fof(f32,plain,(
% 1.27/1.01    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.27/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 1.27/1.01  
% 1.27/1.01  fof(f50,plain,(
% 1.27/1.01    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK1(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.27/1.01    inference(cnf_transformation,[],[f32])).
% 1.27/1.01  
% 1.27/1.01  fof(f51,plain,(
% 1.27/1.01    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK1(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.27/1.01    inference(cnf_transformation,[],[f32])).
% 1.27/1.01  
% 1.27/1.01  fof(f48,plain,(
% 1.27/1.01    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.27/1.01    inference(cnf_transformation,[],[f32])).
% 1.27/1.01  
% 1.27/1.01  fof(f49,plain,(
% 1.27/1.01    ( ! [X0,X1] : (v3_tex_2(X1,X0) | v2_tex_2(sK1(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.27/1.01    inference(cnf_transformation,[],[f32])).
% 1.27/1.01  
% 1.27/1.01  fof(f60,plain,(
% 1.27/1.01    ~v1_xboole_0(sK3)),
% 1.27/1.01    inference(cnf_transformation,[],[f38])).
% 1.27/1.01  
% 1.27/1.01  fof(f55,plain,(
% 1.27/1.01    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.27/1.01    inference(cnf_transformation,[],[f33])).
% 1.27/1.01  
% 1.27/1.01  fof(f62,plain,(
% 1.27/1.01    v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2)),
% 1.27/1.01    inference(cnf_transformation,[],[f38])).
% 1.27/1.01  
% 1.27/1.01  fof(f46,plain,(
% 1.27/1.01    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.27/1.01    inference(cnf_transformation,[],[f32])).
% 1.27/1.01  
% 1.27/1.01  fof(f7,axiom,(
% 1.27/1.01    ! [X0,X1] : ~(k6_subset_1(X1,X0) = k1_xboole_0 & X0 != X1 & r1_tarski(X0,X1))),
% 1.27/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.27/1.01  
% 1.27/1.01  fof(f19,plain,(
% 1.27/1.01    ! [X0,X1] : (k6_subset_1(X1,X0) != k1_xboole_0 | X0 = X1 | ~r1_tarski(X0,X1))),
% 1.27/1.01    inference(ennf_transformation,[],[f7])).
% 1.27/1.01  
% 1.27/1.01  fof(f52,plain,(
% 1.27/1.01    ( ! [X0,X1] : (k6_subset_1(X1,X0) != k1_xboole_0 | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.27/1.01    inference(cnf_transformation,[],[f19])).
% 1.27/1.01  
% 1.27/1.01  cnf(c_1,plain,
% 1.27/1.01      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
% 1.27/1.01      inference(cnf_transformation,[],[f40]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_2,plain,
% 1.27/1.01      ( ~ r2_hidden(X0,X1)
% 1.27/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.27/1.01      | ~ v1_xboole_0(X2) ),
% 1.27/1.01      inference(cnf_transformation,[],[f41]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_5,plain,
% 1.27/1.01      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 1.27/1.01      inference(cnf_transformation,[],[f42]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_354,plain,
% 1.27/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.27/1.01      | ~ v1_xboole_0(X1)
% 1.27/1.01      | X2 != X0
% 1.27/1.01      | sK0(X2) != X3
% 1.27/1.01      | k1_xboole_0 = X2 ),
% 1.27/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_5]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_355,plain,
% 1.27/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.27/1.01      | ~ v1_xboole_0(X1)
% 1.27/1.01      | k1_xboole_0 = X0 ),
% 1.27/1.01      inference(unflattening,[status(thm)],[c_354]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_16,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,X1)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.27/1.01      | v2_struct_0(X1)
% 1.27/1.01      | ~ l1_pre_topc(X1)
% 1.27/1.01      | ~ v2_tdlat_3(X1)
% 1.27/1.01      | ~ v2_pre_topc(X1)
% 1.27/1.01      | v1_xboole_0(X0)
% 1.27/1.01      | v1_zfmisc_1(X0) ),
% 1.27/1.01      inference(cnf_transformation,[],[f54]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_0,plain,
% 1.27/1.01      ( ~ v1_xboole_0(X0) | v1_zfmisc_1(X0) ),
% 1.27/1.01      inference(cnf_transformation,[],[f39]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_139,plain,
% 1.27/1.01      ( ~ v2_pre_topc(X1)
% 1.27/1.01      | ~ v2_tdlat_3(X1)
% 1.27/1.01      | ~ l1_pre_topc(X1)
% 1.27/1.01      | v2_struct_0(X1)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.27/1.01      | ~ v2_tex_2(X0,X1)
% 1.27/1.01      | v1_zfmisc_1(X0) ),
% 1.27/1.01      inference(global_propositional_subsumption,
% 1.27/1.01                [status(thm)],
% 1.27/1.01                [c_16,c_0]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_140,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,X1)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.27/1.01      | v2_struct_0(X1)
% 1.27/1.01      | ~ l1_pre_topc(X1)
% 1.27/1.01      | ~ v2_tdlat_3(X1)
% 1.27/1.01      | ~ v2_pre_topc(X1)
% 1.27/1.01      | v1_zfmisc_1(X0) ),
% 1.27/1.01      inference(renaming,[status(thm)],[c_139]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_24,negated_conjecture,
% 1.27/1.01      ( ~ v2_struct_0(sK2) ),
% 1.27/1.01      inference(cnf_transformation,[],[f56]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_377,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,X1)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.27/1.01      | ~ l1_pre_topc(X1)
% 1.27/1.01      | ~ v2_tdlat_3(X1)
% 1.27/1.01      | ~ v2_pre_topc(X1)
% 1.27/1.01      | v1_zfmisc_1(X0)
% 1.27/1.01      | sK2 != X1 ),
% 1.27/1.01      inference(resolution_lifted,[status(thm)],[c_140,c_24]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_378,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | ~ l1_pre_topc(sK2)
% 1.27/1.01      | ~ v2_tdlat_3(sK2)
% 1.27/1.01      | ~ v2_pre_topc(sK2)
% 1.27/1.01      | v1_zfmisc_1(X0) ),
% 1.27/1.01      inference(unflattening,[status(thm)],[c_377]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_23,negated_conjecture,
% 1.27/1.01      ( v2_pre_topc(sK2) ),
% 1.27/1.01      inference(cnf_transformation,[],[f57]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_22,negated_conjecture,
% 1.27/1.01      ( v2_tdlat_3(sK2) ),
% 1.27/1.01      inference(cnf_transformation,[],[f58]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_21,negated_conjecture,
% 1.27/1.01      ( l1_pre_topc(sK2) ),
% 1.27/1.01      inference(cnf_transformation,[],[f59]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_382,plain,
% 1.27/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | ~ v2_tex_2(X0,sK2)
% 1.27/1.01      | v1_zfmisc_1(X0) ),
% 1.27/1.01      inference(global_propositional_subsumption,
% 1.27/1.01                [status(thm)],
% 1.27/1.01                [c_378,c_23,c_22,c_21]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_383,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | v1_zfmisc_1(X0) ),
% 1.27/1.01      inference(renaming,[status(thm)],[c_382]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_17,negated_conjecture,
% 1.27/1.01      ( ~ v3_tex_2(sK3,sK2) | ~ v1_zfmisc_1(sK3) ),
% 1.27/1.01      inference(cnf_transformation,[],[f63]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_190,plain,
% 1.27/1.01      ( ~ v1_zfmisc_1(sK3) | ~ v3_tex_2(sK3,sK2) ),
% 1.27/1.01      inference(prop_impl,[status(thm)],[c_17]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_191,plain,
% 1.27/1.01      ( ~ v3_tex_2(sK3,sK2) | ~ v1_zfmisc_1(sK3) ),
% 1.27/1.01      inference(renaming,[status(thm)],[c_190]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_760,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,sK2)
% 1.27/1.01      | ~ v3_tex_2(sK3,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | sK3 != X0 ),
% 1.27/1.01      inference(resolution_lifted,[status(thm)],[c_383,c_191]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_761,plain,
% 1.27/1.01      ( ~ v2_tex_2(sK3,sK2)
% 1.27/1.01      | ~ v3_tex_2(sK3,sK2)
% 1.27/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.27/1.01      inference(unflattening,[status(thm)],[c_760]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_19,negated_conjecture,
% 1.27/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.27/1.01      inference(cnf_transformation,[],[f61]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_763,plain,
% 1.27/1.01      ( ~ v3_tex_2(sK3,sK2) | ~ v2_tex_2(sK3,sK2) ),
% 1.27/1.01      inference(global_propositional_subsumption,
% 1.27/1.01                [status(thm)],
% 1.27/1.01                [c_761,c_19]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_764,plain,
% 1.27/1.01      ( ~ v2_tex_2(sK3,sK2) | ~ v3_tex_2(sK3,sK2) ),
% 1.27/1.01      inference(renaming,[status(thm)],[c_763]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_14,plain,
% 1.27/1.01      ( ~ r1_tarski(X0,X1)
% 1.27/1.01      | v1_xboole_0(X0)
% 1.27/1.01      | v1_xboole_0(X1)
% 1.27/1.01      | ~ v1_zfmisc_1(X1)
% 1.27/1.01      | X1 = X0 ),
% 1.27/1.01      inference(cnf_transformation,[],[f53]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_8,plain,
% 1.27/1.01      ( r1_tarski(X0,sK1(X1,X0))
% 1.27/1.01      | ~ v2_tex_2(X0,X1)
% 1.27/1.01      | v3_tex_2(X0,X1)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.27/1.01      | ~ l1_pre_topc(X1) ),
% 1.27/1.01      inference(cnf_transformation,[],[f50]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_598,plain,
% 1.27/1.01      ( r1_tarski(X0,sK1(X1,X0))
% 1.27/1.01      | ~ v2_tex_2(X0,X1)
% 1.27/1.01      | v3_tex_2(X0,X1)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.27/1.01      | sK2 != X1 ),
% 1.27/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_599,plain,
% 1.27/1.01      ( r1_tarski(X0,sK1(sK2,X0))
% 1.27/1.01      | ~ v2_tex_2(X0,sK2)
% 1.27/1.01      | v3_tex_2(X0,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.27/1.01      inference(unflattening,[status(thm)],[c_598]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_691,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,sK2)
% 1.27/1.01      | v3_tex_2(X0,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | v1_xboole_0(X1)
% 1.27/1.01      | v1_xboole_0(X2)
% 1.27/1.01      | ~ v1_zfmisc_1(X2)
% 1.27/1.01      | X0 != X1
% 1.27/1.01      | X2 = X1
% 1.27/1.01      | sK1(sK2,X0) != X2 ),
% 1.27/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_599]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_692,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,sK2)
% 1.27/1.01      | v3_tex_2(X0,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | v1_xboole_0(X0)
% 1.27/1.01      | v1_xboole_0(sK1(sK2,X0))
% 1.27/1.01      | ~ v1_zfmisc_1(sK1(sK2,X0))
% 1.27/1.01      | sK1(sK2,X0) = X0 ),
% 1.27/1.01      inference(unflattening,[status(thm)],[c_691]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_7,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,X1)
% 1.27/1.01      | v3_tex_2(X0,X1)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.27/1.01      | ~ l1_pre_topc(X1)
% 1.27/1.01      | sK1(X1,X0) != X0 ),
% 1.27/1.01      inference(cnf_transformation,[],[f51]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_616,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,X1)
% 1.27/1.01      | v3_tex_2(X0,X1)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.27/1.01      | sK1(X1,X0) != X0
% 1.27/1.01      | sK2 != X1 ),
% 1.27/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_617,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,sK2)
% 1.27/1.01      | v3_tex_2(X0,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | sK1(sK2,X0) != X0 ),
% 1.27/1.01      inference(unflattening,[status(thm)],[c_616]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_696,plain,
% 1.27/1.01      ( ~ v1_zfmisc_1(sK1(sK2,X0))
% 1.27/1.01      | v1_xboole_0(sK1(sK2,X0))
% 1.27/1.01      | v1_xboole_0(X0)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | v3_tex_2(X0,sK2)
% 1.27/1.01      | ~ v2_tex_2(X0,sK2) ),
% 1.27/1.01      inference(global_propositional_subsumption,
% 1.27/1.01                [status(thm)],
% 1.27/1.01                [c_692,c_617]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_697,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,sK2)
% 1.27/1.01      | v3_tex_2(X0,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | v1_xboole_0(X0)
% 1.27/1.01      | v1_xboole_0(sK1(sK2,X0))
% 1.27/1.01      | ~ v1_zfmisc_1(sK1(sK2,X0)) ),
% 1.27/1.01      inference(renaming,[status(thm)],[c_696]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_790,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,sK2)
% 1.27/1.01      | ~ v2_tex_2(X1,sK2)
% 1.27/1.01      | v3_tex_2(X1,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | v1_xboole_0(X1)
% 1.27/1.01      | v1_xboole_0(sK1(sK2,X1))
% 1.27/1.01      | sK1(sK2,X1) != X0 ),
% 1.27/1.01      inference(resolution_lifted,[status(thm)],[c_383,c_697]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_791,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,sK2)
% 1.27/1.01      | ~ v2_tex_2(sK1(sK2,X0),sK2)
% 1.27/1.01      | v3_tex_2(X0,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | ~ m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | v1_xboole_0(X0)
% 1.27/1.01      | v1_xboole_0(sK1(sK2,X0)) ),
% 1.27/1.01      inference(unflattening,[status(thm)],[c_790]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_10,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,X1)
% 1.27/1.01      | v3_tex_2(X0,X1)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.27/1.01      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.27/1.01      | ~ l1_pre_topc(X1) ),
% 1.27/1.01      inference(cnf_transformation,[],[f48]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_562,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,X1)
% 1.27/1.01      | v3_tex_2(X0,X1)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.27/1.01      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.27/1.01      | sK2 != X1 ),
% 1.27/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_563,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,sK2)
% 1.27/1.01      | v3_tex_2(X0,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.27/1.01      inference(unflattening,[status(thm)],[c_562]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_9,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,X1)
% 1.27/1.01      | v2_tex_2(sK1(X1,X0),X1)
% 1.27/1.01      | v3_tex_2(X0,X1)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.27/1.01      | ~ l1_pre_topc(X1) ),
% 1.27/1.01      inference(cnf_transformation,[],[f49]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_580,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,X1)
% 1.27/1.01      | v2_tex_2(sK1(X1,X0),X1)
% 1.27/1.01      | v3_tex_2(X0,X1)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.27/1.01      | sK2 != X1 ),
% 1.27/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_581,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,sK2)
% 1.27/1.01      | v2_tex_2(sK1(sK2,X0),sK2)
% 1.27/1.01      | v3_tex_2(X0,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.27/1.01      inference(unflattening,[status(thm)],[c_580]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_795,plain,
% 1.27/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | v3_tex_2(X0,sK2)
% 1.27/1.01      | ~ v2_tex_2(X0,sK2)
% 1.27/1.01      | v1_xboole_0(X0)
% 1.27/1.01      | v1_xboole_0(sK1(sK2,X0)) ),
% 1.27/1.01      inference(global_propositional_subsumption,
% 1.27/1.01                [status(thm)],
% 1.27/1.01                [c_791,c_563,c_581]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_796,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,sK2)
% 1.27/1.01      | v3_tex_2(X0,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | v1_xboole_0(X0)
% 1.27/1.01      | v1_xboole_0(sK1(sK2,X0)) ),
% 1.27/1.01      inference(renaming,[status(thm)],[c_795]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_854,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,sK2)
% 1.27/1.01      | ~ v2_tex_2(sK3,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | v1_xboole_0(X0)
% 1.27/1.01      | v1_xboole_0(sK1(sK2,X0))
% 1.27/1.01      | sK2 != sK2
% 1.27/1.01      | sK3 != X0 ),
% 1.27/1.01      inference(resolution_lifted,[status(thm)],[c_764,c_796]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_855,plain,
% 1.27/1.01      ( ~ v2_tex_2(sK3,sK2)
% 1.27/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | v1_xboole_0(sK1(sK2,sK3))
% 1.27/1.01      | v1_xboole_0(sK3) ),
% 1.27/1.01      inference(unflattening,[status(thm)],[c_854]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_20,negated_conjecture,
% 1.27/1.01      ( ~ v1_xboole_0(sK3) ),
% 1.27/1.01      inference(cnf_transformation,[],[f60]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_15,plain,
% 1.27/1.01      ( v2_tex_2(X0,X1)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.27/1.01      | v2_struct_0(X1)
% 1.27/1.01      | ~ l1_pre_topc(X1)
% 1.27/1.01      | ~ v2_tdlat_3(X1)
% 1.27/1.01      | ~ v2_pre_topc(X1)
% 1.27/1.01      | v1_xboole_0(X0)
% 1.27/1.01      | ~ v1_zfmisc_1(X0) ),
% 1.27/1.01      inference(cnf_transformation,[],[f55]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_398,plain,
% 1.27/1.01      ( v2_tex_2(X0,X1)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.27/1.01      | ~ l1_pre_topc(X1)
% 1.27/1.01      | ~ v2_tdlat_3(X1)
% 1.27/1.01      | ~ v2_pre_topc(X1)
% 1.27/1.01      | v1_xboole_0(X0)
% 1.27/1.01      | ~ v1_zfmisc_1(X0)
% 1.27/1.01      | sK2 != X1 ),
% 1.27/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_399,plain,
% 1.27/1.01      ( v2_tex_2(X0,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | ~ l1_pre_topc(sK2)
% 1.27/1.01      | ~ v2_tdlat_3(sK2)
% 1.27/1.01      | ~ v2_pre_topc(sK2)
% 1.27/1.01      | v1_xboole_0(X0)
% 1.27/1.01      | ~ v1_zfmisc_1(X0) ),
% 1.27/1.01      inference(unflattening,[status(thm)],[c_398]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_403,plain,
% 1.27/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | v2_tex_2(X0,sK2)
% 1.27/1.01      | v1_xboole_0(X0)
% 1.27/1.01      | ~ v1_zfmisc_1(X0) ),
% 1.27/1.01      inference(global_propositional_subsumption,
% 1.27/1.01                [status(thm)],
% 1.27/1.01                [c_399,c_23,c_22,c_21]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_404,plain,
% 1.27/1.01      ( v2_tex_2(X0,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | v1_xboole_0(X0)
% 1.27/1.01      | ~ v1_zfmisc_1(X0) ),
% 1.27/1.01      inference(renaming,[status(thm)],[c_403]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_18,negated_conjecture,
% 1.27/1.01      ( v3_tex_2(sK3,sK2) | v1_zfmisc_1(sK3) ),
% 1.27/1.01      inference(cnf_transformation,[],[f62]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_192,plain,
% 1.27/1.01      ( v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2) ),
% 1.27/1.01      inference(prop_impl,[status(thm)],[c_18]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_193,plain,
% 1.27/1.01      ( v3_tex_2(sK3,sK2) | v1_zfmisc_1(sK3) ),
% 1.27/1.01      inference(renaming,[status(thm)],[c_192]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_776,plain,
% 1.27/1.01      ( v2_tex_2(X0,sK2)
% 1.27/1.01      | v3_tex_2(sK3,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | v1_xboole_0(X0)
% 1.27/1.01      | sK3 != X0 ),
% 1.27/1.01      inference(resolution_lifted,[status(thm)],[c_404,c_193]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_777,plain,
% 1.27/1.01      ( v2_tex_2(sK3,sK2)
% 1.27/1.01      | v3_tex_2(sK3,sK2)
% 1.27/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | v1_xboole_0(sK3) ),
% 1.27/1.01      inference(unflattening,[status(thm)],[c_776]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_779,plain,
% 1.27/1.01      ( v2_tex_2(sK3,sK2) | v3_tex_2(sK3,sK2) ),
% 1.27/1.01      inference(global_propositional_subsumption,
% 1.27/1.01                [status(thm)],
% 1.27/1.01                [c_777,c_20,c_19]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_12,plain,
% 1.27/1.01      ( v2_tex_2(X0,X1)
% 1.27/1.01      | ~ v3_tex_2(X0,X1)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.27/1.01      | ~ l1_pre_topc(X1) ),
% 1.27/1.01      inference(cnf_transformation,[],[f46]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_547,plain,
% 1.27/1.01      ( v2_tex_2(X0,X1)
% 1.27/1.01      | ~ v3_tex_2(X0,X1)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.27/1.01      | sK2 != X1 ),
% 1.27/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_548,plain,
% 1.27/1.01      ( v2_tex_2(X0,sK2)
% 1.27/1.01      | ~ v3_tex_2(X0,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.27/1.01      inference(unflattening,[status(thm)],[c_547]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_843,plain,
% 1.27/1.01      ( v2_tex_2(X0,sK2)
% 1.27/1.01      | v2_tex_2(sK3,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | sK2 != sK2
% 1.27/1.01      | sK3 != X0 ),
% 1.27/1.01      inference(resolution_lifted,[status(thm)],[c_779,c_548]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_844,plain,
% 1.27/1.01      ( v2_tex_2(sK3,sK2)
% 1.27/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.27/1.01      inference(unflattening,[status(thm)],[c_843]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_857,plain,
% 1.27/1.01      ( v1_xboole_0(sK1(sK2,sK3)) ),
% 1.27/1.01      inference(global_propositional_subsumption,
% 1.27/1.01                [status(thm)],
% 1.27/1.01                [c_855,c_20,c_19,c_844]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_913,plain,
% 1.27/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.27/1.01      | sK1(sK2,sK3) != X1
% 1.27/1.01      | k1_xboole_0 = X0 ),
% 1.27/1.01      inference(resolution_lifted,[status(thm)],[c_355,c_857]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_914,plain,
% 1.27/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK2,sK3))) | k1_xboole_0 = X0 ),
% 1.27/1.01      inference(unflattening,[status(thm)],[c_913]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_929,plain,
% 1.27/1.01      ( k6_subset_1(X0,X1) != X2
% 1.27/1.01      | k1_zfmisc_1(sK1(sK2,sK3)) != k1_zfmisc_1(X0)
% 1.27/1.01      | k1_xboole_0 = X2 ),
% 1.27/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_914]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_930,plain,
% 1.27/1.01      ( k1_zfmisc_1(sK1(sK2,sK3)) != k1_zfmisc_1(X0)
% 1.27/1.01      | k1_xboole_0 = k6_subset_1(X0,X1) ),
% 1.27/1.01      inference(unflattening,[status(thm)],[c_929]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_1004,plain,
% 1.27/1.01      ( k1_zfmisc_1(sK1(sK2,sK3)) != k1_zfmisc_1(sK1(sK2,sK3))
% 1.27/1.01      | k1_xboole_0 = k6_subset_1(sK1(sK2,sK3),X0) ),
% 1.27/1.01      inference(instantiation,[status(thm)],[c_930]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_1052,plain,
% 1.27/1.01      ( k1_zfmisc_1(sK1(sK2,sK3)) != k1_zfmisc_1(sK1(sK2,sK3))
% 1.27/1.01      | k1_xboole_0 = k6_subset_1(sK1(sK2,sK3),sK3) ),
% 1.27/1.01      inference(instantiation,[status(thm)],[c_1004]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_967,plain,( X0 = X0 ),theory(equality) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_1028,plain,
% 1.27/1.01      ( k6_subset_1(sK1(sK2,sK3),sK3) = k6_subset_1(sK1(sK2,sK3),sK3) ),
% 1.27/1.01      inference(instantiation,[status(thm)],[c_967]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_968,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_1013,plain,
% 1.27/1.01      ( k6_subset_1(sK1(sK2,sK3),sK3) != X0
% 1.27/1.01      | k6_subset_1(sK1(sK2,sK3),sK3) = k1_xboole_0
% 1.27/1.01      | k1_xboole_0 != X0 ),
% 1.27/1.01      inference(instantiation,[status(thm)],[c_968]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_1027,plain,
% 1.27/1.01      ( k6_subset_1(sK1(sK2,sK3),sK3) != k6_subset_1(sK1(sK2,sK3),sK3)
% 1.27/1.01      | k6_subset_1(sK1(sK2,sK3),sK3) = k1_xboole_0
% 1.27/1.01      | k1_xboole_0 != k6_subset_1(sK1(sK2,sK3),sK3) ),
% 1.27/1.01      inference(instantiation,[status(thm)],[c_1013]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_1005,plain,
% 1.27/1.01      ( k1_zfmisc_1(sK1(sK2,sK3)) = k1_zfmisc_1(sK1(sK2,sK3)) ),
% 1.27/1.01      inference(instantiation,[status(thm)],[c_967]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_13,plain,
% 1.27/1.01      ( ~ r1_tarski(X0,X1)
% 1.27/1.01      | X1 = X0
% 1.27/1.01      | k6_subset_1(X1,X0) != k1_xboole_0 ),
% 1.27/1.01      inference(cnf_transformation,[],[f52]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_721,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,sK2)
% 1.27/1.01      | v3_tex_2(X0,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | X0 != X1
% 1.27/1.01      | X2 = X1
% 1.27/1.01      | sK1(sK2,X0) != X2
% 1.27/1.01      | k6_subset_1(X2,X1) != k1_xboole_0 ),
% 1.27/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_599]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_722,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,sK2)
% 1.27/1.01      | v3_tex_2(X0,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | sK1(sK2,X0) = X0
% 1.27/1.01      | k6_subset_1(sK1(sK2,X0),X0) != k1_xboole_0 ),
% 1.27/1.01      inference(unflattening,[status(thm)],[c_721]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_726,plain,
% 1.27/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | v3_tex_2(X0,sK2)
% 1.27/1.01      | ~ v2_tex_2(X0,sK2)
% 1.27/1.01      | k6_subset_1(sK1(sK2,X0),X0) != k1_xboole_0 ),
% 1.27/1.01      inference(global_propositional_subsumption,
% 1.27/1.01                [status(thm)],
% 1.27/1.01                [c_722,c_617]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_727,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,sK2)
% 1.27/1.01      | v3_tex_2(X0,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | k6_subset_1(sK1(sK2,X0),X0) != k1_xboole_0 ),
% 1.27/1.01      inference(renaming,[status(thm)],[c_726]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_865,plain,
% 1.27/1.01      ( ~ v2_tex_2(X0,sK2)
% 1.27/1.01      | ~ v2_tex_2(sK3,sK2)
% 1.27/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | k6_subset_1(sK1(sK2,X0),X0) != k1_xboole_0
% 1.27/1.01      | sK2 != sK2
% 1.27/1.01      | sK3 != X0 ),
% 1.27/1.01      inference(resolution_lifted,[status(thm)],[c_764,c_727]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(c_866,plain,
% 1.27/1.01      ( ~ v2_tex_2(sK3,sK2)
% 1.27/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.27/1.01      | k6_subset_1(sK1(sK2,sK3),sK3) != k1_xboole_0 ),
% 1.27/1.01      inference(unflattening,[status(thm)],[c_865]) ).
% 1.27/1.01  
% 1.27/1.01  cnf(contradiction,plain,
% 1.27/1.01      ( $false ),
% 1.27/1.01      inference(minisat,
% 1.27/1.01                [status(thm)],
% 1.27/1.01                [c_1052,c_1028,c_1027,c_1005,c_866,c_844,c_19]) ).
% 1.27/1.01  
% 1.27/1.01  
% 1.27/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.27/1.01  
% 1.27/1.01  ------                               Statistics
% 1.27/1.01  
% 1.27/1.01  ------ General
% 1.27/1.01  
% 1.27/1.01  abstr_ref_over_cycles:                  0
% 1.27/1.01  abstr_ref_under_cycles:                 0
% 1.27/1.01  gc_basic_clause_elim:                   0
% 1.27/1.01  forced_gc_time:                         0
% 1.27/1.01  parsing_time:                           0.011
% 1.27/1.01  unif_index_cands_time:                  0.
% 1.27/1.01  unif_index_add_time:                    0.
% 1.27/1.01  orderings_time:                         0.
% 1.27/1.01  out_proof_time:                         0.014
% 1.27/1.01  total_time:                             0.071
% 1.27/1.01  num_of_symbols:                         51
% 1.27/1.01  num_of_terms:                           809
% 1.27/1.01  
% 1.27/1.01  ------ Preprocessing
% 1.27/1.01  
% 1.27/1.01  num_of_splits:                          0
% 1.27/1.01  num_of_split_atoms:                     0
% 1.27/1.01  num_of_reused_defs:                     0
% 1.27/1.01  num_eq_ax_congr_red:                    15
% 1.27/1.01  num_of_sem_filtered_clauses:            0
% 1.27/1.01  num_of_subtypes:                        0
% 1.27/1.01  monotx_restored_types:                  0
% 1.27/1.01  sat_num_of_epr_types:                   0
% 1.27/1.01  sat_num_of_non_cyclic_types:            0
% 1.27/1.01  sat_guarded_non_collapsed_types:        0
% 1.27/1.01  num_pure_diseq_elim:                    0
% 1.27/1.01  simp_replaced_by:                       0
% 1.27/1.01  res_preprocessed:                       46
% 1.27/1.01  prep_upred:                             0
% 1.27/1.01  prep_unflattend:                        41
% 1.27/1.01  smt_new_axioms:                         0
% 1.27/1.01  pred_elim_cands:                        0
% 1.27/1.01  pred_elim:                              11
% 1.27/1.01  pred_elim_cl:                           18
% 1.27/1.01  pred_elim_cycles:                       13
% 1.27/1.01  merged_defs:                            2
% 1.27/1.01  merged_defs_ncl:                        0
% 1.27/1.01  bin_hyper_res:                          2
% 1.27/1.01  prep_cycles:                            3
% 1.27/1.01  pred_elim_time:                         0.012
% 1.27/1.01  splitting_time:                         0.
% 1.27/1.01  sem_filter_time:                        0.
% 1.27/1.01  monotx_time:                            0.
% 1.27/1.01  subtype_inf_time:                       0.
% 1.27/1.01  
% 1.27/1.01  ------ Problem properties
% 1.27/1.01  
% 1.27/1.01  clauses:                                7
% 1.27/1.01  conjectures:                            0
% 1.27/1.01  epr:                                    0
% 1.27/1.01  horn:                                   7
% 1.27/1.01  ground:                                 4
% 1.27/1.01  unary:                                  2
% 1.27/1.01  binary:                                 5
% 1.27/1.01  lits:                                   12
% 1.27/1.01  lits_eq:                                12
% 1.27/1.01  fd_pure:                                0
% 1.27/1.01  fd_pseudo:                              0
% 1.27/1.01  fd_cond:                                2
% 1.27/1.01  fd_pseudo_cond:                         0
% 1.27/1.01  ac_symbols:                             0
% 1.27/1.01  
% 1.27/1.01  ------ Propositional Solver
% 1.27/1.01  
% 1.27/1.01  prop_solver_calls:                      20
% 1.27/1.01  prop_fast_solver_calls:                 444
% 1.27/1.01  smt_solver_calls:                       0
% 1.27/1.01  smt_fast_solver_calls:                  0
% 1.27/1.01  prop_num_of_clauses:                    261
% 1.27/1.01  prop_preprocess_simplified:             1211
% 1.27/1.01  prop_fo_subsumed:                       31
% 1.27/1.01  prop_solver_time:                       0.
% 1.27/1.01  smt_solver_time:                        0.
% 1.27/1.01  smt_fast_solver_time:                   0.
% 1.27/1.01  prop_fast_solver_time:                  0.
% 1.27/1.01  prop_unsat_core_time:                   0.
% 1.27/1.01  
% 1.27/1.01  ------ QBF
% 1.27/1.01  
% 1.27/1.01  qbf_q_res:                              0
% 1.27/1.01  qbf_num_tautologies:                    0
% 1.27/1.01  qbf_prep_cycles:                        0
% 1.27/1.01  
% 1.27/1.01  ------ BMC1
% 1.27/1.01  
% 1.27/1.01  bmc1_current_bound:                     -1
% 1.27/1.01  bmc1_last_solved_bound:                 -1
% 1.27/1.01  bmc1_unsat_core_size:                   -1
% 1.27/1.01  bmc1_unsat_core_parents_size:           -1
% 1.27/1.01  bmc1_merge_next_fun:                    0
% 1.27/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.27/1.01  
% 1.27/1.01  ------ Instantiation
% 1.27/1.01  
% 1.27/1.01  inst_num_of_clauses:                    34
% 1.27/1.01  inst_num_in_passive:                    10
% 1.27/1.01  inst_num_in_active:                     20
% 1.27/1.01  inst_num_in_unprocessed:                3
% 1.27/1.01  inst_num_of_loops:                      22
% 1.27/1.01  inst_num_of_learning_restarts:          0
% 1.27/1.01  inst_num_moves_active_passive:          0
% 1.27/1.01  inst_lit_activity:                      0
% 1.27/1.01  inst_lit_activity_moves:                0
% 1.27/1.01  inst_num_tautologies:                   0
% 1.27/1.01  inst_num_prop_implied:                  0
% 1.27/1.01  inst_num_existing_simplified:           0
% 1.27/1.01  inst_num_eq_res_simplified:             0
% 1.27/1.01  inst_num_child_elim:                    0
% 1.27/1.01  inst_num_of_dismatching_blockings:      2
% 1.27/1.01  inst_num_of_non_proper_insts:           14
% 1.27/1.01  inst_num_of_duplicates:                 0
% 1.27/1.01  inst_inst_num_from_inst_to_res:         0
% 1.27/1.01  inst_dismatching_checking_time:         0.
% 1.27/1.01  
% 1.27/1.01  ------ Resolution
% 1.27/1.01  
% 1.27/1.01  res_num_of_clauses:                     0
% 1.27/1.01  res_num_in_passive:                     0
% 1.27/1.01  res_num_in_active:                      0
% 1.27/1.01  res_num_of_loops:                       49
% 1.27/1.01  res_forward_subset_subsumed:            4
% 1.27/1.01  res_backward_subset_subsumed:           0
% 1.27/1.01  res_forward_subsumed:                   1
% 1.27/1.01  res_backward_subsumed:                  0
% 1.27/1.01  res_forward_subsumption_resolution:     0
% 1.27/1.01  res_backward_subsumption_resolution:    0
% 1.27/1.01  res_clause_to_clause_subsumption:       21
% 1.27/1.01  res_orphan_elimination:                 0
% 1.27/1.01  res_tautology_del:                      15
% 1.27/1.01  res_num_eq_res_simplified:              0
% 1.27/1.01  res_num_sel_changes:                    0
% 1.27/1.01  res_moves_from_active_to_pass:          0
% 1.27/1.01  
% 1.27/1.01  ------ Superposition
% 1.27/1.01  
% 1.27/1.01  sup_time_total:                         0.
% 1.27/1.01  sup_time_generating:                    0.
% 1.27/1.01  sup_time_sim_full:                      0.
% 1.27/1.01  sup_time_sim_immed:                     0.
% 1.27/1.01  
% 1.27/1.01  sup_num_of_clauses:                     7
% 1.27/1.01  sup_num_in_active:                      4
% 1.27/1.01  sup_num_in_passive:                     3
% 1.27/1.01  sup_num_of_loops:                       4
% 1.27/1.01  sup_fw_superposition:                   0
% 1.27/1.01  sup_bw_superposition:                   0
% 1.27/1.01  sup_immediate_simplified:               0
% 1.27/1.01  sup_given_eliminated:                   0
% 1.27/1.01  comparisons_done:                       0
% 1.27/1.01  comparisons_avoided:                    0
% 1.27/1.01  
% 1.27/1.01  ------ Simplifications
% 1.27/1.01  
% 1.27/1.01  
% 1.27/1.01  sim_fw_subset_subsumed:                 0
% 1.27/1.01  sim_bw_subset_subsumed:                 0
% 1.27/1.01  sim_fw_subsumed:                        0
% 1.27/1.01  sim_bw_subsumed:                        0
% 1.27/1.01  sim_fw_subsumption_res:                 0
% 1.27/1.01  sim_bw_subsumption_res:                 0
% 1.27/1.01  sim_tautology_del:                      0
% 1.27/1.01  sim_eq_tautology_del:                   0
% 1.27/1.01  sim_eq_res_simp:                        0
% 1.27/1.01  sim_fw_demodulated:                     0
% 1.27/1.01  sim_bw_demodulated:                     0
% 1.27/1.01  sim_light_normalised:                   0
% 1.27/1.01  sim_joinable_taut:                      0
% 1.27/1.01  sim_joinable_simp:                      0
% 1.27/1.01  sim_ac_normalised:                      0
% 1.27/1.01  sim_smt_subsumption:                    0
% 1.27/1.01  
%------------------------------------------------------------------------------
