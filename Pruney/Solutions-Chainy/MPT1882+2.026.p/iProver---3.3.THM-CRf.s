%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:23 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 765 expanded)
%              Number of clauses        :   81 ( 185 expanded)
%              Number of leaves         :   23 ( 169 expanded)
%              Depth                    :   17
%              Number of atoms          :  616 (5602 expanded)
%              Number of equality atoms :  173 ( 420 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f49,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f46,f48,f47])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
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

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK1(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,
    ( v1_zfmisc_1(sK3)
    | v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f19,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f84,plain,
    ( ~ v1_zfmisc_1(sK3)
    | ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f74,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK1(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK1(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f37])).

fof(f63,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f55,f60,f60])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f51,f85])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f89,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f53,f60])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f86,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f57])).

fof(f90,plain,(
    ! [X2,X0,X1] : k6_subset_1(k6_subset_1(X0,X1),X2) = k6_subset_1(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(definition_unfolding,[],[f54,f60,f86,f60,f60])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f88,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f52,f60])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( k1_xboole_0 = k6_subset_1(X1,X0)
        & X0 != X1
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1027,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | r1_tarski(X0,sK1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1037,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_tex_2(X0,X1) != iProver_top
    | v3_tex_2(X0,X1) = iProver_top
    | r1_tarski(X0,sK1(X1,X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6311,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top
    | r1_tarski(sK3,sK1(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1027,c_1037])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_31,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_32,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_33,plain,
    ( v2_tdlat_3(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_34,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v3_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_37,plain,
    ( v3_tex_2(sK3,sK2) = iProver_top
    | v1_zfmisc_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1411,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(X0,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1627,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(sK3,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ v1_zfmisc_1(sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1411])).

cnf(c_1628,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_tex_2(sK3,sK2) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_tdlat_3(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_zfmisc_1(sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1627])).

cnf(c_1758,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(sK3,sK2)
    | v3_tex_2(sK3,sK2)
    | r1_tarski(sK3,sK1(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1765,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top
    | r1_tarski(sK3,sK1(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1758])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1033,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v2_tex_2(X0,X1) = iProver_top
    | v3_tex_2(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2273,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top
    | v3_tex_2(sK3,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1027,c_1033])).

cnf(c_23,negated_conjecture,
    ( ~ v3_tex_2(sK3,sK2)
    | ~ v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_38,plain,
    ( v3_tex_2(sK3,sK2) != iProver_top
    | v1_zfmisc_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_6,plain,
    ( v1_zfmisc_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_291,plain,
    ( v1_zfmisc_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_6])).

cnf(c_292,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_291])).

cnf(c_1760,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(sK3,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v1_zfmisc_1(sK3) ),
    inference(instantiation,[status(thm)],[c_292])).

cnf(c_1761,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_tdlat_3(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_zfmisc_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1760])).

cnf(c_2559,plain,
    ( v3_tex_2(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2273,c_31,c_32,c_33,c_34,c_36,c_38,c_1761])).

cnf(c_6719,plain,
    ( r1_tarski(sK3,sK1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6311,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_1628,c_1761,c_1765,c_2273])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1031,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6725,plain,
    ( sK1(sK2,sK3) = sK3
    | v1_zfmisc_1(sK1(sK2,sK3)) != iProver_top
    | v1_xboole_0(sK1(sK2,sK3)) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6719,c_1031])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1759,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(sK3,sK2)
    | v3_tex_2(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1763,plain,
    ( sK1(sK2,sK3) != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1759])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK1(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1757,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(sK1(sK2,sK3),sK2)
    | ~ v2_tex_2(sK3,sK2)
    | v3_tex_2(sK3,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1767,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_tex_2(sK1(sK2,sK3),sK2) = iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1757])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1756,plain,
    ( m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(sK3,sK2)
    | v3_tex_2(sK3,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1769,plain,
    ( m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1756])).

cnf(c_2352,plain,
    ( ~ m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(sK1(sK2,sK3),sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v1_zfmisc_1(sK1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_292])).

cnf(c_2353,plain,
    ( m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v2_tex_2(sK1(sK2,sK3),sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_tdlat_3(sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v1_zfmisc_1(sK1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2352])).

cnf(c_6814,plain,
    ( v1_xboole_0(sK1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6725,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_1628,c_1761,c_1763,c_1767,c_1769,c_2273,c_2353])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1047,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1045,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5766,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_1045])).

cnf(c_6819,plain,
    ( sK1(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6814,c_5766])).

cnf(c_6938,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6819,c_6719])).

cnf(c_11,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1040,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1,plain,
    ( k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3,plain,
    ( k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1066,plain,
    ( k6_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1,c_3])).

cnf(c_4,plain,
    ( k6_subset_1(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = k6_subset_1(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1046,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1941,plain,
    ( r1_tarski(k6_subset_1(k6_subset_1(X0,X1),X2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1046])).

cnf(c_2138,plain,
    ( r1_tarski(k6_subset_1(k1_xboole_0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1066,c_1941])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1043,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3902,plain,
    ( r2_hidden(X0,k6_subset_1(k1_xboole_0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2138,c_1043])).

cnf(c_4283,plain,
    ( k6_subset_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1040,c_3902])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | X1 = X0
    | k6_subset_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1032,plain,
    ( X0 = X1
    | k6_subset_1(X0,X1) != k1_xboole_0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8643,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4283,c_1032])).

cnf(c_9721,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6938,c_8643])).

cnf(c_325,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1324,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_1326,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1324])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9721,c_1326,c_0,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:19:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.83/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/0.98  
% 3.83/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.83/0.98  
% 3.83/0.98  ------  iProver source info
% 3.83/0.98  
% 3.83/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.83/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.83/0.98  git: non_committed_changes: false
% 3.83/0.98  git: last_make_outside_of_git: false
% 3.83/0.98  
% 3.83/0.98  ------ 
% 3.83/0.98  ------ Parsing...
% 3.83/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.83/0.98  
% 3.83/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.83/0.98  
% 3.83/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.83/0.98  
% 3.83/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.83/0.98  ------ Proving...
% 3.83/0.98  ------ Problem Properties 
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  clauses                                 31
% 3.83/0.98  conjectures                             8
% 3.83/0.98  EPR                                     13
% 3.83/0.98  Horn                                    23
% 3.83/0.98  unary                                   12
% 3.83/0.98  binary                                  5
% 3.83/0.98  lits                                    88
% 3.83/0.98  lits eq                                 15
% 3.83/0.98  fd_pure                                 0
% 3.83/0.98  fd_pseudo                               0
% 3.83/0.98  fd_cond                                 3
% 3.83/0.98  fd_pseudo_cond                          4
% 3.83/0.98  AC symbols                              0
% 3.83/0.98  
% 3.83/0.98  ------ Input Options Time Limit: Unbounded
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  ------ 
% 3.83/0.98  Current options:
% 3.83/0.98  ------ 
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  ------ Proving...
% 3.83/0.98  
% 3.83/0.98  
% 3.83/0.98  % SZS status Theorem for theBenchmark.p
% 3.83/0.98  
% 3.83/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.83/0.98  
% 3.83/0.98  fof(f20,conjecture,(
% 3.83/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.83/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.98  
% 3.83/0.98  fof(f21,negated_conjecture,(
% 3.83/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.83/0.98    inference(negated_conjecture,[],[f20])).
% 3.83/0.98  
% 3.83/0.98  fof(f35,plain,(
% 3.83/0.98    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.83/0.98    inference(ennf_transformation,[],[f21])).
% 3.83/0.98  
% 3.83/0.98  fof(f36,plain,(
% 3.83/0.98    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.83/0.98    inference(flattening,[],[f35])).
% 3.83/0.98  
% 3.83/0.98  fof(f45,plain,(
% 3.83/0.98    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.83/0.98    inference(nnf_transformation,[],[f36])).
% 3.83/0.98  
% 3.83/0.98  fof(f46,plain,(
% 3.83/0.98    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.83/0.98    inference(flattening,[],[f45])).
% 3.83/0.98  
% 3.83/0.98  fof(f48,plain,(
% 3.83/0.98    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,X0)) & (v1_zfmisc_1(sK3) | v3_tex_2(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK3))) )),
% 3.83/0.98    introduced(choice_axiom,[])).
% 3.83/0.98  
% 3.83/0.98  fof(f47,plain,(
% 3.83/0.98    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK2)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.83/0.98    introduced(choice_axiom,[])).
% 3.83/0.98  
% 3.83/0.98  fof(f49,plain,(
% 3.83/0.98    ((~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,sK2)) & (v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.83/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f46,f48,f47])).
% 3.83/0.98  
% 3.83/0.98  fof(f82,plain,(
% 3.83/0.98    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.83/0.98    inference(cnf_transformation,[],[f49])).
% 3.83/0.98  
% 3.83/0.98  fof(f16,axiom,(
% 3.83/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 3.83/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.98  
% 3.83/0.98  fof(f28,plain,(
% 3.83/0.98    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.83/0.98    inference(ennf_transformation,[],[f16])).
% 3.83/0.98  
% 3.83/0.98  fof(f29,plain,(
% 3.83/0.98    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.83/0.99    inference(flattening,[],[f28])).
% 3.83/0.99  
% 3.83/0.99  fof(f39,plain,(
% 3.83/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.83/0.99    inference(nnf_transformation,[],[f29])).
% 3.83/0.99  
% 3.83/0.99  fof(f40,plain,(
% 3.83/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.83/0.99    inference(flattening,[],[f39])).
% 3.83/0.99  
% 3.83/0.99  fof(f41,plain,(
% 3.83/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.83/0.99    inference(rectify,[],[f40])).
% 3.83/0.99  
% 3.83/0.99  fof(f42,plain,(
% 3.83/0.99    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f43,plain,(
% 3.83/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.83/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 3.83/0.99  
% 3.83/0.99  fof(f71,plain,(
% 3.83/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK1(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f43])).
% 3.83/0.99  
% 3.83/0.99  fof(f77,plain,(
% 3.83/0.99    ~v2_struct_0(sK2)),
% 3.83/0.99    inference(cnf_transformation,[],[f49])).
% 3.83/0.99  
% 3.83/0.99  fof(f78,plain,(
% 3.83/0.99    v2_pre_topc(sK2)),
% 3.83/0.99    inference(cnf_transformation,[],[f49])).
% 3.83/0.99  
% 3.83/0.99  fof(f79,plain,(
% 3.83/0.99    v2_tdlat_3(sK2)),
% 3.83/0.99    inference(cnf_transformation,[],[f49])).
% 3.83/0.99  
% 3.83/0.99  fof(f80,plain,(
% 3.83/0.99    l1_pre_topc(sK2)),
% 3.83/0.99    inference(cnf_transformation,[],[f49])).
% 3.83/0.99  
% 3.83/0.99  fof(f81,plain,(
% 3.83/0.99    ~v1_xboole_0(sK3)),
% 3.83/0.99    inference(cnf_transformation,[],[f49])).
% 3.83/0.99  
% 3.83/0.99  fof(f83,plain,(
% 3.83/0.99    v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2)),
% 3.83/0.99    inference(cnf_transformation,[],[f49])).
% 3.83/0.99  
% 3.83/0.99  fof(f19,axiom,(
% 3.83/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f33,plain,(
% 3.83/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.83/0.99    inference(ennf_transformation,[],[f19])).
% 3.83/0.99  
% 3.83/0.99  fof(f34,plain,(
% 3.83/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.83/0.99    inference(flattening,[],[f33])).
% 3.83/0.99  
% 3.83/0.99  fof(f44,plain,(
% 3.83/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.83/0.99    inference(nnf_transformation,[],[f34])).
% 3.83/0.99  
% 3.83/0.99  fof(f76,plain,(
% 3.83/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f44])).
% 3.83/0.99  
% 3.83/0.99  fof(f67,plain,(
% 3.83/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f43])).
% 3.83/0.99  
% 3.83/0.99  fof(f84,plain,(
% 3.83/0.99    ~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,sK2)),
% 3.83/0.99    inference(cnf_transformation,[],[f49])).
% 3.83/0.99  
% 3.83/0.99  fof(f75,plain,(
% 3.83/0.99    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f44])).
% 3.83/0.99  
% 3.83/0.99  fof(f9,axiom,(
% 3.83/0.99    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f23,plain,(
% 3.83/0.99    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 3.83/0.99    inference(ennf_transformation,[],[f9])).
% 3.83/0.99  
% 3.83/0.99  fof(f58,plain,(
% 3.83/0.99    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f23])).
% 3.83/0.99  
% 3.83/0.99  fof(f18,axiom,(
% 3.83/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f31,plain,(
% 3.83/0.99    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 3.83/0.99    inference(ennf_transformation,[],[f18])).
% 3.83/0.99  
% 3.83/0.99  fof(f32,plain,(
% 3.83/0.99    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.83/0.99    inference(flattening,[],[f31])).
% 3.83/0.99  
% 3.83/0.99  fof(f74,plain,(
% 3.83/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f32])).
% 3.83/0.99  
% 3.83/0.99  fof(f72,plain,(
% 3.83/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK1(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f43])).
% 3.83/0.99  
% 3.83/0.99  fof(f70,plain,(
% 3.83/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | v2_tex_2(sK1(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f43])).
% 3.83/0.99  
% 3.83/0.99  fof(f69,plain,(
% 3.83/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f43])).
% 3.83/0.99  
% 3.83/0.99  fof(f1,axiom,(
% 3.83/0.99    v1_xboole_0(k1_xboole_0)),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f50,plain,(
% 3.83/0.99    v1_xboole_0(k1_xboole_0)),
% 3.83/0.99    inference(cnf_transformation,[],[f1])).
% 3.83/0.99  
% 3.83/0.99  fof(f7,axiom,(
% 3.83/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f22,plain,(
% 3.83/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.83/0.99    inference(ennf_transformation,[],[f7])).
% 3.83/0.99  
% 3.83/0.99  fof(f56,plain,(
% 3.83/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f22])).
% 3.83/0.99  
% 3.83/0.99  fof(f14,axiom,(
% 3.83/0.99    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f25,plain,(
% 3.83/0.99    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.83/0.99    inference(ennf_transformation,[],[f14])).
% 3.83/0.99  
% 3.83/0.99  fof(f37,plain,(
% 3.83/0.99    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 3.83/0.99    introduced(choice_axiom,[])).
% 3.83/0.99  
% 3.83/0.99  fof(f38,plain,(
% 3.83/0.99    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 3.83/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f37])).
% 3.83/0.99  
% 3.83/0.99  fof(f63,plain,(
% 3.83/0.99    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.83/0.99    inference(cnf_transformation,[],[f38])).
% 3.83/0.99  
% 3.83/0.99  fof(f2,axiom,(
% 3.83/0.99    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f51,plain,(
% 3.83/0.99    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f2])).
% 3.83/0.99  
% 3.83/0.99  fof(f6,axiom,(
% 3.83/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f55,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.83/0.99    inference(cnf_transformation,[],[f6])).
% 3.83/0.99  
% 3.83/0.99  fof(f11,axiom,(
% 3.83/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f60,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f11])).
% 3.83/0.99  
% 3.83/0.99  fof(f85,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 3.83/0.99    inference(definition_unfolding,[],[f55,f60,f60])).
% 3.83/0.99  
% 3.83/0.99  fof(f87,plain,(
% 3.83/0.99    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0))) )),
% 3.83/0.99    inference(definition_unfolding,[],[f51,f85])).
% 3.83/0.99  
% 3.83/0.99  fof(f4,axiom,(
% 3.83/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f53,plain,(
% 3.83/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.83/0.99    inference(cnf_transformation,[],[f4])).
% 3.83/0.99  
% 3.83/0.99  fof(f89,plain,(
% 3.83/0.99    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 3.83/0.99    inference(definition_unfolding,[],[f53,f60])).
% 3.83/0.99  
% 3.83/0.99  fof(f5,axiom,(
% 3.83/0.99    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f54,plain,(
% 3.83/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f5])).
% 3.83/0.99  
% 3.83/0.99  fof(f10,axiom,(
% 3.83/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f59,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.83/0.99    inference(cnf_transformation,[],[f10])).
% 3.83/0.99  
% 3.83/0.99  fof(f8,axiom,(
% 3.83/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f57,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f8])).
% 3.83/0.99  
% 3.83/0.99  fof(f86,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.83/0.99    inference(definition_unfolding,[],[f59,f57])).
% 3.83/0.99  
% 3.83/0.99  fof(f90,plain,(
% 3.83/0.99    ( ! [X2,X0,X1] : (k6_subset_1(k6_subset_1(X0,X1),X2) = k6_subset_1(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) )),
% 3.83/0.99    inference(definition_unfolding,[],[f54,f60,f86,f60,f60])).
% 3.83/0.99  
% 3.83/0.99  fof(f3,axiom,(
% 3.83/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f52,plain,(
% 3.83/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f3])).
% 3.83/0.99  
% 3.83/0.99  fof(f88,plain,(
% 3.83/0.99    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 3.83/0.99    inference(definition_unfolding,[],[f52,f60])).
% 3.83/0.99  
% 3.83/0.99  fof(f13,axiom,(
% 3.83/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f24,plain,(
% 3.83/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.83/0.99    inference(ennf_transformation,[],[f13])).
% 3.83/0.99  
% 3.83/0.99  fof(f62,plain,(
% 3.83/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f24])).
% 3.83/0.99  
% 3.83/0.99  fof(f17,axiom,(
% 3.83/0.99    ! [X0,X1] : ~(k1_xboole_0 = k6_subset_1(X1,X0) & X0 != X1 & r1_tarski(X0,X1))),
% 3.83/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/0.99  
% 3.83/0.99  fof(f30,plain,(
% 3.83/0.99    ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1))),
% 3.83/0.99    inference(ennf_transformation,[],[f17])).
% 3.83/0.99  
% 3.83/0.99  fof(f73,plain,(
% 3.83/0.99    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.83/0.99    inference(cnf_transformation,[],[f30])).
% 3.83/0.99  
% 3.83/0.99  cnf(c_25,negated_conjecture,
% 3.83/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.83/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1027,plain,
% 3.83/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_14,plain,
% 3.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.99      | ~ v2_tex_2(X0,X1)
% 3.83/0.99      | v3_tex_2(X0,X1)
% 3.83/0.99      | r1_tarski(X0,sK1(X1,X0))
% 3.83/0.99      | ~ l1_pre_topc(X1) ),
% 3.83/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1037,plain,
% 3.83/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.83/0.99      | v2_tex_2(X0,X1) != iProver_top
% 3.83/0.99      | v3_tex_2(X0,X1) = iProver_top
% 3.83/0.99      | r1_tarski(X0,sK1(X1,X0)) = iProver_top
% 3.83/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_6311,plain,
% 3.83/0.99      ( v2_tex_2(sK3,sK2) != iProver_top
% 3.83/0.99      | v3_tex_2(sK3,sK2) = iProver_top
% 3.83/0.99      | r1_tarski(sK3,sK1(sK2,sK3)) = iProver_top
% 3.83/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_1027,c_1037]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_30,negated_conjecture,
% 3.83/0.99      ( ~ v2_struct_0(sK2) ),
% 3.83/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_31,plain,
% 3.83/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_29,negated_conjecture,
% 3.83/0.99      ( v2_pre_topc(sK2) ),
% 3.83/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_32,plain,
% 3.83/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_28,negated_conjecture,
% 3.83/0.99      ( v2_tdlat_3(sK2) ),
% 3.83/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_33,plain,
% 3.83/0.99      ( v2_tdlat_3(sK2) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_27,negated_conjecture,
% 3.83/0.99      ( l1_pre_topc(sK2) ),
% 3.83/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_34,plain,
% 3.83/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_26,negated_conjecture,
% 3.83/0.99      ( ~ v1_xboole_0(sK3) ),
% 3.83/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_35,plain,
% 3.83/0.99      ( v1_xboole_0(sK3) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_36,plain,
% 3.83/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_24,negated_conjecture,
% 3.83/0.99      ( v3_tex_2(sK3,sK2) | v1_zfmisc_1(sK3) ),
% 3.83/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_37,plain,
% 3.83/0.99      ( v3_tex_2(sK3,sK2) = iProver_top
% 3.83/0.99      | v1_zfmisc_1(sK3) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_21,plain,
% 3.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.99      | v2_tex_2(X0,X1)
% 3.83/0.99      | v2_struct_0(X1)
% 3.83/0.99      | ~ l1_pre_topc(X1)
% 3.83/0.99      | ~ v2_tdlat_3(X1)
% 3.83/0.99      | ~ v2_pre_topc(X1)
% 3.83/0.99      | ~ v1_zfmisc_1(X0)
% 3.83/0.99      | v1_xboole_0(X0) ),
% 3.83/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1411,plain,
% 3.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.83/0.99      | v2_tex_2(X0,sK2)
% 3.83/0.99      | v2_struct_0(sK2)
% 3.83/0.99      | ~ l1_pre_topc(sK2)
% 3.83/0.99      | ~ v2_tdlat_3(sK2)
% 3.83/0.99      | ~ v2_pre_topc(sK2)
% 3.83/0.99      | ~ v1_zfmisc_1(X0)
% 3.83/0.99      | v1_xboole_0(X0) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1627,plain,
% 3.83/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.83/0.99      | v2_tex_2(sK3,sK2)
% 3.83/0.99      | v2_struct_0(sK2)
% 3.83/0.99      | ~ l1_pre_topc(sK2)
% 3.83/0.99      | ~ v2_tdlat_3(sK2)
% 3.83/0.99      | ~ v2_pre_topc(sK2)
% 3.83/0.99      | ~ v1_zfmisc_1(sK3)
% 3.83/0.99      | v1_xboole_0(sK3) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_1411]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1628,plain,
% 3.83/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.83/0.99      | v2_tex_2(sK3,sK2) = iProver_top
% 3.83/0.99      | v2_struct_0(sK2) = iProver_top
% 3.83/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.83/0.99      | v2_tdlat_3(sK2) != iProver_top
% 3.83/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.83/0.99      | v1_zfmisc_1(sK3) != iProver_top
% 3.83/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1627]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1758,plain,
% 3.83/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.83/0.99      | ~ v2_tex_2(sK3,sK2)
% 3.83/0.99      | v3_tex_2(sK3,sK2)
% 3.83/0.99      | r1_tarski(sK3,sK1(sK2,sK3))
% 3.83/0.99      | ~ l1_pre_topc(sK2) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1765,plain,
% 3.83/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.83/0.99      | v2_tex_2(sK3,sK2) != iProver_top
% 3.83/0.99      | v3_tex_2(sK3,sK2) = iProver_top
% 3.83/0.99      | r1_tarski(sK3,sK1(sK2,sK3)) = iProver_top
% 3.83/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1758]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_18,plain,
% 3.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.99      | v2_tex_2(X0,X1)
% 3.83/0.99      | ~ v3_tex_2(X0,X1)
% 3.83/0.99      | ~ l1_pre_topc(X1) ),
% 3.83/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1033,plain,
% 3.83/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.83/0.99      | v2_tex_2(X0,X1) = iProver_top
% 3.83/0.99      | v3_tex_2(X0,X1) != iProver_top
% 3.83/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_2273,plain,
% 3.83/0.99      ( v2_tex_2(sK3,sK2) = iProver_top
% 3.83/0.99      | v3_tex_2(sK3,sK2) != iProver_top
% 3.83/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_1027,c_1033]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_23,negated_conjecture,
% 3.83/0.99      ( ~ v3_tex_2(sK3,sK2) | ~ v1_zfmisc_1(sK3) ),
% 3.83/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_38,plain,
% 3.83/0.99      ( v3_tex_2(sK3,sK2) != iProver_top
% 3.83/0.99      | v1_zfmisc_1(sK3) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_22,plain,
% 3.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.99      | ~ v2_tex_2(X0,X1)
% 3.83/0.99      | v2_struct_0(X1)
% 3.83/0.99      | ~ l1_pre_topc(X1)
% 3.83/0.99      | ~ v2_tdlat_3(X1)
% 3.83/0.99      | ~ v2_pre_topc(X1)
% 3.83/0.99      | v1_zfmisc_1(X0)
% 3.83/0.99      | v1_xboole_0(X0) ),
% 3.83/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_6,plain,
% 3.83/0.99      ( v1_zfmisc_1(X0) | ~ v1_xboole_0(X0) ),
% 3.83/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_291,plain,
% 3.83/0.99      ( v1_zfmisc_1(X0)
% 3.83/0.99      | ~ v2_pre_topc(X1)
% 3.83/0.99      | ~ v2_tdlat_3(X1)
% 3.83/0.99      | ~ l1_pre_topc(X1)
% 3.83/0.99      | v2_struct_0(X1)
% 3.83/0.99      | ~ v2_tex_2(X0,X1)
% 3.83/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ),
% 3.83/0.99      inference(global_propositional_subsumption,
% 3.83/0.99                [status(thm)],
% 3.83/0.99                [c_22,c_6]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_292,plain,
% 3.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.99      | ~ v2_tex_2(X0,X1)
% 3.83/0.99      | v2_struct_0(X1)
% 3.83/0.99      | ~ l1_pre_topc(X1)
% 3.83/0.99      | ~ v2_tdlat_3(X1)
% 3.83/0.99      | ~ v2_pre_topc(X1)
% 3.83/0.99      | v1_zfmisc_1(X0) ),
% 3.83/0.99      inference(renaming,[status(thm)],[c_291]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1760,plain,
% 3.83/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.83/0.99      | ~ v2_tex_2(sK3,sK2)
% 3.83/0.99      | v2_struct_0(sK2)
% 3.83/0.99      | ~ l1_pre_topc(sK2)
% 3.83/0.99      | ~ v2_tdlat_3(sK2)
% 3.83/0.99      | ~ v2_pre_topc(sK2)
% 3.83/0.99      | v1_zfmisc_1(sK3) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_292]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1761,plain,
% 3.83/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.83/0.99      | v2_tex_2(sK3,sK2) != iProver_top
% 3.83/0.99      | v2_struct_0(sK2) = iProver_top
% 3.83/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.83/0.99      | v2_tdlat_3(sK2) != iProver_top
% 3.83/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.83/0.99      | v1_zfmisc_1(sK3) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1760]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_2559,plain,
% 3.83/0.99      ( v3_tex_2(sK3,sK2) != iProver_top ),
% 3.83/0.99      inference(global_propositional_subsumption,
% 3.83/0.99                [status(thm)],
% 3.83/0.99                [c_2273,c_31,c_32,c_33,c_34,c_36,c_38,c_1761]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_6719,plain,
% 3.83/0.99      ( r1_tarski(sK3,sK1(sK2,sK3)) = iProver_top ),
% 3.83/0.99      inference(global_propositional_subsumption,
% 3.83/0.99                [status(thm)],
% 3.83/0.99                [c_6311,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_1628,
% 3.83/0.99                 c_1761,c_1765,c_2273]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_20,plain,
% 3.83/0.99      ( ~ r1_tarski(X0,X1)
% 3.83/0.99      | ~ v1_zfmisc_1(X1)
% 3.83/0.99      | v1_xboole_0(X1)
% 3.83/0.99      | v1_xboole_0(X0)
% 3.83/0.99      | X1 = X0 ),
% 3.83/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1031,plain,
% 3.83/0.99      ( X0 = X1
% 3.83/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.83/0.99      | v1_zfmisc_1(X0) != iProver_top
% 3.83/0.99      | v1_xboole_0(X1) = iProver_top
% 3.83/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_6725,plain,
% 3.83/0.99      ( sK1(sK2,sK3) = sK3
% 3.83/0.99      | v1_zfmisc_1(sK1(sK2,sK3)) != iProver_top
% 3.83/0.99      | v1_xboole_0(sK1(sK2,sK3)) = iProver_top
% 3.83/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_6719,c_1031]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_13,plain,
% 3.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.99      | ~ v2_tex_2(X0,X1)
% 3.83/0.99      | v3_tex_2(X0,X1)
% 3.83/0.99      | ~ l1_pre_topc(X1)
% 3.83/0.99      | sK1(X1,X0) != X0 ),
% 3.83/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1759,plain,
% 3.83/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.83/0.99      | ~ v2_tex_2(sK3,sK2)
% 3.83/0.99      | v3_tex_2(sK3,sK2)
% 3.83/0.99      | ~ l1_pre_topc(sK2)
% 3.83/0.99      | sK1(sK2,sK3) != sK3 ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1763,plain,
% 3.83/0.99      ( sK1(sK2,sK3) != sK3
% 3.83/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.83/0.99      | v2_tex_2(sK3,sK2) != iProver_top
% 3.83/0.99      | v3_tex_2(sK3,sK2) = iProver_top
% 3.83/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1759]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_15,plain,
% 3.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.99      | ~ v2_tex_2(X0,X1)
% 3.83/0.99      | v2_tex_2(sK1(X1,X0),X1)
% 3.83/0.99      | v3_tex_2(X0,X1)
% 3.83/0.99      | ~ l1_pre_topc(X1) ),
% 3.83/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1757,plain,
% 3.83/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.83/0.99      | v2_tex_2(sK1(sK2,sK3),sK2)
% 3.83/0.99      | ~ v2_tex_2(sK3,sK2)
% 3.83/0.99      | v3_tex_2(sK3,sK2)
% 3.83/0.99      | ~ l1_pre_topc(sK2) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1767,plain,
% 3.83/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.83/0.99      | v2_tex_2(sK1(sK2,sK3),sK2) = iProver_top
% 3.83/0.99      | v2_tex_2(sK3,sK2) != iProver_top
% 3.83/0.99      | v3_tex_2(sK3,sK2) = iProver_top
% 3.83/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1757]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_16,plain,
% 3.83/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.99      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.83/0.99      | ~ v2_tex_2(X0,X1)
% 3.83/0.99      | v3_tex_2(X0,X1)
% 3.83/0.99      | ~ l1_pre_topc(X1) ),
% 3.83/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1756,plain,
% 3.83/0.99      ( m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.83/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.83/0.99      | ~ v2_tex_2(sK3,sK2)
% 3.83/0.99      | v3_tex_2(sK3,sK2)
% 3.83/0.99      | ~ l1_pre_topc(sK2) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1769,plain,
% 3.83/0.99      ( m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.83/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.83/0.99      | v2_tex_2(sK3,sK2) != iProver_top
% 3.83/0.99      | v3_tex_2(sK3,sK2) = iProver_top
% 3.83/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_1756]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_2352,plain,
% 3.83/0.99      ( ~ m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.83/0.99      | ~ v2_tex_2(sK1(sK2,sK3),sK2)
% 3.83/0.99      | v2_struct_0(sK2)
% 3.83/0.99      | ~ l1_pre_topc(sK2)
% 3.83/0.99      | ~ v2_tdlat_3(sK2)
% 3.83/0.99      | ~ v2_pre_topc(sK2)
% 3.83/0.99      | v1_zfmisc_1(sK1(sK2,sK3)) ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_292]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_2353,plain,
% 3.83/0.99      ( m1_subset_1(sK1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.83/0.99      | v2_tex_2(sK1(sK2,sK3),sK2) != iProver_top
% 3.83/0.99      | v2_struct_0(sK2) = iProver_top
% 3.83/0.99      | l1_pre_topc(sK2) != iProver_top
% 3.83/0.99      | v2_tdlat_3(sK2) != iProver_top
% 3.83/0.99      | v2_pre_topc(sK2) != iProver_top
% 3.83/0.99      | v1_zfmisc_1(sK1(sK2,sK3)) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_2352]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_6814,plain,
% 3.83/0.99      ( v1_xboole_0(sK1(sK2,sK3)) = iProver_top ),
% 3.83/0.99      inference(global_propositional_subsumption,
% 3.83/0.99                [status(thm)],
% 3.83/0.99                [c_6725,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_1628,
% 3.83/0.99                 c_1761,c_1763,c_1767,c_1769,c_2273,c_2353]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_0,plain,
% 3.83/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.83/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1047,plain,
% 3.83/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_5,plain,
% 3.83/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 3.83/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1045,plain,
% 3.83/0.99      ( X0 = X1
% 3.83/0.99      | v1_xboole_0(X0) != iProver_top
% 3.83/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_5766,plain,
% 3.83/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_1047,c_1045]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_6819,plain,
% 3.83/0.99      ( sK1(sK2,sK3) = k1_xboole_0 ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_6814,c_5766]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_6938,plain,
% 3.83/0.99      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.83/0.99      inference(demodulation,[status(thm)],[c_6819,c_6719]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_11,plain,
% 3.83/0.99      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 3.83/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1040,plain,
% 3.83/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1,plain,
% 3.83/0.99      ( k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.83/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_3,plain,
% 3.83/0.99      ( k6_subset_1(X0,k1_xboole_0) = X0 ),
% 3.83/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1066,plain,
% 3.83/0.99      ( k6_subset_1(X0,X0) = k1_xboole_0 ),
% 3.83/0.99      inference(light_normalisation,[status(thm)],[c_1,c_3]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_4,plain,
% 3.83/0.99      ( k6_subset_1(X0,k3_tarski(k1_enumset1(X1,X1,X2))) = k6_subset_1(k6_subset_1(X0,X1),X2) ),
% 3.83/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_2,plain,
% 3.83/0.99      ( r1_tarski(k6_subset_1(X0,X1),X0) ),
% 3.83/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1046,plain,
% 3.83/0.99      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1941,plain,
% 3.83/0.99      ( r1_tarski(k6_subset_1(k6_subset_1(X0,X1),X2),X0) = iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_4,c_1046]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_2138,plain,
% 3.83/0.99      ( r1_tarski(k6_subset_1(k1_xboole_0,X0),X1) = iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_1066,c_1941]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_8,plain,
% 3.83/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.83/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1043,plain,
% 3.83/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.83/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_3902,plain,
% 3.83/0.99      ( r2_hidden(X0,k6_subset_1(k1_xboole_0,X1)) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_2138,c_1043]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_4283,plain,
% 3.83/0.99      ( k6_subset_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_1040,c_3902]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_19,plain,
% 3.83/0.99      ( ~ r1_tarski(X0,X1)
% 3.83/0.99      | X1 = X0
% 3.83/0.99      | k6_subset_1(X1,X0) != k1_xboole_0 ),
% 3.83/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1032,plain,
% 3.83/0.99      ( X0 = X1
% 3.83/0.99      | k6_subset_1(X0,X1) != k1_xboole_0
% 3.83/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.83/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_8643,plain,
% 3.83/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_4283,c_1032]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_9721,plain,
% 3.83/0.99      ( sK3 = k1_xboole_0 ),
% 3.83/0.99      inference(superposition,[status(thm)],[c_6938,c_8643]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_325,plain,
% 3.83/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.83/0.99      theory(equality) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1324,plain,
% 3.83/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_325]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(c_1326,plain,
% 3.83/0.99      ( v1_xboole_0(sK3)
% 3.83/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.83/0.99      | sK3 != k1_xboole_0 ),
% 3.83/0.99      inference(instantiation,[status(thm)],[c_1324]) ).
% 3.83/0.99  
% 3.83/0.99  cnf(contradiction,plain,
% 3.83/0.99      ( $false ),
% 3.83/0.99      inference(minisat,[status(thm)],[c_9721,c_1326,c_0,c_26]) ).
% 3.83/0.99  
% 3.83/0.99  
% 3.83/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.83/0.99  
% 3.83/0.99  ------                               Statistics
% 3.83/0.99  
% 3.83/0.99  ------ Selected
% 3.83/0.99  
% 3.83/0.99  total_time:                             0.228
% 3.83/0.99  
%------------------------------------------------------------------------------
