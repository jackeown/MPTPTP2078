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
% DateTime   : Thu Dec  3 12:27:20 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  148 (1174 expanded)
%              Number of clauses        :   97 ( 270 expanded)
%              Number of leaves         :   15 ( 265 expanded)
%              Depth                    :   23
%              Number of atoms          :  659 (9284 expanded)
%              Number of equality atoms :  152 ( 299 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f34])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ( ~ v1_zfmisc_1(sK4)
          | ~ v3_tex_2(sK4,X0) )
        & ( v1_zfmisc_1(sK4)
          | v3_tex_2(sK4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
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
            | ~ v3_tex_2(X1,sK3) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( ~ v1_zfmisc_1(sK4)
      | ~ v3_tex_2(sK4,sK3) )
    & ( v1_zfmisc_1(sK4)
      | v3_tex_2(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & ~ v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f48,f50,f49])).

fof(f82,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

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

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f80,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f32])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f33])).

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
    inference(cnf_transformation,[],[f46])).

fof(f77,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,
    ( v1_zfmisc_1(sK4)
    | v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

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
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f84,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f74,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK2(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3268,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | r1_tarski(X0,sK2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_746,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | r1_tarski(X0,sK2(X1,X0))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_29])).

cnf(c_747,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X0,sK3)
    | v3_tex_2(X0,sK3)
    | r1_tarski(X0,sK2(sK3,X0)) ),
    inference(unflattening,[status(thm)],[c_746])).

cnf(c_3262,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | v3_tex_2(X0,sK3) = iProver_top
    | r1_tarski(X0,sK2(sK3,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_747])).

cnf(c_3583,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v3_tex_2(sK4,sK3) = iProver_top
    | r1_tarski(sK4,sK2(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3268,c_3262])).

cnf(c_38,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_tex_2(X0,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_30,negated_conjecture,
    ( v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_460,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_31,c_30,c_29])).

cnf(c_461,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_tex_2(X0,sK3)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_460])).

cnf(c_26,negated_conjecture,
    ( v3_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_259,plain,
    ( v1_zfmisc_1(sK4)
    | v3_tex_2(sK4,sK3) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_260,plain,
    ( v3_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(renaming,[status(thm)],[c_259])).

cnf(c_1003,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_tex_2(X0,sK3)
    | v3_tex_2(sK4,sK3)
    | v1_xboole_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_461,c_260])).

cnf(c_1004,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_tex_2(sK4,sK3)
    | v3_tex_2(sK4,sK3)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1003])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1006,plain,
    ( v3_tex_2(sK4,sK3)
    | v2_tex_2(sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1004,c_28,c_27])).

cnf(c_1007,plain,
    ( v2_tex_2(sK4,sK3)
    | v3_tex_2(sK4,sK3) ),
    inference(renaming,[status(thm)],[c_1006])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_673,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_674,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_tex_2(X0,sK3)
    | ~ v3_tex_2(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_673])).

cnf(c_1442,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_tex_2(X0,sK3)
    | v2_tex_2(sK4,sK3)
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1007,c_674])).

cnf(c_1443,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_tex_2(sK4,sK3) ),
    inference(unflattening,[status(thm)],[c_1442])).

cnf(c_1444,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_tex_2(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1443])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_11,plain,
    ( v1_zfmisc_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_183,plain,
    ( v1_zfmisc_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_11])).

cnf(c_184,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_183])).

cnf(c_436,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_184,c_32])).

cnf(c_437,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X0,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_441,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_zfmisc_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_31,c_30,c_29])).

cnf(c_442,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X0,sK3)
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_441])).

cnf(c_25,negated_conjecture,
    ( ~ v3_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_257,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v3_tex_2(sK4,sK3) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_258,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | ~ v1_zfmisc_1(sK4) ),
    inference(renaming,[status(thm)],[c_257])).

cnf(c_987,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X0,sK3)
    | ~ v3_tex_2(sK4,sK3)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_442,c_258])).

cnf(c_988,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(sK4,sK3)
    | ~ v3_tex_2(sK4,sK3) ),
    inference(unflattening,[status(thm)],[c_987])).

cnf(c_990,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ v3_tex_2(sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_988,c_27])).

cnf(c_1461,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X0,sK3)
    | ~ v2_tex_2(sK4,sK3)
    | r1_tarski(X0,sK2(sK3,X0))
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_990,c_747])).

cnf(c_1462,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(sK4,sK3)
    | r1_tarski(sK4,sK2(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_1461])).

cnf(c_1463,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_tex_2(sK4,sK3) != iProver_top
    | r1_tarski(sK4,sK2(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1462])).

cnf(c_3586,plain,
    ( r1_tarski(sK4,sK2(sK3,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3583,c_38,c_1444,c_1463])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_710,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_711,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X0,sK3)
    | v3_tex_2(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_710])).

cnf(c_3264,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | v3_tex_2(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_711])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_963,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X0,sK3)
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | X2 != X0
    | X1 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_442,c_22])).

cnf(c_964,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X0,sK3)
    | ~ r1_tarski(X1,X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_963])).

cnf(c_3260,plain,
    ( X0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_tex_2(X1,sK3) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_964])).

cnf(c_4199,plain,
    ( sK2(sK3,X0) = X1
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | v2_tex_2(sK2(sK3,X0),sK3) != iProver_top
    | v3_tex_2(X0,sK3) = iProver_top
    | r1_tarski(X1,sK2(sK3,X0)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK2(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3264,c_3260])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK2(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_728,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK2(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_729,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X0,sK3)
    | v2_tex_2(sK2(sK3,X0),sK3)
    | v3_tex_2(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_728])).

cnf(c_730,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | v2_tex_2(sK2(sK3,X0),sK3) = iProver_top
    | v3_tex_2(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_4755,plain,
    ( v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | sK2(sK3,X0) = X1
    | v3_tex_2(X0,sK3) = iProver_top
    | r1_tarski(X1,sK2(sK3,X0)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK2(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4199,c_730])).

cnf(c_4756,plain,
    ( sK2(sK3,X0) = X1
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v2_tex_2(X0,sK3) != iProver_top
    | v3_tex_2(X0,sK3) = iProver_top
    | r1_tarski(X1,sK2(sK3,X0)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK2(sK3,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4755])).

cnf(c_4766,plain,
    ( sK2(sK3,sK4) = X0
    | v2_tex_2(sK4,sK3) != iProver_top
    | v3_tex_2(sK4,sK3) = iProver_top
    | r1_tarski(X0,sK2(sK3,sK4)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3268,c_4756])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_102,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_992,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | v3_tex_2(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_990])).

cnf(c_2646,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3493,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_2646])).

cnf(c_3495,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3493])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3600,plain,
    ( ~ r1_tarski(sK4,k1_xboole_0)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2643,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3613,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_2643])).

cnf(c_2644,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3595,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_2644])).

cnf(c_3847,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3595])).

cnf(c_3848,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_3847])).

cnf(c_2648,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3623,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK4,sK2(sK3,sK4))
    | X1 != sK2(sK3,sK4)
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_2648])).

cnf(c_3879,plain,
    ( r1_tarski(sK4,X0)
    | ~ r1_tarski(sK4,sK2(sK3,sK4))
    | X0 != sK2(sK3,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3623])).

cnf(c_3881,plain,
    ( ~ r1_tarski(sK4,sK2(sK3,sK4))
    | r1_tarski(sK4,k1_xboole_0)
    | sK4 != sK4
    | k1_xboole_0 != sK2(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_3879])).

cnf(c_10,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3904,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK2(sK3,sK4))
    | X0 = sK2(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3905,plain,
    ( X0 = sK2(sK3,sK4)
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3904])).

cnf(c_3907,plain,
    ( k1_xboole_0 = sK2(sK3,sK4)
    | v1_xboole_0(sK2(sK3,sK4)) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3905])).

cnf(c_4801,plain,
    ( v1_xboole_0(X0) = iProver_top
    | r1_tarski(X0,sK2(sK3,sK4)) != iProver_top
    | sK2(sK3,sK4) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4766,c_28,c_27,c_38,c_3,c_102,c_992,c_1443,c_1444,c_1462,c_3495,c_3600,c_3613,c_3848,c_3881,c_3907])).

cnf(c_4802,plain,
    ( sK2(sK3,sK4) = X0
    | r1_tarski(X0,sK2(sK3,sK4)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4801])).

cnf(c_4809,plain,
    ( sK2(sK3,sK4) = sK4
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3586,c_4802])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_764,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | sK2(X1,X0) != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_29])).

cnf(c_765,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X0,sK3)
    | v3_tex_2(X0,sK3)
    | sK2(sK3,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_764])).

cnf(c_1453,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(X0,sK3)
    | ~ v2_tex_2(sK4,sK3)
    | sK2(sK3,X0) != X0
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_990,c_765])).

cnf(c_1454,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_tex_2(sK4,sK3)
    | sK2(sK3,sK4) != sK4 ),
    inference(unflattening,[status(thm)],[c_1453])).

cnf(c_37,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4809,c_1454,c_1443,c_27,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:13:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.66/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/0.99  
% 1.66/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.66/0.99  
% 1.66/0.99  ------  iProver source info
% 1.66/0.99  
% 1.66/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.66/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.66/0.99  git: non_committed_changes: false
% 1.66/0.99  git: last_make_outside_of_git: false
% 1.66/0.99  
% 1.66/0.99  ------ 
% 1.66/0.99  
% 1.66/0.99  ------ Input Options
% 1.66/0.99  
% 1.66/0.99  --out_options                           all
% 1.66/0.99  --tptp_safe_out                         true
% 1.66/0.99  --problem_path                          ""
% 1.66/0.99  --include_path                          ""
% 1.66/0.99  --clausifier                            res/vclausify_rel
% 1.66/0.99  --clausifier_options                    --mode clausify
% 1.66/0.99  --stdin                                 false
% 1.66/0.99  --stats_out                             all
% 1.66/0.99  
% 1.66/0.99  ------ General Options
% 1.66/0.99  
% 1.66/0.99  --fof                                   false
% 1.66/0.99  --time_out_real                         305.
% 1.66/0.99  --time_out_virtual                      -1.
% 1.66/0.99  --symbol_type_check                     false
% 1.66/0.99  --clausify_out                          false
% 1.66/0.99  --sig_cnt_out                           false
% 1.66/1.00  --trig_cnt_out                          false
% 1.66/1.00  --trig_cnt_out_tolerance                1.
% 1.66/1.00  --trig_cnt_out_sk_spl                   false
% 1.66/1.00  --abstr_cl_out                          false
% 1.66/1.00  
% 1.66/1.00  ------ Global Options
% 1.66/1.00  
% 1.66/1.00  --schedule                              default
% 1.66/1.00  --add_important_lit                     false
% 1.66/1.00  --prop_solver_per_cl                    1000
% 1.66/1.00  --min_unsat_core                        false
% 1.66/1.00  --soft_assumptions                      false
% 1.66/1.00  --soft_lemma_size                       3
% 1.66/1.00  --prop_impl_unit_size                   0
% 1.66/1.00  --prop_impl_unit                        []
% 1.66/1.00  --share_sel_clauses                     true
% 1.66/1.00  --reset_solvers                         false
% 1.66/1.00  --bc_imp_inh                            [conj_cone]
% 1.66/1.00  --conj_cone_tolerance                   3.
% 1.66/1.00  --extra_neg_conj                        none
% 1.66/1.00  --large_theory_mode                     true
% 1.66/1.00  --prolific_symb_bound                   200
% 1.66/1.00  --lt_threshold                          2000
% 1.66/1.00  --clause_weak_htbl                      true
% 1.66/1.00  --gc_record_bc_elim                     false
% 1.66/1.00  
% 1.66/1.00  ------ Preprocessing Options
% 1.66/1.00  
% 1.66/1.00  --preprocessing_flag                    true
% 1.66/1.00  --time_out_prep_mult                    0.1
% 1.66/1.00  --splitting_mode                        input
% 1.66/1.00  --splitting_grd                         true
% 1.66/1.00  --splitting_cvd                         false
% 1.66/1.00  --splitting_cvd_svl                     false
% 1.66/1.00  --splitting_nvd                         32
% 1.66/1.00  --sub_typing                            true
% 1.66/1.00  --prep_gs_sim                           true
% 1.66/1.00  --prep_unflatten                        true
% 1.66/1.00  --prep_res_sim                          true
% 1.66/1.00  --prep_upred                            true
% 1.66/1.00  --prep_sem_filter                       exhaustive
% 1.66/1.00  --prep_sem_filter_out                   false
% 1.66/1.00  --pred_elim                             true
% 1.66/1.00  --res_sim_input                         true
% 1.66/1.00  --eq_ax_congr_red                       true
% 1.66/1.00  --pure_diseq_elim                       true
% 1.66/1.00  --brand_transform                       false
% 1.66/1.00  --non_eq_to_eq                          false
% 1.66/1.00  --prep_def_merge                        true
% 1.66/1.00  --prep_def_merge_prop_impl              false
% 1.66/1.00  --prep_def_merge_mbd                    true
% 1.66/1.00  --prep_def_merge_tr_red                 false
% 1.66/1.00  --prep_def_merge_tr_cl                  false
% 1.66/1.00  --smt_preprocessing                     true
% 1.66/1.00  --smt_ac_axioms                         fast
% 1.66/1.00  --preprocessed_out                      false
% 1.66/1.00  --preprocessed_stats                    false
% 1.66/1.00  
% 1.66/1.00  ------ Abstraction refinement Options
% 1.66/1.00  
% 1.66/1.00  --abstr_ref                             []
% 1.66/1.00  --abstr_ref_prep                        false
% 1.66/1.00  --abstr_ref_until_sat                   false
% 1.66/1.00  --abstr_ref_sig_restrict                funpre
% 1.66/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.66/1.00  --abstr_ref_under                       []
% 1.66/1.00  
% 1.66/1.00  ------ SAT Options
% 1.66/1.00  
% 1.66/1.00  --sat_mode                              false
% 1.66/1.00  --sat_fm_restart_options                ""
% 1.66/1.00  --sat_gr_def                            false
% 1.66/1.00  --sat_epr_types                         true
% 1.66/1.00  --sat_non_cyclic_types                  false
% 1.66/1.00  --sat_finite_models                     false
% 1.66/1.00  --sat_fm_lemmas                         false
% 1.66/1.00  --sat_fm_prep                           false
% 1.66/1.00  --sat_fm_uc_incr                        true
% 1.66/1.00  --sat_out_model                         small
% 1.66/1.00  --sat_out_clauses                       false
% 1.66/1.00  
% 1.66/1.00  ------ QBF Options
% 1.66/1.00  
% 1.66/1.00  --qbf_mode                              false
% 1.66/1.00  --qbf_elim_univ                         false
% 1.66/1.00  --qbf_dom_inst                          none
% 1.66/1.00  --qbf_dom_pre_inst                      false
% 1.66/1.00  --qbf_sk_in                             false
% 1.66/1.00  --qbf_pred_elim                         true
% 1.66/1.00  --qbf_split                             512
% 1.66/1.00  
% 1.66/1.00  ------ BMC1 Options
% 1.66/1.00  
% 1.66/1.00  --bmc1_incremental                      false
% 1.66/1.00  --bmc1_axioms                           reachable_all
% 1.66/1.00  --bmc1_min_bound                        0
% 1.66/1.00  --bmc1_max_bound                        -1
% 1.66/1.00  --bmc1_max_bound_default                -1
% 1.66/1.00  --bmc1_symbol_reachability              true
% 1.66/1.00  --bmc1_property_lemmas                  false
% 1.66/1.00  --bmc1_k_induction                      false
% 1.66/1.00  --bmc1_non_equiv_states                 false
% 1.66/1.00  --bmc1_deadlock                         false
% 1.66/1.00  --bmc1_ucm                              false
% 1.66/1.00  --bmc1_add_unsat_core                   none
% 1.66/1.00  --bmc1_unsat_core_children              false
% 1.66/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.66/1.00  --bmc1_out_stat                         full
% 1.66/1.00  --bmc1_ground_init                      false
% 1.66/1.00  --bmc1_pre_inst_next_state              false
% 1.66/1.00  --bmc1_pre_inst_state                   false
% 1.66/1.00  --bmc1_pre_inst_reach_state             false
% 1.66/1.00  --bmc1_out_unsat_core                   false
% 1.66/1.00  --bmc1_aig_witness_out                  false
% 1.66/1.00  --bmc1_verbose                          false
% 1.66/1.00  --bmc1_dump_clauses_tptp                false
% 1.66/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.66/1.00  --bmc1_dump_file                        -
% 1.66/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.66/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.66/1.00  --bmc1_ucm_extend_mode                  1
% 1.66/1.00  --bmc1_ucm_init_mode                    2
% 1.66/1.00  --bmc1_ucm_cone_mode                    none
% 1.66/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.66/1.00  --bmc1_ucm_relax_model                  4
% 1.66/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.66/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.66/1.00  --bmc1_ucm_layered_model                none
% 1.66/1.00  --bmc1_ucm_max_lemma_size               10
% 1.66/1.00  
% 1.66/1.00  ------ AIG Options
% 1.66/1.00  
% 1.66/1.00  --aig_mode                              false
% 1.66/1.00  
% 1.66/1.00  ------ Instantiation Options
% 1.66/1.00  
% 1.66/1.00  --instantiation_flag                    true
% 1.66/1.00  --inst_sos_flag                         false
% 1.66/1.00  --inst_sos_phase                        true
% 1.66/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.66/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.66/1.00  --inst_lit_sel_side                     num_symb
% 1.66/1.00  --inst_solver_per_active                1400
% 1.66/1.00  --inst_solver_calls_frac                1.
% 1.66/1.00  --inst_passive_queue_type               priority_queues
% 1.66/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.66/1.00  --inst_passive_queues_freq              [25;2]
% 1.66/1.00  --inst_dismatching                      true
% 1.66/1.00  --inst_eager_unprocessed_to_passive     true
% 1.66/1.00  --inst_prop_sim_given                   true
% 1.66/1.00  --inst_prop_sim_new                     false
% 1.66/1.00  --inst_subs_new                         false
% 1.66/1.00  --inst_eq_res_simp                      false
% 1.66/1.00  --inst_subs_given                       false
% 1.66/1.00  --inst_orphan_elimination               true
% 1.66/1.00  --inst_learning_loop_flag               true
% 1.66/1.00  --inst_learning_start                   3000
% 1.66/1.00  --inst_learning_factor                  2
% 1.66/1.00  --inst_start_prop_sim_after_learn       3
% 1.66/1.00  --inst_sel_renew                        solver
% 1.66/1.00  --inst_lit_activity_flag                true
% 1.66/1.00  --inst_restr_to_given                   false
% 1.66/1.00  --inst_activity_threshold               500
% 1.66/1.00  --inst_out_proof                        true
% 1.66/1.00  
% 1.66/1.00  ------ Resolution Options
% 1.66/1.00  
% 1.66/1.00  --resolution_flag                       true
% 1.66/1.00  --res_lit_sel                           adaptive
% 1.66/1.00  --res_lit_sel_side                      none
% 1.66/1.00  --res_ordering                          kbo
% 1.66/1.00  --res_to_prop_solver                    active
% 1.66/1.00  --res_prop_simpl_new                    false
% 1.66/1.00  --res_prop_simpl_given                  true
% 1.66/1.00  --res_passive_queue_type                priority_queues
% 1.66/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.66/1.00  --res_passive_queues_freq               [15;5]
% 1.66/1.00  --res_forward_subs                      full
% 1.66/1.00  --res_backward_subs                     full
% 1.66/1.00  --res_forward_subs_resolution           true
% 1.66/1.00  --res_backward_subs_resolution          true
% 1.66/1.00  --res_orphan_elimination                true
% 1.66/1.00  --res_time_limit                        2.
% 1.66/1.00  --res_out_proof                         true
% 1.66/1.00  
% 1.66/1.00  ------ Superposition Options
% 1.66/1.00  
% 1.66/1.00  --superposition_flag                    true
% 1.66/1.00  --sup_passive_queue_type                priority_queues
% 1.66/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.66/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.66/1.00  --demod_completeness_check              fast
% 1.66/1.00  --demod_use_ground                      true
% 1.66/1.00  --sup_to_prop_solver                    passive
% 1.66/1.00  --sup_prop_simpl_new                    true
% 1.66/1.00  --sup_prop_simpl_given                  true
% 1.66/1.00  --sup_fun_splitting                     false
% 1.66/1.00  --sup_smt_interval                      50000
% 1.66/1.00  
% 1.66/1.00  ------ Superposition Simplification Setup
% 1.66/1.00  
% 1.66/1.00  --sup_indices_passive                   []
% 1.66/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.66/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.00  --sup_full_bw                           [BwDemod]
% 1.66/1.00  --sup_immed_triv                        [TrivRules]
% 1.66/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.66/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.00  --sup_immed_bw_main                     []
% 1.66/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.66/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/1.00  
% 1.66/1.00  ------ Combination Options
% 1.66/1.00  
% 1.66/1.00  --comb_res_mult                         3
% 1.66/1.00  --comb_sup_mult                         2
% 1.66/1.00  --comb_inst_mult                        10
% 1.66/1.00  
% 1.66/1.00  ------ Debug Options
% 1.66/1.00  
% 1.66/1.00  --dbg_backtrace                         false
% 1.66/1.00  --dbg_dump_prop_clauses                 false
% 1.66/1.00  --dbg_dump_prop_clauses_file            -
% 1.66/1.00  --dbg_out_stat                          false
% 1.66/1.00  ------ Parsing...
% 1.66/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.66/1.00  
% 1.66/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.66/1.00  
% 1.66/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.66/1.00  
% 1.66/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.66/1.00  ------ Proving...
% 1.66/1.00  ------ Problem Properties 
% 1.66/1.00  
% 1.66/1.00  
% 1.66/1.00  clauses                                 26
% 1.66/1.00  conjectures                             2
% 1.66/1.00  EPR                                     8
% 1.66/1.00  Horn                                    19
% 1.66/1.00  unary                                   8
% 1.66/1.00  binary                                  6
% 1.66/1.00  lits                                    66
% 1.66/1.00  lits eq                                 14
% 1.66/1.00  fd_pure                                 0
% 1.66/1.00  fd_pseudo                               0
% 1.66/1.00  fd_cond                                 5
% 1.66/1.00  fd_pseudo_cond                          3
% 1.66/1.00  AC symbols                              0
% 1.66/1.00  
% 1.66/1.00  ------ Schedule dynamic 5 is on 
% 1.66/1.00  
% 1.66/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.66/1.00  
% 1.66/1.00  
% 1.66/1.00  ------ 
% 1.66/1.00  Current options:
% 1.66/1.00  ------ 
% 1.66/1.00  
% 1.66/1.00  ------ Input Options
% 1.66/1.00  
% 1.66/1.00  --out_options                           all
% 1.66/1.00  --tptp_safe_out                         true
% 1.66/1.00  --problem_path                          ""
% 1.66/1.00  --include_path                          ""
% 1.66/1.00  --clausifier                            res/vclausify_rel
% 1.66/1.00  --clausifier_options                    --mode clausify
% 1.66/1.00  --stdin                                 false
% 1.66/1.00  --stats_out                             all
% 1.66/1.00  
% 1.66/1.00  ------ General Options
% 1.66/1.00  
% 1.66/1.00  --fof                                   false
% 1.66/1.00  --time_out_real                         305.
% 1.66/1.00  --time_out_virtual                      -1.
% 1.66/1.00  --symbol_type_check                     false
% 1.66/1.00  --clausify_out                          false
% 1.66/1.00  --sig_cnt_out                           false
% 1.66/1.00  --trig_cnt_out                          false
% 1.66/1.00  --trig_cnt_out_tolerance                1.
% 1.66/1.00  --trig_cnt_out_sk_spl                   false
% 1.66/1.00  --abstr_cl_out                          false
% 1.66/1.00  
% 1.66/1.00  ------ Global Options
% 1.66/1.00  
% 1.66/1.00  --schedule                              default
% 1.66/1.00  --add_important_lit                     false
% 1.66/1.00  --prop_solver_per_cl                    1000
% 1.66/1.00  --min_unsat_core                        false
% 1.66/1.00  --soft_assumptions                      false
% 1.66/1.00  --soft_lemma_size                       3
% 1.66/1.00  --prop_impl_unit_size                   0
% 1.66/1.00  --prop_impl_unit                        []
% 1.66/1.00  --share_sel_clauses                     true
% 1.66/1.00  --reset_solvers                         false
% 1.66/1.00  --bc_imp_inh                            [conj_cone]
% 1.66/1.00  --conj_cone_tolerance                   3.
% 1.66/1.00  --extra_neg_conj                        none
% 1.66/1.00  --large_theory_mode                     true
% 1.66/1.00  --prolific_symb_bound                   200
% 1.66/1.00  --lt_threshold                          2000
% 1.66/1.00  --clause_weak_htbl                      true
% 1.66/1.00  --gc_record_bc_elim                     false
% 1.66/1.00  
% 1.66/1.00  ------ Preprocessing Options
% 1.66/1.00  
% 1.66/1.00  --preprocessing_flag                    true
% 1.66/1.00  --time_out_prep_mult                    0.1
% 1.66/1.00  --splitting_mode                        input
% 1.66/1.00  --splitting_grd                         true
% 1.66/1.00  --splitting_cvd                         false
% 1.66/1.00  --splitting_cvd_svl                     false
% 1.66/1.00  --splitting_nvd                         32
% 1.66/1.00  --sub_typing                            true
% 1.66/1.00  --prep_gs_sim                           true
% 1.66/1.00  --prep_unflatten                        true
% 1.66/1.00  --prep_res_sim                          true
% 1.66/1.00  --prep_upred                            true
% 1.66/1.00  --prep_sem_filter                       exhaustive
% 1.66/1.00  --prep_sem_filter_out                   false
% 1.66/1.00  --pred_elim                             true
% 1.66/1.00  --res_sim_input                         true
% 1.66/1.00  --eq_ax_congr_red                       true
% 1.66/1.00  --pure_diseq_elim                       true
% 1.66/1.00  --brand_transform                       false
% 1.66/1.00  --non_eq_to_eq                          false
% 1.66/1.00  --prep_def_merge                        true
% 1.66/1.00  --prep_def_merge_prop_impl              false
% 1.66/1.00  --prep_def_merge_mbd                    true
% 1.66/1.00  --prep_def_merge_tr_red                 false
% 1.66/1.00  --prep_def_merge_tr_cl                  false
% 1.66/1.00  --smt_preprocessing                     true
% 1.66/1.00  --smt_ac_axioms                         fast
% 1.66/1.00  --preprocessed_out                      false
% 1.66/1.00  --preprocessed_stats                    false
% 1.66/1.00  
% 1.66/1.00  ------ Abstraction refinement Options
% 1.66/1.00  
% 1.66/1.00  --abstr_ref                             []
% 1.66/1.00  --abstr_ref_prep                        false
% 1.66/1.00  --abstr_ref_until_sat                   false
% 1.66/1.00  --abstr_ref_sig_restrict                funpre
% 1.66/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.66/1.00  --abstr_ref_under                       []
% 1.66/1.00  
% 1.66/1.00  ------ SAT Options
% 1.66/1.00  
% 1.66/1.00  --sat_mode                              false
% 1.66/1.00  --sat_fm_restart_options                ""
% 1.66/1.00  --sat_gr_def                            false
% 1.66/1.00  --sat_epr_types                         true
% 1.66/1.00  --sat_non_cyclic_types                  false
% 1.66/1.00  --sat_finite_models                     false
% 1.66/1.00  --sat_fm_lemmas                         false
% 1.66/1.00  --sat_fm_prep                           false
% 1.66/1.00  --sat_fm_uc_incr                        true
% 1.66/1.00  --sat_out_model                         small
% 1.66/1.00  --sat_out_clauses                       false
% 1.66/1.00  
% 1.66/1.00  ------ QBF Options
% 1.66/1.00  
% 1.66/1.00  --qbf_mode                              false
% 1.66/1.00  --qbf_elim_univ                         false
% 1.66/1.00  --qbf_dom_inst                          none
% 1.66/1.00  --qbf_dom_pre_inst                      false
% 1.66/1.00  --qbf_sk_in                             false
% 1.66/1.00  --qbf_pred_elim                         true
% 1.66/1.00  --qbf_split                             512
% 1.66/1.00  
% 1.66/1.00  ------ BMC1 Options
% 1.66/1.00  
% 1.66/1.00  --bmc1_incremental                      false
% 1.66/1.00  --bmc1_axioms                           reachable_all
% 1.66/1.00  --bmc1_min_bound                        0
% 1.66/1.00  --bmc1_max_bound                        -1
% 1.66/1.00  --bmc1_max_bound_default                -1
% 1.66/1.00  --bmc1_symbol_reachability              true
% 1.66/1.00  --bmc1_property_lemmas                  false
% 1.66/1.00  --bmc1_k_induction                      false
% 1.66/1.00  --bmc1_non_equiv_states                 false
% 1.66/1.00  --bmc1_deadlock                         false
% 1.66/1.00  --bmc1_ucm                              false
% 1.66/1.00  --bmc1_add_unsat_core                   none
% 1.66/1.00  --bmc1_unsat_core_children              false
% 1.66/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.66/1.00  --bmc1_out_stat                         full
% 1.66/1.00  --bmc1_ground_init                      false
% 1.66/1.00  --bmc1_pre_inst_next_state              false
% 1.66/1.00  --bmc1_pre_inst_state                   false
% 1.66/1.00  --bmc1_pre_inst_reach_state             false
% 1.66/1.00  --bmc1_out_unsat_core                   false
% 1.66/1.00  --bmc1_aig_witness_out                  false
% 1.66/1.00  --bmc1_verbose                          false
% 1.66/1.00  --bmc1_dump_clauses_tptp                false
% 1.66/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.66/1.00  --bmc1_dump_file                        -
% 1.66/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.66/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.66/1.00  --bmc1_ucm_extend_mode                  1
% 1.66/1.00  --bmc1_ucm_init_mode                    2
% 1.66/1.00  --bmc1_ucm_cone_mode                    none
% 1.66/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.66/1.00  --bmc1_ucm_relax_model                  4
% 1.66/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.66/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.66/1.00  --bmc1_ucm_layered_model                none
% 1.66/1.00  --bmc1_ucm_max_lemma_size               10
% 1.66/1.00  
% 1.66/1.00  ------ AIG Options
% 1.66/1.00  
% 1.66/1.00  --aig_mode                              false
% 1.66/1.00  
% 1.66/1.00  ------ Instantiation Options
% 1.66/1.00  
% 1.66/1.00  --instantiation_flag                    true
% 1.66/1.00  --inst_sos_flag                         false
% 1.66/1.00  --inst_sos_phase                        true
% 1.66/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.66/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.66/1.00  --inst_lit_sel_side                     none
% 1.66/1.00  --inst_solver_per_active                1400
% 1.66/1.00  --inst_solver_calls_frac                1.
% 1.66/1.00  --inst_passive_queue_type               priority_queues
% 1.66/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.66/1.00  --inst_passive_queues_freq              [25;2]
% 1.66/1.00  --inst_dismatching                      true
% 1.66/1.00  --inst_eager_unprocessed_to_passive     true
% 1.66/1.00  --inst_prop_sim_given                   true
% 1.66/1.00  --inst_prop_sim_new                     false
% 1.66/1.00  --inst_subs_new                         false
% 1.66/1.00  --inst_eq_res_simp                      false
% 1.66/1.00  --inst_subs_given                       false
% 1.66/1.00  --inst_orphan_elimination               true
% 1.66/1.00  --inst_learning_loop_flag               true
% 1.66/1.00  --inst_learning_start                   3000
% 1.66/1.00  --inst_learning_factor                  2
% 1.66/1.00  --inst_start_prop_sim_after_learn       3
% 1.66/1.00  --inst_sel_renew                        solver
% 1.66/1.00  --inst_lit_activity_flag                true
% 1.66/1.00  --inst_restr_to_given                   false
% 1.66/1.00  --inst_activity_threshold               500
% 1.66/1.00  --inst_out_proof                        true
% 1.66/1.00  
% 1.66/1.00  ------ Resolution Options
% 1.66/1.00  
% 1.66/1.00  --resolution_flag                       false
% 1.66/1.00  --res_lit_sel                           adaptive
% 1.66/1.00  --res_lit_sel_side                      none
% 1.66/1.00  --res_ordering                          kbo
% 1.66/1.00  --res_to_prop_solver                    active
% 1.66/1.00  --res_prop_simpl_new                    false
% 1.66/1.00  --res_prop_simpl_given                  true
% 1.66/1.00  --res_passive_queue_type                priority_queues
% 1.66/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.66/1.00  --res_passive_queues_freq               [15;5]
% 1.66/1.00  --res_forward_subs                      full
% 1.66/1.00  --res_backward_subs                     full
% 1.66/1.00  --res_forward_subs_resolution           true
% 1.66/1.00  --res_backward_subs_resolution          true
% 1.66/1.00  --res_orphan_elimination                true
% 1.66/1.00  --res_time_limit                        2.
% 1.66/1.00  --res_out_proof                         true
% 1.66/1.00  
% 1.66/1.00  ------ Superposition Options
% 1.66/1.00  
% 1.66/1.00  --superposition_flag                    true
% 1.66/1.00  --sup_passive_queue_type                priority_queues
% 1.66/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.66/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.66/1.00  --demod_completeness_check              fast
% 1.66/1.00  --demod_use_ground                      true
% 1.66/1.00  --sup_to_prop_solver                    passive
% 1.66/1.00  --sup_prop_simpl_new                    true
% 1.66/1.00  --sup_prop_simpl_given                  true
% 1.66/1.00  --sup_fun_splitting                     false
% 1.66/1.00  --sup_smt_interval                      50000
% 1.66/1.00  
% 1.66/1.00  ------ Superposition Simplification Setup
% 1.66/1.00  
% 1.66/1.00  --sup_indices_passive                   []
% 1.66/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.66/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.66/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.00  --sup_full_bw                           [BwDemod]
% 1.66/1.00  --sup_immed_triv                        [TrivRules]
% 1.66/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.66/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.00  --sup_immed_bw_main                     []
% 1.66/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.66/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.66/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.66/1.00  
% 1.66/1.00  ------ Combination Options
% 1.66/1.00  
% 1.66/1.00  --comb_res_mult                         3
% 1.66/1.00  --comb_sup_mult                         2
% 1.66/1.00  --comb_inst_mult                        10
% 1.66/1.00  
% 1.66/1.00  ------ Debug Options
% 1.66/1.00  
% 1.66/1.00  --dbg_backtrace                         false
% 1.66/1.00  --dbg_dump_prop_clauses                 false
% 1.66/1.00  --dbg_dump_prop_clauses_file            -
% 1.66/1.00  --dbg_out_stat                          false
% 1.66/1.00  
% 1.66/1.00  
% 1.66/1.00  
% 1.66/1.00  
% 1.66/1.00  ------ Proving...
% 1.66/1.00  
% 1.66/1.00  
% 1.66/1.00  % SZS status Theorem for theBenchmark.p
% 1.66/1.00  
% 1.66/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.66/1.00  
% 1.66/1.00  fof(f16,conjecture,(
% 1.66/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.00  
% 1.66/1.00  fof(f17,negated_conjecture,(
% 1.66/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.66/1.00    inference(negated_conjecture,[],[f16])).
% 1.66/1.00  
% 1.66/1.00  fof(f34,plain,(
% 1.66/1.00    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.66/1.00    inference(ennf_transformation,[],[f17])).
% 1.66/1.00  
% 1.66/1.00  fof(f35,plain,(
% 1.66/1.00    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.66/1.00    inference(flattening,[],[f34])).
% 1.66/1.00  
% 1.66/1.00  fof(f47,plain,(
% 1.66/1.00    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.66/1.00    inference(nnf_transformation,[],[f35])).
% 1.66/1.00  
% 1.66/1.00  fof(f48,plain,(
% 1.66/1.00    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.66/1.00    inference(flattening,[],[f47])).
% 1.66/1.00  
% 1.66/1.00  fof(f50,plain,(
% 1.66/1.00    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK4) | ~v3_tex_2(sK4,X0)) & (v1_zfmisc_1(sK4) | v3_tex_2(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK4))) )),
% 1.66/1.00    introduced(choice_axiom,[])).
% 1.66/1.00  
% 1.66/1.00  fof(f49,plain,(
% 1.66/1.00    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 1.66/1.00    introduced(choice_axiom,[])).
% 1.66/1.00  
% 1.66/1.00  fof(f51,plain,(
% 1.66/1.00    ((~v1_zfmisc_1(sK4) | ~v3_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v3_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 1.66/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f48,f50,f49])).
% 1.66/1.00  
% 1.66/1.00  fof(f82,plain,(
% 1.66/1.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.66/1.00    inference(cnf_transformation,[],[f51])).
% 1.66/1.00  
% 1.66/1.00  fof(f13,axiom,(
% 1.66/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.00  
% 1.66/1.00  fof(f28,plain,(
% 1.66/1.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.66/1.00    inference(ennf_transformation,[],[f13])).
% 1.66/1.00  
% 1.66/1.00  fof(f29,plain,(
% 1.66/1.00    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.66/1.00    inference(flattening,[],[f28])).
% 1.66/1.00  
% 1.66/1.00  fof(f41,plain,(
% 1.66/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.66/1.00    inference(nnf_transformation,[],[f29])).
% 1.66/1.00  
% 1.66/1.00  fof(f42,plain,(
% 1.66/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.66/1.00    inference(flattening,[],[f41])).
% 1.66/1.00  
% 1.66/1.00  fof(f43,plain,(
% 1.66/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.66/1.00    inference(rectify,[],[f42])).
% 1.66/1.00  
% 1.66/1.00  fof(f44,plain,(
% 1.66/1.00    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.66/1.00    introduced(choice_axiom,[])).
% 1.66/1.00  
% 1.66/1.00  fof(f45,plain,(
% 1.66/1.00    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.66/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 1.66/1.00  
% 1.66/1.00  fof(f72,plain,(
% 1.66/1.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.66/1.00    inference(cnf_transformation,[],[f45])).
% 1.66/1.00  
% 1.66/1.00  fof(f80,plain,(
% 1.66/1.00    l1_pre_topc(sK3)),
% 1.66/1.00    inference(cnf_transformation,[],[f51])).
% 1.66/1.00  
% 1.66/1.00  fof(f15,axiom,(
% 1.66/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.00  
% 1.66/1.00  fof(f32,plain,(
% 1.66/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.66/1.00    inference(ennf_transformation,[],[f15])).
% 1.66/1.00  
% 1.66/1.00  fof(f33,plain,(
% 1.66/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/1.00    inference(flattening,[],[f32])).
% 1.66/1.00  
% 1.66/1.00  fof(f46,plain,(
% 1.66/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/1.00    inference(nnf_transformation,[],[f33])).
% 1.66/1.00  
% 1.66/1.00  fof(f76,plain,(
% 1.66/1.00    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/1.00    inference(cnf_transformation,[],[f46])).
% 1.66/1.00  
% 1.66/1.00  fof(f77,plain,(
% 1.66/1.00    ~v2_struct_0(sK3)),
% 1.66/1.00    inference(cnf_transformation,[],[f51])).
% 1.66/1.00  
% 1.66/1.00  fof(f78,plain,(
% 1.66/1.00    v2_pre_topc(sK3)),
% 1.66/1.00    inference(cnf_transformation,[],[f51])).
% 1.66/1.00  
% 1.66/1.00  fof(f79,plain,(
% 1.66/1.00    v2_tdlat_3(sK3)),
% 1.66/1.00    inference(cnf_transformation,[],[f51])).
% 1.66/1.00  
% 1.66/1.00  fof(f83,plain,(
% 1.66/1.00    v1_zfmisc_1(sK4) | v3_tex_2(sK4,sK3)),
% 1.66/1.00    inference(cnf_transformation,[],[f51])).
% 1.66/1.00  
% 1.66/1.00  fof(f81,plain,(
% 1.66/1.00    ~v1_xboole_0(sK4)),
% 1.66/1.00    inference(cnf_transformation,[],[f51])).
% 1.66/1.00  
% 1.66/1.00  fof(f68,plain,(
% 1.66/1.00    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.66/1.00    inference(cnf_transformation,[],[f45])).
% 1.66/1.00  
% 1.66/1.00  fof(f75,plain,(
% 1.66/1.00    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/1.00    inference(cnf_transformation,[],[f46])).
% 1.66/1.00  
% 1.66/1.00  fof(f10,axiom,(
% 1.66/1.00    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 1.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.00  
% 1.66/1.00  fof(f24,plain,(
% 1.66/1.00    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 1.66/1.00    inference(ennf_transformation,[],[f10])).
% 1.66/1.00  
% 1.66/1.00  fof(f63,plain,(
% 1.66/1.00    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 1.66/1.00    inference(cnf_transformation,[],[f24])).
% 1.66/1.00  
% 1.66/1.00  fof(f84,plain,(
% 1.66/1.00    ~v1_zfmisc_1(sK4) | ~v3_tex_2(sK4,sK3)),
% 1.66/1.00    inference(cnf_transformation,[],[f51])).
% 1.66/1.00  
% 1.66/1.00  fof(f70,plain,(
% 1.66/1.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.66/1.00    inference(cnf_transformation,[],[f45])).
% 1.66/1.00  
% 1.66/1.00  fof(f14,axiom,(
% 1.66/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.00  
% 1.66/1.00  fof(f30,plain,(
% 1.66/1.00    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.66/1.00    inference(ennf_transformation,[],[f14])).
% 1.66/1.00  
% 1.66/1.00  fof(f31,plain,(
% 1.66/1.00    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.66/1.00    inference(flattening,[],[f30])).
% 1.66/1.00  
% 1.66/1.00  fof(f74,plain,(
% 1.66/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.66/1.00    inference(cnf_transformation,[],[f31])).
% 1.66/1.00  
% 1.66/1.00  fof(f71,plain,(
% 1.66/1.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | v2_tex_2(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.66/1.00    inference(cnf_transformation,[],[f45])).
% 1.66/1.00  
% 1.66/1.00  fof(f3,axiom,(
% 1.66/1.00    v1_xboole_0(k1_xboole_0)),
% 1.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.00  
% 1.66/1.00  fof(f55,plain,(
% 1.66/1.00    v1_xboole_0(k1_xboole_0)),
% 1.66/1.00    inference(cnf_transformation,[],[f3])).
% 1.66/1.00  
% 1.66/1.00  fof(f6,axiom,(
% 1.66/1.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.00  
% 1.66/1.00  fof(f20,plain,(
% 1.66/1.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.66/1.00    inference(ennf_transformation,[],[f6])).
% 1.66/1.00  
% 1.66/1.00  fof(f59,plain,(
% 1.66/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.66/1.00    inference(cnf_transformation,[],[f20])).
% 1.66/1.00  
% 1.66/1.00  fof(f9,axiom,(
% 1.66/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.66/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.66/1.00  
% 1.66/1.00  fof(f23,plain,(
% 1.66/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.66/1.00    inference(ennf_transformation,[],[f9])).
% 1.66/1.00  
% 1.66/1.00  fof(f62,plain,(
% 1.66/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.66/1.00    inference(cnf_transformation,[],[f23])).
% 1.66/1.00  
% 1.66/1.00  fof(f73,plain,(
% 1.66/1.00    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK2(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.66/1.00    inference(cnf_transformation,[],[f45])).
% 1.66/1.00  
% 1.66/1.00  cnf(c_27,negated_conjecture,
% 1.66/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.66/1.00      inference(cnf_transformation,[],[f82]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_3268,plain,
% 1.66/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 1.66/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_17,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/1.00      | ~ v2_tex_2(X0,X1)
% 1.66/1.00      | v3_tex_2(X0,X1)
% 1.66/1.00      | r1_tarski(X0,sK2(X1,X0))
% 1.66/1.00      | ~ l1_pre_topc(X1) ),
% 1.66/1.00      inference(cnf_transformation,[],[f72]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_29,negated_conjecture,
% 1.66/1.00      ( l1_pre_topc(sK3) ),
% 1.66/1.00      inference(cnf_transformation,[],[f80]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_746,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/1.00      | ~ v2_tex_2(X0,X1)
% 1.66/1.00      | v3_tex_2(X0,X1)
% 1.66/1.00      | r1_tarski(X0,sK2(X1,X0))
% 1.66/1.00      | sK3 != X1 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_29]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_747,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | ~ v2_tex_2(X0,sK3)
% 1.66/1.00      | v3_tex_2(X0,sK3)
% 1.66/1.00      | r1_tarski(X0,sK2(sK3,X0)) ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_746]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_3262,plain,
% 1.66/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.66/1.00      | v2_tex_2(X0,sK3) != iProver_top
% 1.66/1.00      | v3_tex_2(X0,sK3) = iProver_top
% 1.66/1.00      | r1_tarski(X0,sK2(sK3,X0)) = iProver_top ),
% 1.66/1.00      inference(predicate_to_equality,[status(thm)],[c_747]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_3583,plain,
% 1.66/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 1.66/1.00      | v3_tex_2(sK4,sK3) = iProver_top
% 1.66/1.00      | r1_tarski(sK4,sK2(sK3,sK4)) = iProver_top ),
% 1.66/1.00      inference(superposition,[status(thm)],[c_3268,c_3262]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_38,plain,
% 1.66/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 1.66/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_23,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/1.00      | v2_tex_2(X0,X1)
% 1.66/1.00      | v2_struct_0(X1)
% 1.66/1.00      | ~ l1_pre_topc(X1)
% 1.66/1.00      | ~ v2_tdlat_3(X1)
% 1.66/1.00      | ~ v2_pre_topc(X1)
% 1.66/1.00      | ~ v1_zfmisc_1(X0)
% 1.66/1.00      | v1_xboole_0(X0) ),
% 1.66/1.00      inference(cnf_transformation,[],[f76]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_32,negated_conjecture,
% 1.66/1.00      ( ~ v2_struct_0(sK3) ),
% 1.66/1.00      inference(cnf_transformation,[],[f77]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_457,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/1.00      | v2_tex_2(X0,X1)
% 1.66/1.00      | ~ l1_pre_topc(X1)
% 1.66/1.00      | ~ v2_tdlat_3(X1)
% 1.66/1.00      | ~ v2_pre_topc(X1)
% 1.66/1.00      | ~ v1_zfmisc_1(X0)
% 1.66/1.00      | v1_xboole_0(X0)
% 1.66/1.00      | sK3 != X1 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_458,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | v2_tex_2(X0,sK3)
% 1.66/1.00      | ~ l1_pre_topc(sK3)
% 1.66/1.00      | ~ v2_tdlat_3(sK3)
% 1.66/1.00      | ~ v2_pre_topc(sK3)
% 1.66/1.00      | ~ v1_zfmisc_1(X0)
% 1.66/1.00      | v1_xboole_0(X0) ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_457]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_31,negated_conjecture,
% 1.66/1.00      ( v2_pre_topc(sK3) ),
% 1.66/1.00      inference(cnf_transformation,[],[f78]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_30,negated_conjecture,
% 1.66/1.00      ( v2_tdlat_3(sK3) ),
% 1.66/1.00      inference(cnf_transformation,[],[f79]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_460,plain,
% 1.66/1.00      ( v2_tex_2(X0,sK3)
% 1.66/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | ~ v1_zfmisc_1(X0)
% 1.66/1.00      | v1_xboole_0(X0) ),
% 1.66/1.00      inference(global_propositional_subsumption,
% 1.66/1.00                [status(thm)],
% 1.66/1.00                [c_458,c_31,c_30,c_29]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_461,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | v2_tex_2(X0,sK3)
% 1.66/1.00      | ~ v1_zfmisc_1(X0)
% 1.66/1.00      | v1_xboole_0(X0) ),
% 1.66/1.00      inference(renaming,[status(thm)],[c_460]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_26,negated_conjecture,
% 1.66/1.00      ( v3_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 1.66/1.00      inference(cnf_transformation,[],[f83]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_259,plain,
% 1.66/1.00      ( v1_zfmisc_1(sK4) | v3_tex_2(sK4,sK3) ),
% 1.66/1.00      inference(prop_impl,[status(thm)],[c_26]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_260,plain,
% 1.66/1.00      ( v3_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) ),
% 1.66/1.00      inference(renaming,[status(thm)],[c_259]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1003,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | v2_tex_2(X0,sK3)
% 1.66/1.00      | v3_tex_2(sK4,sK3)
% 1.66/1.00      | v1_xboole_0(X0)
% 1.66/1.00      | sK4 != X0 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_461,c_260]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1004,plain,
% 1.66/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | v2_tex_2(sK4,sK3)
% 1.66/1.00      | v3_tex_2(sK4,sK3)
% 1.66/1.00      | v1_xboole_0(sK4) ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_1003]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_28,negated_conjecture,
% 1.66/1.00      ( ~ v1_xboole_0(sK4) ),
% 1.66/1.00      inference(cnf_transformation,[],[f81]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1006,plain,
% 1.66/1.00      ( v3_tex_2(sK4,sK3) | v2_tex_2(sK4,sK3) ),
% 1.66/1.00      inference(global_propositional_subsumption,
% 1.66/1.00                [status(thm)],
% 1.66/1.00                [c_1004,c_28,c_27]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1007,plain,
% 1.66/1.00      ( v2_tex_2(sK4,sK3) | v3_tex_2(sK4,sK3) ),
% 1.66/1.00      inference(renaming,[status(thm)],[c_1006]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_21,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/1.00      | v2_tex_2(X0,X1)
% 1.66/1.00      | ~ v3_tex_2(X0,X1)
% 1.66/1.00      | ~ l1_pre_topc(X1) ),
% 1.66/1.00      inference(cnf_transformation,[],[f68]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_673,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/1.00      | v2_tex_2(X0,X1)
% 1.66/1.00      | ~ v3_tex_2(X0,X1)
% 1.66/1.00      | sK3 != X1 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_674,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | v2_tex_2(X0,sK3)
% 1.66/1.00      | ~ v3_tex_2(X0,sK3) ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_673]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1442,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | v2_tex_2(X0,sK3)
% 1.66/1.00      | v2_tex_2(sK4,sK3)
% 1.66/1.00      | sK3 != sK3
% 1.66/1.00      | sK4 != X0 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_1007,c_674]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1443,plain,
% 1.66/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | v2_tex_2(sK4,sK3) ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_1442]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1444,plain,
% 1.66/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.66/1.00      | v2_tex_2(sK4,sK3) = iProver_top ),
% 1.66/1.00      inference(predicate_to_equality,[status(thm)],[c_1443]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_24,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/1.00      | ~ v2_tex_2(X0,X1)
% 1.66/1.00      | v2_struct_0(X1)
% 1.66/1.00      | ~ l1_pre_topc(X1)
% 1.66/1.00      | ~ v2_tdlat_3(X1)
% 1.66/1.00      | ~ v2_pre_topc(X1)
% 1.66/1.00      | v1_zfmisc_1(X0)
% 1.66/1.00      | v1_xboole_0(X0) ),
% 1.66/1.00      inference(cnf_transformation,[],[f75]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_11,plain,
% 1.66/1.00      ( v1_zfmisc_1(X0) | ~ v1_xboole_0(X0) ),
% 1.66/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_183,plain,
% 1.66/1.00      ( v1_zfmisc_1(X0)
% 1.66/1.00      | ~ v2_pre_topc(X1)
% 1.66/1.00      | ~ v2_tdlat_3(X1)
% 1.66/1.00      | ~ l1_pre_topc(X1)
% 1.66/1.00      | v2_struct_0(X1)
% 1.66/1.00      | ~ v2_tex_2(X0,X1)
% 1.66/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ),
% 1.66/1.00      inference(global_propositional_subsumption,
% 1.66/1.00                [status(thm)],
% 1.66/1.00                [c_24,c_11]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_184,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/1.00      | ~ v2_tex_2(X0,X1)
% 1.66/1.00      | v2_struct_0(X1)
% 1.66/1.00      | ~ l1_pre_topc(X1)
% 1.66/1.00      | ~ v2_tdlat_3(X1)
% 1.66/1.00      | ~ v2_pre_topc(X1)
% 1.66/1.00      | v1_zfmisc_1(X0) ),
% 1.66/1.00      inference(renaming,[status(thm)],[c_183]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_436,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/1.00      | ~ v2_tex_2(X0,X1)
% 1.66/1.00      | ~ l1_pre_topc(X1)
% 1.66/1.00      | ~ v2_tdlat_3(X1)
% 1.66/1.00      | ~ v2_pre_topc(X1)
% 1.66/1.00      | v1_zfmisc_1(X0)
% 1.66/1.00      | sK3 != X1 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_184,c_32]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_437,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | ~ v2_tex_2(X0,sK3)
% 1.66/1.00      | ~ l1_pre_topc(sK3)
% 1.66/1.00      | ~ v2_tdlat_3(sK3)
% 1.66/1.00      | ~ v2_pre_topc(sK3)
% 1.66/1.00      | v1_zfmisc_1(X0) ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_436]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_441,plain,
% 1.66/1.00      ( ~ v2_tex_2(X0,sK3)
% 1.66/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | v1_zfmisc_1(X0) ),
% 1.66/1.00      inference(global_propositional_subsumption,
% 1.66/1.00                [status(thm)],
% 1.66/1.00                [c_437,c_31,c_30,c_29]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_442,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | ~ v2_tex_2(X0,sK3)
% 1.66/1.00      | v1_zfmisc_1(X0) ),
% 1.66/1.00      inference(renaming,[status(thm)],[c_441]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_25,negated_conjecture,
% 1.66/1.00      ( ~ v3_tex_2(sK4,sK3) | ~ v1_zfmisc_1(sK4) ),
% 1.66/1.00      inference(cnf_transformation,[],[f84]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_257,plain,
% 1.66/1.00      ( ~ v1_zfmisc_1(sK4) | ~ v3_tex_2(sK4,sK3) ),
% 1.66/1.00      inference(prop_impl,[status(thm)],[c_25]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_258,plain,
% 1.66/1.00      ( ~ v3_tex_2(sK4,sK3) | ~ v1_zfmisc_1(sK4) ),
% 1.66/1.00      inference(renaming,[status(thm)],[c_257]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_987,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | ~ v2_tex_2(X0,sK3)
% 1.66/1.00      | ~ v3_tex_2(sK4,sK3)
% 1.66/1.00      | sK4 != X0 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_442,c_258]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_988,plain,
% 1.66/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | ~ v2_tex_2(sK4,sK3)
% 1.66/1.00      | ~ v3_tex_2(sK4,sK3) ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_987]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_990,plain,
% 1.66/1.00      ( ~ v2_tex_2(sK4,sK3) | ~ v3_tex_2(sK4,sK3) ),
% 1.66/1.00      inference(global_propositional_subsumption,
% 1.66/1.00                [status(thm)],
% 1.66/1.00                [c_988,c_27]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1461,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | ~ v2_tex_2(X0,sK3)
% 1.66/1.00      | ~ v2_tex_2(sK4,sK3)
% 1.66/1.00      | r1_tarski(X0,sK2(sK3,X0))
% 1.66/1.00      | sK3 != sK3
% 1.66/1.00      | sK4 != X0 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_990,c_747]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1462,plain,
% 1.66/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | ~ v2_tex_2(sK4,sK3)
% 1.66/1.00      | r1_tarski(sK4,sK2(sK3,sK4)) ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_1461]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1463,plain,
% 1.66/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.66/1.00      | v2_tex_2(sK4,sK3) != iProver_top
% 1.66/1.00      | r1_tarski(sK4,sK2(sK3,sK4)) = iProver_top ),
% 1.66/1.00      inference(predicate_to_equality,[status(thm)],[c_1462]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_3586,plain,
% 1.66/1.00      ( r1_tarski(sK4,sK2(sK3,sK4)) = iProver_top ),
% 1.66/1.00      inference(global_propositional_subsumption,
% 1.66/1.00                [status(thm)],
% 1.66/1.00                [c_3583,c_38,c_1444,c_1463]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_19,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/1.00      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/1.00      | ~ v2_tex_2(X0,X1)
% 1.66/1.00      | v3_tex_2(X0,X1)
% 1.66/1.00      | ~ l1_pre_topc(X1) ),
% 1.66/1.00      inference(cnf_transformation,[],[f70]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_710,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/1.00      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/1.00      | ~ v2_tex_2(X0,X1)
% 1.66/1.00      | v3_tex_2(X0,X1)
% 1.66/1.00      | sK3 != X1 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_711,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | m1_subset_1(sK2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | ~ v2_tex_2(X0,sK3)
% 1.66/1.00      | v3_tex_2(X0,sK3) ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_710]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_3264,plain,
% 1.66/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.66/1.00      | m1_subset_1(sK2(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 1.66/1.00      | v2_tex_2(X0,sK3) != iProver_top
% 1.66/1.00      | v3_tex_2(X0,sK3) = iProver_top ),
% 1.66/1.00      inference(predicate_to_equality,[status(thm)],[c_711]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_22,plain,
% 1.66/1.00      ( ~ r1_tarski(X0,X1)
% 1.66/1.00      | ~ v1_zfmisc_1(X1)
% 1.66/1.00      | v1_xboole_0(X1)
% 1.66/1.00      | v1_xboole_0(X0)
% 1.66/1.00      | X1 = X0 ),
% 1.66/1.00      inference(cnf_transformation,[],[f74]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_963,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | ~ v2_tex_2(X0,sK3)
% 1.66/1.00      | ~ r1_tarski(X1,X2)
% 1.66/1.00      | v1_xboole_0(X2)
% 1.66/1.00      | v1_xboole_0(X1)
% 1.66/1.00      | X2 != X0
% 1.66/1.00      | X1 = X2 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_442,c_22]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_964,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | ~ v2_tex_2(X0,sK3)
% 1.66/1.00      | ~ r1_tarski(X1,X0)
% 1.66/1.00      | v1_xboole_0(X1)
% 1.66/1.00      | v1_xboole_0(X0)
% 1.66/1.00      | X1 = X0 ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_963]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_3260,plain,
% 1.66/1.00      ( X0 = X1
% 1.66/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.66/1.00      | v2_tex_2(X1,sK3) != iProver_top
% 1.66/1.00      | r1_tarski(X0,X1) != iProver_top
% 1.66/1.00      | v1_xboole_0(X1) = iProver_top
% 1.66/1.00      | v1_xboole_0(X0) = iProver_top ),
% 1.66/1.00      inference(predicate_to_equality,[status(thm)],[c_964]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_4199,plain,
% 1.66/1.00      ( sK2(sK3,X0) = X1
% 1.66/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.66/1.00      | v2_tex_2(X0,sK3) != iProver_top
% 1.66/1.00      | v2_tex_2(sK2(sK3,X0),sK3) != iProver_top
% 1.66/1.00      | v3_tex_2(X0,sK3) = iProver_top
% 1.66/1.00      | r1_tarski(X1,sK2(sK3,X0)) != iProver_top
% 1.66/1.00      | v1_xboole_0(X1) = iProver_top
% 1.66/1.00      | v1_xboole_0(sK2(sK3,X0)) = iProver_top ),
% 1.66/1.00      inference(superposition,[status(thm)],[c_3264,c_3260]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_18,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/1.00      | ~ v2_tex_2(X0,X1)
% 1.66/1.00      | v2_tex_2(sK2(X1,X0),X1)
% 1.66/1.00      | v3_tex_2(X0,X1)
% 1.66/1.00      | ~ l1_pre_topc(X1) ),
% 1.66/1.00      inference(cnf_transformation,[],[f71]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_728,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/1.00      | ~ v2_tex_2(X0,X1)
% 1.66/1.00      | v2_tex_2(sK2(X1,X0),X1)
% 1.66/1.00      | v3_tex_2(X0,X1)
% 1.66/1.00      | sK3 != X1 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_729,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | ~ v2_tex_2(X0,sK3)
% 1.66/1.00      | v2_tex_2(sK2(sK3,X0),sK3)
% 1.66/1.00      | v3_tex_2(X0,sK3) ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_728]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_730,plain,
% 1.66/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.66/1.00      | v2_tex_2(X0,sK3) != iProver_top
% 1.66/1.00      | v2_tex_2(sK2(sK3,X0),sK3) = iProver_top
% 1.66/1.00      | v3_tex_2(X0,sK3) = iProver_top ),
% 1.66/1.00      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_4755,plain,
% 1.66/1.00      ( v2_tex_2(X0,sK3) != iProver_top
% 1.66/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.66/1.00      | sK2(sK3,X0) = X1
% 1.66/1.00      | v3_tex_2(X0,sK3) = iProver_top
% 1.66/1.00      | r1_tarski(X1,sK2(sK3,X0)) != iProver_top
% 1.66/1.00      | v1_xboole_0(X1) = iProver_top
% 1.66/1.00      | v1_xboole_0(sK2(sK3,X0)) = iProver_top ),
% 1.66/1.00      inference(global_propositional_subsumption,
% 1.66/1.00                [status(thm)],
% 1.66/1.00                [c_4199,c_730]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_4756,plain,
% 1.66/1.00      ( sK2(sK3,X0) = X1
% 1.66/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.66/1.00      | v2_tex_2(X0,sK3) != iProver_top
% 1.66/1.00      | v3_tex_2(X0,sK3) = iProver_top
% 1.66/1.00      | r1_tarski(X1,sK2(sK3,X0)) != iProver_top
% 1.66/1.00      | v1_xboole_0(X1) = iProver_top
% 1.66/1.00      | v1_xboole_0(sK2(sK3,X0)) = iProver_top ),
% 1.66/1.00      inference(renaming,[status(thm)],[c_4755]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_4766,plain,
% 1.66/1.00      ( sK2(sK3,sK4) = X0
% 1.66/1.00      | v2_tex_2(sK4,sK3) != iProver_top
% 1.66/1.00      | v3_tex_2(sK4,sK3) = iProver_top
% 1.66/1.00      | r1_tarski(X0,sK2(sK3,sK4)) != iProver_top
% 1.66/1.00      | v1_xboole_0(X0) = iProver_top
% 1.66/1.00      | v1_xboole_0(sK2(sK3,sK4)) = iProver_top ),
% 1.66/1.00      inference(superposition,[status(thm)],[c_3268,c_4756]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_3,plain,
% 1.66/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 1.66/1.00      inference(cnf_transformation,[],[f55]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_102,plain,
% 1.66/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.66/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_992,plain,
% 1.66/1.00      ( v2_tex_2(sK4,sK3) != iProver_top
% 1.66/1.00      | v3_tex_2(sK4,sK3) != iProver_top ),
% 1.66/1.00      inference(predicate_to_equality,[status(thm)],[c_990]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_2646,plain,
% 1.66/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 1.66/1.00      theory(equality) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_3493,plain,
% 1.66/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK4) | sK4 != X0 ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_2646]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_3495,plain,
% 1.66/1.00      ( v1_xboole_0(sK4)
% 1.66/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 1.66/1.00      | sK4 != k1_xboole_0 ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_3493]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_7,plain,
% 1.66/1.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 1.66/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_3600,plain,
% 1.66/1.00      ( ~ r1_tarski(sK4,k1_xboole_0) | k1_xboole_0 = sK4 ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_2643,plain,( X0 = X0 ),theory(equality) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_3613,plain,
% 1.66/1.00      ( sK4 = sK4 ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_2643]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_2644,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_3595,plain,
% 1.66/1.00      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_2644]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_3847,plain,
% 1.66/1.00      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_3595]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_3848,plain,
% 1.66/1.00      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_3847]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_2648,plain,
% 1.66/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.66/1.00      theory(equality) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_3623,plain,
% 1.66/1.00      ( r1_tarski(X0,X1)
% 1.66/1.00      | ~ r1_tarski(sK4,sK2(sK3,sK4))
% 1.66/1.00      | X1 != sK2(sK3,sK4)
% 1.66/1.00      | X0 != sK4 ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_2648]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_3879,plain,
% 1.66/1.00      ( r1_tarski(sK4,X0)
% 1.66/1.00      | ~ r1_tarski(sK4,sK2(sK3,sK4))
% 1.66/1.00      | X0 != sK2(sK3,sK4)
% 1.66/1.00      | sK4 != sK4 ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_3623]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_3881,plain,
% 1.66/1.00      ( ~ r1_tarski(sK4,sK2(sK3,sK4))
% 1.66/1.00      | r1_tarski(sK4,k1_xboole_0)
% 1.66/1.00      | sK4 != sK4
% 1.66/1.00      | k1_xboole_0 != sK2(sK3,sK4) ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_3879]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_10,plain,
% 1.66/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 1.66/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_3904,plain,
% 1.66/1.00      ( ~ v1_xboole_0(X0)
% 1.66/1.00      | ~ v1_xboole_0(sK2(sK3,sK4))
% 1.66/1.00      | X0 = sK2(sK3,sK4) ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_3905,plain,
% 1.66/1.00      ( X0 = sK2(sK3,sK4)
% 1.66/1.00      | v1_xboole_0(X0) != iProver_top
% 1.66/1.00      | v1_xboole_0(sK2(sK3,sK4)) != iProver_top ),
% 1.66/1.00      inference(predicate_to_equality,[status(thm)],[c_3904]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_3907,plain,
% 1.66/1.00      ( k1_xboole_0 = sK2(sK3,sK4)
% 1.66/1.00      | v1_xboole_0(sK2(sK3,sK4)) != iProver_top
% 1.66/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.66/1.00      inference(instantiation,[status(thm)],[c_3905]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_4801,plain,
% 1.66/1.00      ( v1_xboole_0(X0) = iProver_top
% 1.66/1.00      | r1_tarski(X0,sK2(sK3,sK4)) != iProver_top
% 1.66/1.00      | sK2(sK3,sK4) = X0 ),
% 1.66/1.00      inference(global_propositional_subsumption,
% 1.66/1.00                [status(thm)],
% 1.66/1.00                [c_4766,c_28,c_27,c_38,c_3,c_102,c_992,c_1443,c_1444,
% 1.66/1.00                 c_1462,c_3495,c_3600,c_3613,c_3848,c_3881,c_3907]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_4802,plain,
% 1.66/1.00      ( sK2(sK3,sK4) = X0
% 1.66/1.00      | r1_tarski(X0,sK2(sK3,sK4)) != iProver_top
% 1.66/1.00      | v1_xboole_0(X0) = iProver_top ),
% 1.66/1.00      inference(renaming,[status(thm)],[c_4801]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_4809,plain,
% 1.66/1.00      ( sK2(sK3,sK4) = sK4 | v1_xboole_0(sK4) = iProver_top ),
% 1.66/1.00      inference(superposition,[status(thm)],[c_3586,c_4802]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_16,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/1.00      | ~ v2_tex_2(X0,X1)
% 1.66/1.00      | v3_tex_2(X0,X1)
% 1.66/1.00      | ~ l1_pre_topc(X1)
% 1.66/1.00      | sK2(X1,X0) != X0 ),
% 1.66/1.00      inference(cnf_transformation,[],[f73]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_764,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.66/1.00      | ~ v2_tex_2(X0,X1)
% 1.66/1.00      | v3_tex_2(X0,X1)
% 1.66/1.00      | sK2(X1,X0) != X0
% 1.66/1.00      | sK3 != X1 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_29]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_765,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | ~ v2_tex_2(X0,sK3)
% 1.66/1.00      | v3_tex_2(X0,sK3)
% 1.66/1.00      | sK2(sK3,X0) != X0 ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_764]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1453,plain,
% 1.66/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | ~ v2_tex_2(X0,sK3)
% 1.66/1.00      | ~ v2_tex_2(sK4,sK3)
% 1.66/1.00      | sK2(sK3,X0) != X0
% 1.66/1.00      | sK3 != sK3
% 1.66/1.00      | sK4 != X0 ),
% 1.66/1.00      inference(resolution_lifted,[status(thm)],[c_990,c_765]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_1454,plain,
% 1.66/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.66/1.00      | ~ v2_tex_2(sK4,sK3)
% 1.66/1.00      | sK2(sK3,sK4) != sK4 ),
% 1.66/1.00      inference(unflattening,[status(thm)],[c_1453]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(c_37,plain,
% 1.66/1.00      ( v1_xboole_0(sK4) != iProver_top ),
% 1.66/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 1.66/1.00  
% 1.66/1.00  cnf(contradiction,plain,
% 1.66/1.00      ( $false ),
% 1.66/1.00      inference(minisat,[status(thm)],[c_4809,c_1454,c_1443,c_27,c_37]) ).
% 1.66/1.00  
% 1.66/1.00  
% 1.66/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.66/1.00  
% 1.66/1.00  ------                               Statistics
% 1.66/1.00  
% 1.66/1.00  ------ General
% 1.66/1.00  
% 1.66/1.00  abstr_ref_over_cycles:                  0
% 1.66/1.00  abstr_ref_under_cycles:                 0
% 1.66/1.00  gc_basic_clause_elim:                   0
% 1.66/1.00  forced_gc_time:                         0
% 1.66/1.00  parsing_time:                           0.013
% 1.66/1.00  unif_index_cands_time:                  0.
% 1.66/1.00  unif_index_add_time:                    0.
% 1.66/1.00  orderings_time:                         0.
% 1.66/1.00  out_proof_time:                         0.012
% 1.66/1.00  total_time:                             0.137
% 1.66/1.00  num_of_symbols:                         54
% 1.66/1.00  num_of_terms:                           2045
% 1.66/1.00  
% 1.66/1.00  ------ Preprocessing
% 1.66/1.00  
% 1.66/1.00  num_of_splits:                          0
% 1.66/1.00  num_of_split_atoms:                     0
% 1.66/1.00  num_of_reused_defs:                     0
% 1.66/1.00  num_eq_ax_congr_red:                    35
% 1.66/1.00  num_of_sem_filtered_clauses:            1
% 1.66/1.00  num_of_subtypes:                        0
% 1.66/1.00  monotx_restored_types:                  0
% 1.66/1.00  sat_num_of_epr_types:                   0
% 1.66/1.00  sat_num_of_non_cyclic_types:            0
% 1.66/1.00  sat_guarded_non_collapsed_types:        0
% 1.66/1.00  num_pure_diseq_elim:                    0
% 1.66/1.00  simp_replaced_by:                       0
% 1.66/1.00  res_preprocessed:                       136
% 1.66/1.00  prep_upred:                             0
% 1.66/1.00  prep_unflattend:                        141
% 1.66/1.00  smt_new_axioms:                         0
% 1.66/1.00  pred_elim_cands:                        7
% 1.66/1.00  pred_elim:                              5
% 1.66/1.00  pred_elim_cl:                           7
% 1.66/1.00  pred_elim_cycles:                       16
% 1.66/1.00  merged_defs:                            10
% 1.66/1.00  merged_defs_ncl:                        0
% 1.66/1.00  bin_hyper_res:                          10
% 1.66/1.00  prep_cycles:                            4
% 1.66/1.00  pred_elim_time:                         0.033
% 1.66/1.00  splitting_time:                         0.
% 1.66/1.00  sem_filter_time:                        0.
% 1.66/1.00  monotx_time:                            0.001
% 1.66/1.00  subtype_inf_time:                       0.
% 1.66/1.00  
% 1.66/1.00  ------ Problem properties
% 1.66/1.00  
% 1.66/1.00  clauses:                                26
% 1.66/1.00  conjectures:                            2
% 1.66/1.00  epr:                                    8
% 1.66/1.00  horn:                                   19
% 1.66/1.00  ground:                                 5
% 1.66/1.00  unary:                                  8
% 1.66/1.00  binary:                                 6
% 1.66/1.00  lits:                                   66
% 1.66/1.00  lits_eq:                                14
% 1.66/1.00  fd_pure:                                0
% 1.66/1.00  fd_pseudo:                              0
% 1.66/1.00  fd_cond:                                5
% 1.66/1.00  fd_pseudo_cond:                         3
% 1.66/1.00  ac_symbols:                             0
% 1.66/1.00  
% 1.66/1.00  ------ Propositional Solver
% 1.66/1.00  
% 1.66/1.00  prop_solver_calls:                      26
% 1.66/1.00  prop_fast_solver_calls:                 1353
% 1.66/1.00  smt_solver_calls:                       0
% 1.66/1.00  smt_fast_solver_calls:                  0
% 1.66/1.00  prop_num_of_clauses:                    854
% 1.66/1.00  prop_preprocess_simplified:             5163
% 1.66/1.00  prop_fo_subsumed:                       65
% 1.66/1.00  prop_solver_time:                       0.
% 1.66/1.00  smt_solver_time:                        0.
% 1.66/1.00  smt_fast_solver_time:                   0.
% 1.66/1.00  prop_fast_solver_time:                  0.
% 1.66/1.00  prop_unsat_core_time:                   0.
% 1.66/1.00  
% 1.66/1.00  ------ QBF
% 1.66/1.00  
% 1.66/1.00  qbf_q_res:                              0
% 1.66/1.00  qbf_num_tautologies:                    0
% 1.66/1.00  qbf_prep_cycles:                        0
% 1.66/1.00  
% 1.66/1.00  ------ BMC1
% 1.66/1.00  
% 1.66/1.00  bmc1_current_bound:                     -1
% 1.66/1.00  bmc1_last_solved_bound:                 -1
% 1.66/1.00  bmc1_unsat_core_size:                   -1
% 1.66/1.00  bmc1_unsat_core_parents_size:           -1
% 1.66/1.00  bmc1_merge_next_fun:                    0
% 1.66/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.66/1.00  
% 1.66/1.00  ------ Instantiation
% 1.66/1.00  
% 1.66/1.00  inst_num_of_clauses:                    218
% 1.66/1.00  inst_num_in_passive:                    25
% 1.66/1.00  inst_num_in_active:                     133
% 1.66/1.00  inst_num_in_unprocessed:                60
% 1.66/1.00  inst_num_of_loops:                      150
% 1.66/1.00  inst_num_of_learning_restarts:          0
% 1.66/1.00  inst_num_moves_active_passive:          15
% 1.66/1.00  inst_lit_activity:                      0
% 1.66/1.00  inst_lit_activity_moves:                0
% 1.66/1.00  inst_num_tautologies:                   0
% 1.66/1.00  inst_num_prop_implied:                  0
% 1.66/1.00  inst_num_existing_simplified:           0
% 1.66/1.00  inst_num_eq_res_simplified:             0
% 1.66/1.00  inst_num_child_elim:                    0
% 1.66/1.00  inst_num_of_dismatching_blockings:      27
% 1.66/1.00  inst_num_of_non_proper_insts:           220
% 1.66/1.00  inst_num_of_duplicates:                 0
% 1.66/1.00  inst_inst_num_from_inst_to_res:         0
% 1.66/1.00  inst_dismatching_checking_time:         0.
% 1.66/1.00  
% 1.66/1.00  ------ Resolution
% 1.66/1.00  
% 1.66/1.00  res_num_of_clauses:                     0
% 1.66/1.00  res_num_in_passive:                     0
% 1.66/1.00  res_num_in_active:                      0
% 1.66/1.00  res_num_of_loops:                       140
% 1.66/1.00  res_forward_subset_subsumed:            54
% 1.66/1.00  res_backward_subset_subsumed:           1
% 1.66/1.00  res_forward_subsumed:                   0
% 1.66/1.00  res_backward_subsumed:                  4
% 1.66/1.00  res_forward_subsumption_resolution:     0
% 1.66/1.00  res_backward_subsumption_resolution:    1
% 1.66/1.00  res_clause_to_clause_subsumption:       180
% 1.66/1.00  res_orphan_elimination:                 0
% 1.66/1.00  res_tautology_del:                      56
% 1.66/1.00  res_num_eq_res_simplified:              0
% 1.66/1.00  res_num_sel_changes:                    0
% 1.66/1.00  res_moves_from_active_to_pass:          0
% 1.66/1.00  
% 1.66/1.00  ------ Superposition
% 1.66/1.00  
% 1.66/1.00  sup_time_total:                         0.
% 1.66/1.00  sup_time_generating:                    0.
% 1.66/1.00  sup_time_sim_full:                      0.
% 1.66/1.00  sup_time_sim_immed:                     0.
% 1.66/1.00  
% 1.66/1.00  sup_num_of_clauses:                     45
% 1.66/1.00  sup_num_in_active:                      30
% 1.66/1.00  sup_num_in_passive:                     15
% 1.66/1.00  sup_num_of_loops:                       29
% 1.66/1.00  sup_fw_superposition:                   19
% 1.66/1.00  sup_bw_superposition:                   5
% 1.66/1.00  sup_immediate_simplified:               4
% 1.66/1.00  sup_given_eliminated:                   0
% 1.66/1.00  comparisons_done:                       0
% 1.66/1.00  comparisons_avoided:                    0
% 1.66/1.00  
% 1.66/1.00  ------ Simplifications
% 1.66/1.00  
% 1.66/1.00  
% 1.66/1.00  sim_fw_subset_subsumed:                 3
% 1.66/1.00  sim_bw_subset_subsumed:                 0
% 1.66/1.00  sim_fw_subsumed:                        1
% 1.66/1.00  sim_bw_subsumed:                        0
% 1.66/1.00  sim_fw_subsumption_res:                 0
% 1.66/1.00  sim_bw_subsumption_res:                 0
% 1.66/1.00  sim_tautology_del:                      0
% 1.66/1.00  sim_eq_tautology_del:                   0
% 1.66/1.00  sim_eq_res_simp:                        0
% 1.66/1.00  sim_fw_demodulated:                     0
% 1.66/1.00  sim_bw_demodulated:                     0
% 1.66/1.00  sim_light_normalised:                   0
% 1.66/1.00  sim_joinable_taut:                      0
% 1.66/1.00  sim_joinable_simp:                      0
% 1.66/1.00  sim_ac_normalised:                      0
% 1.66/1.00  sim_smt_subsumption:                    0
% 1.66/1.00  
%------------------------------------------------------------------------------
