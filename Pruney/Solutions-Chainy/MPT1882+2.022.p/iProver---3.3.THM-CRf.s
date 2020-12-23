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
% DateTime   : Thu Dec  3 12:27:23 EST 2020

% Result     : Theorem 0.97s
% Output     : CNFRefutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 693 expanded)
%              Number of clauses        :   83 ( 159 expanded)
%              Number of leaves         :   13 ( 153 expanded)
%              Depth                    :   29
%              Number of atoms          :  648 (5473 expanded)
%              Number of equality atoms :   84 ( 189 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ( ( r2_hidden(X3,X1)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f27])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f24])).

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
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(nnf_transformation,[],[f26])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f38,f37])).

fof(f55,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f56,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,
    ( ~ v1_zfmisc_1(sK3)
    | ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f6])).

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
    inference(nnf_transformation,[],[f19])).

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
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK1(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK1(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK1(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

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
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,
    ( v1_zfmisc_1(sK3)
    | v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( k6_subset_1(X1,X0) = k1_xboole_0
        & X0 != X1
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X1,X0) != k1_xboole_0
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X1,X0) != k1_xboole_0
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_1,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_313,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | X2 != X0
    | sK0(X2) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_314,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_14,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0)
    | v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_129,plain,
    ( ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v1_zfmisc_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_0])).

cnf(c_130,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_129])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_332,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_130,c_22])).

cnf(c_333,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_20,negated_conjecture,
    ( v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_337,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tex_2(X0,sK2)
    | v1_zfmisc_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_333,c_21,c_20,c_19])).

cnf(c_338,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_337])).

cnf(c_15,negated_conjecture,
    ( ~ v3_tex_2(sK3,sK2)
    | ~ v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_176,plain,
    ( ~ v1_zfmisc_1(sK3)
    | ~ v3_tex_2(sK3,sK2) ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_177,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | ~ v1_zfmisc_1(sK3) ),
    inference(renaming,[status(thm)],[c_176])).

cnf(c_715,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_338,c_177])).

cnf(c_716,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_715])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_718,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_716,c_17])).

cnf(c_719,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ v3_tex_2(sK3,sK2) ),
    inference(renaming,[status(thm)],[c_718])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_6,plain,
    ( r1_tarski(X0,sK1(X1,X0))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_553,plain,
    ( r1_tarski(X0,sK1(X1,X0))
    | ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_19])).

cnf(c_554,plain,
    ( r1_tarski(X0,sK1(sK2,X0))
    | ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_646,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_zfmisc_1(X2)
    | X0 != X1
    | X2 = X1
    | sK1(sK2,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_554])).

cnf(c_647,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK2,X0))
    | ~ v1_zfmisc_1(sK1(sK2,X0))
    | sK1(sK2,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_5,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_571,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK1(X1,X0) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_19])).

cnf(c_572,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_651,plain,
    ( ~ v1_zfmisc_1(sK1(sK2,X0))
    | v1_xboole_0(sK1(sK2,X0))
    | v1_xboole_0(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_tex_2(X0,sK2)
    | ~ v2_tex_2(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_647,c_572])).

cnf(c_652,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK2,X0))
    | ~ v1_zfmisc_1(sK1(sK2,X0)) ),
    inference(renaming,[status(thm)],[c_651])).

cnf(c_745,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(X1,sK2)
    | v3_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(sK1(sK2,X1))
    | sK1(sK2,X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_338,c_652])).

cnf(c_746,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(sK1(sK2,X0),sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_745])).

cnf(c_8,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_517,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_518,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_7,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK1(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_535,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK1(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_536,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(sK1(sK2,X0),sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_750,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_tex_2(X0,sK2)
    | ~ v2_tex_2(X0,sK2)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_746,c_518,c_536])).

cnf(c_751,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK2,X0)) ),
    inference(renaming,[status(thm)],[c_750])).

cnf(c_809,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK2,X0))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_719,c_751])).

cnf(c_810,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK1(sK2,sK3))
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_809])).

cnf(c_18,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_13,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_353,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_354,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_358,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(X0,sK2)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_354,c_21,c_20,c_19])).

cnf(c_359,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_358])).

cnf(c_16,negated_conjecture,
    ( v3_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_178,plain,
    ( v1_zfmisc_1(sK3)
    | v3_tex_2(sK3,sK2) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_179,plain,
    ( v3_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3) ),
    inference(renaming,[status(thm)],[c_178])).

cnf(c_731,plain,
    ( v2_tex_2(X0,sK2)
    | v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_359,c_179])).

cnf(c_732,plain,
    ( v2_tex_2(sK3,sK2)
    | v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_731])).

cnf(c_734,plain,
    ( v2_tex_2(sK3,sK2)
    | v3_tex_2(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_732,c_18,c_17])).

cnf(c_10,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_502,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_503,plain,
    ( v2_tex_2(X0,sK2)
    | ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_798,plain,
    ( v2_tex_2(X0,sK2)
    | v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_734,c_503])).

cnf(c_799,plain,
    ( v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_798])).

cnf(c_812,plain,
    ( v1_xboole_0(sK1(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_810,c_18,c_17,c_799])).

cnf(c_868,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | sK1(sK2,sK3) != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_314,c_812])).

cnf(c_869,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK2,sK3)))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_868])).

cnf(c_884,plain,
    ( k6_subset_1(X0,X1) != X2
    | k1_zfmisc_1(sK1(sK2,sK3)) != k1_zfmisc_1(X0)
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_869])).

cnf(c_885,plain,
    ( k1_zfmisc_1(sK1(sK2,sK3)) != k1_zfmisc_1(X0)
    | k1_xboole_0 = k6_subset_1(X0,X1) ),
    inference(unflattening,[status(thm)],[c_884])).

cnf(c_923,plain,
    ( k1_xboole_0 = k6_subset_1(X0_48,X1_48)
    | k1_zfmisc_1(sK1(sK2,sK3)) != k1_zfmisc_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_885])).

cnf(c_1028,plain,
    ( k6_subset_1(sK1(sK2,sK3),X0_48) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_923])).

cnf(c_1029,plain,
    ( k6_subset_1(sK1(sK2,sK3),sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | X1 = X0
    | k6_subset_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_676,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 != X1
    | X2 = X1
    | sK1(sK2,X0) != X2
    | k6_subset_1(X2,X1) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_554])).

cnf(c_677,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(sK2,X0) = X0
    | k6_subset_1(sK1(sK2,X0),X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_676])).

cnf(c_681,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_tex_2(X0,sK2)
    | ~ v2_tex_2(X0,sK2)
    | k6_subset_1(sK1(sK2,X0),X0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_677,c_572])).

cnf(c_682,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k6_subset_1(sK1(sK2,X0),X0) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_681])).

cnf(c_820,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k6_subset_1(sK1(sK2,X0),X0) != k1_xboole_0
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_719,c_682])).

cnf(c_821,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k6_subset_1(sK1(sK2,sK3),sK3) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_820])).

cnf(c_823,plain,
    ( k6_subset_1(sK1(sK2,sK3),sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_821,c_17,c_799])).

cnf(c_925,plain,
    ( k6_subset_1(sK1(sK2,sK3),sK3) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_823])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1029,c_925])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.97/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.97/0.99  
% 0.97/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.97/0.99  
% 0.97/0.99  ------  iProver source info
% 0.97/0.99  
% 0.97/0.99  git: date: 2020-06-30 10:37:57 +0100
% 0.97/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.97/0.99  git: non_committed_changes: false
% 0.97/0.99  git: last_make_outside_of_git: false
% 0.97/0.99  
% 0.97/0.99  ------ 
% 0.97/0.99  
% 0.97/0.99  ------ Input Options
% 0.97/0.99  
% 0.97/0.99  --out_options                           all
% 0.97/0.99  --tptp_safe_out                         true
% 0.97/0.99  --problem_path                          ""
% 0.97/0.99  --include_path                          ""
% 0.97/0.99  --clausifier                            res/vclausify_rel
% 0.97/0.99  --clausifier_options                    --mode clausify
% 0.97/0.99  --stdin                                 false
% 0.97/0.99  --stats_out                             all
% 0.97/0.99  
% 0.97/0.99  ------ General Options
% 0.97/0.99  
% 0.97/0.99  --fof                                   false
% 0.97/0.99  --time_out_real                         305.
% 0.97/0.99  --time_out_virtual                      -1.
% 0.97/0.99  --symbol_type_check                     false
% 0.97/0.99  --clausify_out                          false
% 0.97/0.99  --sig_cnt_out                           false
% 0.97/0.99  --trig_cnt_out                          false
% 0.97/0.99  --trig_cnt_out_tolerance                1.
% 0.97/0.99  --trig_cnt_out_sk_spl                   false
% 0.97/0.99  --abstr_cl_out                          false
% 0.97/0.99  
% 0.97/0.99  ------ Global Options
% 0.97/0.99  
% 0.97/0.99  --schedule                              default
% 0.97/0.99  --add_important_lit                     false
% 0.97/0.99  --prop_solver_per_cl                    1000
% 0.97/0.99  --min_unsat_core                        false
% 0.97/0.99  --soft_assumptions                      false
% 0.97/0.99  --soft_lemma_size                       3
% 0.97/0.99  --prop_impl_unit_size                   0
% 0.97/0.99  --prop_impl_unit                        []
% 0.97/0.99  --share_sel_clauses                     true
% 0.97/0.99  --reset_solvers                         false
% 0.97/0.99  --bc_imp_inh                            [conj_cone]
% 0.97/0.99  --conj_cone_tolerance                   3.
% 0.97/0.99  --extra_neg_conj                        none
% 0.97/0.99  --large_theory_mode                     true
% 0.97/0.99  --prolific_symb_bound                   200
% 0.97/0.99  --lt_threshold                          2000
% 0.97/0.99  --clause_weak_htbl                      true
% 0.97/0.99  --gc_record_bc_elim                     false
% 0.97/0.99  
% 0.97/0.99  ------ Preprocessing Options
% 0.97/0.99  
% 0.97/0.99  --preprocessing_flag                    true
% 0.97/0.99  --time_out_prep_mult                    0.1
% 0.97/0.99  --splitting_mode                        input
% 0.97/0.99  --splitting_grd                         true
% 0.97/0.99  --splitting_cvd                         false
% 0.97/0.99  --splitting_cvd_svl                     false
% 0.97/0.99  --splitting_nvd                         32
% 0.97/0.99  --sub_typing                            true
% 0.97/0.99  --prep_gs_sim                           true
% 0.97/0.99  --prep_unflatten                        true
% 0.97/0.99  --prep_res_sim                          true
% 0.97/0.99  --prep_upred                            true
% 0.97/0.99  --prep_sem_filter                       exhaustive
% 0.97/0.99  --prep_sem_filter_out                   false
% 0.97/0.99  --pred_elim                             true
% 0.97/0.99  --res_sim_input                         true
% 0.97/0.99  --eq_ax_congr_red                       true
% 0.97/0.99  --pure_diseq_elim                       true
% 0.97/0.99  --brand_transform                       false
% 0.97/0.99  --non_eq_to_eq                          false
% 0.97/0.99  --prep_def_merge                        true
% 0.97/0.99  --prep_def_merge_prop_impl              false
% 0.97/0.99  --prep_def_merge_mbd                    true
% 0.97/0.99  --prep_def_merge_tr_red                 false
% 0.97/0.99  --prep_def_merge_tr_cl                  false
% 0.97/0.99  --smt_preprocessing                     true
% 0.97/0.99  --smt_ac_axioms                         fast
% 0.97/0.99  --preprocessed_out                      false
% 0.97/0.99  --preprocessed_stats                    false
% 0.97/0.99  
% 0.97/0.99  ------ Abstraction refinement Options
% 0.97/0.99  
% 0.97/0.99  --abstr_ref                             []
% 0.97/0.99  --abstr_ref_prep                        false
% 0.97/0.99  --abstr_ref_until_sat                   false
% 0.97/0.99  --abstr_ref_sig_restrict                funpre
% 0.97/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.97/0.99  --abstr_ref_under                       []
% 0.97/0.99  
% 0.97/0.99  ------ SAT Options
% 0.97/0.99  
% 0.97/0.99  --sat_mode                              false
% 0.97/0.99  --sat_fm_restart_options                ""
% 0.97/0.99  --sat_gr_def                            false
% 0.97/0.99  --sat_epr_types                         true
% 0.97/0.99  --sat_non_cyclic_types                  false
% 0.97/0.99  --sat_finite_models                     false
% 0.97/0.99  --sat_fm_lemmas                         false
% 0.97/0.99  --sat_fm_prep                           false
% 0.97/0.99  --sat_fm_uc_incr                        true
% 0.97/0.99  --sat_out_model                         small
% 0.97/0.99  --sat_out_clauses                       false
% 0.97/0.99  
% 0.97/0.99  ------ QBF Options
% 0.97/0.99  
% 0.97/0.99  --qbf_mode                              false
% 0.97/0.99  --qbf_elim_univ                         false
% 0.97/0.99  --qbf_dom_inst                          none
% 0.97/0.99  --qbf_dom_pre_inst                      false
% 0.97/0.99  --qbf_sk_in                             false
% 0.97/0.99  --qbf_pred_elim                         true
% 0.97/0.99  --qbf_split                             512
% 0.97/0.99  
% 0.97/0.99  ------ BMC1 Options
% 0.97/0.99  
% 0.97/0.99  --bmc1_incremental                      false
% 0.97/0.99  --bmc1_axioms                           reachable_all
% 0.97/0.99  --bmc1_min_bound                        0
% 0.97/0.99  --bmc1_max_bound                        -1
% 0.97/0.99  --bmc1_max_bound_default                -1
% 0.97/0.99  --bmc1_symbol_reachability              true
% 0.97/0.99  --bmc1_property_lemmas                  false
% 0.97/0.99  --bmc1_k_induction                      false
% 0.97/0.99  --bmc1_non_equiv_states                 false
% 0.97/0.99  --bmc1_deadlock                         false
% 0.97/0.99  --bmc1_ucm                              false
% 0.97/0.99  --bmc1_add_unsat_core                   none
% 0.97/0.99  --bmc1_unsat_core_children              false
% 0.97/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.97/0.99  --bmc1_out_stat                         full
% 0.97/0.99  --bmc1_ground_init                      false
% 0.97/0.99  --bmc1_pre_inst_next_state              false
% 0.97/0.99  --bmc1_pre_inst_state                   false
% 0.97/0.99  --bmc1_pre_inst_reach_state             false
% 0.97/0.99  --bmc1_out_unsat_core                   false
% 0.97/0.99  --bmc1_aig_witness_out                  false
% 0.97/0.99  --bmc1_verbose                          false
% 0.97/0.99  --bmc1_dump_clauses_tptp                false
% 0.97/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.97/0.99  --bmc1_dump_file                        -
% 0.97/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.97/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.97/0.99  --bmc1_ucm_extend_mode                  1
% 0.97/0.99  --bmc1_ucm_init_mode                    2
% 0.97/0.99  --bmc1_ucm_cone_mode                    none
% 0.97/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.97/0.99  --bmc1_ucm_relax_model                  4
% 0.97/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.97/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.97/0.99  --bmc1_ucm_layered_model                none
% 0.97/0.99  --bmc1_ucm_max_lemma_size               10
% 0.97/0.99  
% 0.97/0.99  ------ AIG Options
% 0.97/0.99  
% 0.97/0.99  --aig_mode                              false
% 0.97/0.99  
% 0.97/0.99  ------ Instantiation Options
% 0.97/0.99  
% 0.97/0.99  --instantiation_flag                    true
% 0.97/0.99  --inst_sos_flag                         false
% 0.97/0.99  --inst_sos_phase                        true
% 0.97/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.97/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.97/0.99  --inst_lit_sel_side                     num_symb
% 0.97/0.99  --inst_solver_per_active                1400
% 0.97/0.99  --inst_solver_calls_frac                1.
% 0.97/0.99  --inst_passive_queue_type               priority_queues
% 0.97/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.97/0.99  --inst_passive_queues_freq              [25;2]
% 0.97/0.99  --inst_dismatching                      true
% 0.97/0.99  --inst_eager_unprocessed_to_passive     true
% 0.97/0.99  --inst_prop_sim_given                   true
% 0.97/0.99  --inst_prop_sim_new                     false
% 0.97/0.99  --inst_subs_new                         false
% 0.97/0.99  --inst_eq_res_simp                      false
% 0.97/0.99  --inst_subs_given                       false
% 0.97/0.99  --inst_orphan_elimination               true
% 0.97/0.99  --inst_learning_loop_flag               true
% 0.97/0.99  --inst_learning_start                   3000
% 0.97/0.99  --inst_learning_factor                  2
% 0.97/0.99  --inst_start_prop_sim_after_learn       3
% 0.97/0.99  --inst_sel_renew                        solver
% 0.97/0.99  --inst_lit_activity_flag                true
% 0.97/0.99  --inst_restr_to_given                   false
% 0.97/0.99  --inst_activity_threshold               500
% 0.97/0.99  --inst_out_proof                        true
% 0.97/0.99  
% 0.97/0.99  ------ Resolution Options
% 0.97/0.99  
% 0.97/0.99  --resolution_flag                       true
% 0.97/0.99  --res_lit_sel                           adaptive
% 0.97/0.99  --res_lit_sel_side                      none
% 0.97/0.99  --res_ordering                          kbo
% 0.97/0.99  --res_to_prop_solver                    active
% 0.97/0.99  --res_prop_simpl_new                    false
% 0.97/0.99  --res_prop_simpl_given                  true
% 0.97/0.99  --res_passive_queue_type                priority_queues
% 0.97/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.97/0.99  --res_passive_queues_freq               [15;5]
% 0.97/0.99  --res_forward_subs                      full
% 0.97/0.99  --res_backward_subs                     full
% 0.97/0.99  --res_forward_subs_resolution           true
% 0.97/0.99  --res_backward_subs_resolution          true
% 0.97/0.99  --res_orphan_elimination                true
% 0.97/0.99  --res_time_limit                        2.
% 0.97/0.99  --res_out_proof                         true
% 0.97/0.99  
% 0.97/0.99  ------ Superposition Options
% 0.97/0.99  
% 0.97/0.99  --superposition_flag                    true
% 0.97/0.99  --sup_passive_queue_type                priority_queues
% 0.97/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.97/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.97/0.99  --demod_completeness_check              fast
% 0.97/0.99  --demod_use_ground                      true
% 0.97/0.99  --sup_to_prop_solver                    passive
% 0.97/0.99  --sup_prop_simpl_new                    true
% 0.97/0.99  --sup_prop_simpl_given                  true
% 0.97/0.99  --sup_fun_splitting                     false
% 0.97/0.99  --sup_smt_interval                      50000
% 0.97/0.99  
% 0.97/0.99  ------ Superposition Simplification Setup
% 0.97/0.99  
% 0.97/0.99  --sup_indices_passive                   []
% 0.97/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.97/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.97/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.97/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.97/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.97/0.99  --sup_full_bw                           [BwDemod]
% 0.97/0.99  --sup_immed_triv                        [TrivRules]
% 0.97/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.97/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.97/0.99  --sup_immed_bw_main                     []
% 0.97/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.97/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.97/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.97/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.97/0.99  
% 0.97/0.99  ------ Combination Options
% 0.97/0.99  
% 0.97/0.99  --comb_res_mult                         3
% 0.97/0.99  --comb_sup_mult                         2
% 0.97/0.99  --comb_inst_mult                        10
% 0.97/0.99  
% 0.97/0.99  ------ Debug Options
% 0.97/0.99  
% 0.97/0.99  --dbg_backtrace                         false
% 0.97/0.99  --dbg_dump_prop_clauses                 false
% 0.97/0.99  --dbg_dump_prop_clauses_file            -
% 0.97/0.99  --dbg_out_stat                          false
% 0.97/0.99  ------ Parsing...
% 0.97/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.97/0.99  
% 0.97/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 12 0s  sf_e  pe_s  pe_e 
% 0.97/0.99  
% 0.97/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.97/0.99  
% 0.97/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 0.97/0.99  ------ Proving...
% 0.97/0.99  ------ Problem Properties 
% 0.97/0.99  
% 0.97/0.99  
% 0.97/0.99  clauses                                 5
% 0.97/0.99  conjectures                             0
% 0.97/0.99  EPR                                     0
% 0.97/0.99  Horn                                    5
% 0.97/0.99  unary                                   2
% 0.97/0.99  binary                                  3
% 0.97/0.99  lits                                    8
% 0.97/0.99  lits eq                                 8
% 0.97/0.99  fd_pure                                 0
% 0.97/0.99  fd_pseudo                               0
% 0.97/0.99  fd_cond                                 0
% 0.97/0.99  fd_pseudo_cond                          0
% 0.97/0.99  AC symbols                              0
% 0.97/0.99  
% 0.97/0.99  ------ Schedule dynamic 5 is on 
% 0.97/0.99  
% 0.97/0.99  ------ no conjectures: strip conj schedule 
% 0.97/0.99  
% 0.97/0.99  ------ pure equality problem: resolution off 
% 0.97/0.99  
% 0.97/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 0.97/0.99  
% 0.97/0.99  
% 0.97/0.99  ------ 
% 0.97/0.99  Current options:
% 0.97/0.99  ------ 
% 0.97/0.99  
% 0.97/0.99  ------ Input Options
% 0.97/0.99  
% 0.97/0.99  --out_options                           all
% 0.97/0.99  --tptp_safe_out                         true
% 0.97/0.99  --problem_path                          ""
% 0.97/0.99  --include_path                          ""
% 0.97/0.99  --clausifier                            res/vclausify_rel
% 0.97/0.99  --clausifier_options                    --mode clausify
% 0.97/0.99  --stdin                                 false
% 0.97/0.99  --stats_out                             all
% 0.97/0.99  
% 0.97/0.99  ------ General Options
% 0.97/0.99  
% 0.97/0.99  --fof                                   false
% 0.97/0.99  --time_out_real                         305.
% 0.97/0.99  --time_out_virtual                      -1.
% 0.97/0.99  --symbol_type_check                     false
% 0.97/0.99  --clausify_out                          false
% 0.97/0.99  --sig_cnt_out                           false
% 0.97/0.99  --trig_cnt_out                          false
% 0.97/0.99  --trig_cnt_out_tolerance                1.
% 0.97/0.99  --trig_cnt_out_sk_spl                   false
% 0.97/0.99  --abstr_cl_out                          false
% 0.97/0.99  
% 0.97/0.99  ------ Global Options
% 0.97/0.99  
% 0.97/0.99  --schedule                              default
% 0.97/0.99  --add_important_lit                     false
% 0.97/0.99  --prop_solver_per_cl                    1000
% 0.97/0.99  --min_unsat_core                        false
% 0.97/0.99  --soft_assumptions                      false
% 0.97/0.99  --soft_lemma_size                       3
% 0.97/0.99  --prop_impl_unit_size                   0
% 0.97/0.99  --prop_impl_unit                        []
% 0.97/0.99  --share_sel_clauses                     true
% 0.97/0.99  --reset_solvers                         false
% 0.97/0.99  --bc_imp_inh                            [conj_cone]
% 0.97/0.99  --conj_cone_tolerance                   3.
% 0.97/0.99  --extra_neg_conj                        none
% 0.97/0.99  --large_theory_mode                     true
% 0.97/0.99  --prolific_symb_bound                   200
% 0.97/0.99  --lt_threshold                          2000
% 0.97/0.99  --clause_weak_htbl                      true
% 0.97/0.99  --gc_record_bc_elim                     false
% 0.97/0.99  
% 0.97/0.99  ------ Preprocessing Options
% 0.97/0.99  
% 0.97/0.99  --preprocessing_flag                    true
% 0.97/0.99  --time_out_prep_mult                    0.1
% 0.97/0.99  --splitting_mode                        input
% 0.97/0.99  --splitting_grd                         true
% 0.97/0.99  --splitting_cvd                         false
% 0.97/0.99  --splitting_cvd_svl                     false
% 0.97/0.99  --splitting_nvd                         32
% 0.97/0.99  --sub_typing                            true
% 0.97/0.99  --prep_gs_sim                           true
% 0.97/0.99  --prep_unflatten                        true
% 0.97/0.99  --prep_res_sim                          true
% 0.97/0.99  --prep_upred                            true
% 0.97/0.99  --prep_sem_filter                       exhaustive
% 0.97/0.99  --prep_sem_filter_out                   false
% 0.97/0.99  --pred_elim                             true
% 0.97/0.99  --res_sim_input                         true
% 0.97/0.99  --eq_ax_congr_red                       true
% 0.97/0.99  --pure_diseq_elim                       true
% 0.97/0.99  --brand_transform                       false
% 0.97/0.99  --non_eq_to_eq                          false
% 0.97/0.99  --prep_def_merge                        true
% 0.97/0.99  --prep_def_merge_prop_impl              false
% 0.97/0.99  --prep_def_merge_mbd                    true
% 0.97/0.99  --prep_def_merge_tr_red                 false
% 0.97/0.99  --prep_def_merge_tr_cl                  false
% 0.97/0.99  --smt_preprocessing                     true
% 0.97/0.99  --smt_ac_axioms                         fast
% 0.97/0.99  --preprocessed_out                      false
% 0.97/0.99  --preprocessed_stats                    false
% 0.97/0.99  
% 0.97/0.99  ------ Abstraction refinement Options
% 0.97/0.99  
% 0.97/0.99  --abstr_ref                             []
% 0.97/0.99  --abstr_ref_prep                        false
% 0.97/0.99  --abstr_ref_until_sat                   false
% 0.97/0.99  --abstr_ref_sig_restrict                funpre
% 0.97/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.97/0.99  --abstr_ref_under                       []
% 0.97/0.99  
% 0.97/0.99  ------ SAT Options
% 0.97/0.99  
% 0.97/0.99  --sat_mode                              false
% 0.97/0.99  --sat_fm_restart_options                ""
% 0.97/0.99  --sat_gr_def                            false
% 0.97/0.99  --sat_epr_types                         true
% 0.97/0.99  --sat_non_cyclic_types                  false
% 0.97/0.99  --sat_finite_models                     false
% 0.97/0.99  --sat_fm_lemmas                         false
% 0.97/0.99  --sat_fm_prep                           false
% 0.97/0.99  --sat_fm_uc_incr                        true
% 0.97/0.99  --sat_out_model                         small
% 0.97/0.99  --sat_out_clauses                       false
% 0.97/0.99  
% 0.97/0.99  ------ QBF Options
% 0.97/0.99  
% 0.97/0.99  --qbf_mode                              false
% 0.97/0.99  --qbf_elim_univ                         false
% 0.97/0.99  --qbf_dom_inst                          none
% 0.97/0.99  --qbf_dom_pre_inst                      false
% 0.97/0.99  --qbf_sk_in                             false
% 0.97/0.99  --qbf_pred_elim                         true
% 0.97/0.99  --qbf_split                             512
% 0.97/0.99  
% 0.97/0.99  ------ BMC1 Options
% 0.97/0.99  
% 0.97/0.99  --bmc1_incremental                      false
% 0.97/0.99  --bmc1_axioms                           reachable_all
% 0.97/0.99  --bmc1_min_bound                        0
% 0.97/0.99  --bmc1_max_bound                        -1
% 0.97/0.99  --bmc1_max_bound_default                -1
% 0.97/0.99  --bmc1_symbol_reachability              true
% 0.97/0.99  --bmc1_property_lemmas                  false
% 0.97/0.99  --bmc1_k_induction                      false
% 0.97/0.99  --bmc1_non_equiv_states                 false
% 0.97/0.99  --bmc1_deadlock                         false
% 0.97/0.99  --bmc1_ucm                              false
% 0.97/0.99  --bmc1_add_unsat_core                   none
% 0.97/0.99  --bmc1_unsat_core_children              false
% 0.97/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.97/0.99  --bmc1_out_stat                         full
% 0.97/0.99  --bmc1_ground_init                      false
% 0.97/0.99  --bmc1_pre_inst_next_state              false
% 0.97/0.99  --bmc1_pre_inst_state                   false
% 0.97/0.99  --bmc1_pre_inst_reach_state             false
% 0.97/0.99  --bmc1_out_unsat_core                   false
% 0.97/0.99  --bmc1_aig_witness_out                  false
% 0.97/0.99  --bmc1_verbose                          false
% 0.97/0.99  --bmc1_dump_clauses_tptp                false
% 0.97/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.97/0.99  --bmc1_dump_file                        -
% 0.97/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.97/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.97/0.99  --bmc1_ucm_extend_mode                  1
% 0.97/0.99  --bmc1_ucm_init_mode                    2
% 0.97/0.99  --bmc1_ucm_cone_mode                    none
% 0.97/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.97/0.99  --bmc1_ucm_relax_model                  4
% 0.97/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.97/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.97/0.99  --bmc1_ucm_layered_model                none
% 0.97/0.99  --bmc1_ucm_max_lemma_size               10
% 0.97/0.99  
% 0.97/0.99  ------ AIG Options
% 0.97/0.99  
% 0.97/0.99  --aig_mode                              false
% 0.97/0.99  
% 0.97/0.99  ------ Instantiation Options
% 0.97/0.99  
% 0.97/0.99  --instantiation_flag                    true
% 0.97/0.99  --inst_sos_flag                         false
% 0.97/0.99  --inst_sos_phase                        true
% 0.97/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.97/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.97/0.99  --inst_lit_sel_side                     none
% 0.97/0.99  --inst_solver_per_active                1400
% 0.97/0.99  --inst_solver_calls_frac                1.
% 0.97/0.99  --inst_passive_queue_type               priority_queues
% 0.97/0.99  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 0.97/0.99  --inst_passive_queues_freq              [25;2]
% 0.97/0.99  --inst_dismatching                      true
% 0.97/0.99  --inst_eager_unprocessed_to_passive     true
% 0.97/0.99  --inst_prop_sim_given                   true
% 0.97/0.99  --inst_prop_sim_new                     false
% 0.97/0.99  --inst_subs_new                         false
% 0.97/0.99  --inst_eq_res_simp                      false
% 0.97/0.99  --inst_subs_given                       false
% 0.97/0.99  --inst_orphan_elimination               true
% 0.97/0.99  --inst_learning_loop_flag               true
% 0.97/0.99  --inst_learning_start                   3000
% 0.97/0.99  --inst_learning_factor                  2
% 0.97/0.99  --inst_start_prop_sim_after_learn       3
% 0.97/0.99  --inst_sel_renew                        solver
% 0.97/0.99  --inst_lit_activity_flag                true
% 0.97/0.99  --inst_restr_to_given                   false
% 0.97/0.99  --inst_activity_threshold               500
% 0.97/0.99  --inst_out_proof                        true
% 0.97/0.99  
% 0.97/0.99  ------ Resolution Options
% 0.97/0.99  
% 0.97/0.99  --resolution_flag                       false
% 0.97/0.99  --res_lit_sel                           adaptive
% 0.97/0.99  --res_lit_sel_side                      none
% 0.97/0.99  --res_ordering                          kbo
% 0.97/0.99  --res_to_prop_solver                    active
% 0.97/0.99  --res_prop_simpl_new                    false
% 0.97/0.99  --res_prop_simpl_given                  true
% 0.97/0.99  --res_passive_queue_type                priority_queues
% 0.97/0.99  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 0.97/0.99  --res_passive_queues_freq               [15;5]
% 0.97/0.99  --res_forward_subs                      full
% 0.97/0.99  --res_backward_subs                     full
% 0.97/0.99  --res_forward_subs_resolution           true
% 0.97/0.99  --res_backward_subs_resolution          true
% 0.97/0.99  --res_orphan_elimination                true
% 0.97/0.99  --res_time_limit                        2.
% 0.97/0.99  --res_out_proof                         true
% 0.97/0.99  
% 0.97/0.99  ------ Superposition Options
% 0.97/0.99  
% 0.97/0.99  --superposition_flag                    true
% 0.97/0.99  --sup_passive_queue_type                priority_queues
% 0.97/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.97/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.97/0.99  --demod_completeness_check              fast
% 0.97/0.99  --demod_use_ground                      true
% 0.97/0.99  --sup_to_prop_solver                    passive
% 0.97/0.99  --sup_prop_simpl_new                    true
% 0.97/0.99  --sup_prop_simpl_given                  true
% 0.97/0.99  --sup_fun_splitting                     false
% 0.97/0.99  --sup_smt_interval                      50000
% 0.97/0.99  
% 0.97/0.99  ------ Superposition Simplification Setup
% 0.97/0.99  
% 0.97/0.99  --sup_indices_passive                   []
% 0.97/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.97/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.97/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.97/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.97/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.97/0.99  --sup_full_bw                           [BwDemod]
% 0.97/0.99  --sup_immed_triv                        [TrivRules]
% 0.97/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.97/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.97/0.99  --sup_immed_bw_main                     []
% 0.97/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.97/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.97/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.97/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.97/0.99  
% 0.97/0.99  ------ Combination Options
% 0.97/0.99  
% 0.97/0.99  --comb_res_mult                         3
% 0.97/0.99  --comb_sup_mult                         2
% 0.97/0.99  --comb_inst_mult                        10
% 0.97/0.99  
% 0.97/0.99  ------ Debug Options
% 0.97/0.99  
% 0.97/0.99  --dbg_backtrace                         false
% 0.97/0.99  --dbg_dump_prop_clauses                 false
% 0.97/0.99  --dbg_dump_prop_clauses_file            -
% 0.97/0.99  --dbg_out_stat                          false
% 0.97/0.99  
% 0.97/0.99  
% 0.97/0.99  
% 0.97/0.99  
% 0.97/0.99  ------ Proving...
% 0.97/0.99  
% 0.97/0.99  
% 0.97/0.99  % SZS status Theorem for theBenchmark.p
% 0.97/0.99  
% 0.97/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 0.97/0.99  
% 0.97/0.99  fof(f2,axiom,(
% 0.97/0.99    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/0.99  
% 0.97/0.99  fof(f41,plain,(
% 0.97/0.99    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.97/0.99    inference(cnf_transformation,[],[f2])).
% 0.97/0.99  
% 0.97/0.99  fof(f3,axiom,(
% 0.97/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/0.99  
% 0.97/0.99  fof(f14,plain,(
% 0.97/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.97/0.99    inference(ennf_transformation,[],[f3])).
% 0.97/0.99  
% 0.97/0.99  fof(f42,plain,(
% 0.97/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.97/0.99    inference(cnf_transformation,[],[f14])).
% 0.97/0.99  
% 0.97/0.99  fof(f4,axiom,(
% 0.97/0.99    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ((r2_hidden(X3,X1) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/0.99  
% 0.97/0.99  fof(f12,plain,(
% 0.97/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.97/0.99    inference(pure_predicate_removal,[],[f4])).
% 0.97/0.99  
% 0.97/0.99  fof(f15,plain,(
% 0.97/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.97/0.99    inference(ennf_transformation,[],[f12])).
% 0.97/0.99  
% 0.97/0.99  fof(f27,plain,(
% 0.97/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 0.97/0.99    introduced(choice_axiom,[])).
% 0.97/0.99  
% 0.97/0.99  fof(f28,plain,(
% 0.97/0.99    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 0.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f27])).
% 0.97/0.99  
% 0.97/0.99  fof(f43,plain,(
% 0.97/0.99    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 0.97/0.99    inference(cnf_transformation,[],[f28])).
% 0.97/0.99  
% 0.97/0.99  fof(f9,axiom,(
% 0.97/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/0.99  
% 0.97/0.99  fof(f23,plain,(
% 0.97/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.97/0.99    inference(ennf_transformation,[],[f9])).
% 0.97/0.99  
% 0.97/0.99  fof(f24,plain,(
% 0.97/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.97/0.99    inference(flattening,[],[f23])).
% 0.97/0.99  
% 0.97/0.99  fof(f34,plain,(
% 0.97/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.97/0.99    inference(nnf_transformation,[],[f24])).
% 0.97/0.99  
% 0.97/0.99  fof(f53,plain,(
% 0.97/0.99    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.97/0.99    inference(cnf_transformation,[],[f34])).
% 0.97/0.99  
% 0.97/0.99  fof(f1,axiom,(
% 0.97/0.99    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 0.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/0.99  
% 0.97/0.99  fof(f13,plain,(
% 0.97/0.99    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 0.97/0.99    inference(ennf_transformation,[],[f1])).
% 0.97/0.99  
% 0.97/0.99  fof(f40,plain,(
% 0.97/0.99    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 0.97/0.99    inference(cnf_transformation,[],[f13])).
% 0.97/0.99  
% 0.97/0.99  fof(f10,conjecture,(
% 0.97/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/0.99  
% 0.97/0.99  fof(f11,negated_conjecture,(
% 0.97/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.97/0.99    inference(negated_conjecture,[],[f10])).
% 0.97/0.99  
% 0.97/0.99  fof(f25,plain,(
% 0.97/0.99    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.97/0.99    inference(ennf_transformation,[],[f11])).
% 0.97/0.99  
% 0.97/0.99  fof(f26,plain,(
% 0.97/0.99    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.97/0.99    inference(flattening,[],[f25])).
% 0.97/0.99  
% 0.97/0.99  fof(f35,plain,(
% 0.97/0.99    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.97/0.99    inference(nnf_transformation,[],[f26])).
% 0.97/0.99  
% 0.97/0.99  fof(f36,plain,(
% 0.97/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.97/0.99    inference(flattening,[],[f35])).
% 0.97/0.99  
% 0.97/0.99  fof(f38,plain,(
% 0.97/0.99    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,X0)) & (v1_zfmisc_1(sK3) | v3_tex_2(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK3))) )),
% 0.97/0.99    introduced(choice_axiom,[])).
% 0.97/0.99  
% 0.97/0.99  fof(f37,plain,(
% 0.97/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK2)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.97/0.99    introduced(choice_axiom,[])).
% 0.97/0.99  
% 0.97/0.99  fof(f39,plain,(
% 0.97/0.99    ((~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,sK2)) & (v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f38,f37])).
% 0.97/0.99  
% 0.97/0.99  fof(f55,plain,(
% 0.97/0.99    ~v2_struct_0(sK2)),
% 0.97/0.99    inference(cnf_transformation,[],[f39])).
% 0.97/0.99  
% 0.97/0.99  fof(f56,plain,(
% 0.97/0.99    v2_pre_topc(sK2)),
% 0.97/0.99    inference(cnf_transformation,[],[f39])).
% 0.97/0.99  
% 0.97/0.99  fof(f57,plain,(
% 0.97/0.99    v2_tdlat_3(sK2)),
% 0.97/0.99    inference(cnf_transformation,[],[f39])).
% 0.97/0.99  
% 0.97/0.99  fof(f58,plain,(
% 0.97/0.99    l1_pre_topc(sK2)),
% 0.97/0.99    inference(cnf_transformation,[],[f39])).
% 0.97/0.99  
% 0.97/0.99  fof(f62,plain,(
% 0.97/0.99    ~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,sK2)),
% 0.97/0.99    inference(cnf_transformation,[],[f39])).
% 0.97/0.99  
% 0.97/0.99  fof(f60,plain,(
% 0.97/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.97/0.99    inference(cnf_transformation,[],[f39])).
% 0.97/0.99  
% 0.97/0.99  fof(f8,axiom,(
% 0.97/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/0.99  
% 0.97/0.99  fof(f21,plain,(
% 0.97/0.99    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.97/0.99    inference(ennf_transformation,[],[f8])).
% 0.97/0.99  
% 0.97/0.99  fof(f22,plain,(
% 0.97/0.99    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.97/0.99    inference(flattening,[],[f21])).
% 0.97/0.99  
% 0.97/0.99  fof(f52,plain,(
% 0.97/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.97/0.99    inference(cnf_transformation,[],[f22])).
% 0.97/0.99  
% 0.97/0.99  fof(f6,axiom,(
% 0.97/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/0.99  
% 0.97/0.99  fof(f18,plain,(
% 0.97/0.99    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.97/0.99    inference(ennf_transformation,[],[f6])).
% 0.97/0.99  
% 0.97/0.99  fof(f19,plain,(
% 0.97/0.99    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.97/0.99    inference(flattening,[],[f18])).
% 0.97/0.99  
% 0.97/0.99  fof(f29,plain,(
% 0.97/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.97/0.99    inference(nnf_transformation,[],[f19])).
% 0.97/0.99  
% 0.97/0.99  fof(f30,plain,(
% 0.97/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.97/0.99    inference(flattening,[],[f29])).
% 0.97/0.99  
% 0.97/0.99  fof(f31,plain,(
% 0.97/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.97/0.99    inference(rectify,[],[f30])).
% 0.97/0.99  
% 0.97/0.99  fof(f32,plain,(
% 0.97/0.99    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.97/0.99    introduced(choice_axiom,[])).
% 0.97/0.99  
% 0.97/0.99  fof(f33,plain,(
% 0.97/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 0.97/0.99  
% 0.97/0.99  fof(f49,plain,(
% 0.97/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK1(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.97/0.99    inference(cnf_transformation,[],[f33])).
% 0.97/0.99  
% 0.97/0.99  fof(f50,plain,(
% 0.97/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK1(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.97/0.99    inference(cnf_transformation,[],[f33])).
% 0.97/0.99  
% 0.97/0.99  fof(f47,plain,(
% 0.97/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.97/0.99    inference(cnf_transformation,[],[f33])).
% 0.97/0.99  
% 0.97/0.99  fof(f48,plain,(
% 0.97/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | v2_tex_2(sK1(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.97/0.99    inference(cnf_transformation,[],[f33])).
% 0.97/0.99  
% 0.97/0.99  fof(f59,plain,(
% 0.97/0.99    ~v1_xboole_0(sK3)),
% 0.97/0.99    inference(cnf_transformation,[],[f39])).
% 0.97/0.99  
% 0.97/0.99  fof(f54,plain,(
% 0.97/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.97/0.99    inference(cnf_transformation,[],[f34])).
% 0.97/0.99  
% 0.97/0.99  fof(f61,plain,(
% 0.97/0.99    v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2)),
% 0.97/0.99    inference(cnf_transformation,[],[f39])).
% 0.97/0.99  
% 0.97/0.99  fof(f45,plain,(
% 0.97/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.97/0.99    inference(cnf_transformation,[],[f33])).
% 0.97/0.99  
% 0.97/0.99  fof(f7,axiom,(
% 0.97/0.99    ! [X0,X1] : ~(k6_subset_1(X1,X0) = k1_xboole_0 & X0 != X1 & r1_tarski(X0,X1))),
% 0.97/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.97/0.99  
% 0.97/0.99  fof(f20,plain,(
% 0.97/0.99    ! [X0,X1] : (k6_subset_1(X1,X0) != k1_xboole_0 | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.97/0.99    inference(ennf_transformation,[],[f7])).
% 0.97/0.99  
% 0.97/0.99  fof(f51,plain,(
% 0.97/0.99    ( ! [X0,X1] : (k6_subset_1(X1,X0) != k1_xboole_0 | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.97/0.99    inference(cnf_transformation,[],[f20])).
% 0.97/0.99  
% 0.97/0.99  cnf(c_1,plain,
% 0.97/0.99      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
% 0.97/0.99      inference(cnf_transformation,[],[f41]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_2,plain,
% 0.97/0.99      ( ~ r2_hidden(X0,X1)
% 0.97/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 0.97/0.99      | ~ v1_xboole_0(X2) ),
% 0.97/0.99      inference(cnf_transformation,[],[f42]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_3,plain,
% 0.97/0.99      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 0.97/0.99      inference(cnf_transformation,[],[f43]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_313,plain,
% 0.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.97/0.99      | ~ v1_xboole_0(X1)
% 0.97/0.99      | X2 != X0
% 0.97/0.99      | sK0(X2) != X3
% 0.97/0.99      | k1_xboole_0 = X2 ),
% 0.97/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_3]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_314,plain,
% 0.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.97/0.99      | ~ v1_xboole_0(X1)
% 0.97/0.99      | k1_xboole_0 = X0 ),
% 0.97/0.99      inference(unflattening,[status(thm)],[c_313]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_14,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,X1)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.97/0.99      | v2_struct_0(X1)
% 0.97/0.99      | ~ l1_pre_topc(X1)
% 0.97/0.99      | ~ v2_tdlat_3(X1)
% 0.97/0.99      | ~ v2_pre_topc(X1)
% 0.97/0.99      | v1_xboole_0(X0)
% 0.97/0.99      | v1_zfmisc_1(X0) ),
% 0.97/0.99      inference(cnf_transformation,[],[f53]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_0,plain,
% 0.97/0.99      ( ~ v1_xboole_0(X0) | v1_zfmisc_1(X0) ),
% 0.97/0.99      inference(cnf_transformation,[],[f40]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_129,plain,
% 0.97/0.99      ( ~ v2_pre_topc(X1)
% 0.97/0.99      | ~ v2_tdlat_3(X1)
% 0.97/0.99      | ~ l1_pre_topc(X1)
% 0.97/0.99      | v2_struct_0(X1)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.97/0.99      | ~ v2_tex_2(X0,X1)
% 0.97/0.99      | v1_zfmisc_1(X0) ),
% 0.97/0.99      inference(global_propositional_subsumption,
% 0.97/0.99                [status(thm)],
% 0.97/0.99                [c_14,c_0]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_130,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,X1)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.97/0.99      | v2_struct_0(X1)
% 0.97/0.99      | ~ l1_pre_topc(X1)
% 0.97/0.99      | ~ v2_tdlat_3(X1)
% 0.97/0.99      | ~ v2_pre_topc(X1)
% 0.97/0.99      | v1_zfmisc_1(X0) ),
% 0.97/0.99      inference(renaming,[status(thm)],[c_129]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_22,negated_conjecture,
% 0.97/0.99      ( ~ v2_struct_0(sK2) ),
% 0.97/0.99      inference(cnf_transformation,[],[f55]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_332,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,X1)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.97/0.99      | ~ l1_pre_topc(X1)
% 0.97/0.99      | ~ v2_tdlat_3(X1)
% 0.97/0.99      | ~ v2_pre_topc(X1)
% 0.97/0.99      | v1_zfmisc_1(X0)
% 0.97/0.99      | sK2 != X1 ),
% 0.97/0.99      inference(resolution_lifted,[status(thm)],[c_130,c_22]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_333,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | ~ l1_pre_topc(sK2)
% 0.97/0.99      | ~ v2_tdlat_3(sK2)
% 0.97/0.99      | ~ v2_pre_topc(sK2)
% 0.97/0.99      | v1_zfmisc_1(X0) ),
% 0.97/0.99      inference(unflattening,[status(thm)],[c_332]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_21,negated_conjecture,
% 0.97/0.99      ( v2_pre_topc(sK2) ),
% 0.97/0.99      inference(cnf_transformation,[],[f56]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_20,negated_conjecture,
% 0.97/0.99      ( v2_tdlat_3(sK2) ),
% 0.97/0.99      inference(cnf_transformation,[],[f57]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_19,negated_conjecture,
% 0.97/0.99      ( l1_pre_topc(sK2) ),
% 0.97/0.99      inference(cnf_transformation,[],[f58]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_337,plain,
% 0.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | ~ v2_tex_2(X0,sK2)
% 0.97/0.99      | v1_zfmisc_1(X0) ),
% 0.97/0.99      inference(global_propositional_subsumption,
% 0.97/0.99                [status(thm)],
% 0.97/0.99                [c_333,c_21,c_20,c_19]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_338,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | v1_zfmisc_1(X0) ),
% 0.97/0.99      inference(renaming,[status(thm)],[c_337]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_15,negated_conjecture,
% 0.97/0.99      ( ~ v3_tex_2(sK3,sK2) | ~ v1_zfmisc_1(sK3) ),
% 0.97/0.99      inference(cnf_transformation,[],[f62]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_176,plain,
% 0.97/0.99      ( ~ v1_zfmisc_1(sK3) | ~ v3_tex_2(sK3,sK2) ),
% 0.97/0.99      inference(prop_impl,[status(thm)],[c_15]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_177,plain,
% 0.97/0.99      ( ~ v3_tex_2(sK3,sK2) | ~ v1_zfmisc_1(sK3) ),
% 0.97/0.99      inference(renaming,[status(thm)],[c_176]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_715,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,sK2)
% 0.97/0.99      | ~ v3_tex_2(sK3,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | sK3 != X0 ),
% 0.97/0.99      inference(resolution_lifted,[status(thm)],[c_338,c_177]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_716,plain,
% 0.97/0.99      ( ~ v2_tex_2(sK3,sK2)
% 0.97/0.99      | ~ v3_tex_2(sK3,sK2)
% 0.97/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.97/0.99      inference(unflattening,[status(thm)],[c_715]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_17,negated_conjecture,
% 0.97/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.97/0.99      inference(cnf_transformation,[],[f60]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_718,plain,
% 0.97/0.99      ( ~ v3_tex_2(sK3,sK2) | ~ v2_tex_2(sK3,sK2) ),
% 0.97/0.99      inference(global_propositional_subsumption,
% 0.97/0.99                [status(thm)],
% 0.97/0.99                [c_716,c_17]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_719,plain,
% 0.97/0.99      ( ~ v2_tex_2(sK3,sK2) | ~ v3_tex_2(sK3,sK2) ),
% 0.97/0.99      inference(renaming,[status(thm)],[c_718]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_12,plain,
% 0.97/0.99      ( ~ r1_tarski(X0,X1)
% 0.97/0.99      | v1_xboole_0(X0)
% 0.97/0.99      | v1_xboole_0(X1)
% 0.97/0.99      | ~ v1_zfmisc_1(X1)
% 0.97/0.99      | X1 = X0 ),
% 0.97/0.99      inference(cnf_transformation,[],[f52]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_6,plain,
% 0.97/0.99      ( r1_tarski(X0,sK1(X1,X0))
% 0.97/0.99      | ~ v2_tex_2(X0,X1)
% 0.97/0.99      | v3_tex_2(X0,X1)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.97/0.99      | ~ l1_pre_topc(X1) ),
% 0.97/0.99      inference(cnf_transformation,[],[f49]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_553,plain,
% 0.97/0.99      ( r1_tarski(X0,sK1(X1,X0))
% 0.97/0.99      | ~ v2_tex_2(X0,X1)
% 0.97/0.99      | v3_tex_2(X0,X1)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.97/0.99      | sK2 != X1 ),
% 0.97/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_19]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_554,plain,
% 0.97/0.99      ( r1_tarski(X0,sK1(sK2,X0))
% 0.97/0.99      | ~ v2_tex_2(X0,sK2)
% 0.97/0.99      | v3_tex_2(X0,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.97/0.99      inference(unflattening,[status(thm)],[c_553]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_646,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,sK2)
% 0.97/0.99      | v3_tex_2(X0,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | v1_xboole_0(X1)
% 0.97/0.99      | v1_xboole_0(X2)
% 0.97/0.99      | ~ v1_zfmisc_1(X2)
% 0.97/0.99      | X0 != X1
% 0.97/0.99      | X2 = X1
% 0.97/0.99      | sK1(sK2,X0) != X2 ),
% 0.97/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_554]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_647,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,sK2)
% 0.97/0.99      | v3_tex_2(X0,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | v1_xboole_0(X0)
% 0.97/0.99      | v1_xboole_0(sK1(sK2,X0))
% 0.97/0.99      | ~ v1_zfmisc_1(sK1(sK2,X0))
% 0.97/0.99      | sK1(sK2,X0) = X0 ),
% 0.97/0.99      inference(unflattening,[status(thm)],[c_646]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_5,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,X1)
% 0.97/0.99      | v3_tex_2(X0,X1)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.97/0.99      | ~ l1_pre_topc(X1)
% 0.97/0.99      | sK1(X1,X0) != X0 ),
% 0.97/0.99      inference(cnf_transformation,[],[f50]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_571,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,X1)
% 0.97/0.99      | v3_tex_2(X0,X1)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.97/0.99      | sK1(X1,X0) != X0
% 0.97/0.99      | sK2 != X1 ),
% 0.97/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_19]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_572,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,sK2)
% 0.97/0.99      | v3_tex_2(X0,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | sK1(sK2,X0) != X0 ),
% 0.97/0.99      inference(unflattening,[status(thm)],[c_571]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_651,plain,
% 0.97/0.99      ( ~ v1_zfmisc_1(sK1(sK2,X0))
% 0.97/0.99      | v1_xboole_0(sK1(sK2,X0))
% 0.97/0.99      | v1_xboole_0(X0)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | v3_tex_2(X0,sK2)
% 0.97/0.99      | ~ v2_tex_2(X0,sK2) ),
% 0.97/0.99      inference(global_propositional_subsumption,
% 0.97/0.99                [status(thm)],
% 0.97/0.99                [c_647,c_572]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_652,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,sK2)
% 0.97/0.99      | v3_tex_2(X0,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | v1_xboole_0(X0)
% 0.97/0.99      | v1_xboole_0(sK1(sK2,X0))
% 0.97/0.99      | ~ v1_zfmisc_1(sK1(sK2,X0)) ),
% 0.97/0.99      inference(renaming,[status(thm)],[c_651]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_745,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,sK2)
% 0.97/0.99      | ~ v2_tex_2(X1,sK2)
% 0.97/0.99      | v3_tex_2(X1,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | v1_xboole_0(X1)
% 0.97/0.99      | v1_xboole_0(sK1(sK2,X1))
% 0.97/0.99      | sK1(sK2,X1) != X0 ),
% 0.97/0.99      inference(resolution_lifted,[status(thm)],[c_338,c_652]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_746,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,sK2)
% 0.97/0.99      | ~ v2_tex_2(sK1(sK2,X0),sK2)
% 0.97/0.99      | v3_tex_2(X0,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | ~ m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | v1_xboole_0(X0)
% 0.97/0.99      | v1_xboole_0(sK1(sK2,X0)) ),
% 0.97/0.99      inference(unflattening,[status(thm)],[c_745]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_8,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,X1)
% 0.97/0.99      | v3_tex_2(X0,X1)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.97/0.99      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 0.97/0.99      | ~ l1_pre_topc(X1) ),
% 0.97/0.99      inference(cnf_transformation,[],[f47]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_517,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,X1)
% 0.97/0.99      | v3_tex_2(X0,X1)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.97/0.99      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 0.97/0.99      | sK2 != X1 ),
% 0.97/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_518,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,sK2)
% 0.97/0.99      | v3_tex_2(X0,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.97/0.99      inference(unflattening,[status(thm)],[c_517]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_7,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,X1)
% 0.97/0.99      | v2_tex_2(sK1(X1,X0),X1)
% 0.97/0.99      | v3_tex_2(X0,X1)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.97/0.99      | ~ l1_pre_topc(X1) ),
% 0.97/0.99      inference(cnf_transformation,[],[f48]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_535,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,X1)
% 0.97/0.99      | v2_tex_2(sK1(X1,X0),X1)
% 0.97/0.99      | v3_tex_2(X0,X1)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.97/0.99      | sK2 != X1 ),
% 0.97/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_536,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,sK2)
% 0.97/0.99      | v2_tex_2(sK1(sK2,X0),sK2)
% 0.97/0.99      | v3_tex_2(X0,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.97/0.99      inference(unflattening,[status(thm)],[c_535]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_750,plain,
% 0.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | v3_tex_2(X0,sK2)
% 0.97/0.99      | ~ v2_tex_2(X0,sK2)
% 0.97/0.99      | v1_xboole_0(X0)
% 0.97/0.99      | v1_xboole_0(sK1(sK2,X0)) ),
% 0.97/0.99      inference(global_propositional_subsumption,
% 0.97/0.99                [status(thm)],
% 0.97/0.99                [c_746,c_518,c_536]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_751,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,sK2)
% 0.97/0.99      | v3_tex_2(X0,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | v1_xboole_0(X0)
% 0.97/0.99      | v1_xboole_0(sK1(sK2,X0)) ),
% 0.97/0.99      inference(renaming,[status(thm)],[c_750]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_809,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,sK2)
% 0.97/0.99      | ~ v2_tex_2(sK3,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | v1_xboole_0(X0)
% 0.97/0.99      | v1_xboole_0(sK1(sK2,X0))
% 0.97/0.99      | sK2 != sK2
% 0.97/0.99      | sK3 != X0 ),
% 0.97/0.99      inference(resolution_lifted,[status(thm)],[c_719,c_751]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_810,plain,
% 0.97/0.99      ( ~ v2_tex_2(sK3,sK2)
% 0.97/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | v1_xboole_0(sK1(sK2,sK3))
% 0.97/0.99      | v1_xboole_0(sK3) ),
% 0.97/0.99      inference(unflattening,[status(thm)],[c_809]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_18,negated_conjecture,
% 0.97/0.99      ( ~ v1_xboole_0(sK3) ),
% 0.97/0.99      inference(cnf_transformation,[],[f59]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_13,plain,
% 0.97/0.99      ( v2_tex_2(X0,X1)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.97/0.99      | v2_struct_0(X1)
% 0.97/0.99      | ~ l1_pre_topc(X1)
% 0.97/0.99      | ~ v2_tdlat_3(X1)
% 0.97/0.99      | ~ v2_pre_topc(X1)
% 0.97/0.99      | v1_xboole_0(X0)
% 0.97/0.99      | ~ v1_zfmisc_1(X0) ),
% 0.97/0.99      inference(cnf_transformation,[],[f54]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_353,plain,
% 0.97/0.99      ( v2_tex_2(X0,X1)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.97/0.99      | ~ l1_pre_topc(X1)
% 0.97/0.99      | ~ v2_tdlat_3(X1)
% 0.97/0.99      | ~ v2_pre_topc(X1)
% 0.97/0.99      | v1_xboole_0(X0)
% 0.97/0.99      | ~ v1_zfmisc_1(X0)
% 0.97/0.99      | sK2 != X1 ),
% 0.97/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_354,plain,
% 0.97/0.99      ( v2_tex_2(X0,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | ~ l1_pre_topc(sK2)
% 0.97/0.99      | ~ v2_tdlat_3(sK2)
% 0.97/0.99      | ~ v2_pre_topc(sK2)
% 0.97/0.99      | v1_xboole_0(X0)
% 0.97/0.99      | ~ v1_zfmisc_1(X0) ),
% 0.97/0.99      inference(unflattening,[status(thm)],[c_353]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_358,plain,
% 0.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | v2_tex_2(X0,sK2)
% 0.97/0.99      | v1_xboole_0(X0)
% 0.97/0.99      | ~ v1_zfmisc_1(X0) ),
% 0.97/0.99      inference(global_propositional_subsumption,
% 0.97/0.99                [status(thm)],
% 0.97/0.99                [c_354,c_21,c_20,c_19]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_359,plain,
% 0.97/0.99      ( v2_tex_2(X0,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | v1_xboole_0(X0)
% 0.97/0.99      | ~ v1_zfmisc_1(X0) ),
% 0.97/0.99      inference(renaming,[status(thm)],[c_358]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_16,negated_conjecture,
% 0.97/0.99      ( v3_tex_2(sK3,sK2) | v1_zfmisc_1(sK3) ),
% 0.97/0.99      inference(cnf_transformation,[],[f61]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_178,plain,
% 0.97/0.99      ( v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2) ),
% 0.97/0.99      inference(prop_impl,[status(thm)],[c_16]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_179,plain,
% 0.97/0.99      ( v3_tex_2(sK3,sK2) | v1_zfmisc_1(sK3) ),
% 0.97/0.99      inference(renaming,[status(thm)],[c_178]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_731,plain,
% 0.97/0.99      ( v2_tex_2(X0,sK2)
% 0.97/0.99      | v3_tex_2(sK3,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | v1_xboole_0(X0)
% 0.97/0.99      | sK3 != X0 ),
% 0.97/0.99      inference(resolution_lifted,[status(thm)],[c_359,c_179]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_732,plain,
% 0.97/0.99      ( v2_tex_2(sK3,sK2)
% 0.97/0.99      | v3_tex_2(sK3,sK2)
% 0.97/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | v1_xboole_0(sK3) ),
% 0.97/0.99      inference(unflattening,[status(thm)],[c_731]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_734,plain,
% 0.97/0.99      ( v2_tex_2(sK3,sK2) | v3_tex_2(sK3,sK2) ),
% 0.97/0.99      inference(global_propositional_subsumption,
% 0.97/0.99                [status(thm)],
% 0.97/0.99                [c_732,c_18,c_17]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_10,plain,
% 0.97/0.99      ( v2_tex_2(X0,X1)
% 0.97/0.99      | ~ v3_tex_2(X0,X1)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.97/0.99      | ~ l1_pre_topc(X1) ),
% 0.97/0.99      inference(cnf_transformation,[],[f45]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_502,plain,
% 0.97/0.99      ( v2_tex_2(X0,X1)
% 0.97/0.99      | ~ v3_tex_2(X0,X1)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.97/0.99      | sK2 != X1 ),
% 0.97/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_503,plain,
% 0.97/0.99      ( v2_tex_2(X0,sK2)
% 0.97/0.99      | ~ v3_tex_2(X0,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.97/0.99      inference(unflattening,[status(thm)],[c_502]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_798,plain,
% 0.97/0.99      ( v2_tex_2(X0,sK2)
% 0.97/0.99      | v2_tex_2(sK3,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | sK2 != sK2
% 0.97/0.99      | sK3 != X0 ),
% 0.97/0.99      inference(resolution_lifted,[status(thm)],[c_734,c_503]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_799,plain,
% 0.97/0.99      ( v2_tex_2(sK3,sK2)
% 0.97/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.97/0.99      inference(unflattening,[status(thm)],[c_798]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_812,plain,
% 0.97/0.99      ( v1_xboole_0(sK1(sK2,sK3)) ),
% 0.97/0.99      inference(global_propositional_subsumption,
% 0.97/0.99                [status(thm)],
% 0.97/0.99                [c_810,c_18,c_17,c_799]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_868,plain,
% 0.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.97/0.99      | sK1(sK2,sK3) != X1
% 0.97/0.99      | k1_xboole_0 = X0 ),
% 0.97/0.99      inference(resolution_lifted,[status(thm)],[c_314,c_812]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_869,plain,
% 0.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK2,sK3))) | k1_xboole_0 = X0 ),
% 0.97/0.99      inference(unflattening,[status(thm)],[c_868]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_884,plain,
% 0.97/0.99      ( k6_subset_1(X0,X1) != X2
% 0.97/0.99      | k1_zfmisc_1(sK1(sK2,sK3)) != k1_zfmisc_1(X0)
% 0.97/0.99      | k1_xboole_0 = X2 ),
% 0.97/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_869]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_885,plain,
% 0.97/0.99      ( k1_zfmisc_1(sK1(sK2,sK3)) != k1_zfmisc_1(X0)
% 0.97/0.99      | k1_xboole_0 = k6_subset_1(X0,X1) ),
% 0.97/0.99      inference(unflattening,[status(thm)],[c_884]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_923,plain,
% 0.97/0.99      ( k1_xboole_0 = k6_subset_1(X0_48,X1_48)
% 0.97/0.99      | k1_zfmisc_1(sK1(sK2,sK3)) != k1_zfmisc_1(X0_48) ),
% 0.97/0.99      inference(subtyping,[status(esa)],[c_885]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_1028,plain,
% 0.97/0.99      ( k6_subset_1(sK1(sK2,sK3),X0_48) = k1_xboole_0 ),
% 0.97/0.99      inference(equality_resolution,[status(thm)],[c_923]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_1029,plain,
% 0.97/0.99      ( k6_subset_1(sK1(sK2,sK3),sK3) = k1_xboole_0 ),
% 0.97/0.99      inference(instantiation,[status(thm)],[c_1028]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_11,plain,
% 0.97/0.99      ( ~ r1_tarski(X0,X1)
% 0.97/0.99      | X1 = X0
% 0.97/0.99      | k6_subset_1(X1,X0) != k1_xboole_0 ),
% 0.97/0.99      inference(cnf_transformation,[],[f51]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_676,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,sK2)
% 0.97/0.99      | v3_tex_2(X0,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | X0 != X1
% 0.97/0.99      | X2 = X1
% 0.97/0.99      | sK1(sK2,X0) != X2
% 0.97/0.99      | k6_subset_1(X2,X1) != k1_xboole_0 ),
% 0.97/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_554]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_677,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,sK2)
% 0.97/0.99      | v3_tex_2(X0,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | sK1(sK2,X0) = X0
% 0.97/0.99      | k6_subset_1(sK1(sK2,X0),X0) != k1_xboole_0 ),
% 0.97/0.99      inference(unflattening,[status(thm)],[c_676]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_681,plain,
% 0.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | v3_tex_2(X0,sK2)
% 0.97/0.99      | ~ v2_tex_2(X0,sK2)
% 0.97/0.99      | k6_subset_1(sK1(sK2,X0),X0) != k1_xboole_0 ),
% 0.97/0.99      inference(global_propositional_subsumption,
% 0.97/0.99                [status(thm)],
% 0.97/0.99                [c_677,c_572]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_682,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,sK2)
% 0.97/0.99      | v3_tex_2(X0,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | k6_subset_1(sK1(sK2,X0),X0) != k1_xboole_0 ),
% 0.97/0.99      inference(renaming,[status(thm)],[c_681]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_820,plain,
% 0.97/0.99      ( ~ v2_tex_2(X0,sK2)
% 0.97/0.99      | ~ v2_tex_2(sK3,sK2)
% 0.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | k6_subset_1(sK1(sK2,X0),X0) != k1_xboole_0
% 0.97/0.99      | sK2 != sK2
% 0.97/0.99      | sK3 != X0 ),
% 0.97/0.99      inference(resolution_lifted,[status(thm)],[c_719,c_682]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_821,plain,
% 0.97/0.99      ( ~ v2_tex_2(sK3,sK2)
% 0.97/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.97/0.99      | k6_subset_1(sK1(sK2,sK3),sK3) != k1_xboole_0 ),
% 0.97/0.99      inference(unflattening,[status(thm)],[c_820]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_823,plain,
% 0.97/0.99      ( k6_subset_1(sK1(sK2,sK3),sK3) != k1_xboole_0 ),
% 0.97/0.99      inference(global_propositional_subsumption,
% 0.97/0.99                [status(thm)],
% 0.97/0.99                [c_821,c_17,c_799]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(c_925,plain,
% 0.97/0.99      ( k6_subset_1(sK1(sK2,sK3),sK3) != k1_xboole_0 ),
% 0.97/0.99      inference(subtyping,[status(esa)],[c_823]) ).
% 0.97/0.99  
% 0.97/0.99  cnf(contradiction,plain,
% 0.97/0.99      ( $false ),
% 0.97/0.99      inference(minisat,[status(thm)],[c_1029,c_925]) ).
% 0.97/0.99  
% 0.97/0.99  
% 0.97/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 0.97/0.99  
% 0.97/0.99  ------                               Statistics
% 0.97/0.99  
% 0.97/0.99  ------ General
% 0.97/0.99  
% 0.97/0.99  abstr_ref_over_cycles:                  0
% 0.97/0.99  abstr_ref_under_cycles:                 0
% 0.97/0.99  gc_basic_clause_elim:                   0
% 0.97/0.99  forced_gc_time:                         0
% 0.97/0.99  parsing_time:                           0.009
% 0.97/0.99  unif_index_cands_time:                  0.
% 0.97/0.99  unif_index_add_time:                    0.
% 0.97/0.99  orderings_time:                         0.
% 0.97/0.99  out_proof_time:                         0.01
% 0.97/0.99  total_time:                             0.062
% 0.97/0.99  num_of_symbols:                         53
% 0.97/0.99  num_of_terms:                           941
% 0.97/0.99  
% 0.97/0.99  ------ Preprocessing
% 0.97/0.99  
% 0.97/0.99  num_of_splits:                          0
% 0.97/0.99  num_of_split_atoms:                     0
% 0.97/0.99  num_of_reused_defs:                     0
% 0.97/0.99  num_eq_ax_congr_red:                    10
% 0.97/0.99  num_of_sem_filtered_clauses:            0
% 0.97/0.99  num_of_subtypes:                        3
% 0.97/0.99  monotx_restored_types:                  0
% 0.97/0.99  sat_num_of_epr_types:                   0
% 0.97/0.99  sat_num_of_non_cyclic_types:            0
% 0.97/0.99  sat_guarded_non_collapsed_types:        0
% 0.97/0.99  num_pure_diseq_elim:                    0
% 0.97/0.99  simp_replaced_by:                       0
% 0.97/0.99  res_preprocessed:                       40
% 0.97/0.99  prep_upred:                             0
% 0.97/0.99  prep_unflattend:                        37
% 0.97/0.99  smt_new_axioms:                         0
% 0.97/0.99  pred_elim_cands:                        0
% 0.97/0.99  pred_elim:                              11
% 0.97/0.99  pred_elim_cl:                           18
% 0.97/0.99  pred_elim_cycles:                       13
% 0.97/0.99  merged_defs:                            2
% 0.97/0.99  merged_defs_ncl:                        0
% 0.97/0.99  bin_hyper_res:                          2
% 0.97/0.99  prep_cycles:                            3
% 0.97/0.99  pred_elim_time:                         0.012
% 0.97/0.99  splitting_time:                         0.
% 0.97/0.99  sem_filter_time:                        0.
% 0.97/0.99  monotx_time:                            0.
% 0.97/0.99  subtype_inf_time:                       0.
% 0.97/0.99  
% 0.97/0.99  ------ Problem properties
% 0.97/0.99  
% 0.97/0.99  clauses:                                5
% 0.97/0.99  conjectures:                            0
% 0.97/0.99  epr:                                    0
% 0.97/0.99  horn:                                   5
% 0.97/0.99  ground:                                 4
% 0.97/0.99  unary:                                  2
% 0.97/0.99  binary:                                 3
% 0.97/0.99  lits:                                   8
% 0.97/0.99  lits_eq:                                8
% 0.97/0.99  fd_pure:                                0
% 0.97/0.99  fd_pseudo:                              0
% 0.97/0.99  fd_cond:                                0
% 0.97/0.99  fd_pseudo_cond:                         0
% 0.97/0.99  ac_symbols:                             0
% 0.97/0.99  
% 0.97/0.99  ------ Propositional Solver
% 0.97/0.99  
% 0.97/0.99  prop_solver_calls:                      21
% 0.97/0.99  prop_fast_solver_calls:                 410
% 0.97/0.99  smt_solver_calls:                       0
% 0.97/0.99  smt_fast_solver_calls:                  0
% 0.97/0.99  prop_num_of_clauses:                    264
% 0.97/0.99  prop_preprocess_simplified:             1089
% 0.97/0.99  prop_fo_subsumed:                       31
% 0.97/0.99  prop_solver_time:                       0.
% 0.97/0.99  smt_solver_time:                        0.
% 0.97/0.99  smt_fast_solver_time:                   0.
% 0.97/0.99  prop_fast_solver_time:                  0.
% 0.97/0.99  prop_unsat_core_time:                   0.
% 0.97/0.99  
% 0.97/0.99  ------ QBF
% 0.97/0.99  
% 0.97/0.99  qbf_q_res:                              0
% 0.97/0.99  qbf_num_tautologies:                    0
% 0.97/0.99  qbf_prep_cycles:                        0
% 0.97/0.99  
% 0.97/0.99  ------ BMC1
% 0.97/0.99  
% 0.97/0.99  bmc1_current_bound:                     -1
% 0.97/0.99  bmc1_last_solved_bound:                 -1
% 0.97/0.99  bmc1_unsat_core_size:                   -1
% 0.97/0.99  bmc1_unsat_core_parents_size:           -1
% 0.97/0.99  bmc1_merge_next_fun:                    0
% 0.97/0.99  bmc1_unsat_core_clauses_time:           0.
% 0.97/0.99  
% 0.97/0.99  ------ Instantiation
% 0.97/0.99  
% 0.97/0.99  inst_num_of_clauses:                    43
% 0.97/0.99  inst_num_in_passive:                    14
% 0.97/0.99  inst_num_in_active:                     28
% 0.97/0.99  inst_num_in_unprocessed:                1
% 0.97/0.99  inst_num_of_loops:                      30
% 0.97/0.99  inst_num_of_learning_restarts:          0
% 0.97/0.99  inst_num_moves_active_passive:          0
% 0.97/0.99  inst_lit_activity:                      0
% 0.97/0.99  inst_lit_activity_moves:                0
% 0.97/0.99  inst_num_tautologies:                   0
% 0.97/0.99  inst_num_prop_implied:                  0
% 0.97/0.99  inst_num_existing_simplified:           0
% 0.97/0.99  inst_num_eq_res_simplified:             0
% 0.97/0.99  inst_num_child_elim:                    0
% 0.97/0.99  inst_num_of_dismatching_blockings:      1
% 0.97/0.99  inst_num_of_non_proper_insts:           26
% 0.97/0.99  inst_num_of_duplicates:                 0
% 0.97/0.99  inst_inst_num_from_inst_to_res:         0
% 0.97/0.99  inst_dismatching_checking_time:         0.
% 0.97/0.99  
% 0.97/0.99  ------ Resolution
% 0.97/0.99  
% 0.97/0.99  res_num_of_clauses:                     0
% 0.97/0.99  res_num_in_passive:                     0
% 0.97/0.99  res_num_in_active:                      0
% 0.97/0.99  res_num_of_loops:                       43
% 0.97/0.99  res_forward_subset_subsumed:            4
% 0.97/0.99  res_backward_subset_subsumed:           0
% 0.97/0.99  res_forward_subsumed:                   1
% 0.97/0.99  res_backward_subsumed:                  0
% 0.97/0.99  res_forward_subsumption_resolution:     0
% 0.97/0.99  res_backward_subsumption_resolution:    0
% 0.97/0.99  res_clause_to_clause_subsumption:       14
% 0.97/0.99  res_orphan_elimination:                 0
% 0.97/0.99  res_tautology_del:                      18
% 0.97/0.99  res_num_eq_res_simplified:              0
% 0.97/0.99  res_num_sel_changes:                    0
% 0.97/0.99  res_moves_from_active_to_pass:          0
% 0.97/0.99  
% 0.97/0.99  ------ Superposition
% 0.97/0.99  
% 0.97/0.99  sup_time_total:                         0.
% 0.97/0.99  sup_time_generating:                    0.
% 0.97/0.99  sup_time_sim_full:                      0.
% 0.97/0.99  sup_time_sim_immed:                     0.
% 0.97/0.99  
% 0.97/0.99  sup_num_of_clauses:                     6
% 0.97/0.99  sup_num_in_active:                      5
% 0.97/0.99  sup_num_in_passive:                     1
% 0.97/0.99  sup_num_of_loops:                       4
% 0.97/0.99  sup_fw_superposition:                   0
% 0.97/0.99  sup_bw_superposition:                   0
% 0.97/0.99  sup_immediate_simplified:               0
% 0.97/0.99  sup_given_eliminated:                   0
% 0.97/0.99  comparisons_done:                       0
% 0.97/0.99  comparisons_avoided:                    0
% 0.97/0.99  
% 0.97/0.99  ------ Simplifications
% 0.97/0.99  
% 0.97/0.99  
% 0.97/0.99  sim_fw_subset_subsumed:                 0
% 0.97/0.99  sim_bw_subset_subsumed:                 0
% 0.97/0.99  sim_fw_subsumed:                        0
% 0.97/0.99  sim_bw_subsumed:                        0
% 0.97/0.99  sim_fw_subsumption_res:                 0
% 0.97/0.99  sim_bw_subsumption_res:                 0
% 0.97/0.99  sim_tautology_del:                      0
% 0.97/0.99  sim_eq_tautology_del:                   0
% 0.97/0.99  sim_eq_res_simp:                        0
% 0.97/0.99  sim_fw_demodulated:                     0
% 0.97/0.99  sim_bw_demodulated:                     0
% 0.97/0.99  sim_light_normalised:                   0
% 0.97/0.99  sim_joinable_taut:                      0
% 0.97/0.99  sim_joinable_simp:                      0
% 0.97/0.99  sim_ac_normalised:                      0
% 0.97/0.99  sim_smt_subsumption:                    0
% 0.97/0.99  
%------------------------------------------------------------------------------
