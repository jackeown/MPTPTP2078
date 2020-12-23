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
% DateTime   : Thu Dec  3 12:27:22 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :  147 (1173 expanded)
%              Number of clauses        :   96 ( 269 expanded)
%              Number of leaves         :   15 ( 265 expanded)
%              Depth                    :   23
%              Number of atoms          :  652 (9277 expanded)
%              Number of equality atoms :  147 ( 294 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ( ~ v1_zfmisc_1(sK5)
          | ~ v3_tex_2(sK5,X0) )
        & ( v1_zfmisc_1(sK5)
          | v3_tex_2(sK5,X0) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
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
            | ~ v3_tex_2(X1,sK4) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,sK4) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK4)
      & v2_tdlat_3(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ( ~ v1_zfmisc_1(sK5)
      | ~ v3_tex_2(sK5,sK4) )
    & ( v1_zfmisc_1(sK5)
      | v3_tex_2(sK5,sK4) )
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & ~ v1_xboole_0(sK5)
    & l1_pre_topc(sK4)
    & v2_tdlat_3(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f57,f59,f58])).

fof(f95,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f60])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK3(X0,X1) != X1
        & r1_tarski(X1,sK3(X0,X1))
        & v2_tex_2(sK3(X0,X1),X0)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK3(X0,X1) != X1
                & r1_tarski(X1,sK3(X0,X1))
                & v2_tex_2(sK3(X0,X1),X0)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f52,f53])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK3(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f93,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f18,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f91,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f92,plain,(
    v2_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f96,plain,
    ( v1_zfmisc_1(sK5)
    | v3_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f94,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f60])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f73,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f97,plain,
    ( ~ v1_zfmisc_1(sK5)
    | ~ v3_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f60])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f17,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f87,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK3(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK3(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2414,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_21,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,sK3(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_672,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,sK3(X1,X0))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_673,plain,
    ( ~ v2_tex_2(X0,sK4)
    | v3_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(X0,sK3(sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_672])).

cnf(c_2408,plain,
    ( v2_tex_2(X0,sK4) != iProver_top
    | v3_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X0,sK3(sK4,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_673])).

cnf(c_2730,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | v3_tex_2(sK5,sK4) = iProver_top
    | r1_tarski(sK5,sK3(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2414,c_2408])).

cnf(c_42,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_27,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_498,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_36])).

cnf(c_499,plain,
    ( v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_tdlat_3(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_34,negated_conjecture,
    ( v2_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_501,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_tex_2(X0,sK4)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_499,c_35,c_34,c_33])).

cnf(c_502,plain,
    ( v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_501])).

cnf(c_30,negated_conjecture,
    ( v3_tex_2(sK5,sK4)
    | v1_zfmisc_1(sK5) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_285,plain,
    ( v1_zfmisc_1(sK5)
    | v3_tex_2(sK5,sK4) ),
    inference(prop_impl,[status(thm)],[c_30])).

cnf(c_286,plain,
    ( v3_tex_2(sK5,sK4)
    | v1_zfmisc_1(sK5) ),
    inference(renaming,[status(thm)],[c_285])).

cnf(c_802,plain,
    ( v2_tex_2(X0,sK4)
    | v3_tex_2(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_502,c_286])).

cnf(c_803,plain,
    ( v2_tex_2(sK5,sK4)
    | v3_tex_2(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_802])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_805,plain,
    ( v2_tex_2(sK5,sK4)
    | v3_tex_2(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_803,c_32,c_31])).

cnf(c_25,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_599,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_600,plain,
    ( v2_tex_2(X0,sK4)
    | ~ v3_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_599])).

cnf(c_854,plain,
    ( v2_tex_2(X0,sK4)
    | v2_tex_2(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | sK4 != sK4
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_805,c_600])).

cnf(c_855,plain,
    ( v2_tex_2(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_854])).

cnf(c_856,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_855])).

cnf(c_28,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_12,plain,
    ( v1_zfmisc_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_201,plain,
    ( v1_zfmisc_1(X0)
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_12])).

cnf(c_202,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_201])).

cnf(c_477,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | v1_zfmisc_1(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_202,c_36])).

cnf(c_478,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_tdlat_3(sK4)
    | ~ v2_pre_topc(sK4)
    | v1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_482,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_tex_2(X0,sK4)
    | v1_zfmisc_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_35,c_34,c_33])).

cnf(c_483,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_482])).

cnf(c_29,negated_conjecture,
    ( ~ v3_tex_2(sK5,sK4)
    | ~ v1_zfmisc_1(sK5) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_283,plain,
    ( ~ v1_zfmisc_1(sK5)
    | ~ v3_tex_2(sK5,sK4) ),
    inference(prop_impl,[status(thm)],[c_29])).

cnf(c_284,plain,
    ( ~ v3_tex_2(sK5,sK4)
    | ~ v1_zfmisc_1(sK5) ),
    inference(renaming,[status(thm)],[c_283])).

cnf(c_786,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ v3_tex_2(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_483,c_284])).

cnf(c_787,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | ~ v3_tex_2(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_786])).

cnf(c_789,plain,
    ( ~ v3_tex_2(sK5,sK4)
    | ~ v2_tex_2(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_787,c_31])).

cnf(c_790,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | ~ v3_tex_2(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_789])).

cnf(c_877,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ v2_tex_2(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(X0,sK3(sK4,X0))
    | sK4 != sK4
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_790,c_673])).

cnf(c_878,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK5,sK3(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_877])).

cnf(c_879,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK5,sK3(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_878])).

cnf(c_2739,plain,
    ( r1_tarski(sK5,sK3(sK4,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2730,c_42,c_856,c_879])).

cnf(c_23,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_636,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_637,plain,
    ( ~ v2_tex_2(X0,sK4)
    | v3_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_636])).

cnf(c_2410,plain,
    ( v2_tex_2(X0,sK4) != iProver_top
    | v3_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_637])).

cnf(c_26,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_742,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X0 != X2
    | X2 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_483])).

cnf(c_743,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X0 = X1 ),
    inference(unflattening,[status(thm)],[c_742])).

cnf(c_2406,plain,
    ( X0 = X1
    | v2_tex_2(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_3424,plain,
    ( sK3(sK4,X0) = X1
    | v2_tex_2(X0,sK4) != iProver_top
    | v2_tex_2(sK3(sK4,X0),sK4) != iProver_top
    | v3_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X1,sK3(sK4,X0)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK3(sK4,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2410,c_2406])).

cnf(c_22,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK3(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_654,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK3(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_655,plain,
    ( ~ v2_tex_2(X0,sK4)
    | v2_tex_2(sK3(sK4,X0),sK4)
    | v3_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_654])).

cnf(c_656,plain,
    ( v2_tex_2(X0,sK4) != iProver_top
    | v2_tex_2(sK3(sK4,X0),sK4) = iProver_top
    | v3_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_655])).

cnf(c_3644,plain,
    ( v2_tex_2(X0,sK4) != iProver_top
    | sK3(sK4,X0) = X1
    | v3_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X1,sK3(sK4,X0)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK3(sK4,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3424,c_656])).

cnf(c_3645,plain,
    ( sK3(sK4,X0) = X1
    | v2_tex_2(X0,sK4) != iProver_top
    | v3_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X1,sK3(sK4,X0)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK3(sK4,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3644])).

cnf(c_3655,plain,
    ( sK3(sK4,sK5) = X0
    | v2_tex_2(sK5,sK4) != iProver_top
    | v3_tex_2(sK5,sK4) = iProver_top
    | r1_tarski(X0,sK3(sK4,sK5)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK3(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2414,c_3645])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_121,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_791,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | v3_tex_2(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_790])).

cnf(c_1727,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2677,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1727])).

cnf(c_2679,plain,
    ( v1_xboole_0(sK5)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2677])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2799,plain,
    ( ~ r1_tarski(sK5,k1_xboole_0)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1725,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2830,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1725])).

cnf(c_1730,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_2846,plain,
    ( r1_tarski(sK5,X0)
    | ~ r1_tarski(sK5,sK3(sK4,sK5))
    | X0 != sK3(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1730])).

cnf(c_2861,plain,
    ( ~ r1_tarski(sK5,sK3(sK4,sK5))
    | r1_tarski(sK5,k1_xboole_0)
    | k1_xboole_0 != sK3(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2846])).

cnf(c_1726,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2785,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_1726])).

cnf(c_3154,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2785])).

cnf(c_3155,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_3154])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3316,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK3(sK4,sK5))
    | X0 = sK3(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3322,plain,
    ( X0 = sK3(sK4,sK5)
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3316])).

cnf(c_3324,plain,
    ( k1_xboole_0 = sK3(sK4,sK5)
    | v1_xboole_0(sK3(sK4,sK5)) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3322])).

cnf(c_4031,plain,
    ( v1_xboole_0(X0) = iProver_top
    | r1_tarski(X0,sK3(sK4,sK5)) != iProver_top
    | sK3(sK4,sK5) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3655,c_32,c_31,c_42,c_0,c_121,c_791,c_855,c_856,c_878,c_2679,c_2799,c_2830,c_2861,c_3155,c_3324])).

cnf(c_4032,plain,
    ( sK3(sK4,sK5) = X0
    | r1_tarski(X0,sK3(sK4,sK5)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4031])).

cnf(c_4038,plain,
    ( sK3(sK4,sK5) = sK5
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2739,c_4032])).

cnf(c_20,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_690,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK3(X1,X0) != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_33])).

cnf(c_691,plain,
    ( ~ v2_tex_2(X0,sK4)
    | v3_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | sK3(sK4,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_690])).

cnf(c_869,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ v2_tex_2(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | sK3(sK4,X0) != X0
    | sK4 != sK4
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_790,c_691])).

cnf(c_870,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | sK3(sK4,sK5) != sK5 ),
    inference(unflattening,[status(thm)],[c_869])).

cnf(c_41,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4038,c_870,c_855,c_31,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.11/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/0.99  
% 2.11/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.11/0.99  
% 2.11/0.99  ------  iProver source info
% 2.11/0.99  
% 2.11/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.11/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.11/0.99  git: non_committed_changes: false
% 2.11/0.99  git: last_make_outside_of_git: false
% 2.11/0.99  
% 2.11/0.99  ------ 
% 2.11/0.99  
% 2.11/0.99  ------ Input Options
% 2.11/0.99  
% 2.11/0.99  --out_options                           all
% 2.11/0.99  --tptp_safe_out                         true
% 2.11/0.99  --problem_path                          ""
% 2.11/0.99  --include_path                          ""
% 2.11/0.99  --clausifier                            res/vclausify_rel
% 2.11/0.99  --clausifier_options                    --mode clausify
% 2.11/0.99  --stdin                                 false
% 2.11/0.99  --stats_out                             all
% 2.11/0.99  
% 2.11/0.99  ------ General Options
% 2.11/0.99  
% 2.11/0.99  --fof                                   false
% 2.11/0.99  --time_out_real                         305.
% 2.11/0.99  --time_out_virtual                      -1.
% 2.11/0.99  --symbol_type_check                     false
% 2.11/0.99  --clausify_out                          false
% 2.11/0.99  --sig_cnt_out                           false
% 2.11/0.99  --trig_cnt_out                          false
% 2.11/0.99  --trig_cnt_out_tolerance                1.
% 2.11/0.99  --trig_cnt_out_sk_spl                   false
% 2.11/0.99  --abstr_cl_out                          false
% 2.11/0.99  
% 2.11/0.99  ------ Global Options
% 2.11/0.99  
% 2.11/0.99  --schedule                              default
% 2.11/0.99  --add_important_lit                     false
% 2.11/0.99  --prop_solver_per_cl                    1000
% 2.11/0.99  --min_unsat_core                        false
% 2.11/0.99  --soft_assumptions                      false
% 2.11/0.99  --soft_lemma_size                       3
% 2.11/0.99  --prop_impl_unit_size                   0
% 2.11/0.99  --prop_impl_unit                        []
% 2.11/0.99  --share_sel_clauses                     true
% 2.11/0.99  --reset_solvers                         false
% 2.11/0.99  --bc_imp_inh                            [conj_cone]
% 2.11/0.99  --conj_cone_tolerance                   3.
% 2.11/0.99  --extra_neg_conj                        none
% 2.11/0.99  --large_theory_mode                     true
% 2.11/0.99  --prolific_symb_bound                   200
% 2.11/0.99  --lt_threshold                          2000
% 2.11/0.99  --clause_weak_htbl                      true
% 2.11/0.99  --gc_record_bc_elim                     false
% 2.11/0.99  
% 2.11/0.99  ------ Preprocessing Options
% 2.11/0.99  
% 2.11/0.99  --preprocessing_flag                    true
% 2.11/0.99  --time_out_prep_mult                    0.1
% 2.11/0.99  --splitting_mode                        input
% 2.11/0.99  --splitting_grd                         true
% 2.11/0.99  --splitting_cvd                         false
% 2.11/0.99  --splitting_cvd_svl                     false
% 2.11/0.99  --splitting_nvd                         32
% 2.11/0.99  --sub_typing                            true
% 2.11/0.99  --prep_gs_sim                           true
% 2.11/0.99  --prep_unflatten                        true
% 2.11/0.99  --prep_res_sim                          true
% 2.11/0.99  --prep_upred                            true
% 2.11/0.99  --prep_sem_filter                       exhaustive
% 2.11/0.99  --prep_sem_filter_out                   false
% 2.11/0.99  --pred_elim                             true
% 2.11/0.99  --res_sim_input                         true
% 2.11/0.99  --eq_ax_congr_red                       true
% 2.11/0.99  --pure_diseq_elim                       true
% 2.11/0.99  --brand_transform                       false
% 2.11/0.99  --non_eq_to_eq                          false
% 2.11/0.99  --prep_def_merge                        true
% 2.11/0.99  --prep_def_merge_prop_impl              false
% 2.11/0.99  --prep_def_merge_mbd                    true
% 2.11/0.99  --prep_def_merge_tr_red                 false
% 2.11/0.99  --prep_def_merge_tr_cl                  false
% 2.11/0.99  --smt_preprocessing                     true
% 2.11/0.99  --smt_ac_axioms                         fast
% 2.11/0.99  --preprocessed_out                      false
% 2.11/0.99  --preprocessed_stats                    false
% 2.11/0.99  
% 2.11/0.99  ------ Abstraction refinement Options
% 2.11/0.99  
% 2.11/0.99  --abstr_ref                             []
% 2.11/0.99  --abstr_ref_prep                        false
% 2.11/0.99  --abstr_ref_until_sat                   false
% 2.11/0.99  --abstr_ref_sig_restrict                funpre
% 2.11/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.11/0.99  --abstr_ref_under                       []
% 2.11/0.99  
% 2.11/0.99  ------ SAT Options
% 2.11/0.99  
% 2.11/0.99  --sat_mode                              false
% 2.11/0.99  --sat_fm_restart_options                ""
% 2.11/0.99  --sat_gr_def                            false
% 2.11/0.99  --sat_epr_types                         true
% 2.11/0.99  --sat_non_cyclic_types                  false
% 2.11/0.99  --sat_finite_models                     false
% 2.11/0.99  --sat_fm_lemmas                         false
% 2.11/0.99  --sat_fm_prep                           false
% 2.11/0.99  --sat_fm_uc_incr                        true
% 2.11/0.99  --sat_out_model                         small
% 2.11/0.99  --sat_out_clauses                       false
% 2.11/0.99  
% 2.11/0.99  ------ QBF Options
% 2.11/0.99  
% 2.11/0.99  --qbf_mode                              false
% 2.11/0.99  --qbf_elim_univ                         false
% 2.11/0.99  --qbf_dom_inst                          none
% 2.11/0.99  --qbf_dom_pre_inst                      false
% 2.11/0.99  --qbf_sk_in                             false
% 2.11/0.99  --qbf_pred_elim                         true
% 2.11/0.99  --qbf_split                             512
% 2.11/0.99  
% 2.11/0.99  ------ BMC1 Options
% 2.11/0.99  
% 2.11/0.99  --bmc1_incremental                      false
% 2.11/0.99  --bmc1_axioms                           reachable_all
% 2.11/0.99  --bmc1_min_bound                        0
% 2.11/0.99  --bmc1_max_bound                        -1
% 2.11/0.99  --bmc1_max_bound_default                -1
% 2.11/0.99  --bmc1_symbol_reachability              true
% 2.11/0.99  --bmc1_property_lemmas                  false
% 2.11/0.99  --bmc1_k_induction                      false
% 2.11/0.99  --bmc1_non_equiv_states                 false
% 2.11/0.99  --bmc1_deadlock                         false
% 2.11/0.99  --bmc1_ucm                              false
% 2.11/0.99  --bmc1_add_unsat_core                   none
% 2.11/0.99  --bmc1_unsat_core_children              false
% 2.11/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.11/0.99  --bmc1_out_stat                         full
% 2.11/0.99  --bmc1_ground_init                      false
% 2.11/0.99  --bmc1_pre_inst_next_state              false
% 2.11/0.99  --bmc1_pre_inst_state                   false
% 2.11/0.99  --bmc1_pre_inst_reach_state             false
% 2.11/0.99  --bmc1_out_unsat_core                   false
% 2.11/0.99  --bmc1_aig_witness_out                  false
% 2.11/0.99  --bmc1_verbose                          false
% 2.11/0.99  --bmc1_dump_clauses_tptp                false
% 2.11/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.11/0.99  --bmc1_dump_file                        -
% 2.11/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.11/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.11/0.99  --bmc1_ucm_extend_mode                  1
% 2.11/0.99  --bmc1_ucm_init_mode                    2
% 2.11/0.99  --bmc1_ucm_cone_mode                    none
% 2.11/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.11/0.99  --bmc1_ucm_relax_model                  4
% 2.11/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.11/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.11/0.99  --bmc1_ucm_layered_model                none
% 2.11/0.99  --bmc1_ucm_max_lemma_size               10
% 2.11/0.99  
% 2.11/0.99  ------ AIG Options
% 2.11/0.99  
% 2.11/0.99  --aig_mode                              false
% 2.11/0.99  
% 2.11/0.99  ------ Instantiation Options
% 2.11/0.99  
% 2.11/0.99  --instantiation_flag                    true
% 2.11/0.99  --inst_sos_flag                         false
% 2.11/0.99  --inst_sos_phase                        true
% 2.11/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.11/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.11/0.99  --inst_lit_sel_side                     num_symb
% 2.11/0.99  --inst_solver_per_active                1400
% 2.11/0.99  --inst_solver_calls_frac                1.
% 2.11/0.99  --inst_passive_queue_type               priority_queues
% 2.11/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.11/0.99  --inst_passive_queues_freq              [25;2]
% 2.11/0.99  --inst_dismatching                      true
% 2.11/0.99  --inst_eager_unprocessed_to_passive     true
% 2.11/0.99  --inst_prop_sim_given                   true
% 2.11/0.99  --inst_prop_sim_new                     false
% 2.11/0.99  --inst_subs_new                         false
% 2.11/0.99  --inst_eq_res_simp                      false
% 2.11/0.99  --inst_subs_given                       false
% 2.11/0.99  --inst_orphan_elimination               true
% 2.11/0.99  --inst_learning_loop_flag               true
% 2.11/0.99  --inst_learning_start                   3000
% 2.11/0.99  --inst_learning_factor                  2
% 2.11/0.99  --inst_start_prop_sim_after_learn       3
% 2.11/0.99  --inst_sel_renew                        solver
% 2.11/0.99  --inst_lit_activity_flag                true
% 2.11/0.99  --inst_restr_to_given                   false
% 2.11/0.99  --inst_activity_threshold               500
% 2.11/0.99  --inst_out_proof                        true
% 2.11/0.99  
% 2.11/0.99  ------ Resolution Options
% 2.11/0.99  
% 2.11/0.99  --resolution_flag                       true
% 2.11/0.99  --res_lit_sel                           adaptive
% 2.11/0.99  --res_lit_sel_side                      none
% 2.11/0.99  --res_ordering                          kbo
% 2.11/0.99  --res_to_prop_solver                    active
% 2.11/0.99  --res_prop_simpl_new                    false
% 2.11/0.99  --res_prop_simpl_given                  true
% 2.11/0.99  --res_passive_queue_type                priority_queues
% 2.11/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.11/0.99  --res_passive_queues_freq               [15;5]
% 2.11/0.99  --res_forward_subs                      full
% 2.11/0.99  --res_backward_subs                     full
% 2.11/0.99  --res_forward_subs_resolution           true
% 2.11/0.99  --res_backward_subs_resolution          true
% 2.11/0.99  --res_orphan_elimination                true
% 2.11/0.99  --res_time_limit                        2.
% 2.11/0.99  --res_out_proof                         true
% 2.11/0.99  
% 2.11/0.99  ------ Superposition Options
% 2.11/0.99  
% 2.11/0.99  --superposition_flag                    true
% 2.11/0.99  --sup_passive_queue_type                priority_queues
% 2.11/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.11/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.11/0.99  --demod_completeness_check              fast
% 2.11/0.99  --demod_use_ground                      true
% 2.11/0.99  --sup_to_prop_solver                    passive
% 2.11/0.99  --sup_prop_simpl_new                    true
% 2.11/0.99  --sup_prop_simpl_given                  true
% 2.11/0.99  --sup_fun_splitting                     false
% 2.11/0.99  --sup_smt_interval                      50000
% 2.11/0.99  
% 2.11/0.99  ------ Superposition Simplification Setup
% 2.11/0.99  
% 2.11/0.99  --sup_indices_passive                   []
% 2.11/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.11/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/0.99  --sup_full_bw                           [BwDemod]
% 2.11/0.99  --sup_immed_triv                        [TrivRules]
% 2.11/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.11/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/0.99  --sup_immed_bw_main                     []
% 2.11/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.11/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/0.99  
% 2.11/0.99  ------ Combination Options
% 2.11/0.99  
% 2.11/0.99  --comb_res_mult                         3
% 2.11/0.99  --comb_sup_mult                         2
% 2.11/0.99  --comb_inst_mult                        10
% 2.11/0.99  
% 2.11/0.99  ------ Debug Options
% 2.11/0.99  
% 2.11/0.99  --dbg_backtrace                         false
% 2.11/0.99  --dbg_dump_prop_clauses                 false
% 2.11/0.99  --dbg_dump_prop_clauses_file            -
% 2.11/0.99  --dbg_out_stat                          false
% 2.11/0.99  ------ Parsing...
% 2.11/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.11/0.99  
% 2.11/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.11/0.99  
% 2.11/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.11/0.99  
% 2.11/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.11/0.99  ------ Proving...
% 2.11/0.99  ------ Problem Properties 
% 2.11/0.99  
% 2.11/0.99  
% 2.11/0.99  clauses                                 30
% 2.11/0.99  conjectures                             2
% 2.11/0.99  EPR                                     10
% 2.11/0.99  Horn                                    22
% 2.11/0.99  unary                                   9
% 2.11/0.99  binary                                  8
% 2.11/0.99  lits                                    74
% 2.11/0.99  lits eq                                 15
% 2.11/0.99  fd_pure                                 0
% 2.11/0.99  fd_pseudo                               0
% 2.11/0.99  fd_cond                                 4
% 2.11/0.99  fd_pseudo_cond                          5
% 2.11/0.99  AC symbols                              0
% 2.11/0.99  
% 2.11/0.99  ------ Schedule dynamic 5 is on 
% 2.11/0.99  
% 2.11/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.11/0.99  
% 2.11/0.99  
% 2.11/0.99  ------ 
% 2.11/0.99  Current options:
% 2.11/0.99  ------ 
% 2.11/0.99  
% 2.11/0.99  ------ Input Options
% 2.11/0.99  
% 2.11/0.99  --out_options                           all
% 2.11/0.99  --tptp_safe_out                         true
% 2.11/0.99  --problem_path                          ""
% 2.11/0.99  --include_path                          ""
% 2.11/0.99  --clausifier                            res/vclausify_rel
% 2.11/0.99  --clausifier_options                    --mode clausify
% 2.11/0.99  --stdin                                 false
% 2.11/0.99  --stats_out                             all
% 2.11/0.99  
% 2.11/0.99  ------ General Options
% 2.11/0.99  
% 2.11/0.99  --fof                                   false
% 2.11/0.99  --time_out_real                         305.
% 2.11/0.99  --time_out_virtual                      -1.
% 2.11/0.99  --symbol_type_check                     false
% 2.11/0.99  --clausify_out                          false
% 2.11/0.99  --sig_cnt_out                           false
% 2.11/0.99  --trig_cnt_out                          false
% 2.11/0.99  --trig_cnt_out_tolerance                1.
% 2.11/0.99  --trig_cnt_out_sk_spl                   false
% 2.11/0.99  --abstr_cl_out                          false
% 2.11/0.99  
% 2.11/0.99  ------ Global Options
% 2.11/0.99  
% 2.11/0.99  --schedule                              default
% 2.11/0.99  --add_important_lit                     false
% 2.11/0.99  --prop_solver_per_cl                    1000
% 2.11/0.99  --min_unsat_core                        false
% 2.11/0.99  --soft_assumptions                      false
% 2.11/0.99  --soft_lemma_size                       3
% 2.11/0.99  --prop_impl_unit_size                   0
% 2.11/0.99  --prop_impl_unit                        []
% 2.11/0.99  --share_sel_clauses                     true
% 2.11/0.99  --reset_solvers                         false
% 2.11/0.99  --bc_imp_inh                            [conj_cone]
% 2.11/0.99  --conj_cone_tolerance                   3.
% 2.11/0.99  --extra_neg_conj                        none
% 2.11/0.99  --large_theory_mode                     true
% 2.11/0.99  --prolific_symb_bound                   200
% 2.11/0.99  --lt_threshold                          2000
% 2.11/0.99  --clause_weak_htbl                      true
% 2.11/0.99  --gc_record_bc_elim                     false
% 2.11/0.99  
% 2.11/0.99  ------ Preprocessing Options
% 2.11/0.99  
% 2.11/0.99  --preprocessing_flag                    true
% 2.11/0.99  --time_out_prep_mult                    0.1
% 2.11/0.99  --splitting_mode                        input
% 2.11/0.99  --splitting_grd                         true
% 2.11/0.99  --splitting_cvd                         false
% 2.11/0.99  --splitting_cvd_svl                     false
% 2.11/0.99  --splitting_nvd                         32
% 2.11/0.99  --sub_typing                            true
% 2.11/0.99  --prep_gs_sim                           true
% 2.11/0.99  --prep_unflatten                        true
% 2.11/0.99  --prep_res_sim                          true
% 2.11/0.99  --prep_upred                            true
% 2.11/0.99  --prep_sem_filter                       exhaustive
% 2.11/0.99  --prep_sem_filter_out                   false
% 2.11/0.99  --pred_elim                             true
% 2.11/0.99  --res_sim_input                         true
% 2.11/0.99  --eq_ax_congr_red                       true
% 2.11/0.99  --pure_diseq_elim                       true
% 2.11/0.99  --brand_transform                       false
% 2.11/0.99  --non_eq_to_eq                          false
% 2.11/0.99  --prep_def_merge                        true
% 2.11/0.99  --prep_def_merge_prop_impl              false
% 2.11/0.99  --prep_def_merge_mbd                    true
% 2.11/0.99  --prep_def_merge_tr_red                 false
% 2.11/0.99  --prep_def_merge_tr_cl                  false
% 2.11/0.99  --smt_preprocessing                     true
% 2.11/0.99  --smt_ac_axioms                         fast
% 2.11/0.99  --preprocessed_out                      false
% 2.11/0.99  --preprocessed_stats                    false
% 2.11/0.99  
% 2.11/0.99  ------ Abstraction refinement Options
% 2.11/0.99  
% 2.11/0.99  --abstr_ref                             []
% 2.11/0.99  --abstr_ref_prep                        false
% 2.11/0.99  --abstr_ref_until_sat                   false
% 2.11/0.99  --abstr_ref_sig_restrict                funpre
% 2.11/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.11/0.99  --abstr_ref_under                       []
% 2.11/0.99  
% 2.11/0.99  ------ SAT Options
% 2.11/0.99  
% 2.11/0.99  --sat_mode                              false
% 2.11/0.99  --sat_fm_restart_options                ""
% 2.11/0.99  --sat_gr_def                            false
% 2.11/0.99  --sat_epr_types                         true
% 2.11/0.99  --sat_non_cyclic_types                  false
% 2.11/0.99  --sat_finite_models                     false
% 2.11/0.99  --sat_fm_lemmas                         false
% 2.11/0.99  --sat_fm_prep                           false
% 2.11/0.99  --sat_fm_uc_incr                        true
% 2.11/0.99  --sat_out_model                         small
% 2.11/0.99  --sat_out_clauses                       false
% 2.11/0.99  
% 2.11/0.99  ------ QBF Options
% 2.11/0.99  
% 2.11/0.99  --qbf_mode                              false
% 2.11/0.99  --qbf_elim_univ                         false
% 2.11/0.99  --qbf_dom_inst                          none
% 2.11/0.99  --qbf_dom_pre_inst                      false
% 2.11/0.99  --qbf_sk_in                             false
% 2.11/0.99  --qbf_pred_elim                         true
% 2.11/0.99  --qbf_split                             512
% 2.11/0.99  
% 2.11/0.99  ------ BMC1 Options
% 2.11/0.99  
% 2.11/0.99  --bmc1_incremental                      false
% 2.11/0.99  --bmc1_axioms                           reachable_all
% 2.11/0.99  --bmc1_min_bound                        0
% 2.11/0.99  --bmc1_max_bound                        -1
% 2.11/0.99  --bmc1_max_bound_default                -1
% 2.11/0.99  --bmc1_symbol_reachability              true
% 2.11/0.99  --bmc1_property_lemmas                  false
% 2.11/0.99  --bmc1_k_induction                      false
% 2.11/0.99  --bmc1_non_equiv_states                 false
% 2.11/0.99  --bmc1_deadlock                         false
% 2.11/0.99  --bmc1_ucm                              false
% 2.11/0.99  --bmc1_add_unsat_core                   none
% 2.11/0.99  --bmc1_unsat_core_children              false
% 2.11/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.11/0.99  --bmc1_out_stat                         full
% 2.11/0.99  --bmc1_ground_init                      false
% 2.11/0.99  --bmc1_pre_inst_next_state              false
% 2.11/0.99  --bmc1_pre_inst_state                   false
% 2.11/0.99  --bmc1_pre_inst_reach_state             false
% 2.11/0.99  --bmc1_out_unsat_core                   false
% 2.11/0.99  --bmc1_aig_witness_out                  false
% 2.11/0.99  --bmc1_verbose                          false
% 2.11/0.99  --bmc1_dump_clauses_tptp                false
% 2.11/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.11/0.99  --bmc1_dump_file                        -
% 2.11/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.11/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.11/0.99  --bmc1_ucm_extend_mode                  1
% 2.11/0.99  --bmc1_ucm_init_mode                    2
% 2.11/0.99  --bmc1_ucm_cone_mode                    none
% 2.11/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.11/0.99  --bmc1_ucm_relax_model                  4
% 2.11/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.11/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.11/0.99  --bmc1_ucm_layered_model                none
% 2.11/0.99  --bmc1_ucm_max_lemma_size               10
% 2.11/0.99  
% 2.11/0.99  ------ AIG Options
% 2.11/0.99  
% 2.11/0.99  --aig_mode                              false
% 2.11/0.99  
% 2.11/0.99  ------ Instantiation Options
% 2.11/0.99  
% 2.11/0.99  --instantiation_flag                    true
% 2.11/0.99  --inst_sos_flag                         false
% 2.11/0.99  --inst_sos_phase                        true
% 2.11/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.11/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.11/0.99  --inst_lit_sel_side                     none
% 2.11/0.99  --inst_solver_per_active                1400
% 2.11/0.99  --inst_solver_calls_frac                1.
% 2.11/0.99  --inst_passive_queue_type               priority_queues
% 2.11/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.11/0.99  --inst_passive_queues_freq              [25;2]
% 2.11/0.99  --inst_dismatching                      true
% 2.11/0.99  --inst_eager_unprocessed_to_passive     true
% 2.11/0.99  --inst_prop_sim_given                   true
% 2.11/0.99  --inst_prop_sim_new                     false
% 2.11/0.99  --inst_subs_new                         false
% 2.11/0.99  --inst_eq_res_simp                      false
% 2.11/0.99  --inst_subs_given                       false
% 2.11/0.99  --inst_orphan_elimination               true
% 2.11/0.99  --inst_learning_loop_flag               true
% 2.11/0.99  --inst_learning_start                   3000
% 2.11/0.99  --inst_learning_factor                  2
% 2.11/0.99  --inst_start_prop_sim_after_learn       3
% 2.11/0.99  --inst_sel_renew                        solver
% 2.11/0.99  --inst_lit_activity_flag                true
% 2.11/0.99  --inst_restr_to_given                   false
% 2.11/0.99  --inst_activity_threshold               500
% 2.11/0.99  --inst_out_proof                        true
% 2.11/0.99  
% 2.11/0.99  ------ Resolution Options
% 2.11/0.99  
% 2.11/0.99  --resolution_flag                       false
% 2.11/0.99  --res_lit_sel                           adaptive
% 2.11/0.99  --res_lit_sel_side                      none
% 2.11/0.99  --res_ordering                          kbo
% 2.11/0.99  --res_to_prop_solver                    active
% 2.11/0.99  --res_prop_simpl_new                    false
% 2.11/0.99  --res_prop_simpl_given                  true
% 2.11/0.99  --res_passive_queue_type                priority_queues
% 2.11/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.11/0.99  --res_passive_queues_freq               [15;5]
% 2.11/0.99  --res_forward_subs                      full
% 2.11/0.99  --res_backward_subs                     full
% 2.11/0.99  --res_forward_subs_resolution           true
% 2.11/0.99  --res_backward_subs_resolution          true
% 2.11/0.99  --res_orphan_elimination                true
% 2.11/0.99  --res_time_limit                        2.
% 2.11/0.99  --res_out_proof                         true
% 2.11/0.99  
% 2.11/0.99  ------ Superposition Options
% 2.11/0.99  
% 2.11/0.99  --superposition_flag                    true
% 2.11/0.99  --sup_passive_queue_type                priority_queues
% 2.11/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.11/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.11/0.99  --demod_completeness_check              fast
% 2.11/0.99  --demod_use_ground                      true
% 2.11/0.99  --sup_to_prop_solver                    passive
% 2.11/0.99  --sup_prop_simpl_new                    true
% 2.11/0.99  --sup_prop_simpl_given                  true
% 2.11/0.99  --sup_fun_splitting                     false
% 2.11/0.99  --sup_smt_interval                      50000
% 2.11/0.99  
% 2.11/0.99  ------ Superposition Simplification Setup
% 2.11/0.99  
% 2.11/0.99  --sup_indices_passive                   []
% 2.11/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.11/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.11/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/0.99  --sup_full_bw                           [BwDemod]
% 2.11/0.99  --sup_immed_triv                        [TrivRules]
% 2.11/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.11/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/0.99  --sup_immed_bw_main                     []
% 2.11/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.11/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.11/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.11/0.99  
% 2.11/0.99  ------ Combination Options
% 2.11/0.99  
% 2.11/0.99  --comb_res_mult                         3
% 2.11/0.99  --comb_sup_mult                         2
% 2.11/0.99  --comb_inst_mult                        10
% 2.11/0.99  
% 2.11/0.99  ------ Debug Options
% 2.11/0.99  
% 2.11/0.99  --dbg_backtrace                         false
% 2.11/0.99  --dbg_dump_prop_clauses                 false
% 2.11/0.99  --dbg_dump_prop_clauses_file            -
% 2.11/0.99  --dbg_out_stat                          false
% 2.11/0.99  
% 2.11/0.99  
% 2.11/0.99  
% 2.11/0.99  
% 2.11/0.99  ------ Proving...
% 2.11/0.99  
% 2.11/0.99  
% 2.11/0.99  % SZS status Theorem for theBenchmark.p
% 2.11/0.99  
% 2.11/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.11/0.99  
% 2.11/0.99  fof(f19,conjecture,(
% 2.11/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.99  
% 2.11/0.99  fof(f20,negated_conjecture,(
% 2.11/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.11/0.99    inference(negated_conjecture,[],[f19])).
% 2.11/0.99  
% 2.11/0.99  fof(f39,plain,(
% 2.11/0.99    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.11/0.99    inference(ennf_transformation,[],[f20])).
% 2.11/0.99  
% 2.11/0.99  fof(f40,plain,(
% 2.11/0.99    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.11/0.99    inference(flattening,[],[f39])).
% 2.11/0.99  
% 2.11/0.99  fof(f56,plain,(
% 2.11/0.99    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.11/0.99    inference(nnf_transformation,[],[f40])).
% 2.11/0.99  
% 2.11/0.99  fof(f57,plain,(
% 2.11/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.11/0.99    inference(flattening,[],[f56])).
% 2.11/0.99  
% 2.11/0.99  fof(f59,plain,(
% 2.11/0.99    ( ! [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK5) | ~v3_tex_2(sK5,X0)) & (v1_zfmisc_1(sK5) | v3_tex_2(sK5,X0)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK5))) )),
% 2.11/0.99    introduced(choice_axiom,[])).
% 2.11/0.99  
% 2.11/0.99  fof(f58,plain,(
% 2.11/0.99    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK4)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK4)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK4) & v2_tdlat_3(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 2.11/0.99    introduced(choice_axiom,[])).
% 2.11/0.99  
% 2.11/0.99  fof(f60,plain,(
% 2.11/0.99    ((~v1_zfmisc_1(sK5) | ~v3_tex_2(sK5,sK4)) & (v1_zfmisc_1(sK5) | v3_tex_2(sK5,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & ~v1_xboole_0(sK5)) & l1_pre_topc(sK4) & v2_tdlat_3(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 2.11/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f57,f59,f58])).
% 2.11/0.99  
% 2.11/0.99  fof(f95,plain,(
% 2.11/0.99    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 2.11/0.99    inference(cnf_transformation,[],[f60])).
% 2.11/0.99  
% 2.11/0.99  fof(f16,axiom,(
% 2.11/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 2.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.99  
% 2.11/0.99  fof(f33,plain,(
% 2.11/0.99    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.11/0.99    inference(ennf_transformation,[],[f16])).
% 2.11/0.99  
% 2.11/0.99  fof(f34,plain,(
% 2.11/0.99    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.11/0.99    inference(flattening,[],[f33])).
% 2.11/0.99  
% 2.11/0.99  fof(f50,plain,(
% 2.11/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.11/0.99    inference(nnf_transformation,[],[f34])).
% 2.11/0.99  
% 2.11/0.99  fof(f51,plain,(
% 2.11/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.11/0.99    inference(flattening,[],[f50])).
% 2.11/0.99  
% 2.11/0.99  fof(f52,plain,(
% 2.11/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.11/0.99    inference(rectify,[],[f51])).
% 2.11/0.99  
% 2.11/0.99  fof(f53,plain,(
% 2.11/0.99    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK3(X0,X1) != X1 & r1_tarski(X1,sK3(X0,X1)) & v2_tex_2(sK3(X0,X1),X0) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.11/0.99    introduced(choice_axiom,[])).
% 2.11/0.99  
% 2.11/0.99  fof(f54,plain,(
% 2.11/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK3(X0,X1) != X1 & r1_tarski(X1,sK3(X0,X1)) & v2_tex_2(sK3(X0,X1),X0) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.11/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f52,f53])).
% 2.11/0.99  
% 2.11/0.99  fof(f85,plain,(
% 2.11/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK3(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.11/0.99    inference(cnf_transformation,[],[f54])).
% 2.11/0.99  
% 2.11/0.99  fof(f93,plain,(
% 2.11/0.99    l1_pre_topc(sK4)),
% 2.11/0.99    inference(cnf_transformation,[],[f60])).
% 2.11/0.99  
% 2.11/0.99  fof(f18,axiom,(
% 2.11/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 2.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.99  
% 2.11/0.99  fof(f37,plain,(
% 2.11/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.11/0.99    inference(ennf_transformation,[],[f18])).
% 2.11/0.99  
% 2.11/0.99  fof(f38,plain,(
% 2.11/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.11/0.99    inference(flattening,[],[f37])).
% 2.11/0.99  
% 2.11/0.99  fof(f55,plain,(
% 2.11/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.11/0.99    inference(nnf_transformation,[],[f38])).
% 2.11/0.99  
% 2.11/0.99  fof(f89,plain,(
% 2.11/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.11/0.99    inference(cnf_transformation,[],[f55])).
% 2.11/0.99  
% 2.11/0.99  fof(f90,plain,(
% 2.11/0.99    ~v2_struct_0(sK4)),
% 2.11/0.99    inference(cnf_transformation,[],[f60])).
% 2.11/0.99  
% 2.11/0.99  fof(f91,plain,(
% 2.11/0.99    v2_pre_topc(sK4)),
% 2.11/0.99    inference(cnf_transformation,[],[f60])).
% 2.11/0.99  
% 2.11/0.99  fof(f92,plain,(
% 2.11/0.99    v2_tdlat_3(sK4)),
% 2.11/0.99    inference(cnf_transformation,[],[f60])).
% 2.11/0.99  
% 2.11/0.99  fof(f96,plain,(
% 2.11/0.99    v1_zfmisc_1(sK5) | v3_tex_2(sK5,sK4)),
% 2.11/0.99    inference(cnf_transformation,[],[f60])).
% 2.11/0.99  
% 2.11/0.99  fof(f94,plain,(
% 2.11/0.99    ~v1_xboole_0(sK5)),
% 2.11/0.99    inference(cnf_transformation,[],[f60])).
% 2.11/0.99  
% 2.11/0.99  fof(f81,plain,(
% 2.11/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.11/0.99    inference(cnf_transformation,[],[f54])).
% 2.11/0.99  
% 2.11/0.99  fof(f88,plain,(
% 2.11/0.99    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.11/0.99    inference(cnf_transformation,[],[f55])).
% 2.11/0.99  
% 2.11/0.99  fof(f10,axiom,(
% 2.11/0.99    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 2.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.99  
% 2.11/0.99  fof(f29,plain,(
% 2.11/0.99    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 2.11/0.99    inference(ennf_transformation,[],[f10])).
% 2.11/0.99  
% 2.11/0.99  fof(f73,plain,(
% 2.11/0.99    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 2.11/0.99    inference(cnf_transformation,[],[f29])).
% 2.11/0.99  
% 2.11/0.99  fof(f97,plain,(
% 2.11/0.99    ~v1_zfmisc_1(sK5) | ~v3_tex_2(sK5,sK4)),
% 2.11/0.99    inference(cnf_transformation,[],[f60])).
% 2.11/0.99  
% 2.11/0.99  fof(f83,plain,(
% 2.11/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.11/0.99    inference(cnf_transformation,[],[f54])).
% 2.11/0.99  
% 2.11/0.99  fof(f17,axiom,(
% 2.11/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 2.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.99  
% 2.11/0.99  fof(f35,plain,(
% 2.11/0.99    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 2.11/0.99    inference(ennf_transformation,[],[f17])).
% 2.11/0.99  
% 2.11/0.99  fof(f36,plain,(
% 2.11/0.99    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.11/0.99    inference(flattening,[],[f35])).
% 2.11/0.99  
% 2.11/0.99  fof(f87,plain,(
% 2.11/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.11/0.99    inference(cnf_transformation,[],[f36])).
% 2.11/0.99  
% 2.11/0.99  fof(f84,plain,(
% 2.11/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | v2_tex_2(sK3(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.11/0.99    inference(cnf_transformation,[],[f54])).
% 2.11/0.99  
% 2.11/0.99  fof(f1,axiom,(
% 2.11/0.99    v1_xboole_0(k1_xboole_0)),
% 2.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.99  
% 2.11/0.99  fof(f61,plain,(
% 2.11/0.99    v1_xboole_0(k1_xboole_0)),
% 2.11/0.99    inference(cnf_transformation,[],[f1])).
% 2.11/0.99  
% 2.11/0.99  fof(f5,axiom,(
% 2.11/0.99    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.99  
% 2.11/0.99  fof(f23,plain,(
% 2.11/0.99    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.11/0.99    inference(ennf_transformation,[],[f5])).
% 2.11/0.99  
% 2.11/0.99  fof(f65,plain,(
% 2.11/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.11/0.99    inference(cnf_transformation,[],[f23])).
% 2.11/0.99  
% 2.11/0.99  fof(f8,axiom,(
% 2.11/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.11/0.99  
% 2.11/0.99  fof(f28,plain,(
% 2.11/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.11/0.99    inference(ennf_transformation,[],[f8])).
% 2.11/0.99  
% 2.11/0.99  fof(f68,plain,(
% 2.11/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.11/0.99    inference(cnf_transformation,[],[f28])).
% 2.11/0.99  
% 2.11/0.99  fof(f86,plain,(
% 2.11/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK3(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.11/0.99    inference(cnf_transformation,[],[f54])).
% 2.11/0.99  
% 2.11/0.99  cnf(c_31,negated_conjecture,
% 2.11/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.11/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_2414,plain,
% 2.11/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.11/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_21,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,X1)
% 2.11/0.99      | v3_tex_2(X0,X1)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/0.99      | r1_tarski(X0,sK3(X1,X0))
% 2.11/0.99      | ~ l1_pre_topc(X1) ),
% 2.11/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_33,negated_conjecture,
% 2.11/0.99      ( l1_pre_topc(sK4) ),
% 2.11/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_672,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,X1)
% 2.11/0.99      | v3_tex_2(X0,X1)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/0.99      | r1_tarski(X0,sK3(X1,X0))
% 2.11/0.99      | sK4 != X1 ),
% 2.11/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_33]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_673,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,sK4)
% 2.11/0.99      | v3_tex_2(X0,sK4)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.11/0.99      | r1_tarski(X0,sK3(sK4,X0)) ),
% 2.11/0.99      inference(unflattening,[status(thm)],[c_672]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_2408,plain,
% 2.11/0.99      ( v2_tex_2(X0,sK4) != iProver_top
% 2.11/0.99      | v3_tex_2(X0,sK4) = iProver_top
% 2.11/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.11/0.99      | r1_tarski(X0,sK3(sK4,X0)) = iProver_top ),
% 2.11/0.99      inference(predicate_to_equality,[status(thm)],[c_673]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_2730,plain,
% 2.11/0.99      ( v2_tex_2(sK5,sK4) != iProver_top
% 2.11/0.99      | v3_tex_2(sK5,sK4) = iProver_top
% 2.11/0.99      | r1_tarski(sK5,sK3(sK4,sK5)) = iProver_top ),
% 2.11/0.99      inference(superposition,[status(thm)],[c_2414,c_2408]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_42,plain,
% 2.11/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.11/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_27,plain,
% 2.11/0.99      ( v2_tex_2(X0,X1)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/0.99      | v2_struct_0(X1)
% 2.11/0.99      | ~ l1_pre_topc(X1)
% 2.11/0.99      | ~ v2_tdlat_3(X1)
% 2.11/0.99      | ~ v2_pre_topc(X1)
% 2.11/0.99      | ~ v1_zfmisc_1(X0)
% 2.11/0.99      | v1_xboole_0(X0) ),
% 2.11/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_36,negated_conjecture,
% 2.11/0.99      ( ~ v2_struct_0(sK4) ),
% 2.11/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_498,plain,
% 2.11/0.99      ( v2_tex_2(X0,X1)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/0.99      | ~ l1_pre_topc(X1)
% 2.11/0.99      | ~ v2_tdlat_3(X1)
% 2.11/0.99      | ~ v2_pre_topc(X1)
% 2.11/0.99      | ~ v1_zfmisc_1(X0)
% 2.11/0.99      | v1_xboole_0(X0)
% 2.11/0.99      | sK4 != X1 ),
% 2.11/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_36]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_499,plain,
% 2.11/0.99      ( v2_tex_2(X0,sK4)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.11/0.99      | ~ l1_pre_topc(sK4)
% 2.11/0.99      | ~ v2_tdlat_3(sK4)
% 2.11/0.99      | ~ v2_pre_topc(sK4)
% 2.11/0.99      | ~ v1_zfmisc_1(X0)
% 2.11/0.99      | v1_xboole_0(X0) ),
% 2.11/0.99      inference(unflattening,[status(thm)],[c_498]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_35,negated_conjecture,
% 2.11/0.99      ( v2_pre_topc(sK4) ),
% 2.11/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_34,negated_conjecture,
% 2.11/0.99      ( v2_tdlat_3(sK4) ),
% 2.11/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_501,plain,
% 2.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.11/0.99      | v2_tex_2(X0,sK4)
% 2.11/0.99      | ~ v1_zfmisc_1(X0)
% 2.11/0.99      | v1_xboole_0(X0) ),
% 2.11/0.99      inference(global_propositional_subsumption,
% 2.11/0.99                [status(thm)],
% 2.11/0.99                [c_499,c_35,c_34,c_33]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_502,plain,
% 2.11/0.99      ( v2_tex_2(X0,sK4)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.11/0.99      | ~ v1_zfmisc_1(X0)
% 2.11/0.99      | v1_xboole_0(X0) ),
% 2.11/0.99      inference(renaming,[status(thm)],[c_501]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_30,negated_conjecture,
% 2.11/0.99      ( v3_tex_2(sK5,sK4) | v1_zfmisc_1(sK5) ),
% 2.11/0.99      inference(cnf_transformation,[],[f96]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_285,plain,
% 2.11/0.99      ( v1_zfmisc_1(sK5) | v3_tex_2(sK5,sK4) ),
% 2.11/0.99      inference(prop_impl,[status(thm)],[c_30]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_286,plain,
% 2.11/0.99      ( v3_tex_2(sK5,sK4) | v1_zfmisc_1(sK5) ),
% 2.11/0.99      inference(renaming,[status(thm)],[c_285]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_802,plain,
% 2.11/0.99      ( v2_tex_2(X0,sK4)
% 2.11/0.99      | v3_tex_2(sK5,sK4)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.11/0.99      | v1_xboole_0(X0)
% 2.11/0.99      | sK5 != X0 ),
% 2.11/0.99      inference(resolution_lifted,[status(thm)],[c_502,c_286]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_803,plain,
% 2.11/0.99      ( v2_tex_2(sK5,sK4)
% 2.11/0.99      | v3_tex_2(sK5,sK4)
% 2.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.11/0.99      | v1_xboole_0(sK5) ),
% 2.11/0.99      inference(unflattening,[status(thm)],[c_802]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_32,negated_conjecture,
% 2.11/0.99      ( ~ v1_xboole_0(sK5) ),
% 2.11/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_805,plain,
% 2.11/0.99      ( v2_tex_2(sK5,sK4) | v3_tex_2(sK5,sK4) ),
% 2.11/0.99      inference(global_propositional_subsumption,
% 2.11/0.99                [status(thm)],
% 2.11/0.99                [c_803,c_32,c_31]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_25,plain,
% 2.11/0.99      ( v2_tex_2(X0,X1)
% 2.11/0.99      | ~ v3_tex_2(X0,X1)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/0.99      | ~ l1_pre_topc(X1) ),
% 2.11/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_599,plain,
% 2.11/0.99      ( v2_tex_2(X0,X1)
% 2.11/0.99      | ~ v3_tex_2(X0,X1)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/0.99      | sK4 != X1 ),
% 2.11/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_600,plain,
% 2.11/0.99      ( v2_tex_2(X0,sK4)
% 2.11/0.99      | ~ v3_tex_2(X0,sK4)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.11/0.99      inference(unflattening,[status(thm)],[c_599]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_854,plain,
% 2.11/0.99      ( v2_tex_2(X0,sK4)
% 2.11/0.99      | v2_tex_2(sK5,sK4)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.11/0.99      | sK4 != sK4
% 2.11/0.99      | sK5 != X0 ),
% 2.11/0.99      inference(resolution_lifted,[status(thm)],[c_805,c_600]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_855,plain,
% 2.11/0.99      ( v2_tex_2(sK5,sK4)
% 2.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.11/0.99      inference(unflattening,[status(thm)],[c_854]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_856,plain,
% 2.11/0.99      ( v2_tex_2(sK5,sK4) = iProver_top
% 2.11/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.11/0.99      inference(predicate_to_equality,[status(thm)],[c_855]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_28,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,X1)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/0.99      | v2_struct_0(X1)
% 2.11/0.99      | ~ l1_pre_topc(X1)
% 2.11/0.99      | ~ v2_tdlat_3(X1)
% 2.11/0.99      | ~ v2_pre_topc(X1)
% 2.11/0.99      | v1_zfmisc_1(X0)
% 2.11/0.99      | v1_xboole_0(X0) ),
% 2.11/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_12,plain,
% 2.11/0.99      ( v1_zfmisc_1(X0) | ~ v1_xboole_0(X0) ),
% 2.11/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_201,plain,
% 2.11/0.99      ( v1_zfmisc_1(X0)
% 2.11/0.99      | ~ v2_pre_topc(X1)
% 2.11/0.99      | ~ v2_tdlat_3(X1)
% 2.11/0.99      | ~ l1_pre_topc(X1)
% 2.11/0.99      | v2_struct_0(X1)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/0.99      | ~ v2_tex_2(X0,X1) ),
% 2.11/0.99      inference(global_propositional_subsumption,
% 2.11/0.99                [status(thm)],
% 2.11/0.99                [c_28,c_12]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_202,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,X1)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/0.99      | v2_struct_0(X1)
% 2.11/0.99      | ~ l1_pre_topc(X1)
% 2.11/0.99      | ~ v2_tdlat_3(X1)
% 2.11/0.99      | ~ v2_pre_topc(X1)
% 2.11/0.99      | v1_zfmisc_1(X0) ),
% 2.11/0.99      inference(renaming,[status(thm)],[c_201]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_477,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,X1)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/0.99      | ~ l1_pre_topc(X1)
% 2.11/0.99      | ~ v2_tdlat_3(X1)
% 2.11/0.99      | ~ v2_pre_topc(X1)
% 2.11/0.99      | v1_zfmisc_1(X0)
% 2.11/0.99      | sK4 != X1 ),
% 2.11/0.99      inference(resolution_lifted,[status(thm)],[c_202,c_36]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_478,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,sK4)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.11/0.99      | ~ l1_pre_topc(sK4)
% 2.11/0.99      | ~ v2_tdlat_3(sK4)
% 2.11/0.99      | ~ v2_pre_topc(sK4)
% 2.11/0.99      | v1_zfmisc_1(X0) ),
% 2.11/0.99      inference(unflattening,[status(thm)],[c_477]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_482,plain,
% 2.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.11/0.99      | ~ v2_tex_2(X0,sK4)
% 2.11/0.99      | v1_zfmisc_1(X0) ),
% 2.11/0.99      inference(global_propositional_subsumption,
% 2.11/0.99                [status(thm)],
% 2.11/0.99                [c_478,c_35,c_34,c_33]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_483,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,sK4)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.11/0.99      | v1_zfmisc_1(X0) ),
% 2.11/0.99      inference(renaming,[status(thm)],[c_482]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_29,negated_conjecture,
% 2.11/0.99      ( ~ v3_tex_2(sK5,sK4) | ~ v1_zfmisc_1(sK5) ),
% 2.11/0.99      inference(cnf_transformation,[],[f97]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_283,plain,
% 2.11/0.99      ( ~ v1_zfmisc_1(sK5) | ~ v3_tex_2(sK5,sK4) ),
% 2.11/0.99      inference(prop_impl,[status(thm)],[c_29]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_284,plain,
% 2.11/0.99      ( ~ v3_tex_2(sK5,sK4) | ~ v1_zfmisc_1(sK5) ),
% 2.11/0.99      inference(renaming,[status(thm)],[c_283]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_786,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,sK4)
% 2.11/0.99      | ~ v3_tex_2(sK5,sK4)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.11/0.99      | sK5 != X0 ),
% 2.11/0.99      inference(resolution_lifted,[status(thm)],[c_483,c_284]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_787,plain,
% 2.11/0.99      ( ~ v2_tex_2(sK5,sK4)
% 2.11/0.99      | ~ v3_tex_2(sK5,sK4)
% 2.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.11/0.99      inference(unflattening,[status(thm)],[c_786]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_789,plain,
% 2.11/0.99      ( ~ v3_tex_2(sK5,sK4) | ~ v2_tex_2(sK5,sK4) ),
% 2.11/0.99      inference(global_propositional_subsumption,
% 2.11/0.99                [status(thm)],
% 2.11/0.99                [c_787,c_31]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_790,plain,
% 2.11/0.99      ( ~ v2_tex_2(sK5,sK4) | ~ v3_tex_2(sK5,sK4) ),
% 2.11/0.99      inference(renaming,[status(thm)],[c_789]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_877,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,sK4)
% 2.11/0.99      | ~ v2_tex_2(sK5,sK4)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.11/0.99      | r1_tarski(X0,sK3(sK4,X0))
% 2.11/0.99      | sK4 != sK4
% 2.11/0.99      | sK5 != X0 ),
% 2.11/0.99      inference(resolution_lifted,[status(thm)],[c_790,c_673]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_878,plain,
% 2.11/0.99      ( ~ v2_tex_2(sK5,sK4)
% 2.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.11/0.99      | r1_tarski(sK5,sK3(sK4,sK5)) ),
% 2.11/0.99      inference(unflattening,[status(thm)],[c_877]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_879,plain,
% 2.11/0.99      ( v2_tex_2(sK5,sK4) != iProver_top
% 2.11/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.11/0.99      | r1_tarski(sK5,sK3(sK4,sK5)) = iProver_top ),
% 2.11/0.99      inference(predicate_to_equality,[status(thm)],[c_878]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_2739,plain,
% 2.11/0.99      ( r1_tarski(sK5,sK3(sK4,sK5)) = iProver_top ),
% 2.11/0.99      inference(global_propositional_subsumption,
% 2.11/0.99                [status(thm)],
% 2.11/0.99                [c_2730,c_42,c_856,c_879]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_23,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,X1)
% 2.11/0.99      | v3_tex_2(X0,X1)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/0.99      | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/0.99      | ~ l1_pre_topc(X1) ),
% 2.11/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_636,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,X1)
% 2.11/0.99      | v3_tex_2(X0,X1)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/0.99      | m1_subset_1(sK3(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/0.99      | sK4 != X1 ),
% 2.11/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_637,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,sK4)
% 2.11/0.99      | v3_tex_2(X0,sK4)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.11/0.99      | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.11/0.99      inference(unflattening,[status(thm)],[c_636]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_2410,plain,
% 2.11/0.99      ( v2_tex_2(X0,sK4) != iProver_top
% 2.11/0.99      | v3_tex_2(X0,sK4) = iProver_top
% 2.11/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.11/0.99      | m1_subset_1(sK3(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.11/0.99      inference(predicate_to_equality,[status(thm)],[c_637]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_26,plain,
% 2.11/0.99      ( ~ r1_tarski(X0,X1)
% 2.11/0.99      | ~ v1_zfmisc_1(X1)
% 2.11/0.99      | v1_xboole_0(X1)
% 2.11/0.99      | v1_xboole_0(X0)
% 2.11/0.99      | X0 = X1 ),
% 2.11/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_742,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,sK4)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.11/0.99      | ~ r1_tarski(X1,X2)
% 2.11/0.99      | v1_xboole_0(X1)
% 2.11/0.99      | v1_xboole_0(X2)
% 2.11/0.99      | X0 != X2
% 2.11/0.99      | X2 = X1 ),
% 2.11/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_483]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_743,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,sK4)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.11/0.99      | ~ r1_tarski(X1,X0)
% 2.11/0.99      | v1_xboole_0(X1)
% 2.11/0.99      | v1_xboole_0(X0)
% 2.11/0.99      | X0 = X1 ),
% 2.11/0.99      inference(unflattening,[status(thm)],[c_742]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_2406,plain,
% 2.11/0.99      ( X0 = X1
% 2.11/0.99      | v2_tex_2(X0,sK4) != iProver_top
% 2.11/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.11/0.99      | r1_tarski(X1,X0) != iProver_top
% 2.11/0.99      | v1_xboole_0(X0) = iProver_top
% 2.11/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.11/0.99      inference(predicate_to_equality,[status(thm)],[c_743]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_3424,plain,
% 2.11/0.99      ( sK3(sK4,X0) = X1
% 2.11/0.99      | v2_tex_2(X0,sK4) != iProver_top
% 2.11/0.99      | v2_tex_2(sK3(sK4,X0),sK4) != iProver_top
% 2.11/0.99      | v3_tex_2(X0,sK4) = iProver_top
% 2.11/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.11/0.99      | r1_tarski(X1,sK3(sK4,X0)) != iProver_top
% 2.11/0.99      | v1_xboole_0(X1) = iProver_top
% 2.11/0.99      | v1_xboole_0(sK3(sK4,X0)) = iProver_top ),
% 2.11/0.99      inference(superposition,[status(thm)],[c_2410,c_2406]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_22,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,X1)
% 2.11/0.99      | v2_tex_2(sK3(X1,X0),X1)
% 2.11/0.99      | v3_tex_2(X0,X1)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/0.99      | ~ l1_pre_topc(X1) ),
% 2.11/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_654,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,X1)
% 2.11/0.99      | v2_tex_2(sK3(X1,X0),X1)
% 2.11/0.99      | v3_tex_2(X0,X1)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/0.99      | sK4 != X1 ),
% 2.11/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_655,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,sK4)
% 2.11/0.99      | v2_tex_2(sK3(sK4,X0),sK4)
% 2.11/0.99      | v3_tex_2(X0,sK4)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.11/0.99      inference(unflattening,[status(thm)],[c_654]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_656,plain,
% 2.11/0.99      ( v2_tex_2(X0,sK4) != iProver_top
% 2.11/0.99      | v2_tex_2(sK3(sK4,X0),sK4) = iProver_top
% 2.11/0.99      | v3_tex_2(X0,sK4) = iProver_top
% 2.11/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.11/0.99      inference(predicate_to_equality,[status(thm)],[c_655]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_3644,plain,
% 2.11/0.99      ( v2_tex_2(X0,sK4) != iProver_top
% 2.11/0.99      | sK3(sK4,X0) = X1
% 2.11/0.99      | v3_tex_2(X0,sK4) = iProver_top
% 2.11/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.11/0.99      | r1_tarski(X1,sK3(sK4,X0)) != iProver_top
% 2.11/0.99      | v1_xboole_0(X1) = iProver_top
% 2.11/0.99      | v1_xboole_0(sK3(sK4,X0)) = iProver_top ),
% 2.11/0.99      inference(global_propositional_subsumption,
% 2.11/0.99                [status(thm)],
% 2.11/0.99                [c_3424,c_656]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_3645,plain,
% 2.11/0.99      ( sK3(sK4,X0) = X1
% 2.11/0.99      | v2_tex_2(X0,sK4) != iProver_top
% 2.11/0.99      | v3_tex_2(X0,sK4) = iProver_top
% 2.11/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.11/0.99      | r1_tarski(X1,sK3(sK4,X0)) != iProver_top
% 2.11/0.99      | v1_xboole_0(X1) = iProver_top
% 2.11/0.99      | v1_xboole_0(sK3(sK4,X0)) = iProver_top ),
% 2.11/0.99      inference(renaming,[status(thm)],[c_3644]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_3655,plain,
% 2.11/0.99      ( sK3(sK4,sK5) = X0
% 2.11/0.99      | v2_tex_2(sK5,sK4) != iProver_top
% 2.11/0.99      | v3_tex_2(sK5,sK4) = iProver_top
% 2.11/0.99      | r1_tarski(X0,sK3(sK4,sK5)) != iProver_top
% 2.11/0.99      | v1_xboole_0(X0) = iProver_top
% 2.11/0.99      | v1_xboole_0(sK3(sK4,sK5)) = iProver_top ),
% 2.11/0.99      inference(superposition,[status(thm)],[c_2414,c_3645]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_0,plain,
% 2.11/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.11/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_121,plain,
% 2.11/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.11/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_791,plain,
% 2.11/0.99      ( v2_tex_2(sK5,sK4) != iProver_top
% 2.11/0.99      | v3_tex_2(sK5,sK4) != iProver_top ),
% 2.11/0.99      inference(predicate_to_equality,[status(thm)],[c_790]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_1727,plain,
% 2.11/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.11/0.99      theory(equality) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_2677,plain,
% 2.11/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK5) | sK5 != X0 ),
% 2.11/0.99      inference(instantiation,[status(thm)],[c_1727]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_2679,plain,
% 2.11/0.99      ( v1_xboole_0(sK5)
% 2.11/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 2.11/0.99      | sK5 != k1_xboole_0 ),
% 2.11/0.99      inference(instantiation,[status(thm)],[c_2677]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_4,plain,
% 2.11/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.11/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_2799,plain,
% 2.11/0.99      ( ~ r1_tarski(sK5,k1_xboole_0) | k1_xboole_0 = sK5 ),
% 2.11/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_1725,plain,( X0 = X0 ),theory(equality) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_2830,plain,
% 2.11/0.99      ( sK5 = sK5 ),
% 2.11/0.99      inference(instantiation,[status(thm)],[c_1725]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_1730,plain,
% 2.11/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,X2) | X2 != X1 ),
% 2.11/0.99      theory(equality) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_2846,plain,
% 2.11/0.99      ( r1_tarski(sK5,X0)
% 2.11/0.99      | ~ r1_tarski(sK5,sK3(sK4,sK5))
% 2.11/0.99      | X0 != sK3(sK4,sK5) ),
% 2.11/0.99      inference(instantiation,[status(thm)],[c_1730]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_2861,plain,
% 2.11/0.99      ( ~ r1_tarski(sK5,sK3(sK4,sK5))
% 2.11/0.99      | r1_tarski(sK5,k1_xboole_0)
% 2.11/0.99      | k1_xboole_0 != sK3(sK4,sK5) ),
% 2.11/0.99      inference(instantiation,[status(thm)],[c_2846]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_1726,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_2785,plain,
% 2.11/0.99      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 2.11/0.99      inference(instantiation,[status(thm)],[c_1726]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_3154,plain,
% 2.11/0.99      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 2.11/0.99      inference(instantiation,[status(thm)],[c_2785]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_3155,plain,
% 2.11/0.99      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 2.11/0.99      inference(instantiation,[status(thm)],[c_3154]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_7,plain,
% 2.11/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.11/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_3316,plain,
% 2.11/0.99      ( ~ v1_xboole_0(X0)
% 2.11/0.99      | ~ v1_xboole_0(sK3(sK4,sK5))
% 2.11/0.99      | X0 = sK3(sK4,sK5) ),
% 2.11/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_3322,plain,
% 2.11/0.99      ( X0 = sK3(sK4,sK5)
% 2.11/0.99      | v1_xboole_0(X0) != iProver_top
% 2.11/0.99      | v1_xboole_0(sK3(sK4,sK5)) != iProver_top ),
% 2.11/0.99      inference(predicate_to_equality,[status(thm)],[c_3316]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_3324,plain,
% 2.11/0.99      ( k1_xboole_0 = sK3(sK4,sK5)
% 2.11/0.99      | v1_xboole_0(sK3(sK4,sK5)) != iProver_top
% 2.11/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.11/0.99      inference(instantiation,[status(thm)],[c_3322]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_4031,plain,
% 2.11/0.99      ( v1_xboole_0(X0) = iProver_top
% 2.11/0.99      | r1_tarski(X0,sK3(sK4,sK5)) != iProver_top
% 2.11/0.99      | sK3(sK4,sK5) = X0 ),
% 2.11/0.99      inference(global_propositional_subsumption,
% 2.11/0.99                [status(thm)],
% 2.11/0.99                [c_3655,c_32,c_31,c_42,c_0,c_121,c_791,c_855,c_856,c_878,
% 2.11/0.99                 c_2679,c_2799,c_2830,c_2861,c_3155,c_3324]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_4032,plain,
% 2.11/0.99      ( sK3(sK4,sK5) = X0
% 2.11/0.99      | r1_tarski(X0,sK3(sK4,sK5)) != iProver_top
% 2.11/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.11/0.99      inference(renaming,[status(thm)],[c_4031]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_4038,plain,
% 2.11/0.99      ( sK3(sK4,sK5) = sK5 | v1_xboole_0(sK5) = iProver_top ),
% 2.11/0.99      inference(superposition,[status(thm)],[c_2739,c_4032]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_20,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,X1)
% 2.11/0.99      | v3_tex_2(X0,X1)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/0.99      | ~ l1_pre_topc(X1)
% 2.11/0.99      | sK3(X1,X0) != X0 ),
% 2.11/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_690,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,X1)
% 2.11/0.99      | v3_tex_2(X0,X1)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.11/0.99      | sK3(X1,X0) != X0
% 2.11/0.99      | sK4 != X1 ),
% 2.11/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_33]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_691,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,sK4)
% 2.11/0.99      | v3_tex_2(X0,sK4)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.11/0.99      | sK3(sK4,X0) != X0 ),
% 2.11/0.99      inference(unflattening,[status(thm)],[c_690]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_869,plain,
% 2.11/0.99      ( ~ v2_tex_2(X0,sK4)
% 2.11/0.99      | ~ v2_tex_2(sK5,sK4)
% 2.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.11/0.99      | sK3(sK4,X0) != X0
% 2.11/0.99      | sK4 != sK4
% 2.11/0.99      | sK5 != X0 ),
% 2.11/0.99      inference(resolution_lifted,[status(thm)],[c_790,c_691]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_870,plain,
% 2.11/0.99      ( ~ v2_tex_2(sK5,sK4)
% 2.11/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.11/0.99      | sK3(sK4,sK5) != sK5 ),
% 2.11/0.99      inference(unflattening,[status(thm)],[c_869]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(c_41,plain,
% 2.11/0.99      ( v1_xboole_0(sK5) != iProver_top ),
% 2.11/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.11/0.99  
% 2.11/0.99  cnf(contradiction,plain,
% 2.11/0.99      ( $false ),
% 2.11/0.99      inference(minisat,[status(thm)],[c_4038,c_870,c_855,c_31,c_41]) ).
% 2.11/0.99  
% 2.11/0.99  
% 2.11/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.11/0.99  
% 2.11/0.99  ------                               Statistics
% 2.11/0.99  
% 2.11/0.99  ------ General
% 2.11/0.99  
% 2.11/0.99  abstr_ref_over_cycles:                  0
% 2.11/0.99  abstr_ref_under_cycles:                 0
% 2.11/0.99  gc_basic_clause_elim:                   0
% 2.11/0.99  forced_gc_time:                         0
% 2.11/0.99  parsing_time:                           0.009
% 2.11/0.99  unif_index_cands_time:                  0.
% 2.11/0.99  unif_index_add_time:                    0.
% 2.11/0.99  orderings_time:                         0.
% 2.11/0.99  out_proof_time:                         0.01
% 2.11/0.99  total_time:                             0.127
% 2.11/0.99  num_of_symbols:                         54
% 2.11/0.99  num_of_terms:                           2269
% 2.11/0.99  
% 2.11/0.99  ------ Preprocessing
% 2.11/0.99  
% 2.11/0.99  num_of_splits:                          0
% 2.11/0.99  num_of_split_atoms:                     0
% 2.11/0.99  num_of_reused_defs:                     0
% 2.11/0.99  num_eq_ax_congr_red:                    26
% 2.11/0.99  num_of_sem_filtered_clauses:            1
% 2.11/0.99  num_of_subtypes:                        0
% 2.11/0.99  monotx_restored_types:                  0
% 2.11/0.99  sat_num_of_epr_types:                   0
% 2.11/0.99  sat_num_of_non_cyclic_types:            0
% 2.11/0.99  sat_guarded_non_collapsed_types:        0
% 2.11/0.99  num_pure_diseq_elim:                    0
% 2.11/0.99  simp_replaced_by:                       0
% 2.11/0.99  res_preprocessed:                       154
% 2.11/0.99  prep_upred:                             0
% 2.11/0.99  prep_unflattend:                        56
% 2.11/0.99  smt_new_axioms:                         0
% 2.11/0.99  pred_elim_cands:                        7
% 2.11/0.99  pred_elim:                              5
% 2.11/0.99  pred_elim_cl:                           7
% 2.11/0.99  pred_elim_cycles:                       10
% 2.11/0.99  merged_defs:                            10
% 2.11/0.99  merged_defs_ncl:                        0
% 2.11/0.99  bin_hyper_res:                          10
% 2.11/0.99  prep_cycles:                            4
% 2.11/0.99  pred_elim_time:                         0.017
% 2.11/0.99  splitting_time:                         0.
% 2.11/0.99  sem_filter_time:                        0.
% 2.11/0.99  monotx_time:                            0.002
% 2.11/0.99  subtype_inf_time:                       0.
% 2.11/0.99  
% 2.11/0.99  ------ Problem properties
% 2.11/0.99  
% 2.11/0.99  clauses:                                30
% 2.11/0.99  conjectures:                            2
% 2.11/0.99  epr:                                    10
% 2.11/0.99  horn:                                   22
% 2.11/0.99  ground:                                 5
% 2.11/0.99  unary:                                  9
% 2.11/0.99  binary:                                 8
% 2.11/0.99  lits:                                   74
% 2.11/0.99  lits_eq:                                15
% 2.11/0.99  fd_pure:                                0
% 2.11/0.99  fd_pseudo:                              0
% 2.11/0.99  fd_cond:                                4
% 2.11/0.99  fd_pseudo_cond:                         5
% 2.11/0.99  ac_symbols:                             0
% 2.11/0.99  
% 2.11/0.99  ------ Propositional Solver
% 2.11/0.99  
% 2.11/0.99  prop_solver_calls:                      24
% 2.11/0.99  prop_fast_solver_calls:                 1173
% 2.11/0.99  smt_solver_calls:                       0
% 2.11/0.99  smt_fast_solver_calls:                  0
% 2.11/0.99  prop_num_of_clauses:                    862
% 2.11/0.99  prop_preprocess_simplified:             5489
% 2.11/0.99  prop_fo_subsumed:                       49
% 2.11/0.99  prop_solver_time:                       0.
% 2.11/0.99  smt_solver_time:                        0.
% 2.11/0.99  smt_fast_solver_time:                   0.
% 2.11/0.99  prop_fast_solver_time:                  0.
% 2.11/0.99  prop_unsat_core_time:                   0.
% 2.11/0.99  
% 2.11/0.99  ------ QBF
% 2.11/0.99  
% 2.11/0.99  qbf_q_res:                              0
% 2.11/0.99  qbf_num_tautologies:                    0
% 2.11/0.99  qbf_prep_cycles:                        0
% 2.11/0.99  
% 2.11/0.99  ------ BMC1
% 2.11/0.99  
% 2.11/0.99  bmc1_current_bound:                     -1
% 2.11/0.99  bmc1_last_solved_bound:                 -1
% 2.11/0.99  bmc1_unsat_core_size:                   -1
% 2.11/0.99  bmc1_unsat_core_parents_size:           -1
% 2.11/0.99  bmc1_merge_next_fun:                    0
% 2.11/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.11/0.99  
% 2.11/0.99  ------ Instantiation
% 2.11/0.99  
% 2.11/0.99  inst_num_of_clauses:                    236
% 2.11/0.99  inst_num_in_passive:                    78
% 2.11/0.99  inst_num_in_active:                     113
% 2.11/0.99  inst_num_in_unprocessed:                45
% 2.11/0.99  inst_num_of_loops:                      130
% 2.11/0.99  inst_num_of_learning_restarts:          0
% 2.11/0.99  inst_num_moves_active_passive:          16
% 2.11/0.99  inst_lit_activity:                      0
% 2.11/0.99  inst_lit_activity_moves:                0
% 2.11/0.99  inst_num_tautologies:                   0
% 2.11/0.99  inst_num_prop_implied:                  0
% 2.11/0.99  inst_num_existing_simplified:           0
% 2.11/0.99  inst_num_eq_res_simplified:             0
% 2.11/0.99  inst_num_child_elim:                    0
% 2.11/0.99  inst_num_of_dismatching_blockings:      4
% 2.11/0.99  inst_num_of_non_proper_insts:           128
% 2.11/0.99  inst_num_of_duplicates:                 0
% 2.11/0.99  inst_inst_num_from_inst_to_res:         0
% 2.11/0.99  inst_dismatching_checking_time:         0.
% 2.11/0.99  
% 2.11/0.99  ------ Resolution
% 2.11/0.99  
% 2.11/0.99  res_num_of_clauses:                     0
% 2.11/0.99  res_num_in_passive:                     0
% 2.11/0.99  res_num_in_active:                      0
% 2.11/0.99  res_num_of_loops:                       158
% 2.11/0.99  res_forward_subset_subsumed:            45
% 2.11/0.99  res_backward_subset_subsumed:           1
% 2.11/0.99  res_forward_subsumed:                   1
% 2.11/0.99  res_backward_subsumed:                  1
% 2.11/0.99  res_forward_subsumption_resolution:     0
% 2.11/0.99  res_backward_subsumption_resolution:    2
% 2.11/0.99  res_clause_to_clause_subsumption:       192
% 2.11/0.99  res_orphan_elimination:                 0
% 2.11/0.99  res_tautology_del:                      43
% 2.11/0.99  res_num_eq_res_simplified:              0
% 2.11/0.99  res_num_sel_changes:                    0
% 2.11/0.99  res_moves_from_active_to_pass:          0
% 2.11/0.99  
% 2.11/0.99  ------ Superposition
% 2.11/0.99  
% 2.11/0.99  sup_time_total:                         0.
% 2.11/0.99  sup_time_generating:                    0.
% 2.11/0.99  sup_time_sim_full:                      0.
% 2.11/0.99  sup_time_sim_immed:                     0.
% 2.11/0.99  
% 2.11/0.99  sup_num_of_clauses:                     46
% 2.11/0.99  sup_num_in_active:                      26
% 2.11/0.99  sup_num_in_passive:                     20
% 2.11/0.99  sup_num_of_loops:                       25
% 2.11/0.99  sup_fw_superposition:                   10
% 2.11/0.99  sup_bw_superposition:                   10
% 2.11/0.99  sup_immediate_simplified:               3
% 2.11/0.99  sup_given_eliminated:                   0
% 2.11/0.99  comparisons_done:                       0
% 2.11/0.99  comparisons_avoided:                    0
% 2.11/0.99  
% 2.11/0.99  ------ Simplifications
% 2.11/0.99  
% 2.11/0.99  
% 2.11/0.99  sim_fw_subset_subsumed:                 2
% 2.11/0.99  sim_bw_subset_subsumed:                 0
% 2.11/0.99  sim_fw_subsumed:                        1
% 2.11/0.99  sim_bw_subsumed:                        0
% 2.11/0.99  sim_fw_subsumption_res:                 0
% 2.11/0.99  sim_bw_subsumption_res:                 0
% 2.11/0.99  sim_tautology_del:                      0
% 2.11/0.99  sim_eq_tautology_del:                   0
% 2.11/0.99  sim_eq_res_simp:                        0
% 2.11/0.99  sim_fw_demodulated:                     0
% 2.11/0.99  sim_bw_demodulated:                     0
% 2.11/0.99  sim_light_normalised:                   0
% 2.11/0.99  sim_joinable_taut:                      0
% 2.11/0.99  sim_joinable_simp:                      0
% 2.11/0.99  sim_ac_normalised:                      0
% 2.11/0.99  sim_smt_subsumption:                    0
% 2.11/0.99  
%------------------------------------------------------------------------------
