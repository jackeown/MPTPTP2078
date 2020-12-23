%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:11 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 964 expanded)
%              Number of clauses        :   91 ( 247 expanded)
%              Number of leaves         :   19 ( 218 expanded)
%              Depth                    :   20
%              Number of atoms          :  587 (6293 expanded)
%              Number of equality atoms :  155 ( 379 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( v1_subset_1(sK3,u1_struct_0(X0))
          | ~ v3_tex_2(sK3,X0) )
        & ( ~ v1_subset_1(sK3,u1_struct_0(X0))
          | v3_tex_2(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK2))
            | ~ v3_tex_2(X1,sK2) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK2))
            | v3_tex_2(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v1_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( v1_subset_1(sK3,u1_struct_0(sK2))
      | ~ v3_tex_2(sK3,sK2) )
    & ( ~ v1_subset_1(sK3,u1_struct_0(sK2))
      | v3_tex_2(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v1_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f40,f39])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,
    ( ~ v1_subset_1(sK3,u1_struct_0(sK2))
    | v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f70,plain,
    ( v1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK1(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK1(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1857,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_8,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1858,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1869,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1858,c_7])).

cnf(c_19,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_545,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | X2 = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_546,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_21,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_388,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_389,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v1_tdlat_3(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_26,negated_conjecture,
    ( v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_389,c_27,c_26,c_25])).

cnf(c_394,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_393])).

cnf(c_548,plain,
    ( ~ v3_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_546,c_27,c_26,c_25,c_389])).

cnf(c_549,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_548])).

cnf(c_1850,plain,
    ( X0 = X1
    | v3_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_549])).

cnf(c_2376,plain,
    ( u1_struct_0(sK2) = X0
    | v3_tex_2(u1_struct_0(sK2),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(u1_struct_0(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1869,c_1850])).

cnf(c_2459,plain,
    ( u1_struct_0(sK2) = sK3
    | v3_tex_2(u1_struct_0(sK2),sK2) != iProver_top
    | r1_tarski(u1_struct_0(sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1857,c_2376])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_13,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_23,negated_conjecture,
    ( v3_tex_2(sK3,sK2)
    | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_216,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_433,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 = X0
    | u1_struct_0(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_216])).

cnf(c_434,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK2) = sK3 ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_435,plain,
    ( u1_struct_0(sK2) = sK3
    | v3_tex_2(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_434])).

cnf(c_10,plain,
    ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_22,negated_conjecture,
    ( ~ v3_tex_2(sK3,sK2)
    | v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_218,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_421,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | u1_struct_0(sK2) != X0
    | k2_subset_1(X0) != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_218])).

cnf(c_422,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | k2_subset_1(u1_struct_0(sK2)) != sK3 ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_1856,plain,
    ( k2_subset_1(u1_struct_0(sK2)) != sK3
    | v3_tex_2(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_1880,plain,
    ( u1_struct_0(sK2) != sK3
    | v3_tex_2(sK3,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1856,c_7])).

cnf(c_9,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_zfmisc_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_11])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_939,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_940,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_939])).

cnf(c_975,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_374,c_940])).

cnf(c_2122,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_975])).

cnf(c_2123,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2122])).

cnf(c_2021,plain,
    ( sK3 = X0
    | v3_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1857,c_1850])).

cnf(c_2375,plain,
    ( u1_struct_0(sK2) = sK3
    | v3_tex_2(sK3,sK2) != iProver_top
    | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1869,c_2021])).

cnf(c_2401,plain,
    ( v3_tex_2(sK3,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1880,c_33,c_2123,c_2375])).

cnf(c_2482,plain,
    ( u1_struct_0(sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2459,c_33,c_435,c_1880,c_2123,c_2375])).

cnf(c_18,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_568,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_569,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_568])).

cnf(c_573,plain,
    ( v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_569,c_27,c_26,c_25,c_389])).

cnf(c_1849,plain,
    ( v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_573])).

cnf(c_2486,plain,
    ( v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2482,c_1849])).

cnf(c_1853,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_975])).

cnf(c_3438,plain,
    ( v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(sK1(sK2,X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2486,c_1853])).

cnf(c_16,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,sK1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_610,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,sK1(X1,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_611,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0,sK1(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_615,plain,
    ( v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0,sK1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_611,c_27,c_26,c_25,c_389])).

cnf(c_1848,plain,
    ( v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK1(sK2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_2075,plain,
    ( v3_tex_2(sK3,sK2) = iProver_top
    | r1_tarski(sK3,sK1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1857,c_1848])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1860,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2742,plain,
    ( sK1(sK2,sK3) = sK3
    | v3_tex_2(sK3,sK2) = iProver_top
    | r1_tarski(sK1(sK2,sK3),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2075,c_1860])).

cnf(c_15,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_631,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK1(X1,X0) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_632,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_636,plain,
    ( v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(sK2,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_632,c_27,c_26,c_25,c_389])).

cnf(c_1973,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK1(sK2,sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_636])).

cnf(c_1974,plain,
    ( sK1(sK2,sK3) != sK3
    | v3_tex_2(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1973])).

cnf(c_2887,plain,
    ( r1_tarski(sK1(sK2,sK3),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2742,c_33,c_1880,c_1974,c_2123,c_2375])).

cnf(c_3677,plain,
    ( v3_tex_2(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3438,c_2887])).

cnf(c_1592,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2005,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | X1 != k1_zfmisc_1(u1_struct_0(sK2))
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1592])).

cnf(c_2097,plain,
    ( m1_subset_1(sK3,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 != k1_zfmisc_1(u1_struct_0(sK2))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2005])).

cnf(c_2557,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_zfmisc_1(X0) != k1_zfmisc_1(u1_struct_0(sK2))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2097])).

cnf(c_3476,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK3,k1_zfmisc_1(sK3))
    | k1_zfmisc_1(sK3) != k1_zfmisc_1(u1_struct_0(sK2))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2557])).

cnf(c_3477,plain,
    ( k1_zfmisc_1(sK3) != k1_zfmisc_1(u1_struct_0(sK2))
    | sK3 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3476])).

cnf(c_1589,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2203,plain,
    ( X0 != u1_struct_0(sK2)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1589])).

cnf(c_2818,plain,
    ( k1_zfmisc_1(sK3) = k1_zfmisc_1(u1_struct_0(sK2))
    | sK3 != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2203])).

cnf(c_1587,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2040,plain,
    ( u1_struct_0(sK2) != X0
    | sK3 != X0
    | sK3 = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1587])).

cnf(c_2283,plain,
    ( u1_struct_0(sK2) != sK3
    | sK3 = u1_struct_0(sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2040])).

cnf(c_1586,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2098,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1586])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3677,c_3477,c_2818,c_2401,c_2283,c_2098,c_435,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:53:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.84/0.95  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.84/0.95  
% 1.84/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.84/0.95  
% 1.84/0.95  ------  iProver source info
% 1.84/0.95  
% 1.84/0.95  git: date: 2020-06-30 10:37:57 +0100
% 1.84/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.84/0.95  git: non_committed_changes: false
% 1.84/0.95  git: last_make_outside_of_git: false
% 1.84/0.95  
% 1.84/0.95  ------ 
% 1.84/0.95  
% 1.84/0.95  ------ Input Options
% 1.84/0.95  
% 1.84/0.95  --out_options                           all
% 1.84/0.95  --tptp_safe_out                         true
% 1.84/0.95  --problem_path                          ""
% 1.84/0.95  --include_path                          ""
% 1.84/0.95  --clausifier                            res/vclausify_rel
% 1.84/0.95  --clausifier_options                    --mode clausify
% 1.84/0.95  --stdin                                 false
% 1.84/0.95  --stats_out                             all
% 1.84/0.95  
% 1.84/0.95  ------ General Options
% 1.84/0.95  
% 1.84/0.95  --fof                                   false
% 1.84/0.95  --time_out_real                         305.
% 1.84/0.95  --time_out_virtual                      -1.
% 1.84/0.95  --symbol_type_check                     false
% 1.84/0.95  --clausify_out                          false
% 1.84/0.95  --sig_cnt_out                           false
% 1.84/0.95  --trig_cnt_out                          false
% 1.84/0.95  --trig_cnt_out_tolerance                1.
% 1.84/0.95  --trig_cnt_out_sk_spl                   false
% 1.84/0.95  --abstr_cl_out                          false
% 1.84/0.95  
% 1.84/0.95  ------ Global Options
% 1.84/0.95  
% 1.84/0.95  --schedule                              default
% 1.84/0.95  --add_important_lit                     false
% 1.84/0.95  --prop_solver_per_cl                    1000
% 1.84/0.95  --min_unsat_core                        false
% 1.84/0.95  --soft_assumptions                      false
% 1.84/0.95  --soft_lemma_size                       3
% 1.84/0.95  --prop_impl_unit_size                   0
% 1.84/0.95  --prop_impl_unit                        []
% 1.84/0.95  --share_sel_clauses                     true
% 1.84/0.95  --reset_solvers                         false
% 1.84/0.95  --bc_imp_inh                            [conj_cone]
% 1.84/0.95  --conj_cone_tolerance                   3.
% 1.84/0.95  --extra_neg_conj                        none
% 1.84/0.95  --large_theory_mode                     true
% 1.84/0.95  --prolific_symb_bound                   200
% 1.84/0.95  --lt_threshold                          2000
% 1.84/0.95  --clause_weak_htbl                      true
% 1.84/0.95  --gc_record_bc_elim                     false
% 1.84/0.95  
% 1.84/0.95  ------ Preprocessing Options
% 1.84/0.95  
% 1.84/0.95  --preprocessing_flag                    true
% 1.84/0.95  --time_out_prep_mult                    0.1
% 1.84/0.95  --splitting_mode                        input
% 1.84/0.95  --splitting_grd                         true
% 1.84/0.95  --splitting_cvd                         false
% 1.84/0.95  --splitting_cvd_svl                     false
% 1.84/0.95  --splitting_nvd                         32
% 1.84/0.95  --sub_typing                            true
% 1.84/0.95  --prep_gs_sim                           true
% 1.84/0.95  --prep_unflatten                        true
% 1.84/0.95  --prep_res_sim                          true
% 1.84/0.95  --prep_upred                            true
% 1.84/0.95  --prep_sem_filter                       exhaustive
% 1.84/0.95  --prep_sem_filter_out                   false
% 1.84/0.95  --pred_elim                             true
% 1.84/0.95  --res_sim_input                         true
% 1.84/0.95  --eq_ax_congr_red                       true
% 1.84/0.95  --pure_diseq_elim                       true
% 1.84/0.95  --brand_transform                       false
% 1.84/0.95  --non_eq_to_eq                          false
% 1.84/0.95  --prep_def_merge                        true
% 1.84/0.95  --prep_def_merge_prop_impl              false
% 1.84/0.96  --prep_def_merge_mbd                    true
% 1.84/0.96  --prep_def_merge_tr_red                 false
% 1.84/0.96  --prep_def_merge_tr_cl                  false
% 1.84/0.96  --smt_preprocessing                     true
% 1.84/0.96  --smt_ac_axioms                         fast
% 1.84/0.96  --preprocessed_out                      false
% 1.84/0.96  --preprocessed_stats                    false
% 1.84/0.96  
% 1.84/0.96  ------ Abstraction refinement Options
% 1.84/0.96  
% 1.84/0.96  --abstr_ref                             []
% 1.84/0.96  --abstr_ref_prep                        false
% 1.84/0.96  --abstr_ref_until_sat                   false
% 1.84/0.96  --abstr_ref_sig_restrict                funpre
% 1.84/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.84/0.96  --abstr_ref_under                       []
% 1.84/0.96  
% 1.84/0.96  ------ SAT Options
% 1.84/0.96  
% 1.84/0.96  --sat_mode                              false
% 1.84/0.96  --sat_fm_restart_options                ""
% 1.84/0.96  --sat_gr_def                            false
% 1.84/0.96  --sat_epr_types                         true
% 1.84/0.96  --sat_non_cyclic_types                  false
% 1.84/0.96  --sat_finite_models                     false
% 1.84/0.96  --sat_fm_lemmas                         false
% 1.84/0.96  --sat_fm_prep                           false
% 1.84/0.96  --sat_fm_uc_incr                        true
% 1.84/0.96  --sat_out_model                         small
% 1.84/0.96  --sat_out_clauses                       false
% 1.84/0.96  
% 1.84/0.96  ------ QBF Options
% 1.84/0.96  
% 1.84/0.96  --qbf_mode                              false
% 1.84/0.96  --qbf_elim_univ                         false
% 1.84/0.96  --qbf_dom_inst                          none
% 1.84/0.96  --qbf_dom_pre_inst                      false
% 1.84/0.96  --qbf_sk_in                             false
% 1.84/0.96  --qbf_pred_elim                         true
% 1.84/0.96  --qbf_split                             512
% 1.84/0.96  
% 1.84/0.96  ------ BMC1 Options
% 1.84/0.96  
% 1.84/0.96  --bmc1_incremental                      false
% 1.84/0.96  --bmc1_axioms                           reachable_all
% 1.84/0.96  --bmc1_min_bound                        0
% 1.84/0.96  --bmc1_max_bound                        -1
% 1.84/0.96  --bmc1_max_bound_default                -1
% 1.84/0.96  --bmc1_symbol_reachability              true
% 1.84/0.96  --bmc1_property_lemmas                  false
% 1.84/0.96  --bmc1_k_induction                      false
% 1.84/0.96  --bmc1_non_equiv_states                 false
% 1.84/0.96  --bmc1_deadlock                         false
% 1.84/0.96  --bmc1_ucm                              false
% 1.84/0.96  --bmc1_add_unsat_core                   none
% 1.84/0.96  --bmc1_unsat_core_children              false
% 1.84/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.84/0.96  --bmc1_out_stat                         full
% 1.84/0.96  --bmc1_ground_init                      false
% 1.84/0.96  --bmc1_pre_inst_next_state              false
% 1.84/0.96  --bmc1_pre_inst_state                   false
% 1.84/0.96  --bmc1_pre_inst_reach_state             false
% 1.84/0.96  --bmc1_out_unsat_core                   false
% 1.84/0.96  --bmc1_aig_witness_out                  false
% 1.84/0.96  --bmc1_verbose                          false
% 1.84/0.96  --bmc1_dump_clauses_tptp                false
% 1.84/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.84/0.96  --bmc1_dump_file                        -
% 1.84/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.84/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.84/0.96  --bmc1_ucm_extend_mode                  1
% 1.84/0.96  --bmc1_ucm_init_mode                    2
% 1.84/0.96  --bmc1_ucm_cone_mode                    none
% 1.84/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.84/0.96  --bmc1_ucm_relax_model                  4
% 1.84/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.84/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.84/0.96  --bmc1_ucm_layered_model                none
% 1.84/0.96  --bmc1_ucm_max_lemma_size               10
% 1.84/0.96  
% 1.84/0.96  ------ AIG Options
% 1.84/0.96  
% 1.84/0.96  --aig_mode                              false
% 1.84/0.96  
% 1.84/0.96  ------ Instantiation Options
% 1.84/0.96  
% 1.84/0.96  --instantiation_flag                    true
% 1.84/0.96  --inst_sos_flag                         false
% 1.84/0.96  --inst_sos_phase                        true
% 1.84/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.84/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.84/0.96  --inst_lit_sel_side                     num_symb
% 1.84/0.96  --inst_solver_per_active                1400
% 1.84/0.96  --inst_solver_calls_frac                1.
% 1.84/0.96  --inst_passive_queue_type               priority_queues
% 1.84/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.84/0.96  --inst_passive_queues_freq              [25;2]
% 1.84/0.96  --inst_dismatching                      true
% 1.84/0.96  --inst_eager_unprocessed_to_passive     true
% 1.84/0.96  --inst_prop_sim_given                   true
% 1.84/0.96  --inst_prop_sim_new                     false
% 1.84/0.96  --inst_subs_new                         false
% 1.84/0.96  --inst_eq_res_simp                      false
% 1.84/0.96  --inst_subs_given                       false
% 1.84/0.96  --inst_orphan_elimination               true
% 1.84/0.96  --inst_learning_loop_flag               true
% 1.84/0.96  --inst_learning_start                   3000
% 1.84/0.96  --inst_learning_factor                  2
% 1.84/0.96  --inst_start_prop_sim_after_learn       3
% 1.84/0.96  --inst_sel_renew                        solver
% 1.84/0.96  --inst_lit_activity_flag                true
% 1.84/0.96  --inst_restr_to_given                   false
% 1.84/0.96  --inst_activity_threshold               500
% 1.84/0.96  --inst_out_proof                        true
% 1.84/0.96  
% 1.84/0.96  ------ Resolution Options
% 1.84/0.96  
% 1.84/0.96  --resolution_flag                       true
% 1.84/0.96  --res_lit_sel                           adaptive
% 1.84/0.96  --res_lit_sel_side                      none
% 1.84/0.96  --res_ordering                          kbo
% 1.84/0.96  --res_to_prop_solver                    active
% 1.84/0.96  --res_prop_simpl_new                    false
% 1.84/0.96  --res_prop_simpl_given                  true
% 1.84/0.96  --res_passive_queue_type                priority_queues
% 1.84/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.84/0.96  --res_passive_queues_freq               [15;5]
% 1.84/0.96  --res_forward_subs                      full
% 1.84/0.96  --res_backward_subs                     full
% 1.84/0.96  --res_forward_subs_resolution           true
% 1.84/0.96  --res_backward_subs_resolution          true
% 1.84/0.96  --res_orphan_elimination                true
% 1.84/0.96  --res_time_limit                        2.
% 1.84/0.96  --res_out_proof                         true
% 1.84/0.96  
% 1.84/0.96  ------ Superposition Options
% 1.84/0.96  
% 1.84/0.96  --superposition_flag                    true
% 1.84/0.96  --sup_passive_queue_type                priority_queues
% 1.84/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.84/0.96  --sup_passive_queues_freq               [8;1;4]
% 1.84/0.96  --demod_completeness_check              fast
% 1.84/0.96  --demod_use_ground                      true
% 1.84/0.96  --sup_to_prop_solver                    passive
% 1.84/0.96  --sup_prop_simpl_new                    true
% 1.84/0.96  --sup_prop_simpl_given                  true
% 1.84/0.96  --sup_fun_splitting                     false
% 1.84/0.96  --sup_smt_interval                      50000
% 1.84/0.96  
% 1.84/0.96  ------ Superposition Simplification Setup
% 1.84/0.96  
% 1.84/0.96  --sup_indices_passive                   []
% 1.84/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 1.84/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/0.96  --sup_full_bw                           [BwDemod]
% 1.84/0.96  --sup_immed_triv                        [TrivRules]
% 1.84/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.84/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/0.96  --sup_immed_bw_main                     []
% 1.84/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 1.84/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/0.96  
% 1.84/0.96  ------ Combination Options
% 1.84/0.96  
% 1.84/0.96  --comb_res_mult                         3
% 1.84/0.96  --comb_sup_mult                         2
% 1.84/0.96  --comb_inst_mult                        10
% 1.84/0.96  
% 1.84/0.96  ------ Debug Options
% 1.84/0.96  
% 1.84/0.96  --dbg_backtrace                         false
% 1.84/0.96  --dbg_dump_prop_clauses                 false
% 1.84/0.96  --dbg_dump_prop_clauses_file            -
% 1.84/0.96  --dbg_out_stat                          false
% 1.84/0.96  ------ Parsing...
% 1.84/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.84/0.96  
% 1.84/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.84/0.96  
% 1.84/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.84/0.96  
% 1.84/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.84/0.96  ------ Proving...
% 1.84/0.96  ------ Problem Properties 
% 1.84/0.96  
% 1.84/0.96  
% 1.84/0.96  clauses                                 16
% 1.84/0.96  conjectures                             1
% 1.84/0.96  EPR                                     2
% 1.84/0.96  Horn                                    12
% 1.84/0.96  unary                                   5
% 1.84/0.96  binary                                  3
% 1.84/0.96  lits                                    37
% 1.84/0.96  lits eq                                 10
% 1.84/0.96  fd_pure                                 0
% 1.84/0.96  fd_pseudo                               0
% 1.84/0.96  fd_cond                                 0
% 1.84/0.96  fd_pseudo_cond                          2
% 1.84/0.96  AC symbols                              0
% 1.84/0.96  
% 1.84/0.96  ------ Schedule dynamic 5 is on 
% 1.84/0.96  
% 1.84/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.84/0.96  
% 1.84/0.96  
% 1.84/0.96  ------ 
% 1.84/0.96  Current options:
% 1.84/0.96  ------ 
% 1.84/0.96  
% 1.84/0.96  ------ Input Options
% 1.84/0.96  
% 1.84/0.96  --out_options                           all
% 1.84/0.96  --tptp_safe_out                         true
% 1.84/0.96  --problem_path                          ""
% 1.84/0.96  --include_path                          ""
% 1.84/0.96  --clausifier                            res/vclausify_rel
% 1.84/0.96  --clausifier_options                    --mode clausify
% 1.84/0.96  --stdin                                 false
% 1.84/0.96  --stats_out                             all
% 1.84/0.96  
% 1.84/0.96  ------ General Options
% 1.84/0.96  
% 1.84/0.96  --fof                                   false
% 1.84/0.96  --time_out_real                         305.
% 1.84/0.96  --time_out_virtual                      -1.
% 1.84/0.96  --symbol_type_check                     false
% 1.84/0.96  --clausify_out                          false
% 1.84/0.96  --sig_cnt_out                           false
% 1.84/0.96  --trig_cnt_out                          false
% 1.84/0.96  --trig_cnt_out_tolerance                1.
% 1.84/0.96  --trig_cnt_out_sk_spl                   false
% 1.84/0.96  --abstr_cl_out                          false
% 1.84/0.96  
% 1.84/0.96  ------ Global Options
% 1.84/0.96  
% 1.84/0.96  --schedule                              default
% 1.84/0.96  --add_important_lit                     false
% 1.84/0.96  --prop_solver_per_cl                    1000
% 1.84/0.96  --min_unsat_core                        false
% 1.84/0.96  --soft_assumptions                      false
% 1.84/0.96  --soft_lemma_size                       3
% 1.84/0.96  --prop_impl_unit_size                   0
% 1.84/0.96  --prop_impl_unit                        []
% 1.84/0.96  --share_sel_clauses                     true
% 1.84/0.96  --reset_solvers                         false
% 1.84/0.96  --bc_imp_inh                            [conj_cone]
% 1.84/0.96  --conj_cone_tolerance                   3.
% 1.84/0.96  --extra_neg_conj                        none
% 1.84/0.96  --large_theory_mode                     true
% 1.84/0.96  --prolific_symb_bound                   200
% 1.84/0.96  --lt_threshold                          2000
% 1.84/0.96  --clause_weak_htbl                      true
% 1.84/0.96  --gc_record_bc_elim                     false
% 1.84/0.96  
% 1.84/0.96  ------ Preprocessing Options
% 1.84/0.96  
% 1.84/0.96  --preprocessing_flag                    true
% 1.84/0.96  --time_out_prep_mult                    0.1
% 1.84/0.96  --splitting_mode                        input
% 1.84/0.96  --splitting_grd                         true
% 1.84/0.96  --splitting_cvd                         false
% 1.84/0.96  --splitting_cvd_svl                     false
% 1.84/0.96  --splitting_nvd                         32
% 1.84/0.96  --sub_typing                            true
% 1.84/0.96  --prep_gs_sim                           true
% 1.84/0.96  --prep_unflatten                        true
% 1.84/0.96  --prep_res_sim                          true
% 1.84/0.96  --prep_upred                            true
% 1.84/0.96  --prep_sem_filter                       exhaustive
% 1.84/0.96  --prep_sem_filter_out                   false
% 1.84/0.96  --pred_elim                             true
% 1.84/0.96  --res_sim_input                         true
% 1.84/0.96  --eq_ax_congr_red                       true
% 1.84/0.96  --pure_diseq_elim                       true
% 1.84/0.96  --brand_transform                       false
% 1.84/0.96  --non_eq_to_eq                          false
% 1.84/0.96  --prep_def_merge                        true
% 1.84/0.96  --prep_def_merge_prop_impl              false
% 1.84/0.96  --prep_def_merge_mbd                    true
% 1.84/0.96  --prep_def_merge_tr_red                 false
% 1.84/0.96  --prep_def_merge_tr_cl                  false
% 1.84/0.96  --smt_preprocessing                     true
% 1.84/0.96  --smt_ac_axioms                         fast
% 1.84/0.96  --preprocessed_out                      false
% 1.84/0.96  --preprocessed_stats                    false
% 1.84/0.96  
% 1.84/0.96  ------ Abstraction refinement Options
% 1.84/0.96  
% 1.84/0.96  --abstr_ref                             []
% 1.84/0.96  --abstr_ref_prep                        false
% 1.84/0.96  --abstr_ref_until_sat                   false
% 1.84/0.96  --abstr_ref_sig_restrict                funpre
% 1.84/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.84/0.96  --abstr_ref_under                       []
% 1.84/0.96  
% 1.84/0.96  ------ SAT Options
% 1.84/0.96  
% 1.84/0.96  --sat_mode                              false
% 1.84/0.96  --sat_fm_restart_options                ""
% 1.84/0.96  --sat_gr_def                            false
% 1.84/0.96  --sat_epr_types                         true
% 1.84/0.96  --sat_non_cyclic_types                  false
% 1.84/0.96  --sat_finite_models                     false
% 1.84/0.96  --sat_fm_lemmas                         false
% 1.84/0.96  --sat_fm_prep                           false
% 1.84/0.96  --sat_fm_uc_incr                        true
% 1.84/0.96  --sat_out_model                         small
% 1.84/0.96  --sat_out_clauses                       false
% 1.84/0.96  
% 1.84/0.96  ------ QBF Options
% 1.84/0.96  
% 1.84/0.96  --qbf_mode                              false
% 1.84/0.96  --qbf_elim_univ                         false
% 1.84/0.96  --qbf_dom_inst                          none
% 1.84/0.96  --qbf_dom_pre_inst                      false
% 1.84/0.96  --qbf_sk_in                             false
% 1.84/0.96  --qbf_pred_elim                         true
% 1.84/0.96  --qbf_split                             512
% 1.84/0.96  
% 1.84/0.96  ------ BMC1 Options
% 1.84/0.96  
% 1.84/0.96  --bmc1_incremental                      false
% 1.84/0.96  --bmc1_axioms                           reachable_all
% 1.84/0.96  --bmc1_min_bound                        0
% 1.84/0.96  --bmc1_max_bound                        -1
% 1.84/0.96  --bmc1_max_bound_default                -1
% 1.84/0.96  --bmc1_symbol_reachability              true
% 1.84/0.96  --bmc1_property_lemmas                  false
% 1.84/0.96  --bmc1_k_induction                      false
% 1.84/0.96  --bmc1_non_equiv_states                 false
% 1.84/0.96  --bmc1_deadlock                         false
% 1.84/0.96  --bmc1_ucm                              false
% 1.84/0.96  --bmc1_add_unsat_core                   none
% 1.84/0.96  --bmc1_unsat_core_children              false
% 1.84/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.84/0.96  --bmc1_out_stat                         full
% 1.84/0.96  --bmc1_ground_init                      false
% 1.84/0.96  --bmc1_pre_inst_next_state              false
% 1.84/0.96  --bmc1_pre_inst_state                   false
% 1.84/0.96  --bmc1_pre_inst_reach_state             false
% 1.84/0.96  --bmc1_out_unsat_core                   false
% 1.84/0.96  --bmc1_aig_witness_out                  false
% 1.84/0.96  --bmc1_verbose                          false
% 1.84/0.96  --bmc1_dump_clauses_tptp                false
% 1.84/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.84/0.96  --bmc1_dump_file                        -
% 1.84/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.84/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.84/0.96  --bmc1_ucm_extend_mode                  1
% 1.84/0.96  --bmc1_ucm_init_mode                    2
% 1.84/0.96  --bmc1_ucm_cone_mode                    none
% 1.84/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.84/0.96  --bmc1_ucm_relax_model                  4
% 1.84/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.84/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.84/0.96  --bmc1_ucm_layered_model                none
% 1.84/0.96  --bmc1_ucm_max_lemma_size               10
% 1.84/0.96  
% 1.84/0.96  ------ AIG Options
% 1.84/0.96  
% 1.84/0.96  --aig_mode                              false
% 1.84/0.96  
% 1.84/0.96  ------ Instantiation Options
% 1.84/0.96  
% 1.84/0.96  --instantiation_flag                    true
% 1.84/0.96  --inst_sos_flag                         false
% 1.84/0.96  --inst_sos_phase                        true
% 1.84/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.84/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.84/0.96  --inst_lit_sel_side                     none
% 1.84/0.96  --inst_solver_per_active                1400
% 1.84/0.96  --inst_solver_calls_frac                1.
% 1.84/0.96  --inst_passive_queue_type               priority_queues
% 1.84/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.84/0.96  --inst_passive_queues_freq              [25;2]
% 1.84/0.96  --inst_dismatching                      true
% 1.84/0.96  --inst_eager_unprocessed_to_passive     true
% 1.84/0.96  --inst_prop_sim_given                   true
% 1.84/0.96  --inst_prop_sim_new                     false
% 1.84/0.96  --inst_subs_new                         false
% 1.84/0.96  --inst_eq_res_simp                      false
% 1.84/0.96  --inst_subs_given                       false
% 1.84/0.96  --inst_orphan_elimination               true
% 1.84/0.96  --inst_learning_loop_flag               true
% 1.84/0.96  --inst_learning_start                   3000
% 1.84/0.96  --inst_learning_factor                  2
% 1.84/0.96  --inst_start_prop_sim_after_learn       3
% 1.84/0.96  --inst_sel_renew                        solver
% 1.84/0.96  --inst_lit_activity_flag                true
% 1.84/0.96  --inst_restr_to_given                   false
% 1.84/0.96  --inst_activity_threshold               500
% 1.84/0.96  --inst_out_proof                        true
% 1.84/0.96  
% 1.84/0.96  ------ Resolution Options
% 1.84/0.96  
% 1.84/0.96  --resolution_flag                       false
% 1.84/0.96  --res_lit_sel                           adaptive
% 1.84/0.96  --res_lit_sel_side                      none
% 1.84/0.96  --res_ordering                          kbo
% 1.84/0.96  --res_to_prop_solver                    active
% 1.84/0.96  --res_prop_simpl_new                    false
% 1.84/0.96  --res_prop_simpl_given                  true
% 1.84/0.96  --res_passive_queue_type                priority_queues
% 1.84/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.84/0.96  --res_passive_queues_freq               [15;5]
% 1.84/0.96  --res_forward_subs                      full
% 1.84/0.96  --res_backward_subs                     full
% 1.84/0.96  --res_forward_subs_resolution           true
% 1.84/0.96  --res_backward_subs_resolution          true
% 1.84/0.96  --res_orphan_elimination                true
% 1.84/0.96  --res_time_limit                        2.
% 1.84/0.96  --res_out_proof                         true
% 1.84/0.96  
% 1.84/0.96  ------ Superposition Options
% 1.84/0.96  
% 1.84/0.96  --superposition_flag                    true
% 1.84/0.96  --sup_passive_queue_type                priority_queues
% 1.84/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.84/0.96  --sup_passive_queues_freq               [8;1;4]
% 1.84/0.96  --demod_completeness_check              fast
% 1.84/0.96  --demod_use_ground                      true
% 1.84/0.96  --sup_to_prop_solver                    passive
% 1.84/0.96  --sup_prop_simpl_new                    true
% 1.84/0.96  --sup_prop_simpl_given                  true
% 1.84/0.96  --sup_fun_splitting                     false
% 1.84/0.96  --sup_smt_interval                      50000
% 1.84/0.96  
% 1.84/0.96  ------ Superposition Simplification Setup
% 1.84/0.96  
% 1.84/0.96  --sup_indices_passive                   []
% 1.84/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 1.84/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/0.96  --sup_full_bw                           [BwDemod]
% 1.84/0.96  --sup_immed_triv                        [TrivRules]
% 1.84/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.84/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/0.96  --sup_immed_bw_main                     []
% 1.84/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 1.84/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/0.96  
% 1.84/0.96  ------ Combination Options
% 1.84/0.96  
% 1.84/0.96  --comb_res_mult                         3
% 1.84/0.96  --comb_sup_mult                         2
% 1.84/0.96  --comb_inst_mult                        10
% 1.84/0.96  
% 1.84/0.96  ------ Debug Options
% 1.84/0.96  
% 1.84/0.96  --dbg_backtrace                         false
% 1.84/0.96  --dbg_dump_prop_clauses                 false
% 1.84/0.96  --dbg_dump_prop_clauses_file            -
% 1.84/0.96  --dbg_out_stat                          false
% 1.84/0.96  
% 1.84/0.96  
% 1.84/0.96  
% 1.84/0.96  
% 1.84/0.96  ------ Proving...
% 1.84/0.96  
% 1.84/0.96  
% 1.84/0.96  % SZS status Theorem for theBenchmark.p
% 1.84/0.96  
% 1.84/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 1.84/0.96  
% 1.84/0.96  fof(f12,conjecture,(
% 1.84/0.96    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 1.84/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/0.96  
% 1.84/0.96  fof(f13,negated_conjecture,(
% 1.84/0.96    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 1.84/0.96    inference(negated_conjecture,[],[f12])).
% 1.84/0.96  
% 1.84/0.96  fof(f23,plain,(
% 1.84/0.96    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.84/0.96    inference(ennf_transformation,[],[f13])).
% 1.84/0.96  
% 1.84/0.96  fof(f24,plain,(
% 1.84/0.96    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.84/0.96    inference(flattening,[],[f23])).
% 1.84/0.96  
% 1.84/0.96  fof(f37,plain,(
% 1.84/0.96    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.84/0.96    inference(nnf_transformation,[],[f24])).
% 1.84/0.96  
% 1.84/0.96  fof(f38,plain,(
% 1.84/0.96    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.84/0.96    inference(flattening,[],[f37])).
% 1.84/0.96  
% 1.84/0.96  fof(f40,plain,(
% 1.84/0.96    ( ! [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_subset_1(sK3,u1_struct_0(X0)) | ~v3_tex_2(sK3,X0)) & (~v1_subset_1(sK3,u1_struct_0(X0)) | v3_tex_2(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.84/0.96    introduced(choice_axiom,[])).
% 1.84/0.96  
% 1.84/0.96  fof(f39,plain,(
% 1.84/0.96    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK2)) | ~v3_tex_2(X1,sK2)) & (~v1_subset_1(X1,u1_struct_0(sK2)) | v3_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v1_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.84/0.96    introduced(choice_axiom,[])).
% 1.84/0.96  
% 1.84/0.96  fof(f41,plain,(
% 1.84/0.96    ((v1_subset_1(sK3,u1_struct_0(sK2)) | ~v3_tex_2(sK3,sK2)) & (~v1_subset_1(sK3,u1_struct_0(sK2)) | v3_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v1_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.84/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f40,f39])).
% 1.84/0.96  
% 1.84/0.96  fof(f68,plain,(
% 1.84/0.96    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.84/0.96    inference(cnf_transformation,[],[f41])).
% 1.84/0.96  
% 1.84/0.96  fof(f4,axiom,(
% 1.84/0.96    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.84/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/0.96  
% 1.84/0.96  fof(f50,plain,(
% 1.84/0.96    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.84/0.96    inference(cnf_transformation,[],[f4])).
% 1.84/0.96  
% 1.84/0.96  fof(f3,axiom,(
% 1.84/0.96    ! [X0] : k2_subset_1(X0) = X0),
% 1.84/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/0.96  
% 1.84/0.96  fof(f49,plain,(
% 1.84/0.96    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.84/0.96    inference(cnf_transformation,[],[f3])).
% 1.84/0.96  
% 1.84/0.96  fof(f10,axiom,(
% 1.84/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.84/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/0.96  
% 1.84/0.96  fof(f19,plain,(
% 1.84/0.96    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.84/0.96    inference(ennf_transformation,[],[f10])).
% 1.84/0.96  
% 1.84/0.96  fof(f20,plain,(
% 1.84/0.96    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.84/0.96    inference(flattening,[],[f19])).
% 1.84/0.96  
% 1.84/0.96  fof(f32,plain,(
% 1.84/0.96    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.84/0.96    inference(nnf_transformation,[],[f20])).
% 1.84/0.96  
% 1.84/0.96  fof(f33,plain,(
% 1.84/0.96    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.84/0.96    inference(flattening,[],[f32])).
% 1.84/0.96  
% 1.84/0.96  fof(f34,plain,(
% 1.84/0.96    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.84/0.96    inference(rectify,[],[f33])).
% 1.84/0.96  
% 1.84/0.96  fof(f35,plain,(
% 1.84/0.96    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.84/0.96    introduced(choice_axiom,[])).
% 1.84/0.96  
% 1.84/0.96  fof(f36,plain,(
% 1.84/0.96    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.84/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 1.84/0.96  
% 1.84/0.96  fof(f58,plain,(
% 1.84/0.96    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.84/0.96    inference(cnf_transformation,[],[f36])).
% 1.84/0.96  
% 1.84/0.96  fof(f67,plain,(
% 1.84/0.96    l1_pre_topc(sK2)),
% 1.84/0.96    inference(cnf_transformation,[],[f41])).
% 1.84/0.96  
% 1.84/0.96  fof(f11,axiom,(
% 1.84/0.96    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 1.84/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/0.96  
% 1.84/0.96  fof(f21,plain,(
% 1.84/0.96    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.84/0.96    inference(ennf_transformation,[],[f11])).
% 1.84/0.96  
% 1.84/0.96  fof(f22,plain,(
% 1.84/0.96    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.84/0.96    inference(flattening,[],[f21])).
% 1.84/0.96  
% 1.84/0.96  fof(f63,plain,(
% 1.84/0.96    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.84/0.96    inference(cnf_transformation,[],[f22])).
% 1.84/0.96  
% 1.84/0.96  fof(f64,plain,(
% 1.84/0.96    ~v2_struct_0(sK2)),
% 1.84/0.96    inference(cnf_transformation,[],[f41])).
% 1.84/0.96  
% 1.84/0.96  fof(f65,plain,(
% 1.84/0.96    v2_pre_topc(sK2)),
% 1.84/0.96    inference(cnf_transformation,[],[f41])).
% 1.84/0.96  
% 1.84/0.96  fof(f66,plain,(
% 1.84/0.96    v1_tdlat_3(sK2)),
% 1.84/0.96    inference(cnf_transformation,[],[f41])).
% 1.84/0.96  
% 1.84/0.96  fof(f9,axiom,(
% 1.84/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.84/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/0.96  
% 1.84/0.96  fof(f18,plain,(
% 1.84/0.96    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.84/0.96    inference(ennf_transformation,[],[f9])).
% 1.84/0.96  
% 1.84/0.96  fof(f31,plain,(
% 1.84/0.96    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.84/0.96    inference(nnf_transformation,[],[f18])).
% 1.84/0.96  
% 1.84/0.96  fof(f56,plain,(
% 1.84/0.96    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.84/0.96    inference(cnf_transformation,[],[f31])).
% 1.84/0.96  
% 1.84/0.96  fof(f69,plain,(
% 1.84/0.96    ~v1_subset_1(sK3,u1_struct_0(sK2)) | v3_tex_2(sK3,sK2)),
% 1.84/0.96    inference(cnf_transformation,[],[f41])).
% 1.84/0.96  
% 1.84/0.96  fof(f6,axiom,(
% 1.84/0.96    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 1.84/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/0.96  
% 1.84/0.96  fof(f52,plain,(
% 1.84/0.96    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 1.84/0.96    inference(cnf_transformation,[],[f6])).
% 1.84/0.96  
% 1.84/0.96  fof(f70,plain,(
% 1.84/0.96    v1_subset_1(sK3,u1_struct_0(sK2)) | ~v3_tex_2(sK3,sK2)),
% 1.84/0.96    inference(cnf_transformation,[],[f41])).
% 1.84/0.96  
% 1.84/0.96  fof(f5,axiom,(
% 1.84/0.96    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.84/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/0.96  
% 1.84/0.96  fof(f51,plain,(
% 1.84/0.96    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.84/0.96    inference(cnf_transformation,[],[f5])).
% 1.84/0.96  
% 1.84/0.96  fof(f7,axiom,(
% 1.84/0.96    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.84/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/0.96  
% 1.84/0.96  fof(f14,plain,(
% 1.84/0.96    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.84/0.96    inference(ennf_transformation,[],[f7])).
% 1.84/0.96  
% 1.84/0.96  fof(f15,plain,(
% 1.84/0.96    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.84/0.96    inference(flattening,[],[f14])).
% 1.84/0.96  
% 1.84/0.96  fof(f53,plain,(
% 1.84/0.96    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.84/0.96    inference(cnf_transformation,[],[f15])).
% 1.84/0.96  
% 1.84/0.96  fof(f2,axiom,(
% 1.84/0.96    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.84/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/0.96  
% 1.84/0.96  fof(f27,plain,(
% 1.84/0.96    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.84/0.96    inference(nnf_transformation,[],[f2])).
% 1.84/0.96  
% 1.84/0.96  fof(f28,plain,(
% 1.84/0.96    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.84/0.96    inference(rectify,[],[f27])).
% 1.84/0.96  
% 1.84/0.96  fof(f29,plain,(
% 1.84/0.96    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 1.84/0.96    introduced(choice_axiom,[])).
% 1.84/0.96  
% 1.84/0.96  fof(f30,plain,(
% 1.84/0.96    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.84/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 1.84/0.96  
% 1.84/0.96  fof(f45,plain,(
% 1.84/0.96    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.84/0.96    inference(cnf_transformation,[],[f30])).
% 1.84/0.96  
% 1.84/0.96  fof(f74,plain,(
% 1.84/0.96    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.84/0.96    inference(equality_resolution,[],[f45])).
% 1.84/0.96  
% 1.84/0.96  fof(f59,plain,(
% 1.84/0.96    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.84/0.96    inference(cnf_transformation,[],[f36])).
% 1.84/0.96  
% 1.84/0.96  fof(f61,plain,(
% 1.84/0.96    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK1(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.84/0.96    inference(cnf_transformation,[],[f36])).
% 1.84/0.96  
% 1.84/0.96  fof(f1,axiom,(
% 1.84/0.96    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.84/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.84/0.96  
% 1.84/0.96  fof(f25,plain,(
% 1.84/0.96    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.84/0.96    inference(nnf_transformation,[],[f1])).
% 1.84/0.96  
% 1.84/0.96  fof(f26,plain,(
% 1.84/0.96    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.84/0.96    inference(flattening,[],[f25])).
% 1.84/0.96  
% 1.84/0.96  fof(f44,plain,(
% 1.84/0.96    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.84/0.96    inference(cnf_transformation,[],[f26])).
% 1.84/0.96  
% 1.84/0.96  fof(f62,plain,(
% 1.84/0.96    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK1(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.84/0.96    inference(cnf_transformation,[],[f36])).
% 1.84/0.96  
% 1.84/0.96  cnf(c_24,negated_conjecture,
% 1.84/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.84/0.96      inference(cnf_transformation,[],[f68]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_1857,plain,
% 1.84/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.84/0.96      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_8,plain,
% 1.84/0.96      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.84/0.96      inference(cnf_transformation,[],[f50]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_1858,plain,
% 1.84/0.96      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.84/0.96      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_7,plain,
% 1.84/0.96      ( k2_subset_1(X0) = X0 ),
% 1.84/0.96      inference(cnf_transformation,[],[f49]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_1869,plain,
% 1.84/0.96      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.84/0.96      inference(light_normalisation,[status(thm)],[c_1858,c_7]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_19,plain,
% 1.84/0.96      ( ~ v2_tex_2(X0,X1)
% 1.84/0.96      | ~ v3_tex_2(X2,X1)
% 1.84/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/0.96      | ~ r1_tarski(X2,X0)
% 1.84/0.96      | ~ l1_pre_topc(X1)
% 1.84/0.96      | X0 = X2 ),
% 1.84/0.96      inference(cnf_transformation,[],[f58]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_25,negated_conjecture,
% 1.84/0.96      ( l1_pre_topc(sK2) ),
% 1.84/0.96      inference(cnf_transformation,[],[f67]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_545,plain,
% 1.84/0.96      ( ~ v2_tex_2(X0,X1)
% 1.84/0.96      | ~ v3_tex_2(X2,X1)
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/0.96      | ~ r1_tarski(X2,X0)
% 1.84/0.96      | X2 = X0
% 1.84/0.96      | sK2 != X1 ),
% 1.84/0.96      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_546,plain,
% 1.84/0.96      ( ~ v2_tex_2(X0,sK2)
% 1.84/0.96      | ~ v3_tex_2(X1,sK2)
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/0.96      | ~ r1_tarski(X1,X0)
% 1.84/0.96      | X1 = X0 ),
% 1.84/0.96      inference(unflattening,[status(thm)],[c_545]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_21,plain,
% 1.84/0.96      ( v2_tex_2(X0,X1)
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/0.96      | v2_struct_0(X1)
% 1.84/0.96      | ~ l1_pre_topc(X1)
% 1.84/0.96      | ~ v1_tdlat_3(X1)
% 1.84/0.96      | ~ v2_pre_topc(X1) ),
% 1.84/0.96      inference(cnf_transformation,[],[f63]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_28,negated_conjecture,
% 1.84/0.96      ( ~ v2_struct_0(sK2) ),
% 1.84/0.96      inference(cnf_transformation,[],[f64]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_388,plain,
% 1.84/0.96      ( v2_tex_2(X0,X1)
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/0.96      | ~ l1_pre_topc(X1)
% 1.84/0.96      | ~ v1_tdlat_3(X1)
% 1.84/0.96      | ~ v2_pre_topc(X1)
% 1.84/0.96      | sK2 != X1 ),
% 1.84/0.96      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_389,plain,
% 1.84/0.96      ( v2_tex_2(X0,sK2)
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/0.96      | ~ l1_pre_topc(sK2)
% 1.84/0.96      | ~ v1_tdlat_3(sK2)
% 1.84/0.96      | ~ v2_pre_topc(sK2) ),
% 1.84/0.96      inference(unflattening,[status(thm)],[c_388]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_27,negated_conjecture,
% 1.84/0.96      ( v2_pre_topc(sK2) ),
% 1.84/0.96      inference(cnf_transformation,[],[f65]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_26,negated_conjecture,
% 1.84/0.96      ( v1_tdlat_3(sK2) ),
% 1.84/0.96      inference(cnf_transformation,[],[f66]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_393,plain,
% 1.84/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/0.96      | v2_tex_2(X0,sK2) ),
% 1.84/0.96      inference(global_propositional_subsumption,
% 1.84/0.96                [status(thm)],
% 1.84/0.96                [c_389,c_27,c_26,c_25]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_394,plain,
% 1.84/0.96      ( v2_tex_2(X0,sK2)
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.84/0.96      inference(renaming,[status(thm)],[c_393]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_548,plain,
% 1.84/0.96      ( ~ v3_tex_2(X1,sK2)
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/0.96      | ~ r1_tarski(X1,X0)
% 1.84/0.96      | X1 = X0 ),
% 1.84/0.96      inference(global_propositional_subsumption,
% 1.84/0.96                [status(thm)],
% 1.84/0.96                [c_546,c_27,c_26,c_25,c_389]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_549,plain,
% 1.84/0.96      ( ~ v3_tex_2(X0,sK2)
% 1.84/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/0.96      | ~ r1_tarski(X0,X1)
% 1.84/0.96      | X0 = X1 ),
% 1.84/0.96      inference(renaming,[status(thm)],[c_548]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_1850,plain,
% 1.84/0.96      ( X0 = X1
% 1.84/0.96      | v3_tex_2(X0,sK2) != iProver_top
% 1.84/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.84/0.96      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.84/0.96      | r1_tarski(X0,X1) != iProver_top ),
% 1.84/0.96      inference(predicate_to_equality,[status(thm)],[c_549]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_2376,plain,
% 1.84/0.96      ( u1_struct_0(sK2) = X0
% 1.84/0.96      | v3_tex_2(u1_struct_0(sK2),sK2) != iProver_top
% 1.84/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.84/0.96      | r1_tarski(u1_struct_0(sK2),X0) != iProver_top ),
% 1.84/0.96      inference(superposition,[status(thm)],[c_1869,c_1850]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_2459,plain,
% 1.84/0.96      ( u1_struct_0(sK2) = sK3
% 1.84/0.96      | v3_tex_2(u1_struct_0(sK2),sK2) != iProver_top
% 1.84/0.96      | r1_tarski(u1_struct_0(sK2),sK3) != iProver_top ),
% 1.84/0.96      inference(superposition,[status(thm)],[c_1857,c_2376]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_33,plain,
% 1.84/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.84/0.96      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_13,plain,
% 1.84/0.96      ( v1_subset_1(X0,X1)
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.84/0.96      | X0 = X1 ),
% 1.84/0.96      inference(cnf_transformation,[],[f56]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_23,negated_conjecture,
% 1.84/0.96      ( v3_tex_2(sK3,sK2) | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.84/0.96      inference(cnf_transformation,[],[f69]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_216,plain,
% 1.84/0.96      ( v3_tex_2(sK3,sK2) | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.84/0.96      inference(prop_impl,[status(thm)],[c_23]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_433,plain,
% 1.84/0.96      ( v3_tex_2(sK3,sK2)
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.84/0.96      | X1 = X0
% 1.84/0.96      | u1_struct_0(sK2) != X1
% 1.84/0.96      | sK3 != X0 ),
% 1.84/0.96      inference(resolution_lifted,[status(thm)],[c_13,c_216]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_434,plain,
% 1.84/0.96      ( v3_tex_2(sK3,sK2)
% 1.84/0.96      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/0.96      | u1_struct_0(sK2) = sK3 ),
% 1.84/0.96      inference(unflattening,[status(thm)],[c_433]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_435,plain,
% 1.84/0.96      ( u1_struct_0(sK2) = sK3
% 1.84/0.96      | v3_tex_2(sK3,sK2) = iProver_top
% 1.84/0.96      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.84/0.96      inference(predicate_to_equality,[status(thm)],[c_434]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_10,plain,
% 1.84/0.96      ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
% 1.84/0.96      inference(cnf_transformation,[],[f52]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_22,negated_conjecture,
% 1.84/0.96      ( ~ v3_tex_2(sK3,sK2) | v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.84/0.96      inference(cnf_transformation,[],[f70]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_218,plain,
% 1.84/0.96      ( ~ v3_tex_2(sK3,sK2) | v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 1.84/0.96      inference(prop_impl,[status(thm)],[c_22]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_421,plain,
% 1.84/0.96      ( ~ v3_tex_2(sK3,sK2)
% 1.84/0.96      | u1_struct_0(sK2) != X0
% 1.84/0.96      | k2_subset_1(X0) != sK3 ),
% 1.84/0.96      inference(resolution_lifted,[status(thm)],[c_10,c_218]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_422,plain,
% 1.84/0.96      ( ~ v3_tex_2(sK3,sK2) | k2_subset_1(u1_struct_0(sK2)) != sK3 ),
% 1.84/0.96      inference(unflattening,[status(thm)],[c_421]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_1856,plain,
% 1.84/0.96      ( k2_subset_1(u1_struct_0(sK2)) != sK3
% 1.84/0.96      | v3_tex_2(sK3,sK2) != iProver_top ),
% 1.84/0.96      inference(predicate_to_equality,[status(thm)],[c_422]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_1880,plain,
% 1.84/0.96      ( u1_struct_0(sK2) != sK3 | v3_tex_2(sK3,sK2) != iProver_top ),
% 1.84/0.96      inference(demodulation,[status(thm)],[c_1856,c_7]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_9,plain,
% 1.84/0.96      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 1.84/0.96      inference(cnf_transformation,[],[f51]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_11,plain,
% 1.84/0.96      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.84/0.96      inference(cnf_transformation,[],[f53]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_373,plain,
% 1.84/0.96      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_zfmisc_1(X2) != X1 ),
% 1.84/0.96      inference(resolution_lifted,[status(thm)],[c_9,c_11]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_374,plain,
% 1.84/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.84/0.96      | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 1.84/0.96      inference(unflattening,[status(thm)],[c_373]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_6,plain,
% 1.84/0.96      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.84/0.96      inference(cnf_transformation,[],[f74]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_939,plain,
% 1.84/0.96      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 1.84/0.96      inference(prop_impl,[status(thm)],[c_6]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_940,plain,
% 1.84/0.96      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.84/0.96      inference(renaming,[status(thm)],[c_939]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_975,plain,
% 1.84/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.84/0.96      inference(bin_hyper_res,[status(thm)],[c_374,c_940]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_2122,plain,
% 1.84/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/0.96      | r1_tarski(sK3,u1_struct_0(sK2)) ),
% 1.84/0.96      inference(instantiation,[status(thm)],[c_975]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_2123,plain,
% 1.84/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.84/0.96      | r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.84/0.96      inference(predicate_to_equality,[status(thm)],[c_2122]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_2021,plain,
% 1.84/0.96      ( sK3 = X0
% 1.84/0.96      | v3_tex_2(sK3,sK2) != iProver_top
% 1.84/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.84/0.96      | r1_tarski(sK3,X0) != iProver_top ),
% 1.84/0.96      inference(superposition,[status(thm)],[c_1857,c_1850]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_2375,plain,
% 1.84/0.96      ( u1_struct_0(sK2) = sK3
% 1.84/0.96      | v3_tex_2(sK3,sK2) != iProver_top
% 1.84/0.96      | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
% 1.84/0.96      inference(superposition,[status(thm)],[c_1869,c_2021]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_2401,plain,
% 1.84/0.96      ( v3_tex_2(sK3,sK2) != iProver_top ),
% 1.84/0.96      inference(global_propositional_subsumption,
% 1.84/0.96                [status(thm)],
% 1.84/0.96                [c_1880,c_33,c_2123,c_2375]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_2482,plain,
% 1.84/0.96      ( u1_struct_0(sK2) = sK3 ),
% 1.84/0.96      inference(global_propositional_subsumption,
% 1.84/0.96                [status(thm)],
% 1.84/0.96                [c_2459,c_33,c_435,c_1880,c_2123,c_2375]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_18,plain,
% 1.84/0.96      ( ~ v2_tex_2(X0,X1)
% 1.84/0.96      | v3_tex_2(X0,X1)
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/0.96      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/0.96      | ~ l1_pre_topc(X1) ),
% 1.84/0.96      inference(cnf_transformation,[],[f59]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_568,plain,
% 1.84/0.96      ( ~ v2_tex_2(X0,X1)
% 1.84/0.96      | v3_tex_2(X0,X1)
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/0.96      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/0.96      | sK2 != X1 ),
% 1.84/0.96      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_569,plain,
% 1.84/0.96      ( ~ v2_tex_2(X0,sK2)
% 1.84/0.96      | v3_tex_2(X0,sK2)
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/0.96      | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.84/0.96      inference(unflattening,[status(thm)],[c_568]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_573,plain,
% 1.84/0.96      ( v3_tex_2(X0,sK2)
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/0.96      | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.84/0.96      inference(global_propositional_subsumption,
% 1.84/0.96                [status(thm)],
% 1.84/0.96                [c_569,c_27,c_26,c_25,c_389]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_1849,plain,
% 1.84/0.96      ( v3_tex_2(X0,sK2) = iProver_top
% 1.84/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.84/0.96      | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.84/0.96      inference(predicate_to_equality,[status(thm)],[c_573]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_2486,plain,
% 1.84/0.96      ( v3_tex_2(X0,sK2) = iProver_top
% 1.84/0.96      | m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 1.84/0.96      | m1_subset_1(sK1(sK2,X0),k1_zfmisc_1(sK3)) = iProver_top ),
% 1.84/0.96      inference(demodulation,[status(thm)],[c_2482,c_1849]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_1853,plain,
% 1.84/0.96      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.84/0.96      | r1_tarski(X0,X1) = iProver_top ),
% 1.84/0.96      inference(predicate_to_equality,[status(thm)],[c_975]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_3438,plain,
% 1.84/0.96      ( v3_tex_2(X0,sK2) = iProver_top
% 1.84/0.96      | m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 1.84/0.96      | r1_tarski(sK1(sK2,X0),sK3) = iProver_top ),
% 1.84/0.96      inference(superposition,[status(thm)],[c_2486,c_1853]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_16,plain,
% 1.84/0.96      ( ~ v2_tex_2(X0,X1)
% 1.84/0.96      | v3_tex_2(X0,X1)
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/0.96      | r1_tarski(X0,sK1(X1,X0))
% 1.84/0.96      | ~ l1_pre_topc(X1) ),
% 1.84/0.96      inference(cnf_transformation,[],[f61]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_610,plain,
% 1.84/0.96      ( ~ v2_tex_2(X0,X1)
% 1.84/0.96      | v3_tex_2(X0,X1)
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/0.96      | r1_tarski(X0,sK1(X1,X0))
% 1.84/0.96      | sK2 != X1 ),
% 1.84/0.96      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_611,plain,
% 1.84/0.96      ( ~ v2_tex_2(X0,sK2)
% 1.84/0.96      | v3_tex_2(X0,sK2)
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/0.96      | r1_tarski(X0,sK1(sK2,X0)) ),
% 1.84/0.96      inference(unflattening,[status(thm)],[c_610]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_615,plain,
% 1.84/0.96      ( v3_tex_2(X0,sK2)
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/0.96      | r1_tarski(X0,sK1(sK2,X0)) ),
% 1.84/0.96      inference(global_propositional_subsumption,
% 1.84/0.96                [status(thm)],
% 1.84/0.96                [c_611,c_27,c_26,c_25,c_389]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_1848,plain,
% 1.84/0.96      ( v3_tex_2(X0,sK2) = iProver_top
% 1.84/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.84/0.96      | r1_tarski(X0,sK1(sK2,X0)) = iProver_top ),
% 1.84/0.96      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_2075,plain,
% 1.84/0.96      ( v3_tex_2(sK3,sK2) = iProver_top
% 1.84/0.96      | r1_tarski(sK3,sK1(sK2,sK3)) = iProver_top ),
% 1.84/0.96      inference(superposition,[status(thm)],[c_1857,c_1848]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_0,plain,
% 1.84/0.96      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.84/0.96      inference(cnf_transformation,[],[f44]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_1860,plain,
% 1.84/0.96      ( X0 = X1
% 1.84/0.96      | r1_tarski(X1,X0) != iProver_top
% 1.84/0.96      | r1_tarski(X0,X1) != iProver_top ),
% 1.84/0.96      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_2742,plain,
% 1.84/0.96      ( sK1(sK2,sK3) = sK3
% 1.84/0.96      | v3_tex_2(sK3,sK2) = iProver_top
% 1.84/0.96      | r1_tarski(sK1(sK2,sK3),sK3) != iProver_top ),
% 1.84/0.96      inference(superposition,[status(thm)],[c_2075,c_1860]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_15,plain,
% 1.84/0.96      ( ~ v2_tex_2(X0,X1)
% 1.84/0.96      | v3_tex_2(X0,X1)
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/0.96      | ~ l1_pre_topc(X1)
% 1.84/0.96      | sK1(X1,X0) != X0 ),
% 1.84/0.96      inference(cnf_transformation,[],[f62]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_631,plain,
% 1.84/0.96      ( ~ v2_tex_2(X0,X1)
% 1.84/0.96      | v3_tex_2(X0,X1)
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/0.96      | sK1(X1,X0) != X0
% 1.84/0.96      | sK2 != X1 ),
% 1.84/0.96      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_632,plain,
% 1.84/0.96      ( ~ v2_tex_2(X0,sK2)
% 1.84/0.96      | v3_tex_2(X0,sK2)
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/0.96      | sK1(sK2,X0) != X0 ),
% 1.84/0.96      inference(unflattening,[status(thm)],[c_631]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_636,plain,
% 1.84/0.96      ( v3_tex_2(X0,sK2)
% 1.84/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/0.96      | sK1(sK2,X0) != X0 ),
% 1.84/0.96      inference(global_propositional_subsumption,
% 1.84/0.96                [status(thm)],
% 1.84/0.96                [c_632,c_27,c_26,c_25,c_389]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_1973,plain,
% 1.84/0.96      ( v3_tex_2(sK3,sK2)
% 1.84/0.96      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/0.96      | sK1(sK2,sK3) != sK3 ),
% 1.84/0.96      inference(instantiation,[status(thm)],[c_636]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_1974,plain,
% 1.84/0.96      ( sK1(sK2,sK3) != sK3
% 1.84/0.96      | v3_tex_2(sK3,sK2) = iProver_top
% 1.84/0.96      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.84/0.96      inference(predicate_to_equality,[status(thm)],[c_1973]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_2887,plain,
% 1.84/0.96      ( r1_tarski(sK1(sK2,sK3),sK3) != iProver_top ),
% 1.84/0.96      inference(global_propositional_subsumption,
% 1.84/0.96                [status(thm)],
% 1.84/0.96                [c_2742,c_33,c_1880,c_1974,c_2123,c_2375]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_3677,plain,
% 1.84/0.96      ( v3_tex_2(sK3,sK2) = iProver_top
% 1.84/0.96      | m1_subset_1(sK3,k1_zfmisc_1(sK3)) != iProver_top ),
% 1.84/0.96      inference(superposition,[status(thm)],[c_3438,c_2887]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_1592,plain,
% 1.84/0.96      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.84/0.96      theory(equality) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_2005,plain,
% 1.84/0.96      ( m1_subset_1(X0,X1)
% 1.84/0.96      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/0.96      | X1 != k1_zfmisc_1(u1_struct_0(sK2))
% 1.84/0.96      | X0 != sK3 ),
% 1.84/0.96      inference(instantiation,[status(thm)],[c_1592]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_2097,plain,
% 1.84/0.96      ( m1_subset_1(sK3,X0)
% 1.84/0.96      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/0.96      | X0 != k1_zfmisc_1(u1_struct_0(sK2))
% 1.84/0.96      | sK3 != sK3 ),
% 1.84/0.96      inference(instantiation,[status(thm)],[c_2005]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_2557,plain,
% 1.84/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(X0))
% 1.84/0.96      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/0.96      | k1_zfmisc_1(X0) != k1_zfmisc_1(u1_struct_0(sK2))
% 1.84/0.96      | sK3 != sK3 ),
% 1.84/0.96      inference(instantiation,[status(thm)],[c_2097]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_3476,plain,
% 1.84/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.84/0.96      | m1_subset_1(sK3,k1_zfmisc_1(sK3))
% 1.84/0.96      | k1_zfmisc_1(sK3) != k1_zfmisc_1(u1_struct_0(sK2))
% 1.84/0.96      | sK3 != sK3 ),
% 1.84/0.96      inference(instantiation,[status(thm)],[c_2557]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_3477,plain,
% 1.84/0.96      ( k1_zfmisc_1(sK3) != k1_zfmisc_1(u1_struct_0(sK2))
% 1.84/0.96      | sK3 != sK3
% 1.84/0.96      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.84/0.96      | m1_subset_1(sK3,k1_zfmisc_1(sK3)) = iProver_top ),
% 1.84/0.96      inference(predicate_to_equality,[status(thm)],[c_3476]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_1589,plain,
% 1.84/0.96      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 1.84/0.96      theory(equality) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_2203,plain,
% 1.84/0.96      ( X0 != u1_struct_0(sK2)
% 1.84/0.96      | k1_zfmisc_1(X0) = k1_zfmisc_1(u1_struct_0(sK2)) ),
% 1.84/0.96      inference(instantiation,[status(thm)],[c_1589]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_2818,plain,
% 1.84/0.96      ( k1_zfmisc_1(sK3) = k1_zfmisc_1(u1_struct_0(sK2))
% 1.84/0.96      | sK3 != u1_struct_0(sK2) ),
% 1.84/0.96      inference(instantiation,[status(thm)],[c_2203]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_1587,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_2040,plain,
% 1.84/0.96      ( u1_struct_0(sK2) != X0 | sK3 != X0 | sK3 = u1_struct_0(sK2) ),
% 1.84/0.96      inference(instantiation,[status(thm)],[c_1587]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_2283,plain,
% 1.84/0.96      ( u1_struct_0(sK2) != sK3 | sK3 = u1_struct_0(sK2) | sK3 != sK3 ),
% 1.84/0.96      inference(instantiation,[status(thm)],[c_2040]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_1586,plain,( X0 = X0 ),theory(equality) ).
% 1.84/0.96  
% 1.84/0.96  cnf(c_2098,plain,
% 1.84/0.96      ( sK3 = sK3 ),
% 1.84/0.96      inference(instantiation,[status(thm)],[c_1586]) ).
% 1.84/0.96  
% 1.84/0.96  cnf(contradiction,plain,
% 1.84/0.96      ( $false ),
% 1.84/0.96      inference(minisat,
% 1.84/0.96                [status(thm)],
% 1.84/0.96                [c_3677,c_3477,c_2818,c_2401,c_2283,c_2098,c_435,c_33]) ).
% 1.84/0.96  
% 1.84/0.96  
% 1.84/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 1.84/0.96  
% 1.84/0.96  ------                               Statistics
% 1.84/0.96  
% 1.84/0.96  ------ General
% 1.84/0.96  
% 1.84/0.96  abstr_ref_over_cycles:                  0
% 1.84/0.96  abstr_ref_under_cycles:                 0
% 1.84/0.96  gc_basic_clause_elim:                   0
% 1.84/0.96  forced_gc_time:                         0
% 1.84/0.96  parsing_time:                           0.009
% 1.84/0.96  unif_index_cands_time:                  0.
% 1.84/0.96  unif_index_add_time:                    0.
% 1.84/0.96  orderings_time:                         0.
% 1.84/0.96  out_proof_time:                         0.01
% 1.84/0.96  total_time:                             0.14
% 1.84/0.96  num_of_symbols:                         49
% 1.84/0.96  num_of_terms:                           2086
% 1.84/0.96  
% 1.84/0.96  ------ Preprocessing
% 1.84/0.96  
% 1.84/0.96  num_of_splits:                          0
% 1.84/0.96  num_of_split_atoms:                     0
% 1.84/0.96  num_of_reused_defs:                     0
% 1.84/0.96  num_eq_ax_congr_red:                    13
% 1.84/0.96  num_of_sem_filtered_clauses:            1
% 1.84/0.96  num_of_subtypes:                        0
% 1.84/0.96  monotx_restored_types:                  0
% 1.84/0.96  sat_num_of_epr_types:                   0
% 1.84/0.96  sat_num_of_non_cyclic_types:            0
% 1.84/0.96  sat_guarded_non_collapsed_types:        0
% 1.84/0.96  num_pure_diseq_elim:                    0
% 1.84/0.96  simp_replaced_by:                       0
% 1.84/0.96  res_preprocessed:                       115
% 1.84/0.96  prep_upred:                             0
% 1.84/0.96  prep_unflattend:                        47
% 1.84/0.96  smt_new_axioms:                         0
% 1.84/0.96  pred_elim_cands:                        3
% 1.84/0.96  pred_elim:                              8
% 1.84/0.96  pred_elim_cl:                           12
% 1.84/0.96  pred_elim_cycles:                       12
% 1.84/0.96  merged_defs:                            6
% 1.84/0.96  merged_defs_ncl:                        0
% 1.84/0.96  bin_hyper_res:                          7
% 1.84/0.96  prep_cycles:                            5
% 1.84/0.96  pred_elim_time:                         0.016
% 1.84/0.96  splitting_time:                         0.
% 1.84/0.96  sem_filter_time:                        0.
% 1.84/0.96  monotx_time:                            0.001
% 1.84/0.96  subtype_inf_time:                       0.
% 1.84/0.96  
% 1.84/0.96  ------ Problem properties
% 1.84/0.96  
% 1.84/0.96  clauses:                                16
% 1.84/0.96  conjectures:                            1
% 1.84/0.96  epr:                                    2
% 1.84/0.96  horn:                                   12
% 1.84/0.96  ground:                                 4
% 1.84/0.96  unary:                                  5
% 1.84/0.96  binary:                                 3
% 1.84/0.96  lits:                                   37
% 1.84/0.96  lits_eq:                                10
% 1.84/0.96  fd_pure:                                0
% 1.84/0.96  fd_pseudo:                              0
% 1.84/0.96  fd_cond:                                0
% 1.84/0.96  fd_pseudo_cond:                         2
% 1.84/0.96  ac_symbols:                             0
% 1.84/0.96  
% 1.84/0.96  ------ Propositional Solver
% 1.84/0.96  
% 1.84/0.96  prop_solver_calls:                      32
% 1.84/0.96  prop_fast_solver_calls:                 979
% 1.84/0.96  smt_solver_calls:                       0
% 1.84/0.96  smt_fast_solver_calls:                  0
% 1.84/0.96  prop_num_of_clauses:                    959
% 1.84/0.96  prop_preprocess_simplified:             4116
% 1.84/0.96  prop_fo_subsumed:                       45
% 1.84/0.96  prop_solver_time:                       0.
% 1.84/0.96  smt_solver_time:                        0.
% 1.84/0.96  smt_fast_solver_time:                   0.
% 1.84/0.96  prop_fast_solver_time:                  0.
% 1.84/0.96  prop_unsat_core_time:                   0.
% 1.84/0.96  
% 1.84/0.96  ------ QBF
% 1.84/0.96  
% 1.84/0.96  qbf_q_res:                              0
% 1.84/0.96  qbf_num_tautologies:                    0
% 1.84/0.96  qbf_prep_cycles:                        0
% 1.84/0.96  
% 1.84/0.96  ------ BMC1
% 1.84/0.96  
% 1.84/0.96  bmc1_current_bound:                     -1
% 1.84/0.96  bmc1_last_solved_bound:                 -1
% 1.84/0.96  bmc1_unsat_core_size:                   -1
% 1.84/0.96  bmc1_unsat_core_parents_size:           -1
% 1.84/0.96  bmc1_merge_next_fun:                    0
% 1.84/0.96  bmc1_unsat_core_clauses_time:           0.
% 1.84/0.96  
% 1.84/0.96  ------ Instantiation
% 1.84/0.96  
% 1.84/0.96  inst_num_of_clauses:                    258
% 1.84/0.96  inst_num_in_passive:                    105
% 1.84/0.96  inst_num_in_active:                     142
% 1.84/0.96  inst_num_in_unprocessed:                12
% 1.84/0.96  inst_num_of_loops:                      170
% 1.84/0.96  inst_num_of_learning_restarts:          0
% 1.84/0.96  inst_num_moves_active_passive:          25
% 1.84/0.96  inst_lit_activity:                      0
% 1.84/0.96  inst_lit_activity_moves:                0
% 1.84/0.96  inst_num_tautologies:                   0
% 1.84/0.96  inst_num_prop_implied:                  0
% 1.84/0.96  inst_num_existing_simplified:           0
% 1.84/0.96  inst_num_eq_res_simplified:             0
% 1.84/0.96  inst_num_child_elim:                    0
% 1.84/0.96  inst_num_of_dismatching_blockings:      116
% 1.84/0.96  inst_num_of_non_proper_insts:           295
% 1.84/0.96  inst_num_of_duplicates:                 0
% 1.84/0.96  inst_inst_num_from_inst_to_res:         0
% 1.84/0.96  inst_dismatching_checking_time:         0.
% 1.84/0.96  
% 1.84/0.96  ------ Resolution
% 1.84/0.96  
% 1.84/0.96  res_num_of_clauses:                     0
% 1.84/0.96  res_num_in_passive:                     0
% 1.84/0.96  res_num_in_active:                      0
% 1.84/0.96  res_num_of_loops:                       120
% 1.84/0.96  res_forward_subset_subsumed:            49
% 1.84/0.96  res_backward_subset_subsumed:           2
% 1.84/0.96  res_forward_subsumed:                   1
% 1.84/0.96  res_backward_subsumed:                  0
% 1.84/0.96  res_forward_subsumption_resolution:     0
% 1.84/0.96  res_backward_subsumption_resolution:    0
% 1.84/0.96  res_clause_to_clause_subsumption:       355
% 1.84/0.96  res_orphan_elimination:                 0
% 1.84/0.96  res_tautology_del:                      34
% 1.84/0.96  res_num_eq_res_simplified:              0
% 1.84/0.96  res_num_sel_changes:                    0
% 1.84/0.96  res_moves_from_active_to_pass:          0
% 1.84/0.96  
% 1.84/0.96  ------ Superposition
% 1.84/0.96  
% 1.84/0.96  sup_time_total:                         0.
% 1.84/0.96  sup_time_generating:                    0.
% 1.84/0.96  sup_time_sim_full:                      0.
% 1.84/0.96  sup_time_sim_immed:                     0.
% 1.84/0.96  
% 1.84/0.96  sup_num_of_clauses:                     33
% 1.84/0.96  sup_num_in_active:                      27
% 1.84/0.96  sup_num_in_passive:                     6
% 1.84/0.96  sup_num_of_loops:                       33
% 1.84/0.96  sup_fw_superposition:                   22
% 1.84/0.96  sup_bw_superposition:                   13
% 1.84/0.96  sup_immediate_simplified:               2
% 1.84/0.96  sup_given_eliminated:                   0
% 1.84/0.96  comparisons_done:                       0
% 1.84/0.96  comparisons_avoided:                    1
% 1.84/0.96  
% 1.84/0.96  ------ Simplifications
% 1.84/0.96  
% 1.84/0.96  
% 1.84/0.96  sim_fw_subset_subsumed:                 1
% 1.84/0.96  sim_bw_subset_subsumed:                 1
% 1.84/0.96  sim_fw_subsumed:                        2
% 1.84/0.96  sim_bw_subsumed:                        0
% 1.84/0.96  sim_fw_subsumption_res:                 1
% 1.84/0.96  sim_bw_subsumption_res:                 0
% 1.84/0.96  sim_tautology_del:                      5
% 1.84/0.96  sim_eq_tautology_del:                   6
% 1.84/0.96  sim_eq_res_simp:                        0
% 1.84/0.96  sim_fw_demodulated:                     1
% 1.84/0.96  sim_bw_demodulated:                     7
% 1.84/0.96  sim_light_normalised:                   5
% 1.84/0.96  sim_joinable_taut:                      0
% 1.84/0.96  sim_joinable_simp:                      0
% 1.84/0.96  sim_ac_normalised:                      0
% 1.84/0.96  sim_smt_subsumption:                    0
% 1.84/0.96  
%------------------------------------------------------------------------------
