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
% DateTime   : Thu Dec  3 12:27:08 EST 2020

% Result     : Theorem 7.16s
% Output     : CNFRefutation 7.16s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 490 expanded)
%              Number of clauses        :   80 ( 135 expanded)
%              Number of leaves         :   15 ( 121 expanded)
%              Depth                    :   21
%              Number of atoms          :  529 (2886 expanded)
%              Number of equality atoms :  147 ( 274 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v2_tex_2(X1,X0)
                & v1_tops_1(X1,X0) )
             => v3_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tex_2(sK3,X0)
        & v2_tex_2(sK3,X0)
        & v1_tops_1(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tex_2(X1,X0)
            & v2_tex_2(X1,X0)
            & v1_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v3_tex_2(X1,sK2)
          & v2_tex_2(X1,sK2)
          & v1_tops_1(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ v3_tex_2(sK3,sK2)
    & v2_tex_2(sK3,sK2)
    & v1_tops_1(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f34,f33])).

fof(f60,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f15])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f42,f39])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1)
        & r1_tarski(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1)
                & r1_tarski(sK1(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    v1_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK0(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK0(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK0(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2226,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_13,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_499,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_500,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_2218,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2229,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3203,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK0(sK2,X0),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2218,c_2229])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2233,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5218,plain,
    ( k4_xboole_0(sK0(sK2,X0),u1_struct_0(sK2)) = k1_xboole_0
    | v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3203,c_2233])).

cnf(c_6230,plain,
    ( k4_xboole_0(sK0(sK2,sK3),u1_struct_0(sK2)) = k1_xboole_0
    | v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2226,c_5218])).

cnf(c_21,negated_conjecture,
    ( v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_20,negated_conjecture,
    ( ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_636,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_500])).

cnf(c_637,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_636])).

cnf(c_2426,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2670,plain,
    ( ~ m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2426])).

cnf(c_2660,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK2))
    | k4_xboole_0(X0,u1_struct_0(sK2)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3327,plain,
    ( ~ r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2))
    | k4_xboole_0(sK0(sK2,sK3),u1_struct_0(sK2)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2660])).

cnf(c_6246,plain,
    ( k4_xboole_0(sK0(sK2,sK3),u1_struct_0(sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6230,c_23,c_21,c_637,c_2670,c_3327])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2231,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2234,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2231,c_3])).

cnf(c_3204,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2234,c_2229])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_201,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_202,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_201])).

cnf(c_246,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_202])).

cnf(c_2225,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_246])).

cnf(c_4464,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X1,X0,X1) ),
    inference(superposition,[status(thm)],[c_3204,c_2225])).

cnf(c_19773,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = k4_xboole_0(sK0(sK2,sK3),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6246,c_4464])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2232,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6248,plain,
    ( r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6246,c_2232])).

cnf(c_2230,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_19,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_352,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_353,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_357,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_353,c_26,c_24])).

cnf(c_2224,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_3222,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2230,c_2224])).

cnf(c_4169,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,sK3)) = sK3
    | v2_tex_2(X0,sK2) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2226,c_3222])).

cnf(c_9,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,negated_conjecture,
    ( v1_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_344,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_346,plain,
    ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_344,c_24,c_23])).

cnf(c_4173,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)) = sK3
    | v2_tex_2(X0,sK2) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4169,c_346])).

cnf(c_6295,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = sK3
    | v2_tex_2(sK0(sK2,sK3),sK2) != iProver_top
    | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6248,c_4173])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_32,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_11,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,sK0(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_535,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,sK0(X1,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_536,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0,sK0(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_614,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0,sK0(sK2,X0))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_536])).

cnf(c_615,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK3,sK0(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_614])).

cnf(c_616,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK3,sK0(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_12,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_517,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_518,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(sK0(sK2,X0),sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_625,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(sK0(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_518])).

cnf(c_626,plain,
    ( v2_tex_2(sK0(sK2,sK3),sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_627,plain,
    ( v2_tex_2(sK0(sK2,sK3),sK2) = iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_6405,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6295,c_30,c_32,c_616,c_627])).

cnf(c_19787,plain,
    ( k4_xboole_0(sK0(sK2,sK3),k1_xboole_0) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_19773,c_6405])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_19960,plain,
    ( sK0(sK2,sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_19787,c_2])).

cnf(c_10,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_553,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0(X1,X0) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_554,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK0(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_606,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK0(sK2,X0) != X0
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_554])).

cnf(c_607,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK0(sK2,sK3) != sK3 ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19960,c_607,c_21,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:42:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.16/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.16/1.49  
% 7.16/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.16/1.49  
% 7.16/1.49  ------  iProver source info
% 7.16/1.49  
% 7.16/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.16/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.16/1.49  git: non_committed_changes: false
% 7.16/1.49  git: last_make_outside_of_git: false
% 7.16/1.49  
% 7.16/1.49  ------ 
% 7.16/1.49  
% 7.16/1.49  ------ Input Options
% 7.16/1.49  
% 7.16/1.49  --out_options                           all
% 7.16/1.49  --tptp_safe_out                         true
% 7.16/1.49  --problem_path                          ""
% 7.16/1.49  --include_path                          ""
% 7.16/1.49  --clausifier                            res/vclausify_rel
% 7.16/1.49  --clausifier_options                    ""
% 7.16/1.49  --stdin                                 false
% 7.16/1.49  --stats_out                             all
% 7.16/1.49  
% 7.16/1.49  ------ General Options
% 7.16/1.49  
% 7.16/1.49  --fof                                   false
% 7.16/1.49  --time_out_real                         305.
% 7.16/1.49  --time_out_virtual                      -1.
% 7.16/1.49  --symbol_type_check                     false
% 7.16/1.49  --clausify_out                          false
% 7.16/1.49  --sig_cnt_out                           false
% 7.16/1.49  --trig_cnt_out                          false
% 7.16/1.49  --trig_cnt_out_tolerance                1.
% 7.16/1.49  --trig_cnt_out_sk_spl                   false
% 7.16/1.49  --abstr_cl_out                          false
% 7.16/1.49  
% 7.16/1.49  ------ Global Options
% 7.16/1.49  
% 7.16/1.49  --schedule                              default
% 7.16/1.49  --add_important_lit                     false
% 7.16/1.49  --prop_solver_per_cl                    1000
% 7.16/1.49  --min_unsat_core                        false
% 7.16/1.49  --soft_assumptions                      false
% 7.16/1.49  --soft_lemma_size                       3
% 7.16/1.49  --prop_impl_unit_size                   0
% 7.16/1.49  --prop_impl_unit                        []
% 7.16/1.49  --share_sel_clauses                     true
% 7.16/1.49  --reset_solvers                         false
% 7.16/1.49  --bc_imp_inh                            [conj_cone]
% 7.16/1.49  --conj_cone_tolerance                   3.
% 7.16/1.49  --extra_neg_conj                        none
% 7.16/1.49  --large_theory_mode                     true
% 7.16/1.49  --prolific_symb_bound                   200
% 7.16/1.49  --lt_threshold                          2000
% 7.16/1.49  --clause_weak_htbl                      true
% 7.16/1.49  --gc_record_bc_elim                     false
% 7.16/1.49  
% 7.16/1.49  ------ Preprocessing Options
% 7.16/1.49  
% 7.16/1.49  --preprocessing_flag                    true
% 7.16/1.49  --time_out_prep_mult                    0.1
% 7.16/1.49  --splitting_mode                        input
% 7.16/1.49  --splitting_grd                         true
% 7.16/1.49  --splitting_cvd                         false
% 7.16/1.49  --splitting_cvd_svl                     false
% 7.16/1.49  --splitting_nvd                         32
% 7.16/1.49  --sub_typing                            true
% 7.16/1.49  --prep_gs_sim                           true
% 7.16/1.49  --prep_unflatten                        true
% 7.16/1.49  --prep_res_sim                          true
% 7.16/1.49  --prep_upred                            true
% 7.16/1.49  --prep_sem_filter                       exhaustive
% 7.16/1.49  --prep_sem_filter_out                   false
% 7.16/1.49  --pred_elim                             true
% 7.16/1.49  --res_sim_input                         true
% 7.16/1.49  --eq_ax_congr_red                       true
% 7.16/1.49  --pure_diseq_elim                       true
% 7.16/1.49  --brand_transform                       false
% 7.16/1.49  --non_eq_to_eq                          false
% 7.16/1.49  --prep_def_merge                        true
% 7.16/1.49  --prep_def_merge_prop_impl              false
% 7.16/1.49  --prep_def_merge_mbd                    true
% 7.16/1.49  --prep_def_merge_tr_red                 false
% 7.16/1.49  --prep_def_merge_tr_cl                  false
% 7.16/1.49  --smt_preprocessing                     true
% 7.16/1.49  --smt_ac_axioms                         fast
% 7.16/1.49  --preprocessed_out                      false
% 7.16/1.49  --preprocessed_stats                    false
% 7.16/1.49  
% 7.16/1.49  ------ Abstraction refinement Options
% 7.16/1.49  
% 7.16/1.49  --abstr_ref                             []
% 7.16/1.49  --abstr_ref_prep                        false
% 7.16/1.49  --abstr_ref_until_sat                   false
% 7.16/1.49  --abstr_ref_sig_restrict                funpre
% 7.16/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.16/1.49  --abstr_ref_under                       []
% 7.16/1.49  
% 7.16/1.49  ------ SAT Options
% 7.16/1.49  
% 7.16/1.49  --sat_mode                              false
% 7.16/1.49  --sat_fm_restart_options                ""
% 7.16/1.49  --sat_gr_def                            false
% 7.16/1.49  --sat_epr_types                         true
% 7.16/1.49  --sat_non_cyclic_types                  false
% 7.16/1.49  --sat_finite_models                     false
% 7.16/1.49  --sat_fm_lemmas                         false
% 7.16/1.49  --sat_fm_prep                           false
% 7.16/1.49  --sat_fm_uc_incr                        true
% 7.16/1.49  --sat_out_model                         small
% 7.16/1.49  --sat_out_clauses                       false
% 7.16/1.49  
% 7.16/1.49  ------ QBF Options
% 7.16/1.49  
% 7.16/1.49  --qbf_mode                              false
% 7.16/1.49  --qbf_elim_univ                         false
% 7.16/1.49  --qbf_dom_inst                          none
% 7.16/1.49  --qbf_dom_pre_inst                      false
% 7.16/1.49  --qbf_sk_in                             false
% 7.16/1.49  --qbf_pred_elim                         true
% 7.16/1.49  --qbf_split                             512
% 7.16/1.49  
% 7.16/1.49  ------ BMC1 Options
% 7.16/1.49  
% 7.16/1.49  --bmc1_incremental                      false
% 7.16/1.49  --bmc1_axioms                           reachable_all
% 7.16/1.49  --bmc1_min_bound                        0
% 7.16/1.49  --bmc1_max_bound                        -1
% 7.16/1.49  --bmc1_max_bound_default                -1
% 7.16/1.49  --bmc1_symbol_reachability              true
% 7.16/1.49  --bmc1_property_lemmas                  false
% 7.16/1.49  --bmc1_k_induction                      false
% 7.16/1.49  --bmc1_non_equiv_states                 false
% 7.16/1.49  --bmc1_deadlock                         false
% 7.16/1.49  --bmc1_ucm                              false
% 7.16/1.49  --bmc1_add_unsat_core                   none
% 7.16/1.49  --bmc1_unsat_core_children              false
% 7.16/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.16/1.49  --bmc1_out_stat                         full
% 7.16/1.49  --bmc1_ground_init                      false
% 7.16/1.49  --bmc1_pre_inst_next_state              false
% 7.16/1.49  --bmc1_pre_inst_state                   false
% 7.16/1.49  --bmc1_pre_inst_reach_state             false
% 7.16/1.49  --bmc1_out_unsat_core                   false
% 7.16/1.49  --bmc1_aig_witness_out                  false
% 7.16/1.49  --bmc1_verbose                          false
% 7.16/1.49  --bmc1_dump_clauses_tptp                false
% 7.16/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.16/1.49  --bmc1_dump_file                        -
% 7.16/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.16/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.16/1.49  --bmc1_ucm_extend_mode                  1
% 7.16/1.49  --bmc1_ucm_init_mode                    2
% 7.16/1.49  --bmc1_ucm_cone_mode                    none
% 7.16/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.16/1.49  --bmc1_ucm_relax_model                  4
% 7.16/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.16/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.16/1.49  --bmc1_ucm_layered_model                none
% 7.16/1.49  --bmc1_ucm_max_lemma_size               10
% 7.16/1.49  
% 7.16/1.49  ------ AIG Options
% 7.16/1.49  
% 7.16/1.49  --aig_mode                              false
% 7.16/1.49  
% 7.16/1.49  ------ Instantiation Options
% 7.16/1.49  
% 7.16/1.49  --instantiation_flag                    true
% 7.16/1.49  --inst_sos_flag                         true
% 7.16/1.49  --inst_sos_phase                        true
% 7.16/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.16/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.16/1.49  --inst_lit_sel_side                     num_symb
% 7.16/1.49  --inst_solver_per_active                1400
% 7.16/1.49  --inst_solver_calls_frac                1.
% 7.16/1.49  --inst_passive_queue_type               priority_queues
% 7.16/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.16/1.49  --inst_passive_queues_freq              [25;2]
% 7.16/1.49  --inst_dismatching                      true
% 7.16/1.49  --inst_eager_unprocessed_to_passive     true
% 7.16/1.49  --inst_prop_sim_given                   true
% 7.16/1.49  --inst_prop_sim_new                     false
% 7.16/1.49  --inst_subs_new                         false
% 7.16/1.49  --inst_eq_res_simp                      false
% 7.16/1.49  --inst_subs_given                       false
% 7.16/1.49  --inst_orphan_elimination               true
% 7.16/1.49  --inst_learning_loop_flag               true
% 7.16/1.49  --inst_learning_start                   3000
% 7.16/1.49  --inst_learning_factor                  2
% 7.16/1.49  --inst_start_prop_sim_after_learn       3
% 7.16/1.49  --inst_sel_renew                        solver
% 7.16/1.49  --inst_lit_activity_flag                true
% 7.16/1.49  --inst_restr_to_given                   false
% 7.16/1.49  --inst_activity_threshold               500
% 7.16/1.49  --inst_out_proof                        true
% 7.16/1.49  
% 7.16/1.49  ------ Resolution Options
% 7.16/1.49  
% 7.16/1.49  --resolution_flag                       true
% 7.16/1.49  --res_lit_sel                           adaptive
% 7.16/1.49  --res_lit_sel_side                      none
% 7.16/1.49  --res_ordering                          kbo
% 7.16/1.49  --res_to_prop_solver                    active
% 7.16/1.49  --res_prop_simpl_new                    false
% 7.16/1.49  --res_prop_simpl_given                  true
% 7.16/1.49  --res_passive_queue_type                priority_queues
% 7.16/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.16/1.49  --res_passive_queues_freq               [15;5]
% 7.16/1.49  --res_forward_subs                      full
% 7.16/1.49  --res_backward_subs                     full
% 7.16/1.49  --res_forward_subs_resolution           true
% 7.16/1.49  --res_backward_subs_resolution          true
% 7.16/1.49  --res_orphan_elimination                true
% 7.16/1.49  --res_time_limit                        2.
% 7.16/1.49  --res_out_proof                         true
% 7.16/1.49  
% 7.16/1.49  ------ Superposition Options
% 7.16/1.49  
% 7.16/1.49  --superposition_flag                    true
% 7.16/1.49  --sup_passive_queue_type                priority_queues
% 7.16/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.16/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.16/1.49  --demod_completeness_check              fast
% 7.16/1.49  --demod_use_ground                      true
% 7.16/1.49  --sup_to_prop_solver                    passive
% 7.16/1.49  --sup_prop_simpl_new                    true
% 7.16/1.49  --sup_prop_simpl_given                  true
% 7.16/1.49  --sup_fun_splitting                     true
% 7.16/1.49  --sup_smt_interval                      50000
% 7.16/1.49  
% 7.16/1.49  ------ Superposition Simplification Setup
% 7.16/1.49  
% 7.16/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.16/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.16/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.16/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.16/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.16/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.16/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.16/1.49  --sup_immed_triv                        [TrivRules]
% 7.16/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.16/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.16/1.49  --sup_immed_bw_main                     []
% 7.16/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.16/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.16/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.16/1.49  --sup_input_bw                          []
% 7.16/1.49  
% 7.16/1.49  ------ Combination Options
% 7.16/1.49  
% 7.16/1.49  --comb_res_mult                         3
% 7.16/1.49  --comb_sup_mult                         2
% 7.16/1.49  --comb_inst_mult                        10
% 7.16/1.49  
% 7.16/1.49  ------ Debug Options
% 7.16/1.49  
% 7.16/1.49  --dbg_backtrace                         false
% 7.16/1.49  --dbg_dump_prop_clauses                 false
% 7.16/1.49  --dbg_dump_prop_clauses_file            -
% 7.16/1.49  --dbg_out_stat                          false
% 7.16/1.49  ------ Parsing...
% 7.16/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.16/1.49  
% 7.16/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.16/1.49  
% 7.16/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.16/1.49  
% 7.16/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.16/1.49  ------ Proving...
% 7.16/1.49  ------ Problem Properties 
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  clauses                                 22
% 7.16/1.49  conjectures                             3
% 7.16/1.49  EPR                                     2
% 7.16/1.49  Horn                                    17
% 7.16/1.49  unary                                   7
% 7.16/1.49  binary                                  5
% 7.16/1.49  lits                                    56
% 7.16/1.49  lits eq                                 10
% 7.16/1.49  fd_pure                                 0
% 7.16/1.49  fd_pseudo                               0
% 7.16/1.49  fd_cond                                 0
% 7.16/1.49  fd_pseudo_cond                          1
% 7.16/1.49  AC symbols                              0
% 7.16/1.49  
% 7.16/1.49  ------ Schedule dynamic 5 is on 
% 7.16/1.49  
% 7.16/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  ------ 
% 7.16/1.49  Current options:
% 7.16/1.49  ------ 
% 7.16/1.49  
% 7.16/1.49  ------ Input Options
% 7.16/1.49  
% 7.16/1.49  --out_options                           all
% 7.16/1.49  --tptp_safe_out                         true
% 7.16/1.49  --problem_path                          ""
% 7.16/1.49  --include_path                          ""
% 7.16/1.49  --clausifier                            res/vclausify_rel
% 7.16/1.49  --clausifier_options                    ""
% 7.16/1.49  --stdin                                 false
% 7.16/1.49  --stats_out                             all
% 7.16/1.49  
% 7.16/1.49  ------ General Options
% 7.16/1.49  
% 7.16/1.49  --fof                                   false
% 7.16/1.49  --time_out_real                         305.
% 7.16/1.49  --time_out_virtual                      -1.
% 7.16/1.49  --symbol_type_check                     false
% 7.16/1.49  --clausify_out                          false
% 7.16/1.49  --sig_cnt_out                           false
% 7.16/1.49  --trig_cnt_out                          false
% 7.16/1.49  --trig_cnt_out_tolerance                1.
% 7.16/1.49  --trig_cnt_out_sk_spl                   false
% 7.16/1.49  --abstr_cl_out                          false
% 7.16/1.49  
% 7.16/1.49  ------ Global Options
% 7.16/1.49  
% 7.16/1.49  --schedule                              default
% 7.16/1.49  --add_important_lit                     false
% 7.16/1.49  --prop_solver_per_cl                    1000
% 7.16/1.49  --min_unsat_core                        false
% 7.16/1.49  --soft_assumptions                      false
% 7.16/1.49  --soft_lemma_size                       3
% 7.16/1.49  --prop_impl_unit_size                   0
% 7.16/1.49  --prop_impl_unit                        []
% 7.16/1.49  --share_sel_clauses                     true
% 7.16/1.49  --reset_solvers                         false
% 7.16/1.49  --bc_imp_inh                            [conj_cone]
% 7.16/1.49  --conj_cone_tolerance                   3.
% 7.16/1.49  --extra_neg_conj                        none
% 7.16/1.49  --large_theory_mode                     true
% 7.16/1.49  --prolific_symb_bound                   200
% 7.16/1.49  --lt_threshold                          2000
% 7.16/1.49  --clause_weak_htbl                      true
% 7.16/1.49  --gc_record_bc_elim                     false
% 7.16/1.49  
% 7.16/1.49  ------ Preprocessing Options
% 7.16/1.49  
% 7.16/1.49  --preprocessing_flag                    true
% 7.16/1.49  --time_out_prep_mult                    0.1
% 7.16/1.49  --splitting_mode                        input
% 7.16/1.49  --splitting_grd                         true
% 7.16/1.49  --splitting_cvd                         false
% 7.16/1.49  --splitting_cvd_svl                     false
% 7.16/1.49  --splitting_nvd                         32
% 7.16/1.49  --sub_typing                            true
% 7.16/1.49  --prep_gs_sim                           true
% 7.16/1.49  --prep_unflatten                        true
% 7.16/1.49  --prep_res_sim                          true
% 7.16/1.49  --prep_upred                            true
% 7.16/1.49  --prep_sem_filter                       exhaustive
% 7.16/1.49  --prep_sem_filter_out                   false
% 7.16/1.49  --pred_elim                             true
% 7.16/1.49  --res_sim_input                         true
% 7.16/1.49  --eq_ax_congr_red                       true
% 7.16/1.49  --pure_diseq_elim                       true
% 7.16/1.49  --brand_transform                       false
% 7.16/1.49  --non_eq_to_eq                          false
% 7.16/1.49  --prep_def_merge                        true
% 7.16/1.49  --prep_def_merge_prop_impl              false
% 7.16/1.49  --prep_def_merge_mbd                    true
% 7.16/1.49  --prep_def_merge_tr_red                 false
% 7.16/1.49  --prep_def_merge_tr_cl                  false
% 7.16/1.49  --smt_preprocessing                     true
% 7.16/1.49  --smt_ac_axioms                         fast
% 7.16/1.49  --preprocessed_out                      false
% 7.16/1.49  --preprocessed_stats                    false
% 7.16/1.49  
% 7.16/1.49  ------ Abstraction refinement Options
% 7.16/1.49  
% 7.16/1.49  --abstr_ref                             []
% 7.16/1.49  --abstr_ref_prep                        false
% 7.16/1.49  --abstr_ref_until_sat                   false
% 7.16/1.49  --abstr_ref_sig_restrict                funpre
% 7.16/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.16/1.49  --abstr_ref_under                       []
% 7.16/1.49  
% 7.16/1.49  ------ SAT Options
% 7.16/1.49  
% 7.16/1.49  --sat_mode                              false
% 7.16/1.49  --sat_fm_restart_options                ""
% 7.16/1.49  --sat_gr_def                            false
% 7.16/1.49  --sat_epr_types                         true
% 7.16/1.49  --sat_non_cyclic_types                  false
% 7.16/1.49  --sat_finite_models                     false
% 7.16/1.49  --sat_fm_lemmas                         false
% 7.16/1.49  --sat_fm_prep                           false
% 7.16/1.49  --sat_fm_uc_incr                        true
% 7.16/1.49  --sat_out_model                         small
% 7.16/1.49  --sat_out_clauses                       false
% 7.16/1.49  
% 7.16/1.49  ------ QBF Options
% 7.16/1.49  
% 7.16/1.49  --qbf_mode                              false
% 7.16/1.49  --qbf_elim_univ                         false
% 7.16/1.49  --qbf_dom_inst                          none
% 7.16/1.49  --qbf_dom_pre_inst                      false
% 7.16/1.49  --qbf_sk_in                             false
% 7.16/1.49  --qbf_pred_elim                         true
% 7.16/1.49  --qbf_split                             512
% 7.16/1.49  
% 7.16/1.49  ------ BMC1 Options
% 7.16/1.49  
% 7.16/1.49  --bmc1_incremental                      false
% 7.16/1.49  --bmc1_axioms                           reachable_all
% 7.16/1.49  --bmc1_min_bound                        0
% 7.16/1.49  --bmc1_max_bound                        -1
% 7.16/1.49  --bmc1_max_bound_default                -1
% 7.16/1.49  --bmc1_symbol_reachability              true
% 7.16/1.49  --bmc1_property_lemmas                  false
% 7.16/1.49  --bmc1_k_induction                      false
% 7.16/1.49  --bmc1_non_equiv_states                 false
% 7.16/1.49  --bmc1_deadlock                         false
% 7.16/1.49  --bmc1_ucm                              false
% 7.16/1.49  --bmc1_add_unsat_core                   none
% 7.16/1.49  --bmc1_unsat_core_children              false
% 7.16/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.16/1.49  --bmc1_out_stat                         full
% 7.16/1.49  --bmc1_ground_init                      false
% 7.16/1.49  --bmc1_pre_inst_next_state              false
% 7.16/1.49  --bmc1_pre_inst_state                   false
% 7.16/1.49  --bmc1_pre_inst_reach_state             false
% 7.16/1.49  --bmc1_out_unsat_core                   false
% 7.16/1.49  --bmc1_aig_witness_out                  false
% 7.16/1.49  --bmc1_verbose                          false
% 7.16/1.49  --bmc1_dump_clauses_tptp                false
% 7.16/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.16/1.49  --bmc1_dump_file                        -
% 7.16/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.16/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.16/1.49  --bmc1_ucm_extend_mode                  1
% 7.16/1.49  --bmc1_ucm_init_mode                    2
% 7.16/1.49  --bmc1_ucm_cone_mode                    none
% 7.16/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.16/1.49  --bmc1_ucm_relax_model                  4
% 7.16/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.16/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.16/1.49  --bmc1_ucm_layered_model                none
% 7.16/1.49  --bmc1_ucm_max_lemma_size               10
% 7.16/1.49  
% 7.16/1.49  ------ AIG Options
% 7.16/1.49  
% 7.16/1.49  --aig_mode                              false
% 7.16/1.49  
% 7.16/1.49  ------ Instantiation Options
% 7.16/1.49  
% 7.16/1.49  --instantiation_flag                    true
% 7.16/1.49  --inst_sos_flag                         true
% 7.16/1.49  --inst_sos_phase                        true
% 7.16/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.16/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.16/1.49  --inst_lit_sel_side                     none
% 7.16/1.49  --inst_solver_per_active                1400
% 7.16/1.49  --inst_solver_calls_frac                1.
% 7.16/1.49  --inst_passive_queue_type               priority_queues
% 7.16/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.16/1.49  --inst_passive_queues_freq              [25;2]
% 7.16/1.49  --inst_dismatching                      true
% 7.16/1.49  --inst_eager_unprocessed_to_passive     true
% 7.16/1.49  --inst_prop_sim_given                   true
% 7.16/1.49  --inst_prop_sim_new                     false
% 7.16/1.49  --inst_subs_new                         false
% 7.16/1.49  --inst_eq_res_simp                      false
% 7.16/1.49  --inst_subs_given                       false
% 7.16/1.49  --inst_orphan_elimination               true
% 7.16/1.49  --inst_learning_loop_flag               true
% 7.16/1.49  --inst_learning_start                   3000
% 7.16/1.49  --inst_learning_factor                  2
% 7.16/1.49  --inst_start_prop_sim_after_learn       3
% 7.16/1.49  --inst_sel_renew                        solver
% 7.16/1.49  --inst_lit_activity_flag                true
% 7.16/1.49  --inst_restr_to_given                   false
% 7.16/1.49  --inst_activity_threshold               500
% 7.16/1.49  --inst_out_proof                        true
% 7.16/1.49  
% 7.16/1.49  ------ Resolution Options
% 7.16/1.49  
% 7.16/1.49  --resolution_flag                       false
% 7.16/1.49  --res_lit_sel                           adaptive
% 7.16/1.49  --res_lit_sel_side                      none
% 7.16/1.49  --res_ordering                          kbo
% 7.16/1.49  --res_to_prop_solver                    active
% 7.16/1.49  --res_prop_simpl_new                    false
% 7.16/1.49  --res_prop_simpl_given                  true
% 7.16/1.49  --res_passive_queue_type                priority_queues
% 7.16/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.16/1.49  --res_passive_queues_freq               [15;5]
% 7.16/1.49  --res_forward_subs                      full
% 7.16/1.49  --res_backward_subs                     full
% 7.16/1.49  --res_forward_subs_resolution           true
% 7.16/1.49  --res_backward_subs_resolution          true
% 7.16/1.49  --res_orphan_elimination                true
% 7.16/1.49  --res_time_limit                        2.
% 7.16/1.49  --res_out_proof                         true
% 7.16/1.49  
% 7.16/1.49  ------ Superposition Options
% 7.16/1.49  
% 7.16/1.49  --superposition_flag                    true
% 7.16/1.49  --sup_passive_queue_type                priority_queues
% 7.16/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.16/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.16/1.49  --demod_completeness_check              fast
% 7.16/1.49  --demod_use_ground                      true
% 7.16/1.49  --sup_to_prop_solver                    passive
% 7.16/1.49  --sup_prop_simpl_new                    true
% 7.16/1.49  --sup_prop_simpl_given                  true
% 7.16/1.49  --sup_fun_splitting                     true
% 7.16/1.49  --sup_smt_interval                      50000
% 7.16/1.49  
% 7.16/1.49  ------ Superposition Simplification Setup
% 7.16/1.49  
% 7.16/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.16/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.16/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.16/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.16/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.16/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.16/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.16/1.49  --sup_immed_triv                        [TrivRules]
% 7.16/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.16/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.16/1.49  --sup_immed_bw_main                     []
% 7.16/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.16/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.16/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.16/1.49  --sup_input_bw                          []
% 7.16/1.49  
% 7.16/1.49  ------ Combination Options
% 7.16/1.49  
% 7.16/1.49  --comb_res_mult                         3
% 7.16/1.49  --comb_sup_mult                         2
% 7.16/1.49  --comb_inst_mult                        10
% 7.16/1.49  
% 7.16/1.49  ------ Debug Options
% 7.16/1.49  
% 7.16/1.49  --dbg_backtrace                         false
% 7.16/1.49  --dbg_dump_prop_clauses                 false
% 7.16/1.49  --dbg_dump_prop_clauses_file            -
% 7.16/1.49  --dbg_out_stat                          false
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  ------ Proving...
% 7.16/1.49  
% 7.16/1.49  
% 7.16/1.49  % SZS status Theorem for theBenchmark.p
% 7.16/1.49  
% 7.16/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.16/1.49  
% 7.16/1.49  fof(f11,conjecture,(
% 7.16/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f12,negated_conjecture,(
% 7.16/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 7.16/1.49    inference(negated_conjecture,[],[f11])).
% 7.16/1.49  
% 7.16/1.49  fof(f19,plain,(
% 7.16/1.49    ? [X0] : (? [X1] : ((~v3_tex_2(X1,X0) & (v2_tex_2(X1,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.16/1.49    inference(ennf_transformation,[],[f12])).
% 7.16/1.49  
% 7.16/1.49  fof(f20,plain,(
% 7.16/1.49    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.16/1.49    inference(flattening,[],[f19])).
% 7.16/1.49  
% 7.16/1.49  fof(f34,plain,(
% 7.16/1.49    ( ! [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_tex_2(sK3,X0) & v2_tex_2(sK3,X0) & v1_tops_1(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.16/1.49    introduced(choice_axiom,[])).
% 7.16/1.49  
% 7.16/1.49  fof(f33,plain,(
% 7.16/1.49    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v3_tex_2(X1,sK2) & v2_tex_2(X1,sK2) & v1_tops_1(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 7.16/1.49    introduced(choice_axiom,[])).
% 7.16/1.49  
% 7.16/1.49  fof(f35,plain,(
% 7.16/1.49    (~v3_tex_2(sK3,sK2) & v2_tex_2(sK3,sK2) & v1_tops_1(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 7.16/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f34,f33])).
% 7.16/1.49  
% 7.16/1.49  fof(f60,plain,(
% 7.16/1.49    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 7.16/1.49    inference(cnf_transformation,[],[f35])).
% 7.16/1.49  
% 7.16/1.49  fof(f9,axiom,(
% 7.16/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f15,plain,(
% 7.16/1.49    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.16/1.49    inference(ennf_transformation,[],[f9])).
% 7.16/1.49  
% 7.16/1.49  fof(f16,plain,(
% 7.16/1.49    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.16/1.49    inference(flattening,[],[f15])).
% 7.16/1.49  
% 7.16/1.49  fof(f24,plain,(
% 7.16/1.49    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.16/1.49    inference(nnf_transformation,[],[f16])).
% 7.16/1.49  
% 7.16/1.49  fof(f25,plain,(
% 7.16/1.49    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.16/1.49    inference(flattening,[],[f24])).
% 7.16/1.49  
% 7.16/1.49  fof(f26,plain,(
% 7.16/1.49    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.16/1.49    inference(rectify,[],[f25])).
% 7.16/1.49  
% 7.16/1.49  fof(f27,plain,(
% 7.16/1.49    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.16/1.49    introduced(choice_axiom,[])).
% 7.16/1.49  
% 7.16/1.49  fof(f28,plain,(
% 7.16/1.49    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.16/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 7.16/1.49  
% 7.16/1.49  fof(f49,plain,(
% 7.16/1.49    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f28])).
% 7.16/1.49  
% 7.16/1.49  fof(f59,plain,(
% 7.16/1.49    l1_pre_topc(sK2)),
% 7.16/1.49    inference(cnf_transformation,[],[f35])).
% 7.16/1.49  
% 7.16/1.49  fof(f7,axiom,(
% 7.16/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f22,plain,(
% 7.16/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.16/1.49    inference(nnf_transformation,[],[f7])).
% 7.16/1.49  
% 7.16/1.49  fof(f43,plain,(
% 7.16/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.16/1.49    inference(cnf_transformation,[],[f22])).
% 7.16/1.49  
% 7.16/1.49  fof(f1,axiom,(
% 7.16/1.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f21,plain,(
% 7.16/1.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 7.16/1.49    inference(nnf_transformation,[],[f1])).
% 7.16/1.49  
% 7.16/1.49  fof(f37,plain,(
% 7.16/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f21])).
% 7.16/1.49  
% 7.16/1.49  fof(f62,plain,(
% 7.16/1.49    v2_tex_2(sK3,sK2)),
% 7.16/1.49    inference(cnf_transformation,[],[f35])).
% 7.16/1.49  
% 7.16/1.49  fof(f63,plain,(
% 7.16/1.49    ~v3_tex_2(sK3,sK2)),
% 7.16/1.49    inference(cnf_transformation,[],[f35])).
% 7.16/1.49  
% 7.16/1.49  fof(f5,axiom,(
% 7.16/1.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f41,plain,(
% 7.16/1.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 7.16/1.49    inference(cnf_transformation,[],[f5])).
% 7.16/1.49  
% 7.16/1.49  fof(f4,axiom,(
% 7.16/1.49    ! [X0] : k2_subset_1(X0) = X0),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f40,plain,(
% 7.16/1.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.16/1.49    inference(cnf_transformation,[],[f4])).
% 7.16/1.49  
% 7.16/1.49  fof(f6,axiom,(
% 7.16/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f13,plain,(
% 7.16/1.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.16/1.49    inference(ennf_transformation,[],[f6])).
% 7.16/1.49  
% 7.16/1.49  fof(f42,plain,(
% 7.16/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.16/1.49    inference(cnf_transformation,[],[f13])).
% 7.16/1.49  
% 7.16/1.49  fof(f3,axiom,(
% 7.16/1.49    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f39,plain,(
% 7.16/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f3])).
% 7.16/1.49  
% 7.16/1.49  fof(f64,plain,(
% 7.16/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.16/1.49    inference(definition_unfolding,[],[f42,f39])).
% 7.16/1.49  
% 7.16/1.49  fof(f44,plain,(
% 7.16/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f22])).
% 7.16/1.49  
% 7.16/1.49  fof(f36,plain,(
% 7.16/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.16/1.49    inference(cnf_transformation,[],[f21])).
% 7.16/1.49  
% 7.16/1.49  fof(f10,axiom,(
% 7.16/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f17,plain,(
% 7.16/1.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.16/1.49    inference(ennf_transformation,[],[f10])).
% 7.16/1.49  
% 7.16/1.49  fof(f18,plain,(
% 7.16/1.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.16/1.49    inference(flattening,[],[f17])).
% 7.16/1.49  
% 7.16/1.49  fof(f29,plain,(
% 7.16/1.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.16/1.49    inference(nnf_transformation,[],[f18])).
% 7.16/1.49  
% 7.16/1.49  fof(f30,plain,(
% 7.16/1.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.16/1.49    inference(rectify,[],[f29])).
% 7.16/1.49  
% 7.16/1.49  fof(f31,plain,(
% 7.16/1.49    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.16/1.49    introduced(choice_axiom,[])).
% 7.16/1.49  
% 7.16/1.49  fof(f32,plain,(
% 7.16/1.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.16/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 7.16/1.49  
% 7.16/1.49  fof(f53,plain,(
% 7.16/1.49    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f32])).
% 7.16/1.49  
% 7.16/1.49  fof(f58,plain,(
% 7.16/1.49    v2_pre_topc(sK2)),
% 7.16/1.49    inference(cnf_transformation,[],[f35])).
% 7.16/1.49  
% 7.16/1.49  fof(f57,plain,(
% 7.16/1.49    ~v2_struct_0(sK2)),
% 7.16/1.49    inference(cnf_transformation,[],[f35])).
% 7.16/1.49  
% 7.16/1.49  fof(f8,axiom,(
% 7.16/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f14,plain,(
% 7.16/1.49    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.16/1.49    inference(ennf_transformation,[],[f8])).
% 7.16/1.49  
% 7.16/1.49  fof(f23,plain,(
% 7.16/1.49    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.16/1.49    inference(nnf_transformation,[],[f14])).
% 7.16/1.49  
% 7.16/1.49  fof(f45,plain,(
% 7.16/1.49    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f23])).
% 7.16/1.49  
% 7.16/1.49  fof(f61,plain,(
% 7.16/1.49    v1_tops_1(sK3,sK2)),
% 7.16/1.49    inference(cnf_transformation,[],[f35])).
% 7.16/1.49  
% 7.16/1.49  fof(f51,plain,(
% 7.16/1.49    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK0(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f28])).
% 7.16/1.49  
% 7.16/1.49  fof(f50,plain,(
% 7.16/1.49    ( ! [X0,X1] : (v3_tex_2(X1,X0) | v2_tex_2(sK0(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.16/1.49    inference(cnf_transformation,[],[f28])).
% 7.16/1.49  
% 7.16/1.49  fof(f2,axiom,(
% 7.16/1.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.16/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.16/1.49  
% 7.16/1.49  fof(f38,plain,(
% 7.16/1.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.16/1.49    inference(cnf_transformation,[],[f2])).
% 7.16/1.49  
% 7.16/1.49  fof(f52,plain,(
% 7.16/1.49    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK0(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.16/1.50    inference(cnf_transformation,[],[f28])).
% 7.16/1.50  
% 7.16/1.50  cnf(c_23,negated_conjecture,
% 7.16/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 7.16/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_2226,plain,
% 7.16/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_13,plain,
% 7.16/1.50      ( ~ v2_tex_2(X0,X1)
% 7.16/1.50      | v3_tex_2(X0,X1)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.16/1.50      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.16/1.50      | ~ l1_pre_topc(X1) ),
% 7.16/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_24,negated_conjecture,
% 7.16/1.50      ( l1_pre_topc(sK2) ),
% 7.16/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_499,plain,
% 7.16/1.50      ( ~ v2_tex_2(X0,X1)
% 7.16/1.50      | v3_tex_2(X0,X1)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.16/1.50      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.16/1.50      | sK2 != X1 ),
% 7.16/1.50      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_500,plain,
% 7.16/1.50      ( ~ v2_tex_2(X0,sK2)
% 7.16/1.50      | v3_tex_2(X0,sK2)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.16/1.50      | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 7.16/1.50      inference(unflattening,[status(thm)],[c_499]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_2218,plain,
% 7.16/1.50      ( v2_tex_2(X0,sK2) != iProver_top
% 7.16/1.50      | v3_tex_2(X0,sK2) = iProver_top
% 7.16/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.16/1.50      | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_500]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_7,plain,
% 7.16/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.16/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_2229,plain,
% 7.16/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.16/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_3203,plain,
% 7.16/1.50      ( v2_tex_2(X0,sK2) != iProver_top
% 7.16/1.50      | v3_tex_2(X0,sK2) = iProver_top
% 7.16/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.16/1.50      | r1_tarski(sK0(sK2,X0),u1_struct_0(sK2)) = iProver_top ),
% 7.16/1.50      inference(superposition,[status(thm)],[c_2218,c_2229]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_0,plain,
% 7.16/1.50      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.16/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_2233,plain,
% 7.16/1.50      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 7.16/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_5218,plain,
% 7.16/1.50      ( k4_xboole_0(sK0(sK2,X0),u1_struct_0(sK2)) = k1_xboole_0
% 7.16/1.50      | v2_tex_2(X0,sK2) != iProver_top
% 7.16/1.50      | v3_tex_2(X0,sK2) = iProver_top
% 7.16/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 7.16/1.50      inference(superposition,[status(thm)],[c_3203,c_2233]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_6230,plain,
% 7.16/1.50      ( k4_xboole_0(sK0(sK2,sK3),u1_struct_0(sK2)) = k1_xboole_0
% 7.16/1.50      | v2_tex_2(sK3,sK2) != iProver_top
% 7.16/1.50      | v3_tex_2(sK3,sK2) = iProver_top ),
% 7.16/1.50      inference(superposition,[status(thm)],[c_2226,c_5218]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_21,negated_conjecture,
% 7.16/1.50      ( v2_tex_2(sK3,sK2) ),
% 7.16/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_20,negated_conjecture,
% 7.16/1.50      ( ~ v3_tex_2(sK3,sK2) ),
% 7.16/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_636,plain,
% 7.16/1.50      ( ~ v2_tex_2(X0,sK2)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.16/1.50      | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.16/1.50      | sK2 != sK2
% 7.16/1.50      | sK3 != X0 ),
% 7.16/1.50      inference(resolution_lifted,[status(thm)],[c_20,c_500]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_637,plain,
% 7.16/1.50      ( ~ v2_tex_2(sK3,sK2)
% 7.16/1.50      | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.16/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 7.16/1.50      inference(unflattening,[status(thm)],[c_636]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_2426,plain,
% 7.16/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.16/1.50      | r1_tarski(X0,u1_struct_0(sK2)) ),
% 7.16/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_2670,plain,
% 7.16/1.50      ( ~ m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.16/1.50      | r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2)) ),
% 7.16/1.50      inference(instantiation,[status(thm)],[c_2426]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_2660,plain,
% 7.16/1.50      ( ~ r1_tarski(X0,u1_struct_0(sK2))
% 7.16/1.50      | k4_xboole_0(X0,u1_struct_0(sK2)) = k1_xboole_0 ),
% 7.16/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_3327,plain,
% 7.16/1.50      ( ~ r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2))
% 7.16/1.50      | k4_xboole_0(sK0(sK2,sK3),u1_struct_0(sK2)) = k1_xboole_0 ),
% 7.16/1.50      inference(instantiation,[status(thm)],[c_2660]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_6246,plain,
% 7.16/1.50      ( k4_xboole_0(sK0(sK2,sK3),u1_struct_0(sK2)) = k1_xboole_0 ),
% 7.16/1.50      inference(global_propositional_subsumption,
% 7.16/1.50                [status(thm)],
% 7.16/1.50                [c_6230,c_23,c_21,c_637,c_2670,c_3327]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_4,plain,
% 7.16/1.50      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 7.16/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_2231,plain,
% 7.16/1.50      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_3,plain,
% 7.16/1.50      ( k2_subset_1(X0) = X0 ),
% 7.16/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_2234,plain,
% 7.16/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.16/1.50      inference(light_normalisation,[status(thm)],[c_2231,c_3]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_3204,plain,
% 7.16/1.50      ( r1_tarski(X0,X0) = iProver_top ),
% 7.16/1.50      inference(superposition,[status(thm)],[c_2234,c_2229]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_5,plain,
% 7.16/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.16/1.50      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 7.16/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_6,plain,
% 7.16/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.16/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_201,plain,
% 7.16/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.16/1.50      inference(prop_impl,[status(thm)],[c_6]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_202,plain,
% 7.16/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.16/1.50      inference(renaming,[status(thm)],[c_201]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_246,plain,
% 7.16/1.50      ( ~ r1_tarski(X0,X1)
% 7.16/1.50      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 7.16/1.50      inference(bin_hyper_res,[status(thm)],[c_5,c_202]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_2225,plain,
% 7.16/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 7.16/1.50      | r1_tarski(X1,X2) != iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_246]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_4464,plain,
% 7.16/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X1,X0,X1) ),
% 7.16/1.50      inference(superposition,[status(thm)],[c_3204,c_2225]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_19773,plain,
% 7.16/1.50      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = k4_xboole_0(sK0(sK2,sK3),k1_xboole_0) ),
% 7.16/1.50      inference(superposition,[status(thm)],[c_6246,c_4464]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_1,plain,
% 7.16/1.50      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.16/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_2232,plain,
% 7.16/1.50      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 7.16/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_6248,plain,
% 7.16/1.50      ( r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2)) = iProver_top ),
% 7.16/1.50      inference(superposition,[status(thm)],[c_6246,c_2232]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_2230,plain,
% 7.16/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.16/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_19,plain,
% 7.16/1.50      ( ~ v2_tex_2(X0,X1)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.16/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.16/1.50      | ~ r1_tarski(X2,X0)
% 7.16/1.50      | v2_struct_0(X1)
% 7.16/1.50      | ~ v2_pre_topc(X1)
% 7.16/1.50      | ~ l1_pre_topc(X1)
% 7.16/1.50      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
% 7.16/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_25,negated_conjecture,
% 7.16/1.50      ( v2_pre_topc(sK2) ),
% 7.16/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_352,plain,
% 7.16/1.50      ( ~ v2_tex_2(X0,X1)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.16/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.16/1.50      | ~ r1_tarski(X2,X0)
% 7.16/1.50      | v2_struct_0(X1)
% 7.16/1.50      | ~ l1_pre_topc(X1)
% 7.16/1.50      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
% 7.16/1.50      | sK2 != X1 ),
% 7.16/1.50      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_353,plain,
% 7.16/1.50      ( ~ v2_tex_2(X0,sK2)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.16/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.16/1.50      | ~ r1_tarski(X1,X0)
% 7.16/1.50      | v2_struct_0(sK2)
% 7.16/1.50      | ~ l1_pre_topc(sK2)
% 7.16/1.50      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
% 7.16/1.50      inference(unflattening,[status(thm)],[c_352]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_26,negated_conjecture,
% 7.16/1.50      ( ~ v2_struct_0(sK2) ),
% 7.16/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_357,plain,
% 7.16/1.50      ( ~ v2_tex_2(X0,sK2)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.16/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.16/1.50      | ~ r1_tarski(X1,X0)
% 7.16/1.50      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
% 7.16/1.50      inference(global_propositional_subsumption,
% 7.16/1.50                [status(thm)],
% 7.16/1.50                [c_353,c_26,c_24]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_2224,plain,
% 7.16/1.50      ( k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1
% 7.16/1.50      | v2_tex_2(X0,sK2) != iProver_top
% 7.16/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.16/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.16/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_357]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_3222,plain,
% 7.16/1.50      ( k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1
% 7.16/1.50      | v2_tex_2(X0,sK2) != iProver_top
% 7.16/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.16/1.50      | r1_tarski(X1,X0) != iProver_top
% 7.16/1.50      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
% 7.16/1.50      inference(superposition,[status(thm)],[c_2230,c_2224]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_4169,plain,
% 7.16/1.50      ( k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,sK3)) = sK3
% 7.16/1.50      | v2_tex_2(X0,sK2) != iProver_top
% 7.16/1.50      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 7.16/1.50      | r1_tarski(sK3,X0) != iProver_top ),
% 7.16/1.50      inference(superposition,[status(thm)],[c_2226,c_3222]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_9,plain,
% 7.16/1.50      ( ~ v1_tops_1(X0,X1)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.16/1.50      | ~ l1_pre_topc(X1)
% 7.16/1.50      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 7.16/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_22,negated_conjecture,
% 7.16/1.50      ( v1_tops_1(sK3,sK2) ),
% 7.16/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_343,plain,
% 7.16/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.16/1.50      | ~ l1_pre_topc(X1)
% 7.16/1.50      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 7.16/1.50      | sK2 != X1
% 7.16/1.50      | sK3 != X0 ),
% 7.16/1.50      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_344,plain,
% 7.16/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.16/1.50      | ~ l1_pre_topc(sK2)
% 7.16/1.50      | k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
% 7.16/1.50      inference(unflattening,[status(thm)],[c_343]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_346,plain,
% 7.16/1.50      ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
% 7.16/1.50      inference(global_propositional_subsumption,
% 7.16/1.50                [status(thm)],
% 7.16/1.50                [c_344,c_24,c_23]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_4173,plain,
% 7.16/1.50      ( k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)) = sK3
% 7.16/1.50      | v2_tex_2(X0,sK2) != iProver_top
% 7.16/1.50      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 7.16/1.50      | r1_tarski(sK3,X0) != iProver_top ),
% 7.16/1.50      inference(light_normalisation,[status(thm)],[c_4169,c_346]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_6295,plain,
% 7.16/1.50      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = sK3
% 7.16/1.50      | v2_tex_2(sK0(sK2,sK3),sK2) != iProver_top
% 7.16/1.50      | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
% 7.16/1.50      inference(superposition,[status(thm)],[c_6248,c_4173]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_30,plain,
% 7.16/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_32,plain,
% 7.16/1.50      ( v2_tex_2(sK3,sK2) = iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_11,plain,
% 7.16/1.50      ( ~ v2_tex_2(X0,X1)
% 7.16/1.50      | v3_tex_2(X0,X1)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.16/1.50      | r1_tarski(X0,sK0(X1,X0))
% 7.16/1.50      | ~ l1_pre_topc(X1) ),
% 7.16/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_535,plain,
% 7.16/1.50      ( ~ v2_tex_2(X0,X1)
% 7.16/1.50      | v3_tex_2(X0,X1)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.16/1.50      | r1_tarski(X0,sK0(X1,X0))
% 7.16/1.50      | sK2 != X1 ),
% 7.16/1.50      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_536,plain,
% 7.16/1.50      ( ~ v2_tex_2(X0,sK2)
% 7.16/1.50      | v3_tex_2(X0,sK2)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.16/1.50      | r1_tarski(X0,sK0(sK2,X0)) ),
% 7.16/1.50      inference(unflattening,[status(thm)],[c_535]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_614,plain,
% 7.16/1.50      ( ~ v2_tex_2(X0,sK2)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.16/1.50      | r1_tarski(X0,sK0(sK2,X0))
% 7.16/1.50      | sK2 != sK2
% 7.16/1.50      | sK3 != X0 ),
% 7.16/1.50      inference(resolution_lifted,[status(thm)],[c_20,c_536]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_615,plain,
% 7.16/1.50      ( ~ v2_tex_2(sK3,sK2)
% 7.16/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.16/1.50      | r1_tarski(sK3,sK0(sK2,sK3)) ),
% 7.16/1.50      inference(unflattening,[status(thm)],[c_614]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_616,plain,
% 7.16/1.50      ( v2_tex_2(sK3,sK2) != iProver_top
% 7.16/1.50      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.16/1.50      | r1_tarski(sK3,sK0(sK2,sK3)) = iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_12,plain,
% 7.16/1.50      ( ~ v2_tex_2(X0,X1)
% 7.16/1.50      | v2_tex_2(sK0(X1,X0),X1)
% 7.16/1.50      | v3_tex_2(X0,X1)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.16/1.50      | ~ l1_pre_topc(X1) ),
% 7.16/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_517,plain,
% 7.16/1.50      ( ~ v2_tex_2(X0,X1)
% 7.16/1.50      | v2_tex_2(sK0(X1,X0),X1)
% 7.16/1.50      | v3_tex_2(X0,X1)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.16/1.50      | sK2 != X1 ),
% 7.16/1.50      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_518,plain,
% 7.16/1.50      ( ~ v2_tex_2(X0,sK2)
% 7.16/1.50      | v2_tex_2(sK0(sK2,X0),sK2)
% 7.16/1.50      | v3_tex_2(X0,sK2)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 7.16/1.50      inference(unflattening,[status(thm)],[c_517]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_625,plain,
% 7.16/1.50      ( ~ v2_tex_2(X0,sK2)
% 7.16/1.50      | v2_tex_2(sK0(sK2,X0),sK2)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.16/1.50      | sK2 != sK2
% 7.16/1.50      | sK3 != X0 ),
% 7.16/1.50      inference(resolution_lifted,[status(thm)],[c_20,c_518]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_626,plain,
% 7.16/1.50      ( v2_tex_2(sK0(sK2,sK3),sK2)
% 7.16/1.50      | ~ v2_tex_2(sK3,sK2)
% 7.16/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 7.16/1.50      inference(unflattening,[status(thm)],[c_625]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_627,plain,
% 7.16/1.50      ( v2_tex_2(sK0(sK2,sK3),sK2) = iProver_top
% 7.16/1.50      | v2_tex_2(sK3,sK2) != iProver_top
% 7.16/1.50      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 7.16/1.50      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_6405,plain,
% 7.16/1.50      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = sK3 ),
% 7.16/1.50      inference(global_propositional_subsumption,
% 7.16/1.50                [status(thm)],
% 7.16/1.50                [c_6295,c_30,c_32,c_616,c_627]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_19787,plain,
% 7.16/1.50      ( k4_xboole_0(sK0(sK2,sK3),k1_xboole_0) = sK3 ),
% 7.16/1.50      inference(light_normalisation,[status(thm)],[c_19773,c_6405]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_2,plain,
% 7.16/1.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.16/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_19960,plain,
% 7.16/1.50      ( sK0(sK2,sK3) = sK3 ),
% 7.16/1.50      inference(superposition,[status(thm)],[c_19787,c_2]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_10,plain,
% 7.16/1.50      ( ~ v2_tex_2(X0,X1)
% 7.16/1.50      | v3_tex_2(X0,X1)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.16/1.50      | ~ l1_pre_topc(X1)
% 7.16/1.50      | sK0(X1,X0) != X0 ),
% 7.16/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_553,plain,
% 7.16/1.50      ( ~ v2_tex_2(X0,X1)
% 7.16/1.50      | v3_tex_2(X0,X1)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.16/1.50      | sK0(X1,X0) != X0
% 7.16/1.50      | sK2 != X1 ),
% 7.16/1.50      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_554,plain,
% 7.16/1.50      ( ~ v2_tex_2(X0,sK2)
% 7.16/1.50      | v3_tex_2(X0,sK2)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.16/1.50      | sK0(sK2,X0) != X0 ),
% 7.16/1.50      inference(unflattening,[status(thm)],[c_553]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_606,plain,
% 7.16/1.50      ( ~ v2_tex_2(X0,sK2)
% 7.16/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.16/1.50      | sK0(sK2,X0) != X0
% 7.16/1.50      | sK2 != sK2
% 7.16/1.50      | sK3 != X0 ),
% 7.16/1.50      inference(resolution_lifted,[status(thm)],[c_20,c_554]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(c_607,plain,
% 7.16/1.50      ( ~ v2_tex_2(sK3,sK2)
% 7.16/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.16/1.50      | sK0(sK2,sK3) != sK3 ),
% 7.16/1.50      inference(unflattening,[status(thm)],[c_606]) ).
% 7.16/1.50  
% 7.16/1.50  cnf(contradiction,plain,
% 7.16/1.50      ( $false ),
% 7.16/1.50      inference(minisat,[status(thm)],[c_19960,c_607,c_21,c_23]) ).
% 7.16/1.50  
% 7.16/1.50  
% 7.16/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.16/1.50  
% 7.16/1.50  ------                               Statistics
% 7.16/1.50  
% 7.16/1.50  ------ General
% 7.16/1.50  
% 7.16/1.50  abstr_ref_over_cycles:                  0
% 7.16/1.50  abstr_ref_under_cycles:                 0
% 7.16/1.50  gc_basic_clause_elim:                   0
% 7.16/1.50  forced_gc_time:                         0
% 7.16/1.50  parsing_time:                           0.009
% 7.16/1.50  unif_index_cands_time:                  0.
% 7.16/1.50  unif_index_add_time:                    0.
% 7.16/1.50  orderings_time:                         0.
% 7.16/1.50  out_proof_time:                         0.009
% 7.16/1.50  total_time:                             0.703
% 7.16/1.50  num_of_symbols:                         50
% 7.16/1.50  num_of_terms:                           15078
% 7.16/1.50  
% 7.16/1.50  ------ Preprocessing
% 7.16/1.50  
% 7.16/1.50  num_of_splits:                          0
% 7.16/1.50  num_of_split_atoms:                     0
% 7.16/1.50  num_of_reused_defs:                     0
% 7.16/1.50  num_eq_ax_congr_red:                    18
% 7.16/1.50  num_of_sem_filtered_clauses:            1
% 7.16/1.50  num_of_subtypes:                        0
% 7.16/1.50  monotx_restored_types:                  0
% 7.16/1.50  sat_num_of_epr_types:                   0
% 7.16/1.50  sat_num_of_non_cyclic_types:            0
% 7.16/1.50  sat_guarded_non_collapsed_types:        0
% 7.16/1.50  num_pure_diseq_elim:                    0
% 7.16/1.50  simp_replaced_by:                       0
% 7.16/1.50  res_preprocessed:                       120
% 7.16/1.50  prep_upred:                             0
% 7.16/1.50  prep_unflattend:                        84
% 7.16/1.50  smt_new_axioms:                         0
% 7.16/1.50  pred_elim_cands:                        4
% 7.16/1.50  pred_elim:                              4
% 7.16/1.50  pred_elim_cl:                           5
% 7.16/1.50  pred_elim_cycles:                       8
% 7.16/1.50  merged_defs:                            16
% 7.16/1.50  merged_defs_ncl:                        0
% 7.16/1.50  bin_hyper_res:                          17
% 7.16/1.50  prep_cycles:                            4
% 7.16/1.50  pred_elim_time:                         0.028
% 7.16/1.50  splitting_time:                         0.
% 7.16/1.50  sem_filter_time:                        0.
% 7.16/1.50  monotx_time:                            0.014
% 7.16/1.50  subtype_inf_time:                       0.
% 7.16/1.50  
% 7.16/1.50  ------ Problem properties
% 7.16/1.50  
% 7.16/1.50  clauses:                                22
% 7.16/1.50  conjectures:                            3
% 7.16/1.50  epr:                                    2
% 7.16/1.50  horn:                                   17
% 7.16/1.50  ground:                                 4
% 7.16/1.50  unary:                                  7
% 7.16/1.50  binary:                                 5
% 7.16/1.50  lits:                                   56
% 7.16/1.50  lits_eq:                                10
% 7.16/1.50  fd_pure:                                0
% 7.16/1.50  fd_pseudo:                              0
% 7.16/1.50  fd_cond:                                0
% 7.16/1.50  fd_pseudo_cond:                         1
% 7.16/1.50  ac_symbols:                             0
% 7.16/1.50  
% 7.16/1.50  ------ Propositional Solver
% 7.16/1.50  
% 7.16/1.50  prop_solver_calls:                      32
% 7.16/1.50  prop_fast_solver_calls:                 2554
% 7.16/1.50  smt_solver_calls:                       0
% 7.16/1.50  smt_fast_solver_calls:                  0
% 7.16/1.50  prop_num_of_clauses:                    8552
% 7.16/1.50  prop_preprocess_simplified:             20066
% 7.16/1.50  prop_fo_subsumed:                       109
% 7.16/1.50  prop_solver_time:                       0.
% 7.16/1.50  smt_solver_time:                        0.
% 7.16/1.50  smt_fast_solver_time:                   0.
% 7.16/1.50  prop_fast_solver_time:                  0.
% 7.16/1.50  prop_unsat_core_time:                   0.
% 7.16/1.50  
% 7.16/1.50  ------ QBF
% 7.16/1.50  
% 7.16/1.50  qbf_q_res:                              0
% 7.16/1.50  qbf_num_tautologies:                    0
% 7.16/1.50  qbf_prep_cycles:                        0
% 7.16/1.50  
% 7.16/1.50  ------ BMC1
% 7.16/1.50  
% 7.16/1.50  bmc1_current_bound:                     -1
% 7.16/1.50  bmc1_last_solved_bound:                 -1
% 7.16/1.50  bmc1_unsat_core_size:                   -1
% 7.16/1.50  bmc1_unsat_core_parents_size:           -1
% 7.16/1.50  bmc1_merge_next_fun:                    0
% 7.16/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.16/1.50  
% 7.16/1.50  ------ Instantiation
% 7.16/1.50  
% 7.16/1.50  inst_num_of_clauses:                    2666
% 7.16/1.50  inst_num_in_passive:                    890
% 7.16/1.50  inst_num_in_active:                     1303
% 7.16/1.50  inst_num_in_unprocessed:                473
% 7.16/1.50  inst_num_of_loops:                      1560
% 7.16/1.50  inst_num_of_learning_restarts:          0
% 7.16/1.50  inst_num_moves_active_passive:          253
% 7.16/1.50  inst_lit_activity:                      0
% 7.16/1.50  inst_lit_activity_moves:                1
% 7.16/1.50  inst_num_tautologies:                   0
% 7.16/1.50  inst_num_prop_implied:                  0
% 7.16/1.50  inst_num_existing_simplified:           0
% 7.16/1.50  inst_num_eq_res_simplified:             0
% 7.16/1.50  inst_num_child_elim:                    0
% 7.16/1.50  inst_num_of_dismatching_blockings:      1107
% 7.16/1.50  inst_num_of_non_proper_insts:           3270
% 7.16/1.50  inst_num_of_duplicates:                 0
% 7.16/1.50  inst_inst_num_from_inst_to_res:         0
% 7.16/1.50  inst_dismatching_checking_time:         0.
% 7.16/1.50  
% 7.16/1.50  ------ Resolution
% 7.16/1.50  
% 7.16/1.50  res_num_of_clauses:                     0
% 7.16/1.50  res_num_in_passive:                     0
% 7.16/1.50  res_num_in_active:                      0
% 7.16/1.50  res_num_of_loops:                       124
% 7.16/1.50  res_forward_subset_subsumed:            212
% 7.16/1.50  res_backward_subset_subsumed:           0
% 7.16/1.50  res_forward_subsumed:                   0
% 7.16/1.50  res_backward_subsumed:                  0
% 7.16/1.50  res_forward_subsumption_resolution:     0
% 7.16/1.50  res_backward_subsumption_resolution:    0
% 7.16/1.50  res_clause_to_clause_subsumption:       4403
% 7.16/1.50  res_orphan_elimination:                 0
% 7.16/1.50  res_tautology_del:                      165
% 7.16/1.50  res_num_eq_res_simplified:              0
% 7.16/1.50  res_num_sel_changes:                    0
% 7.16/1.50  res_moves_from_active_to_pass:          0
% 7.16/1.50  
% 7.16/1.50  ------ Superposition
% 7.16/1.50  
% 7.16/1.50  sup_time_total:                         0.
% 7.16/1.50  sup_time_generating:                    0.
% 7.16/1.50  sup_time_sim_full:                      0.
% 7.16/1.50  sup_time_sim_immed:                     0.
% 7.16/1.50  
% 7.16/1.50  sup_num_of_clauses:                     600
% 7.16/1.50  sup_num_in_active:                      306
% 7.16/1.50  sup_num_in_passive:                     294
% 7.16/1.50  sup_num_of_loops:                       311
% 7.16/1.50  sup_fw_superposition:                   807
% 7.16/1.50  sup_bw_superposition:                   281
% 7.16/1.50  sup_immediate_simplified:               294
% 7.16/1.50  sup_given_eliminated:                   1
% 7.16/1.50  comparisons_done:                       0
% 7.16/1.50  comparisons_avoided:                    114
% 7.16/1.50  
% 7.16/1.50  ------ Simplifications
% 7.16/1.50  
% 7.16/1.50  
% 7.16/1.50  sim_fw_subset_subsumed:                 138
% 7.16/1.50  sim_bw_subset_subsumed:                 44
% 7.16/1.50  sim_fw_subsumed:                        86
% 7.16/1.50  sim_bw_subsumed:                        33
% 7.16/1.50  sim_fw_subsumption_res:                 0
% 7.16/1.50  sim_bw_subsumption_res:                 0
% 7.16/1.50  sim_tautology_del:                      62
% 7.16/1.50  sim_eq_tautology_del:                   21
% 7.16/1.50  sim_eq_res_simp:                        0
% 7.16/1.50  sim_fw_demodulated:                     17
% 7.16/1.50  sim_bw_demodulated:                     5
% 7.16/1.50  sim_light_normalised:                   14
% 7.16/1.50  sim_joinable_taut:                      0
% 7.16/1.50  sim_joinable_simp:                      0
% 7.16/1.50  sim_ac_normalised:                      0
% 7.16/1.50  sim_smt_subsumption:                    0
% 7.16/1.50  
%------------------------------------------------------------------------------
