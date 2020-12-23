%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:07 EST 2020

% Result     : Theorem 11.60s
% Output     : CNFRefutation 11.60s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 536 expanded)
%              Number of clauses        :   91 ( 158 expanded)
%              Number of leaves         :   17 ( 125 expanded)
%              Depth                    :   23
%              Number of atoms          :  581 (2900 expanded)
%              Number of equality atoms :  232 ( 391 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v2_tex_2(X1,X0)
                & v1_tops_1(X1,X0) )
             => v3_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f45,plain,
    ( ~ v3_tex_2(sK3,sK2)
    & v2_tex_2(sK3,sK2)
    & v1_tops_1(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f44,f43])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,(
    ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f58,f51])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK0(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1)
        & r1_tarski(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    v1_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f56,f51])).

fof(f73,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK0(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK0(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1273,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_19,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1283,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | v3_tex_2(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1289,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6524,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | v3_tex_2(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(sK0(X1,X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1283,c_1289])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1294,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_29880,plain,
    ( k4_xboole_0(sK0(X0,X1),u1_struct_0(X0)) = k1_xboole_0
    | v2_tex_2(X1,X0) != iProver_top
    | v3_tex_2(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6524,c_1294])).

cnf(c_31977,plain,
    ( k4_xboole_0(sK0(sK2,sK3),u1_struct_0(sK2)) = k1_xboole_0
    | v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1273,c_29880])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_27,negated_conjecture,
    ( v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_26,negated_conjecture,
    ( ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1630,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | v3_tex_2(sK3,sK2)
    | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1868,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2311,plain,
    ( ~ m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1868])).

cnf(c_2296,plain,
    ( ~ r1_tarski(X0,u1_struct_0(X1))
    | k4_xboole_0(X0,u1_struct_0(X1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3684,plain,
    ( ~ r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2))
    | k4_xboole_0(sK0(sK2,sK3),u1_struct_0(sK2)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2296])).

cnf(c_32488,plain,
    ( k4_xboole_0(sK0(sK2,sK3),u1_struct_0(sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_31977,c_30,c_29,c_27,c_26,c_1630,c_2311,c_3684])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_32510,plain,
    ( k1_setfam_1(k2_tarski(sK0(sK2,sK3),u1_struct_0(sK2))) = k4_xboole_0(sK0(sK2,sK3),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_32488,c_11])).

cnf(c_18,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1284,plain,
    ( v2_tex_2(X0,X1) != iProver_top
    | v2_tex_2(sK0(X1,X0),X1) = iProver_top
    | v3_tex_2(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5390,plain,
    ( v2_tex_2(sK0(sK2,sK3),sK2) = iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1273,c_1284])).

cnf(c_35,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_38,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_39,plain,
    ( v3_tex_2(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1627,plain,
    ( v2_tex_2(sK0(sK2,sK3),sK2)
    | ~ v2_tex_2(sK3,sK2)
    | v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1628,plain,
    ( v2_tex_2(sK0(sK2,sK3),sK2) = iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1627])).

cnf(c_5617,plain,
    ( v2_tex_2(sK0(sK2,sK3),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5390,c_35,c_36,c_38,c_39,c_1628])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1290,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_25,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1277,plain,
    ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
    | v2_tex_2(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2881,plain,
    ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
    | v2_tex_2(X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1290,c_1277])).

cnf(c_14200,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,sK3)) = sK3
    | v2_tex_2(X0,sK2) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1273,c_2881])).

cnf(c_15,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1287,plain,
    ( k2_pre_topc(X0,X1) = u1_struct_0(X0)
    | v1_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5143,plain,
    ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2)
    | v1_tops_1(sK3,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1273,c_1287])).

cnf(c_28,negated_conjecture,
    ( v1_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1587,plain,
    ( ~ v1_tops_1(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_5611,plain,
    ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5143,c_30,c_29,c_28,c_1587])).

cnf(c_14223,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)) = sK3
    | v2_tex_2(X0,sK2) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14200,c_5611])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1295,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_217,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_218,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_217])).

cnf(c_270,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_218])).

cnf(c_1267,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_1346,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | r1_tarski(X2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1267,c_11])).

cnf(c_3854,plain,
    ( k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1295,c_1346])).

cnf(c_14224,plain,
    ( k1_setfam_1(k2_tarski(X0,u1_struct_0(sK2))) = sK3
    | v2_tex_2(X0,sK2) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14223,c_3854])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_33,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_34,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_14771,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | v2_tex_2(X0,sK2) != iProver_top
    | k1_setfam_1(k2_tarski(X0,u1_struct_0(sK2))) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14224,c_33,c_34,c_35])).

cnf(c_14772,plain,
    ( k1_setfam_1(k2_tarski(X0,u1_struct_0(sK2))) = sK3
    | v2_tex_2(X0,sK2) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_14771])).

cnf(c_29885,plain,
    ( k1_setfam_1(k2_tarski(sK0(sK2,X0),u1_struct_0(sK2))) = sK3
    | v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(sK0(sK2,X0),sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK3,sK0(sK2,X0)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6524,c_14772])).

cnf(c_30296,plain,
    ( r1_tarski(sK3,sK0(sK2,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(sK0(sK2,X0),sK2) != iProver_top
    | v2_tex_2(X0,sK2) != iProver_top
    | k1_setfam_1(k2_tarski(sK0(sK2,X0),u1_struct_0(sK2))) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_29885,c_35])).

cnf(c_30297,plain,
    ( k1_setfam_1(k2_tarski(sK0(sK2,X0),u1_struct_0(sK2))) = sK3
    | v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(sK0(sK2,X0),sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK3,sK0(sK2,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_30296])).

cnf(c_30309,plain,
    ( k1_setfam_1(k2_tarski(sK0(sK2,sK3),u1_struct_0(sK2))) = sK3
    | v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5617,c_30297])).

cnf(c_17,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,sK0(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1624,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK3,sK0(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1625,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK3,sK0(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1624])).

cnf(c_30391,plain,
    ( k1_setfam_1(k2_tarski(sK0(sK2,sK3),u1_struct_0(sK2))) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_30309,c_35,c_36,c_38,c_39,c_1625])).

cnf(c_32512,plain,
    ( k4_xboole_0(sK0(sK2,sK3),k1_xboole_0) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_32510,c_30391])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1291,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2852,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1291,c_1289])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_268,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_218])).

cnf(c_1269,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_268])).

cnf(c_9099,plain,
    ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2852,c_1269])).

cnf(c_9098,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1295,c_1269])).

cnf(c_2497,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1295,c_1294])).

cnf(c_9109,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9098,c_2497])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_269,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_218])).

cnf(c_1268,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_269])).

cnf(c_8121,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1295,c_1268])).

cnf(c_13435,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_9109,c_8121])).

cnf(c_13628,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_9099,c_13435])).

cnf(c_33174,plain,
    ( sK0(sK2,sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_32512,c_13628])).

cnf(c_16,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1286,plain,
    ( sK0(X0,X1) != X1
    | v2_tex_2(X1,X0) != iProver_top
    | v3_tex_2(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_34456,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_33174,c_1286])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34456,c_39,c_38,c_36,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:41:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.60/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.60/1.99  
% 11.60/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.60/1.99  
% 11.60/1.99  ------  iProver source info
% 11.60/1.99  
% 11.60/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.60/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.60/1.99  git: non_committed_changes: false
% 11.60/1.99  git: last_make_outside_of_git: false
% 11.60/1.99  
% 11.60/1.99  ------ 
% 11.60/1.99  ------ Parsing...
% 11.60/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.60/1.99  
% 11.60/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.60/1.99  
% 11.60/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.60/1.99  
% 11.60/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.60/1.99  ------ Proving...
% 11.60/1.99  ------ Problem Properties 
% 11.60/1.99  
% 11.60/1.99  
% 11.60/1.99  clauses                                 32
% 11.60/1.99  conjectures                             7
% 11.60/1.99  EPR                                     8
% 11.60/1.99  Horn                                    25
% 11.60/1.99  unary                                   12
% 11.60/1.99  binary                                  7
% 11.60/1.99  lits                                    94
% 11.60/1.99  lits eq                                 14
% 11.60/1.99  fd_pure                                 0
% 11.60/1.99  fd_pseudo                               0
% 11.60/1.99  fd_cond                                 0
% 11.60/1.99  fd_pseudo_cond                          2
% 11.60/1.99  AC symbols                              0
% 11.60/1.99  
% 11.60/1.99  ------ Input Options Time Limit: Unbounded
% 11.60/1.99  
% 11.60/1.99  
% 11.60/1.99  ------ 
% 11.60/1.99  Current options:
% 11.60/1.99  ------ 
% 11.60/1.99  
% 11.60/1.99  
% 11.60/1.99  
% 11.60/1.99  
% 11.60/1.99  ------ Proving...
% 11.60/1.99  
% 11.60/1.99  
% 11.60/1.99  % SZS status Theorem for theBenchmark.p
% 11.60/1.99  
% 11.60/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.60/1.99  
% 11.60/1.99  fof(f16,conjecture,(
% 11.60/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 11.60/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f17,negated_conjecture,(
% 11.60/1.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 11.60/1.99    inference(negated_conjecture,[],[f16])).
% 11.60/1.99  
% 11.60/1.99  fof(f27,plain,(
% 11.60/1.99    ? [X0] : (? [X1] : ((~v3_tex_2(X1,X0) & (v2_tex_2(X1,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 11.60/1.99    inference(ennf_transformation,[],[f17])).
% 11.60/1.99  
% 11.60/1.99  fof(f28,plain,(
% 11.60/1.99    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.60/1.99    inference(flattening,[],[f27])).
% 11.60/1.99  
% 11.60/1.99  fof(f44,plain,(
% 11.60/1.99    ( ! [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_tex_2(sK3,X0) & v2_tex_2(sK3,X0) & v1_tops_1(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.60/1.99    introduced(choice_axiom,[])).
% 11.60/1.99  
% 11.60/1.99  fof(f43,plain,(
% 11.60/1.99    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v3_tex_2(X1,sK2) & v2_tex_2(X1,sK2) & v1_tops_1(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 11.60/1.99    introduced(choice_axiom,[])).
% 11.60/1.99  
% 11.60/1.99  fof(f45,plain,(
% 11.60/1.99    (~v3_tex_2(sK3,sK2) & v2_tex_2(sK3,sK2) & v1_tops_1(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 11.60/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f28,f44,f43])).
% 11.60/1.99  
% 11.60/1.99  fof(f76,plain,(
% 11.60/1.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 11.60/1.99    inference(cnf_transformation,[],[f45])).
% 11.60/1.99  
% 11.60/1.99  fof(f14,axiom,(
% 11.60/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 11.60/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f23,plain,(
% 11.60/1.99    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.60/1.99    inference(ennf_transformation,[],[f14])).
% 11.60/1.99  
% 11.60/1.99  fof(f24,plain,(
% 11.60/1.99    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.60/1.99    inference(flattening,[],[f23])).
% 11.60/1.99  
% 11.60/1.99  fof(f34,plain,(
% 11.60/1.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.60/1.99    inference(nnf_transformation,[],[f24])).
% 11.60/1.99  
% 11.60/1.99  fof(f35,plain,(
% 11.60/1.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.60/1.99    inference(flattening,[],[f34])).
% 11.60/1.99  
% 11.60/1.99  fof(f36,plain,(
% 11.60/1.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.60/1.99    inference(rectify,[],[f35])).
% 11.60/1.99  
% 11.60/1.99  fof(f37,plain,(
% 11.60/1.99    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.60/1.99    introduced(choice_axiom,[])).
% 11.60/1.99  
% 11.60/1.99  fof(f38,plain,(
% 11.60/1.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.60/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 11.60/1.99  
% 11.60/1.99  fof(f65,plain,(
% 11.60/1.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f38])).
% 11.60/1.99  
% 11.60/1.99  fof(f11,axiom,(
% 11.60/1.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.60/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f32,plain,(
% 11.60/1.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.60/1.99    inference(nnf_transformation,[],[f11])).
% 11.60/1.99  
% 11.60/1.99  fof(f59,plain,(
% 11.60/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.60/1.99    inference(cnf_transformation,[],[f32])).
% 11.60/1.99  
% 11.60/1.99  fof(f2,axiom,(
% 11.60/1.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 11.60/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f31,plain,(
% 11.60/1.99    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 11.60/1.99    inference(nnf_transformation,[],[f2])).
% 11.60/1.99  
% 11.60/1.99  fof(f50,plain,(
% 11.60/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f31])).
% 11.60/1.99  
% 11.60/1.99  fof(f75,plain,(
% 11.60/1.99    l1_pre_topc(sK2)),
% 11.60/1.99    inference(cnf_transformation,[],[f45])).
% 11.60/1.99  
% 11.60/1.99  fof(f78,plain,(
% 11.60/1.99    v2_tex_2(sK3,sK2)),
% 11.60/1.99    inference(cnf_transformation,[],[f45])).
% 11.60/1.99  
% 11.60/1.99  fof(f79,plain,(
% 11.60/1.99    ~v3_tex_2(sK3,sK2)),
% 11.60/1.99    inference(cnf_transformation,[],[f45])).
% 11.60/1.99  
% 11.60/1.99  fof(f10,axiom,(
% 11.60/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.60/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f58,plain,(
% 11.60/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.60/1.99    inference(cnf_transformation,[],[f10])).
% 11.60/1.99  
% 11.60/1.99  fof(f3,axiom,(
% 11.60/1.99    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 11.60/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f51,plain,(
% 11.60/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f3])).
% 11.60/1.99  
% 11.60/1.99  fof(f81,plain,(
% 11.60/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.60/1.99    inference(definition_unfolding,[],[f58,f51])).
% 11.60/1.99  
% 11.60/1.99  fof(f66,plain,(
% 11.60/1.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | v2_tex_2(sK0(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f38])).
% 11.60/1.99  
% 11.60/1.99  fof(f60,plain,(
% 11.60/1.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f32])).
% 11.60/1.99  
% 11.60/1.99  fof(f15,axiom,(
% 11.60/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 11.60/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f25,plain,(
% 11.60/1.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.60/1.99    inference(ennf_transformation,[],[f15])).
% 11.60/1.99  
% 11.60/1.99  fof(f26,plain,(
% 11.60/1.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.60/1.99    inference(flattening,[],[f25])).
% 11.60/1.99  
% 11.60/1.99  fof(f39,plain,(
% 11.60/1.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.60/1.99    inference(nnf_transformation,[],[f26])).
% 11.60/1.99  
% 11.60/1.99  fof(f40,plain,(
% 11.60/1.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.60/1.99    inference(rectify,[],[f39])).
% 11.60/1.99  
% 11.60/1.99  fof(f41,plain,(
% 11.60/1.99    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.60/1.99    introduced(choice_axiom,[])).
% 11.60/1.99  
% 11.60/1.99  fof(f42,plain,(
% 11.60/1.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.60/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).
% 11.60/1.99  
% 11.60/1.99  fof(f69,plain,(
% 11.60/1.99    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f42])).
% 11.60/1.99  
% 11.60/1.99  fof(f13,axiom,(
% 11.60/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 11.60/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f22,plain,(
% 11.60/1.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.60/1.99    inference(ennf_transformation,[],[f13])).
% 11.60/1.99  
% 11.60/1.99  fof(f33,plain,(
% 11.60/1.99    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.60/1.99    inference(nnf_transformation,[],[f22])).
% 11.60/1.99  
% 11.60/1.99  fof(f61,plain,(
% 11.60/1.99    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f33])).
% 11.60/1.99  
% 11.60/1.99  fof(f77,plain,(
% 11.60/1.99    v1_tops_1(sK3,sK2)),
% 11.60/1.99    inference(cnf_transformation,[],[f45])).
% 11.60/1.99  
% 11.60/1.99  fof(f1,axiom,(
% 11.60/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.60/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f29,plain,(
% 11.60/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.60/1.99    inference(nnf_transformation,[],[f1])).
% 11.60/1.99  
% 11.60/1.99  fof(f30,plain,(
% 11.60/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.60/1.99    inference(flattening,[],[f29])).
% 11.60/1.99  
% 11.60/1.99  fof(f47,plain,(
% 11.60/1.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.60/1.99    inference(cnf_transformation,[],[f30])).
% 11.60/1.99  
% 11.60/1.99  fof(f82,plain,(
% 11.60/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.60/1.99    inference(equality_resolution,[],[f47])).
% 11.60/1.99  
% 11.60/1.99  fof(f8,axiom,(
% 11.60/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 11.60/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f21,plain,(
% 11.60/1.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 11.60/1.99    inference(ennf_transformation,[],[f8])).
% 11.60/1.99  
% 11.60/1.99  fof(f56,plain,(
% 11.60/1.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.60/1.99    inference(cnf_transformation,[],[f21])).
% 11.60/1.99  
% 11.60/1.99  fof(f80,plain,(
% 11.60/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.60/1.99    inference(definition_unfolding,[],[f56,f51])).
% 11.60/1.99  
% 11.60/1.99  fof(f73,plain,(
% 11.60/1.99    ~v2_struct_0(sK2)),
% 11.60/1.99    inference(cnf_transformation,[],[f45])).
% 11.60/1.99  
% 11.60/1.99  fof(f74,plain,(
% 11.60/1.99    v2_pre_topc(sK2)),
% 11.60/1.99    inference(cnf_transformation,[],[f45])).
% 11.60/1.99  
% 11.60/1.99  fof(f67,plain,(
% 11.60/1.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK0(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f38])).
% 11.60/1.99  
% 11.60/1.99  fof(f9,axiom,(
% 11.60/1.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 11.60/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f57,plain,(
% 11.60/1.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 11.60/1.99    inference(cnf_transformation,[],[f9])).
% 11.60/1.99  
% 11.60/1.99  fof(f5,axiom,(
% 11.60/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 11.60/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f19,plain,(
% 11.60/1.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.60/1.99    inference(ennf_transformation,[],[f5])).
% 11.60/1.99  
% 11.60/1.99  fof(f53,plain,(
% 11.60/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.60/1.99    inference(cnf_transformation,[],[f19])).
% 11.60/1.99  
% 11.60/1.99  fof(f7,axiom,(
% 11.60/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 11.60/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.60/1.99  
% 11.60/1.99  fof(f20,plain,(
% 11.60/1.99    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.60/1.99    inference(ennf_transformation,[],[f7])).
% 11.60/1.99  
% 11.60/1.99  fof(f55,plain,(
% 11.60/1.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.60/1.99    inference(cnf_transformation,[],[f20])).
% 11.60/1.99  
% 11.60/1.99  fof(f68,plain,(
% 11.60/1.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK0(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.60/1.99    inference(cnf_transformation,[],[f38])).
% 11.60/1.99  
% 11.60/1.99  cnf(c_29,negated_conjecture,
% 11.60/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 11.60/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1273,plain,
% 11.60/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_19,plain,
% 11.60/1.99      ( ~ v2_tex_2(X0,X1)
% 11.60/1.99      | v3_tex_2(X0,X1)
% 11.60/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.99      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.99      | ~ l1_pre_topc(X1) ),
% 11.60/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1283,plain,
% 11.60/1.99      ( v2_tex_2(X0,X1) != iProver_top
% 11.60/1.99      | v3_tex_2(X0,X1) = iProver_top
% 11.60/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.60/1.99      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 11.60/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_13,plain,
% 11.60/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.60/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1289,plain,
% 11.60/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.60/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_6524,plain,
% 11.60/1.99      ( v2_tex_2(X0,X1) != iProver_top
% 11.60/1.99      | v3_tex_2(X0,X1) = iProver_top
% 11.60/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.60/1.99      | r1_tarski(sK0(X1,X0),u1_struct_0(X1)) = iProver_top
% 11.60/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_1283,c_1289]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_3,plain,
% 11.60/1.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.60/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1294,plain,
% 11.60/1.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 11.60/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_29880,plain,
% 11.60/1.99      ( k4_xboole_0(sK0(X0,X1),u1_struct_0(X0)) = k1_xboole_0
% 11.60/1.99      | v2_tex_2(X1,X0) != iProver_top
% 11.60/1.99      | v3_tex_2(X1,X0) = iProver_top
% 11.60/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.60/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_6524,c_1294]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_31977,plain,
% 11.60/1.99      ( k4_xboole_0(sK0(sK2,sK3),u1_struct_0(sK2)) = k1_xboole_0
% 11.60/1.99      | v2_tex_2(sK3,sK2) != iProver_top
% 11.60/1.99      | v3_tex_2(sK3,sK2) = iProver_top
% 11.60/1.99      | l1_pre_topc(sK2) != iProver_top ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_1273,c_29880]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_30,negated_conjecture,
% 11.60/1.99      ( l1_pre_topc(sK2) ),
% 11.60/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_27,negated_conjecture,
% 11.60/1.99      ( v2_tex_2(sK3,sK2) ),
% 11.60/1.99      inference(cnf_transformation,[],[f78]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_26,negated_conjecture,
% 11.60/1.99      ( ~ v3_tex_2(sK3,sK2) ),
% 11.60/1.99      inference(cnf_transformation,[],[f79]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1630,plain,
% 11.60/1.99      ( ~ v2_tex_2(sK3,sK2)
% 11.60/1.99      | v3_tex_2(sK3,sK2)
% 11.60/1.99      | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 11.60/1.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.60/1.99      | ~ l1_pre_topc(sK2) ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_19]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1868,plain,
% 11.60/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.99      | r1_tarski(X0,u1_struct_0(X1)) ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_13]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2311,plain,
% 11.60/1.99      ( ~ m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 11.60/1.99      | r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2)) ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_1868]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2296,plain,
% 11.60/1.99      ( ~ r1_tarski(X0,u1_struct_0(X1))
% 11.60/1.99      | k4_xboole_0(X0,u1_struct_0(X1)) = k1_xboole_0 ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_3684,plain,
% 11.60/1.99      ( ~ r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2))
% 11.60/1.99      | k4_xboole_0(sK0(sK2,sK3),u1_struct_0(sK2)) = k1_xboole_0 ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_2296]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_32488,plain,
% 11.60/1.99      ( k4_xboole_0(sK0(sK2,sK3),u1_struct_0(sK2)) = k1_xboole_0 ),
% 11.60/1.99      inference(global_propositional_subsumption,
% 11.60/1.99                [status(thm)],
% 11.60/1.99                [c_31977,c_30,c_29,c_27,c_26,c_1630,c_2311,c_3684]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_11,plain,
% 11.60/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 11.60/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_32510,plain,
% 11.60/1.99      ( k1_setfam_1(k2_tarski(sK0(sK2,sK3),u1_struct_0(sK2))) = k4_xboole_0(sK0(sK2,sK3),k1_xboole_0) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_32488,c_11]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_18,plain,
% 11.60/1.99      ( ~ v2_tex_2(X0,X1)
% 11.60/1.99      | v2_tex_2(sK0(X1,X0),X1)
% 11.60/1.99      | v3_tex_2(X0,X1)
% 11.60/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.99      | ~ l1_pre_topc(X1) ),
% 11.60/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1284,plain,
% 11.60/1.99      ( v2_tex_2(X0,X1) != iProver_top
% 11.60/1.99      | v2_tex_2(sK0(X1,X0),X1) = iProver_top
% 11.60/1.99      | v3_tex_2(X0,X1) = iProver_top
% 11.60/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.60/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_5390,plain,
% 11.60/1.99      ( v2_tex_2(sK0(sK2,sK3),sK2) = iProver_top
% 11.60/1.99      | v2_tex_2(sK3,sK2) != iProver_top
% 11.60/1.99      | v3_tex_2(sK3,sK2) = iProver_top
% 11.60/1.99      | l1_pre_topc(sK2) != iProver_top ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_1273,c_1284]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_35,plain,
% 11.60/1.99      ( l1_pre_topc(sK2) = iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_36,plain,
% 11.60/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_38,plain,
% 11.60/1.99      ( v2_tex_2(sK3,sK2) = iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_39,plain,
% 11.60/1.99      ( v3_tex_2(sK3,sK2) != iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1627,plain,
% 11.60/1.99      ( v2_tex_2(sK0(sK2,sK3),sK2)
% 11.60/1.99      | ~ v2_tex_2(sK3,sK2)
% 11.60/1.99      | v3_tex_2(sK3,sK2)
% 11.60/1.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.60/1.99      | ~ l1_pre_topc(sK2) ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_18]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1628,plain,
% 11.60/1.99      ( v2_tex_2(sK0(sK2,sK3),sK2) = iProver_top
% 11.60/1.99      | v2_tex_2(sK3,sK2) != iProver_top
% 11.60/1.99      | v3_tex_2(sK3,sK2) = iProver_top
% 11.60/1.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.60/1.99      | l1_pre_topc(sK2) != iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_1627]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_5617,plain,
% 11.60/1.99      ( v2_tex_2(sK0(sK2,sK3),sK2) = iProver_top ),
% 11.60/1.99      inference(global_propositional_subsumption,
% 11.60/1.99                [status(thm)],
% 11.60/1.99                [c_5390,c_35,c_36,c_38,c_39,c_1628]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_12,plain,
% 11.60/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.60/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1290,plain,
% 11.60/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.60/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_25,plain,
% 11.60/1.99      ( ~ v2_tex_2(X0,X1)
% 11.60/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.99      | ~ r1_tarski(X2,X0)
% 11.60/1.99      | v2_struct_0(X1)
% 11.60/1.99      | ~ v2_pre_topc(X1)
% 11.60/1.99      | ~ l1_pre_topc(X1)
% 11.60/1.99      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
% 11.60/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1277,plain,
% 11.60/1.99      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
% 11.60/1.99      | v2_tex_2(X1,X0) != iProver_top
% 11.60/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.60/1.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.60/1.99      | r1_tarski(X2,X1) != iProver_top
% 11.60/1.99      | v2_struct_0(X0) = iProver_top
% 11.60/1.99      | v2_pre_topc(X0) != iProver_top
% 11.60/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2881,plain,
% 11.60/1.99      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
% 11.60/1.99      | v2_tex_2(X1,X0) != iProver_top
% 11.60/1.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.60/1.99      | r1_tarski(X2,X1) != iProver_top
% 11.60/1.99      | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
% 11.60/1.99      | v2_struct_0(X0) = iProver_top
% 11.60/1.99      | v2_pre_topc(X0) != iProver_top
% 11.60/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_1290,c_1277]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_14200,plain,
% 11.60/1.99      ( k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,sK3)) = sK3
% 11.60/1.99      | v2_tex_2(X0,sK2) != iProver_top
% 11.60/1.99      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 11.60/1.99      | r1_tarski(sK3,X0) != iProver_top
% 11.60/1.99      | v2_struct_0(sK2) = iProver_top
% 11.60/1.99      | v2_pre_topc(sK2) != iProver_top
% 11.60/1.99      | l1_pre_topc(sK2) != iProver_top ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_1273,c_2881]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_15,plain,
% 11.60/1.99      ( ~ v1_tops_1(X0,X1)
% 11.60/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.99      | ~ l1_pre_topc(X1)
% 11.60/1.99      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 11.60/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1287,plain,
% 11.60/1.99      ( k2_pre_topc(X0,X1) = u1_struct_0(X0)
% 11.60/1.99      | v1_tops_1(X1,X0) != iProver_top
% 11.60/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.60/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_5143,plain,
% 11.60/1.99      ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2)
% 11.60/1.99      | v1_tops_1(sK3,sK2) != iProver_top
% 11.60/1.99      | l1_pre_topc(sK2) != iProver_top ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_1273,c_1287]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_28,negated_conjecture,
% 11.60/1.99      ( v1_tops_1(sK3,sK2) ),
% 11.60/1.99      inference(cnf_transformation,[],[f77]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1587,plain,
% 11.60/1.99      ( ~ v1_tops_1(sK3,sK2)
% 11.60/1.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.60/1.99      | ~ l1_pre_topc(sK2)
% 11.60/1.99      | k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_15]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_5611,plain,
% 11.60/1.99      ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
% 11.60/1.99      inference(global_propositional_subsumption,
% 11.60/1.99                [status(thm)],
% 11.60/1.99                [c_5143,c_30,c_29,c_28,c_1587]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_14223,plain,
% 11.60/1.99      ( k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)) = sK3
% 11.60/1.99      | v2_tex_2(X0,sK2) != iProver_top
% 11.60/1.99      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 11.60/1.99      | r1_tarski(sK3,X0) != iProver_top
% 11.60/1.99      | v2_struct_0(sK2) = iProver_top
% 11.60/1.99      | v2_pre_topc(sK2) != iProver_top
% 11.60/1.99      | l1_pre_topc(sK2) != iProver_top ),
% 11.60/1.99      inference(light_normalisation,[status(thm)],[c_14200,c_5611]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1,plain,
% 11.60/1.99      ( r1_tarski(X0,X0) ),
% 11.60/1.99      inference(cnf_transformation,[],[f82]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1295,plain,
% 11.60/1.99      ( r1_tarski(X0,X0) = iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_9,plain,
% 11.60/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.60/1.99      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 11.60/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_217,plain,
% 11.60/1.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.60/1.99      inference(prop_impl,[status(thm)],[c_12]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_218,plain,
% 11.60/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.60/1.99      inference(renaming,[status(thm)],[c_217]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_270,plain,
% 11.60/1.99      ( ~ r1_tarski(X0,X1)
% 11.60/1.99      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 11.60/1.99      inference(bin_hyper_res,[status(thm)],[c_9,c_218]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1267,plain,
% 11.60/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 11.60/1.99      | r1_tarski(X1,X2) != iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_270]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1346,plain,
% 11.60/1.99      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 11.60/1.99      | r1_tarski(X2,X0) != iProver_top ),
% 11.60/1.99      inference(light_normalisation,[status(thm)],[c_1267,c_11]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_3854,plain,
% 11.60/1.99      ( k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_1295,c_1346]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_14224,plain,
% 11.60/1.99      ( k1_setfam_1(k2_tarski(X0,u1_struct_0(sK2))) = sK3
% 11.60/1.99      | v2_tex_2(X0,sK2) != iProver_top
% 11.60/1.99      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 11.60/1.99      | r1_tarski(sK3,X0) != iProver_top
% 11.60/1.99      | v2_struct_0(sK2) = iProver_top
% 11.60/1.99      | v2_pre_topc(sK2) != iProver_top
% 11.60/1.99      | l1_pre_topc(sK2) != iProver_top ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_14223,c_3854]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_32,negated_conjecture,
% 11.60/1.99      ( ~ v2_struct_0(sK2) ),
% 11.60/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_33,plain,
% 11.60/1.99      ( v2_struct_0(sK2) != iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_31,negated_conjecture,
% 11.60/1.99      ( v2_pre_topc(sK2) ),
% 11.60/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_34,plain,
% 11.60/1.99      ( v2_pre_topc(sK2) = iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_14771,plain,
% 11.60/1.99      ( r1_tarski(sK3,X0) != iProver_top
% 11.60/1.99      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 11.60/1.99      | v2_tex_2(X0,sK2) != iProver_top
% 11.60/1.99      | k1_setfam_1(k2_tarski(X0,u1_struct_0(sK2))) = sK3 ),
% 11.60/1.99      inference(global_propositional_subsumption,
% 11.60/1.99                [status(thm)],
% 11.60/1.99                [c_14224,c_33,c_34,c_35]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_14772,plain,
% 11.60/1.99      ( k1_setfam_1(k2_tarski(X0,u1_struct_0(sK2))) = sK3
% 11.60/1.99      | v2_tex_2(X0,sK2) != iProver_top
% 11.60/1.99      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 11.60/1.99      | r1_tarski(sK3,X0) != iProver_top ),
% 11.60/1.99      inference(renaming,[status(thm)],[c_14771]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_29885,plain,
% 11.60/1.99      ( k1_setfam_1(k2_tarski(sK0(sK2,X0),u1_struct_0(sK2))) = sK3
% 11.60/1.99      | v2_tex_2(X0,sK2) != iProver_top
% 11.60/1.99      | v2_tex_2(sK0(sK2,X0),sK2) != iProver_top
% 11.60/1.99      | v3_tex_2(X0,sK2) = iProver_top
% 11.60/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.60/1.99      | r1_tarski(sK3,sK0(sK2,X0)) != iProver_top
% 11.60/1.99      | l1_pre_topc(sK2) != iProver_top ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_6524,c_14772]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_30296,plain,
% 11.60/1.99      ( r1_tarski(sK3,sK0(sK2,X0)) != iProver_top
% 11.60/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.60/1.99      | v3_tex_2(X0,sK2) = iProver_top
% 11.60/1.99      | v2_tex_2(sK0(sK2,X0),sK2) != iProver_top
% 11.60/1.99      | v2_tex_2(X0,sK2) != iProver_top
% 11.60/1.99      | k1_setfam_1(k2_tarski(sK0(sK2,X0),u1_struct_0(sK2))) = sK3 ),
% 11.60/1.99      inference(global_propositional_subsumption,
% 11.60/1.99                [status(thm)],
% 11.60/1.99                [c_29885,c_35]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_30297,plain,
% 11.60/1.99      ( k1_setfam_1(k2_tarski(sK0(sK2,X0),u1_struct_0(sK2))) = sK3
% 11.60/1.99      | v2_tex_2(X0,sK2) != iProver_top
% 11.60/1.99      | v2_tex_2(sK0(sK2,X0),sK2) != iProver_top
% 11.60/1.99      | v3_tex_2(X0,sK2) = iProver_top
% 11.60/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.60/1.99      | r1_tarski(sK3,sK0(sK2,X0)) != iProver_top ),
% 11.60/1.99      inference(renaming,[status(thm)],[c_30296]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_30309,plain,
% 11.60/1.99      ( k1_setfam_1(k2_tarski(sK0(sK2,sK3),u1_struct_0(sK2))) = sK3
% 11.60/1.99      | v2_tex_2(sK3,sK2) != iProver_top
% 11.60/1.99      | v3_tex_2(sK3,sK2) = iProver_top
% 11.60/1.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.60/1.99      | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_5617,c_30297]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_17,plain,
% 11.60/1.99      ( ~ v2_tex_2(X0,X1)
% 11.60/1.99      | v3_tex_2(X0,X1)
% 11.60/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.99      | r1_tarski(X0,sK0(X1,X0))
% 11.60/1.99      | ~ l1_pre_topc(X1) ),
% 11.60/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1624,plain,
% 11.60/1.99      ( ~ v2_tex_2(sK3,sK2)
% 11.60/1.99      | v3_tex_2(sK3,sK2)
% 11.60/1.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 11.60/1.99      | r1_tarski(sK3,sK0(sK2,sK3))
% 11.60/1.99      | ~ l1_pre_topc(sK2) ),
% 11.60/1.99      inference(instantiation,[status(thm)],[c_17]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1625,plain,
% 11.60/1.99      ( v2_tex_2(sK3,sK2) != iProver_top
% 11.60/1.99      | v3_tex_2(sK3,sK2) = iProver_top
% 11.60/1.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.60/1.99      | r1_tarski(sK3,sK0(sK2,sK3)) = iProver_top
% 11.60/1.99      | l1_pre_topc(sK2) != iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_1624]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_30391,plain,
% 11.60/1.99      ( k1_setfam_1(k2_tarski(sK0(sK2,sK3),u1_struct_0(sK2))) = sK3 ),
% 11.60/1.99      inference(global_propositional_subsumption,
% 11.60/1.99                [status(thm)],
% 11.60/1.99                [c_30309,c_35,c_36,c_38,c_39,c_1625]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_32512,plain,
% 11.60/1.99      ( k4_xboole_0(sK0(sK2,sK3),k1_xboole_0) = sK3 ),
% 11.60/1.99      inference(light_normalisation,[status(thm)],[c_32510,c_30391]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_10,plain,
% 11.60/1.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 11.60/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1291,plain,
% 11.60/1.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2852,plain,
% 11.60/1.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_1291,c_1289]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_6,plain,
% 11.60/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.60/1.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.60/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_268,plain,
% 11.60/1.99      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.60/1.99      inference(bin_hyper_res,[status(thm)],[c_6,c_218]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1269,plain,
% 11.60/1.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 11.60/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_268]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_9099,plain,
% 11.60/1.99      ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_2852,c_1269]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_9098,plain,
% 11.60/1.99      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_1295,c_1269]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_2497,plain,
% 11.60/1.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_1295,c_1294]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_9109,plain,
% 11.60/1.99      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 11.60/1.99      inference(light_normalisation,[status(thm)],[c_9098,c_2497]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_8,plain,
% 11.60/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.60/1.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 11.60/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_269,plain,
% 11.60/1.99      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 11.60/1.99      inference(bin_hyper_res,[status(thm)],[c_8,c_218]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1268,plain,
% 11.60/1.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 11.60/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_269]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_8121,plain,
% 11.60/1.99      ( k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_1295,c_1268]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_13435,plain,
% 11.60/1.99      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 11.60/1.99      inference(demodulation,[status(thm)],[c_9109,c_8121]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_13628,plain,
% 11.60/1.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.60/1.99      inference(light_normalisation,[status(thm)],[c_9099,c_13435]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_33174,plain,
% 11.60/1.99      ( sK0(sK2,sK3) = sK3 ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_32512,c_13628]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_16,plain,
% 11.60/1.99      ( ~ v2_tex_2(X0,X1)
% 11.60/1.99      | v3_tex_2(X0,X1)
% 11.60/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.60/1.99      | ~ l1_pre_topc(X1)
% 11.60/1.99      | sK0(X1,X0) != X0 ),
% 11.60/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_1286,plain,
% 11.60/1.99      ( sK0(X0,X1) != X1
% 11.60/1.99      | v2_tex_2(X1,X0) != iProver_top
% 11.60/1.99      | v3_tex_2(X1,X0) = iProver_top
% 11.60/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.60/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.60/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(c_34456,plain,
% 11.60/1.99      ( v2_tex_2(sK3,sK2) != iProver_top
% 11.60/1.99      | v3_tex_2(sK3,sK2) = iProver_top
% 11.60/1.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 11.60/1.99      | l1_pre_topc(sK2) != iProver_top ),
% 11.60/1.99      inference(superposition,[status(thm)],[c_33174,c_1286]) ).
% 11.60/1.99  
% 11.60/1.99  cnf(contradiction,plain,
% 11.60/1.99      ( $false ),
% 11.60/1.99      inference(minisat,[status(thm)],[c_34456,c_39,c_38,c_36,c_35]) ).
% 11.60/1.99  
% 11.60/1.99  
% 11.60/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.60/1.99  
% 11.60/1.99  ------                               Statistics
% 11.60/1.99  
% 11.60/1.99  ------ Selected
% 11.60/1.99  
% 11.60/1.99  total_time:                             1.054
% 11.60/1.99  
%------------------------------------------------------------------------------
