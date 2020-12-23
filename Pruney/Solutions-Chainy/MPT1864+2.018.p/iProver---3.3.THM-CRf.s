%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:57 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 419 expanded)
%              Number of clauses        :   69 ( 122 expanded)
%              Number of leaves         :   13 ( 118 expanded)
%              Depth                    :   19
%              Number of atoms          :  444 (2453 expanded)
%              Number of equality atoms :  105 ( 412 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3)
                              & v3_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( k1_tarski(sK4) != k9_subset_1(u1_struct_0(X0),X1,X3)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK4,X1)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ! [X3] :
                ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),sK3,X3)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(X2,sK3)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & v2_tex_2(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3)
                  | ~ v3_pre_topc(X3,sK2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & v2_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ! [X3] :
        ( k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3)
        | ~ v3_pre_topc(X3,sK2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
    & r2_hidden(sK4,sK3)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f26,f25,f24])).

fof(f44,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_enumset1(X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f47])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f47])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v3_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f19])).

fof(f22,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
        & v3_pre_topc(sK1(X0,X1,X4),X0)
        & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
                    & v3_pre_topc(sK1(X0,X1,X4),X0)
                    & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).

fof(f37,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    ! [X3] :
      ( k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3)
      | ~ v3_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X3] :
      ( k1_enumset1(sK4,sK4,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3)
      | ~ v3_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1825,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2289,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1825])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1829,plain,
    ( ~ m1_subset_1(X0_44,X1_44)
    | r2_hidden(X0_44,X1_44)
    | v1_xboole_0(X1_44) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2285,plain,
    ( m1_subset_1(X0_44,X1_44) != iProver_top
    | r2_hidden(X0_44,X1_44) = iProver_top
    | v1_xboole_0(X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1829])).

cnf(c_2661,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2289,c_2285])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_18,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_21,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1828,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | ~ r2_hidden(X2_44,X0_44)
    | ~ v1_xboole_0(X1_44) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2488,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1_44,X0_44)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1828])).

cnf(c_2719,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0_44,sK3)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2488])).

cnf(c_2720,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0_44,sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2719])).

cnf(c_2722,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK4,sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2720])).

cnf(c_2955,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2661,c_18,c_21,c_2722])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_enumset1(X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1832,plain,
    ( ~ r2_hidden(X0_44,X1_44)
    | r1_tarski(k1_enumset1(X0_44,X0_44,X0_44),X1_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2282,plain,
    ( r2_hidden(X0_44,X1_44) != iProver_top
    | r1_tarski(k1_enumset1(X0_44,X0_44,X0_44),X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1832])).

cnf(c_2,plain,
    ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1830,plain,
    ( m1_subset_1(k1_enumset1(X0_44,X0_44,X0_44),k1_zfmisc_1(X1_44))
    | ~ r2_hidden(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2284,plain,
    ( m1_subset_1(k1_enumset1(X0_44,X0_44,X0_44),k1_zfmisc_1(X1_44)) = iProver_top
    | r2_hidden(X0_44,X1_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1830])).

cnf(c_1823,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2291,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1823])).

cnf(c_8,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_488,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_489,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_1820,plain,
    ( ~ v2_tex_2(X0_44,sK2)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1_44,X0_44)
    | k9_subset_1(u1_struct_0(sK2),X0_44,sK1(sK2,X0_44,X1_44)) = X1_44 ),
    inference(subtyping,[status(esa)],[c_489])).

cnf(c_2294,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0_44,sK1(sK2,X0_44,X1_44)) = X1_44
    | v2_tex_2(X0_44,sK2) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1_44,X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1820])).

cnf(c_2815,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0_44)) = X0_44
    | v2_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0_44,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2291,c_2294])).

cnf(c_14,negated_conjecture,
    ( v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_19,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2862,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0_44)) = X0_44
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0_44,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2815,c_19])).

cnf(c_2873,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k1_enumset1(X0_44,X0_44,X0_44))) = k1_enumset1(X0_44,X0_44,X0_44)
    | r2_hidden(X0_44,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_enumset1(X0_44,X0_44,X0_44),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2284,c_2862])).

cnf(c_3344,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k1_enumset1(X0_44,X0_44,X0_44))) = k1_enumset1(X0_44,X0_44,X0_44)
    | r2_hidden(X0_44,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_44,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2282,c_2873])).

cnf(c_3759,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k1_enumset1(sK4,sK4,sK4))) = k1_enumset1(sK4,sK4,sK4)
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2955,c_3344])).

cnf(c_131,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_enumset1(X0,X0,X0),X1) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_408,plain,
    ( r1_tarski(k1_enumset1(X0,X0,X0),X1)
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_131,c_12])).

cnf(c_409,plain,
    ( r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_2441,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0_44,sK3)
    | k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0_44)) = X0_44 ),
    inference(instantiation,[status(thm)],[c_1820])).

cnf(c_2525,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3)
    | k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k1_enumset1(sK4,sK4,sK4))) = k1_enumset1(sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_2441])).

cnf(c_2600,plain,
    ( m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1830])).

cnf(c_2691,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2661])).

cnf(c_2721,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK4,sK3)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2719])).

cnf(c_3929,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k1_enumset1(sK4,sK4,sK4))) = k1_enumset1(sK4,sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3759,c_15,c_14,c_12,c_409,c_2525,c_2600,c_2691,c_2721])).

cnf(c_11,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_enumset1(sK4,sK4,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1827,negated_conjecture,
    ( ~ v3_pre_topc(X0_44,sK2)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_enumset1(sK4,sK4,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X0_44) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2287,plain,
    ( k1_enumset1(sK4,sK4,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X0_44)
    | v3_pre_topc(X0_44,sK2) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1827])).

cnf(c_3932,plain,
    ( v3_pre_topc(sK1(sK2,sK3,k1_enumset1(sK4,sK4,sK4)),sK2) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,k1_enumset1(sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3929,c_2287])).

cnf(c_2601,plain,
    ( m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r2_hidden(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2600])).

cnf(c_9,plain,
    ( v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X2,X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_446,plain,
    ( v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X2,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_447,plain,
    ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
    | ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_1822,plain,
    ( v3_pre_topc(sK1(sK2,X0_44,X1_44),sK2)
    | ~ v2_tex_2(X0_44,sK2)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_447])).

cnf(c_2432,plain,
    ( v3_pre_topc(sK1(sK2,sK3,X0_44),sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0_44,sK3) ),
    inference(instantiation,[status(thm)],[c_1822])).

cnf(c_2522,plain,
    ( v3_pre_topc(sK1(sK2,sK3,k1_enumset1(sK4,sK4,sK4)),sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_2432])).

cnf(c_2523,plain,
    ( v3_pre_topc(sK1(sK2,sK3,k1_enumset1(sK4,sK4,sK4)),sK2) = iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2522])).

cnf(c_10,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_467,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_16])).

cnf(c_468,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_1821,plain,
    ( ~ v2_tex_2(X0_44,sK2)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0_44,X1_44),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_468])).

cnf(c_2427,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,sK3,X0_44),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0_44,sK3) ),
    inference(instantiation,[status(thm)],[c_1821])).

cnf(c_2519,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | m1_subset_1(sK1(sK2,sK3,k1_enumset1(sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_2427])).

cnf(c_2520,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,k1_enumset1(sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2519])).

cnf(c_410,plain,
    ( r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_409])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3932,c_2722,c_2661,c_2601,c_2523,c_2520,c_410,c_21,c_19,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n005.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 17:01:47 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 1.59/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/0.99  
% 1.59/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.59/0.99  
% 1.59/0.99  ------  iProver source info
% 1.59/0.99  
% 1.59/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.59/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.59/0.99  git: non_committed_changes: false
% 1.59/0.99  git: last_make_outside_of_git: false
% 1.59/0.99  
% 1.59/0.99  ------ 
% 1.59/0.99  
% 1.59/0.99  ------ Input Options
% 1.59/0.99  
% 1.59/0.99  --out_options                           all
% 1.59/0.99  --tptp_safe_out                         true
% 1.59/0.99  --problem_path                          ""
% 1.59/0.99  --include_path                          ""
% 1.59/0.99  --clausifier                            res/vclausify_rel
% 1.59/0.99  --clausifier_options                    --mode clausify
% 1.59/0.99  --stdin                                 false
% 1.59/0.99  --stats_out                             all
% 1.59/0.99  
% 1.59/0.99  ------ General Options
% 1.59/0.99  
% 1.59/0.99  --fof                                   false
% 1.59/0.99  --time_out_real                         305.
% 1.59/0.99  --time_out_virtual                      -1.
% 1.59/0.99  --symbol_type_check                     false
% 1.59/0.99  --clausify_out                          false
% 1.59/0.99  --sig_cnt_out                           false
% 1.59/0.99  --trig_cnt_out                          false
% 1.59/0.99  --trig_cnt_out_tolerance                1.
% 1.59/0.99  --trig_cnt_out_sk_spl                   false
% 1.59/0.99  --abstr_cl_out                          false
% 1.59/0.99  
% 1.59/0.99  ------ Global Options
% 1.59/0.99  
% 1.59/0.99  --schedule                              default
% 1.59/0.99  --add_important_lit                     false
% 1.59/0.99  --prop_solver_per_cl                    1000
% 1.59/0.99  --min_unsat_core                        false
% 1.59/0.99  --soft_assumptions                      false
% 1.59/0.99  --soft_lemma_size                       3
% 1.59/0.99  --prop_impl_unit_size                   0
% 1.59/0.99  --prop_impl_unit                        []
% 1.59/0.99  --share_sel_clauses                     true
% 1.59/0.99  --reset_solvers                         false
% 1.59/0.99  --bc_imp_inh                            [conj_cone]
% 1.59/0.99  --conj_cone_tolerance                   3.
% 1.59/0.99  --extra_neg_conj                        none
% 1.59/0.99  --large_theory_mode                     true
% 1.59/0.99  --prolific_symb_bound                   200
% 1.59/0.99  --lt_threshold                          2000
% 1.59/0.99  --clause_weak_htbl                      true
% 1.59/0.99  --gc_record_bc_elim                     false
% 1.59/0.99  
% 1.59/0.99  ------ Preprocessing Options
% 1.59/0.99  
% 1.59/0.99  --preprocessing_flag                    true
% 1.59/0.99  --time_out_prep_mult                    0.1
% 1.59/0.99  --splitting_mode                        input
% 1.59/0.99  --splitting_grd                         true
% 1.59/0.99  --splitting_cvd                         false
% 1.59/0.99  --splitting_cvd_svl                     false
% 1.59/0.99  --splitting_nvd                         32
% 1.59/0.99  --sub_typing                            true
% 1.59/0.99  --prep_gs_sim                           true
% 1.59/0.99  --prep_unflatten                        true
% 1.59/0.99  --prep_res_sim                          true
% 1.59/0.99  --prep_upred                            true
% 1.59/0.99  --prep_sem_filter                       exhaustive
% 1.59/0.99  --prep_sem_filter_out                   false
% 1.59/0.99  --pred_elim                             true
% 1.59/0.99  --res_sim_input                         true
% 1.59/0.99  --eq_ax_congr_red                       true
% 1.59/0.99  --pure_diseq_elim                       true
% 1.59/0.99  --brand_transform                       false
% 1.59/0.99  --non_eq_to_eq                          false
% 1.59/0.99  --prep_def_merge                        true
% 1.59/0.99  --prep_def_merge_prop_impl              false
% 1.59/0.99  --prep_def_merge_mbd                    true
% 1.59/0.99  --prep_def_merge_tr_red                 false
% 1.59/0.99  --prep_def_merge_tr_cl                  false
% 1.59/0.99  --smt_preprocessing                     true
% 1.59/0.99  --smt_ac_axioms                         fast
% 1.59/0.99  --preprocessed_out                      false
% 1.59/0.99  --preprocessed_stats                    false
% 1.59/0.99  
% 1.59/0.99  ------ Abstraction refinement Options
% 1.59/0.99  
% 1.59/0.99  --abstr_ref                             []
% 1.59/0.99  --abstr_ref_prep                        false
% 1.59/0.99  --abstr_ref_until_sat                   false
% 1.59/0.99  --abstr_ref_sig_restrict                funpre
% 1.59/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.59/0.99  --abstr_ref_under                       []
% 1.59/0.99  
% 1.59/0.99  ------ SAT Options
% 1.59/0.99  
% 1.59/0.99  --sat_mode                              false
% 1.59/0.99  --sat_fm_restart_options                ""
% 1.59/0.99  --sat_gr_def                            false
% 1.59/0.99  --sat_epr_types                         true
% 1.59/0.99  --sat_non_cyclic_types                  false
% 1.59/0.99  --sat_finite_models                     false
% 1.59/0.99  --sat_fm_lemmas                         false
% 1.59/0.99  --sat_fm_prep                           false
% 1.59/0.99  --sat_fm_uc_incr                        true
% 1.59/0.99  --sat_out_model                         small
% 1.59/0.99  --sat_out_clauses                       false
% 1.59/0.99  
% 1.59/0.99  ------ QBF Options
% 1.59/0.99  
% 1.59/0.99  --qbf_mode                              false
% 1.59/0.99  --qbf_elim_univ                         false
% 1.59/0.99  --qbf_dom_inst                          none
% 1.59/0.99  --qbf_dom_pre_inst                      false
% 1.59/0.99  --qbf_sk_in                             false
% 1.59/0.99  --qbf_pred_elim                         true
% 1.59/0.99  --qbf_split                             512
% 1.59/0.99  
% 1.59/0.99  ------ BMC1 Options
% 1.59/0.99  
% 1.59/0.99  --bmc1_incremental                      false
% 1.59/0.99  --bmc1_axioms                           reachable_all
% 1.59/0.99  --bmc1_min_bound                        0
% 1.59/0.99  --bmc1_max_bound                        -1
% 1.59/0.99  --bmc1_max_bound_default                -1
% 1.59/0.99  --bmc1_symbol_reachability              true
% 1.59/0.99  --bmc1_property_lemmas                  false
% 1.59/0.99  --bmc1_k_induction                      false
% 1.59/0.99  --bmc1_non_equiv_states                 false
% 1.59/0.99  --bmc1_deadlock                         false
% 1.59/0.99  --bmc1_ucm                              false
% 1.59/0.99  --bmc1_add_unsat_core                   none
% 1.59/0.99  --bmc1_unsat_core_children              false
% 1.59/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.59/0.99  --bmc1_out_stat                         full
% 1.59/0.99  --bmc1_ground_init                      false
% 1.59/0.99  --bmc1_pre_inst_next_state              false
% 1.59/0.99  --bmc1_pre_inst_state                   false
% 1.59/0.99  --bmc1_pre_inst_reach_state             false
% 1.59/0.99  --bmc1_out_unsat_core                   false
% 1.59/0.99  --bmc1_aig_witness_out                  false
% 1.59/0.99  --bmc1_verbose                          false
% 1.59/0.99  --bmc1_dump_clauses_tptp                false
% 1.59/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.59/0.99  --bmc1_dump_file                        -
% 1.59/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.59/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.59/0.99  --bmc1_ucm_extend_mode                  1
% 1.59/0.99  --bmc1_ucm_init_mode                    2
% 1.59/0.99  --bmc1_ucm_cone_mode                    none
% 1.59/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.59/0.99  --bmc1_ucm_relax_model                  4
% 1.59/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.59/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.59/0.99  --bmc1_ucm_layered_model                none
% 1.59/0.99  --bmc1_ucm_max_lemma_size               10
% 1.59/0.99  
% 1.59/0.99  ------ AIG Options
% 1.59/0.99  
% 1.59/0.99  --aig_mode                              false
% 1.59/0.99  
% 1.59/0.99  ------ Instantiation Options
% 1.59/0.99  
% 1.59/0.99  --instantiation_flag                    true
% 1.59/0.99  --inst_sos_flag                         false
% 1.59/0.99  --inst_sos_phase                        true
% 1.59/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.59/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.59/0.99  --inst_lit_sel_side                     num_symb
% 1.59/0.99  --inst_solver_per_active                1400
% 1.59/0.99  --inst_solver_calls_frac                1.
% 1.59/0.99  --inst_passive_queue_type               priority_queues
% 1.59/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.59/0.99  --inst_passive_queues_freq              [25;2]
% 1.59/0.99  --inst_dismatching                      true
% 1.59/0.99  --inst_eager_unprocessed_to_passive     true
% 1.59/0.99  --inst_prop_sim_given                   true
% 1.59/0.99  --inst_prop_sim_new                     false
% 1.59/0.99  --inst_subs_new                         false
% 1.59/0.99  --inst_eq_res_simp                      false
% 1.59/0.99  --inst_subs_given                       false
% 1.59/0.99  --inst_orphan_elimination               true
% 1.59/0.99  --inst_learning_loop_flag               true
% 1.59/0.99  --inst_learning_start                   3000
% 1.59/0.99  --inst_learning_factor                  2
% 1.59/0.99  --inst_start_prop_sim_after_learn       3
% 1.59/0.99  --inst_sel_renew                        solver
% 1.59/0.99  --inst_lit_activity_flag                true
% 1.59/0.99  --inst_restr_to_given                   false
% 1.59/0.99  --inst_activity_threshold               500
% 1.59/0.99  --inst_out_proof                        true
% 1.59/0.99  
% 1.59/0.99  ------ Resolution Options
% 1.59/0.99  
% 1.59/0.99  --resolution_flag                       true
% 1.59/0.99  --res_lit_sel                           adaptive
% 1.59/0.99  --res_lit_sel_side                      none
% 1.59/0.99  --res_ordering                          kbo
% 1.59/0.99  --res_to_prop_solver                    active
% 1.59/0.99  --res_prop_simpl_new                    false
% 1.59/0.99  --res_prop_simpl_given                  true
% 1.59/0.99  --res_passive_queue_type                priority_queues
% 1.59/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.59/0.99  --res_passive_queues_freq               [15;5]
% 1.59/0.99  --res_forward_subs                      full
% 1.59/0.99  --res_backward_subs                     full
% 1.59/0.99  --res_forward_subs_resolution           true
% 1.59/0.99  --res_backward_subs_resolution          true
% 1.59/0.99  --res_orphan_elimination                true
% 1.59/0.99  --res_time_limit                        2.
% 1.59/0.99  --res_out_proof                         true
% 1.59/0.99  
% 1.59/0.99  ------ Superposition Options
% 1.59/0.99  
% 1.59/0.99  --superposition_flag                    true
% 1.59/0.99  --sup_passive_queue_type                priority_queues
% 1.59/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.59/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.59/0.99  --demod_completeness_check              fast
% 1.59/0.99  --demod_use_ground                      true
% 1.59/0.99  --sup_to_prop_solver                    passive
% 1.59/0.99  --sup_prop_simpl_new                    true
% 1.59/0.99  --sup_prop_simpl_given                  true
% 1.59/0.99  --sup_fun_splitting                     false
% 1.59/0.99  --sup_smt_interval                      50000
% 1.59/0.99  
% 1.59/0.99  ------ Superposition Simplification Setup
% 1.59/0.99  
% 1.59/0.99  --sup_indices_passive                   []
% 1.59/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.59/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.59/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.59/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.59/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.59/0.99  --sup_full_bw                           [BwDemod]
% 1.59/0.99  --sup_immed_triv                        [TrivRules]
% 1.59/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.59/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.59/0.99  --sup_immed_bw_main                     []
% 1.59/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.59/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.59/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.59/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.59/0.99  
% 1.59/0.99  ------ Combination Options
% 1.59/0.99  
% 1.59/0.99  --comb_res_mult                         3
% 1.59/0.99  --comb_sup_mult                         2
% 1.59/0.99  --comb_inst_mult                        10
% 1.59/0.99  
% 1.59/0.99  ------ Debug Options
% 1.59/0.99  
% 1.59/0.99  --dbg_backtrace                         false
% 1.59/0.99  --dbg_dump_prop_clauses                 false
% 1.59/0.99  --dbg_dump_prop_clauses_file            -
% 1.59/0.99  --dbg_out_stat                          false
% 1.59/0.99  ------ Parsing...
% 1.59/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.59/0.99  
% 1.59/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.59/0.99  
% 1.59/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.59/0.99  
% 1.59/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.59/0.99  ------ Proving...
% 1.59/0.99  ------ Problem Properties 
% 1.59/0.99  
% 1.59/0.99  
% 1.59/0.99  clauses                                 16
% 1.59/0.99  conjectures                             5
% 1.59/0.99  EPR                                     3
% 1.59/0.99  Horn                                    13
% 1.59/0.99  unary                                   4
% 1.59/0.99  binary                                  3
% 1.59/0.99  lits                                    45
% 1.59/0.99  lits eq                                 3
% 1.59/0.99  fd_pure                                 0
% 1.59/0.99  fd_pseudo                               0
% 1.59/0.99  fd_cond                                 0
% 1.59/0.99  fd_pseudo_cond                          0
% 1.59/0.99  AC symbols                              0
% 1.59/0.99  
% 1.59/0.99  ------ Schedule dynamic 5 is on 
% 1.59/0.99  
% 1.59/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.59/0.99  
% 1.59/0.99  
% 1.59/0.99  ------ 
% 1.59/0.99  Current options:
% 1.59/0.99  ------ 
% 1.59/0.99  
% 1.59/0.99  ------ Input Options
% 1.59/0.99  
% 1.59/0.99  --out_options                           all
% 1.59/0.99  --tptp_safe_out                         true
% 1.59/0.99  --problem_path                          ""
% 1.59/0.99  --include_path                          ""
% 1.59/0.99  --clausifier                            res/vclausify_rel
% 1.59/0.99  --clausifier_options                    --mode clausify
% 1.59/0.99  --stdin                                 false
% 1.59/0.99  --stats_out                             all
% 1.59/0.99  
% 1.59/0.99  ------ General Options
% 1.59/0.99  
% 1.59/0.99  --fof                                   false
% 1.59/0.99  --time_out_real                         305.
% 1.59/0.99  --time_out_virtual                      -1.
% 1.59/0.99  --symbol_type_check                     false
% 1.59/0.99  --clausify_out                          false
% 1.59/0.99  --sig_cnt_out                           false
% 1.59/0.99  --trig_cnt_out                          false
% 1.59/0.99  --trig_cnt_out_tolerance                1.
% 1.59/0.99  --trig_cnt_out_sk_spl                   false
% 1.59/0.99  --abstr_cl_out                          false
% 1.59/0.99  
% 1.59/0.99  ------ Global Options
% 1.59/0.99  
% 1.59/0.99  --schedule                              default
% 1.59/0.99  --add_important_lit                     false
% 1.59/0.99  --prop_solver_per_cl                    1000
% 1.59/0.99  --min_unsat_core                        false
% 1.59/0.99  --soft_assumptions                      false
% 1.59/0.99  --soft_lemma_size                       3
% 1.59/0.99  --prop_impl_unit_size                   0
% 1.59/0.99  --prop_impl_unit                        []
% 1.59/0.99  --share_sel_clauses                     true
% 1.59/0.99  --reset_solvers                         false
% 1.59/0.99  --bc_imp_inh                            [conj_cone]
% 1.59/0.99  --conj_cone_tolerance                   3.
% 1.59/0.99  --extra_neg_conj                        none
% 1.59/0.99  --large_theory_mode                     true
% 1.59/0.99  --prolific_symb_bound                   200
% 1.59/0.99  --lt_threshold                          2000
% 1.59/0.99  --clause_weak_htbl                      true
% 1.59/0.99  --gc_record_bc_elim                     false
% 1.59/0.99  
% 1.59/0.99  ------ Preprocessing Options
% 1.59/0.99  
% 1.59/0.99  --preprocessing_flag                    true
% 1.59/0.99  --time_out_prep_mult                    0.1
% 1.59/0.99  --splitting_mode                        input
% 1.59/0.99  --splitting_grd                         true
% 1.59/0.99  --splitting_cvd                         false
% 1.59/0.99  --splitting_cvd_svl                     false
% 1.59/0.99  --splitting_nvd                         32
% 1.59/0.99  --sub_typing                            true
% 1.59/0.99  --prep_gs_sim                           true
% 1.59/0.99  --prep_unflatten                        true
% 1.59/0.99  --prep_res_sim                          true
% 1.59/0.99  --prep_upred                            true
% 1.59/0.99  --prep_sem_filter                       exhaustive
% 1.59/0.99  --prep_sem_filter_out                   false
% 1.59/0.99  --pred_elim                             true
% 1.59/0.99  --res_sim_input                         true
% 1.59/0.99  --eq_ax_congr_red                       true
% 1.59/0.99  --pure_diseq_elim                       true
% 1.59/0.99  --brand_transform                       false
% 1.59/0.99  --non_eq_to_eq                          false
% 1.59/0.99  --prep_def_merge                        true
% 1.59/0.99  --prep_def_merge_prop_impl              false
% 1.59/0.99  --prep_def_merge_mbd                    true
% 1.59/0.99  --prep_def_merge_tr_red                 false
% 1.59/0.99  --prep_def_merge_tr_cl                  false
% 1.59/0.99  --smt_preprocessing                     true
% 1.59/0.99  --smt_ac_axioms                         fast
% 1.59/0.99  --preprocessed_out                      false
% 1.59/0.99  --preprocessed_stats                    false
% 1.59/0.99  
% 1.59/0.99  ------ Abstraction refinement Options
% 1.59/0.99  
% 1.59/0.99  --abstr_ref                             []
% 1.59/0.99  --abstr_ref_prep                        false
% 1.59/0.99  --abstr_ref_until_sat                   false
% 1.59/0.99  --abstr_ref_sig_restrict                funpre
% 1.59/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.59/0.99  --abstr_ref_under                       []
% 1.59/0.99  
% 1.59/0.99  ------ SAT Options
% 1.59/0.99  
% 1.59/0.99  --sat_mode                              false
% 1.59/0.99  --sat_fm_restart_options                ""
% 1.59/0.99  --sat_gr_def                            false
% 1.59/0.99  --sat_epr_types                         true
% 1.59/0.99  --sat_non_cyclic_types                  false
% 1.59/0.99  --sat_finite_models                     false
% 1.59/0.99  --sat_fm_lemmas                         false
% 1.59/0.99  --sat_fm_prep                           false
% 1.59/0.99  --sat_fm_uc_incr                        true
% 1.59/0.99  --sat_out_model                         small
% 1.59/0.99  --sat_out_clauses                       false
% 1.59/0.99  
% 1.59/0.99  ------ QBF Options
% 1.59/0.99  
% 1.59/0.99  --qbf_mode                              false
% 1.59/0.99  --qbf_elim_univ                         false
% 1.59/0.99  --qbf_dom_inst                          none
% 1.59/0.99  --qbf_dom_pre_inst                      false
% 1.59/0.99  --qbf_sk_in                             false
% 1.59/0.99  --qbf_pred_elim                         true
% 1.59/0.99  --qbf_split                             512
% 1.59/0.99  
% 1.59/0.99  ------ BMC1 Options
% 1.59/0.99  
% 1.59/0.99  --bmc1_incremental                      false
% 1.59/0.99  --bmc1_axioms                           reachable_all
% 1.59/0.99  --bmc1_min_bound                        0
% 1.59/0.99  --bmc1_max_bound                        -1
% 1.59/0.99  --bmc1_max_bound_default                -1
% 1.59/0.99  --bmc1_symbol_reachability              true
% 1.59/0.99  --bmc1_property_lemmas                  false
% 1.59/0.99  --bmc1_k_induction                      false
% 1.59/0.99  --bmc1_non_equiv_states                 false
% 1.59/0.99  --bmc1_deadlock                         false
% 1.59/0.99  --bmc1_ucm                              false
% 1.59/0.99  --bmc1_add_unsat_core                   none
% 1.59/0.99  --bmc1_unsat_core_children              false
% 1.59/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.59/0.99  --bmc1_out_stat                         full
% 1.59/0.99  --bmc1_ground_init                      false
% 1.59/0.99  --bmc1_pre_inst_next_state              false
% 1.59/0.99  --bmc1_pre_inst_state                   false
% 1.59/0.99  --bmc1_pre_inst_reach_state             false
% 1.59/0.99  --bmc1_out_unsat_core                   false
% 1.59/0.99  --bmc1_aig_witness_out                  false
% 1.59/0.99  --bmc1_verbose                          false
% 1.59/0.99  --bmc1_dump_clauses_tptp                false
% 1.59/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.59/0.99  --bmc1_dump_file                        -
% 1.59/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.59/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.59/0.99  --bmc1_ucm_extend_mode                  1
% 1.59/0.99  --bmc1_ucm_init_mode                    2
% 1.59/0.99  --bmc1_ucm_cone_mode                    none
% 1.59/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.59/0.99  --bmc1_ucm_relax_model                  4
% 1.59/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.59/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.59/0.99  --bmc1_ucm_layered_model                none
% 1.59/0.99  --bmc1_ucm_max_lemma_size               10
% 1.59/0.99  
% 1.59/0.99  ------ AIG Options
% 1.59/0.99  
% 1.59/0.99  --aig_mode                              false
% 1.59/0.99  
% 1.59/0.99  ------ Instantiation Options
% 1.59/0.99  
% 1.59/0.99  --instantiation_flag                    true
% 1.59/0.99  --inst_sos_flag                         false
% 1.59/0.99  --inst_sos_phase                        true
% 1.59/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.59/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.59/0.99  --inst_lit_sel_side                     none
% 1.59/0.99  --inst_solver_per_active                1400
% 1.59/0.99  --inst_solver_calls_frac                1.
% 1.59/0.99  --inst_passive_queue_type               priority_queues
% 1.59/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.59/1.00  --inst_passive_queues_freq              [25;2]
% 1.59/1.00  --inst_dismatching                      true
% 1.59/1.00  --inst_eager_unprocessed_to_passive     true
% 1.59/1.00  --inst_prop_sim_given                   true
% 1.59/1.00  --inst_prop_sim_new                     false
% 1.59/1.00  --inst_subs_new                         false
% 1.59/1.00  --inst_eq_res_simp                      false
% 1.59/1.00  --inst_subs_given                       false
% 1.59/1.00  --inst_orphan_elimination               true
% 1.59/1.00  --inst_learning_loop_flag               true
% 1.59/1.00  --inst_learning_start                   3000
% 1.59/1.00  --inst_learning_factor                  2
% 1.59/1.00  --inst_start_prop_sim_after_learn       3
% 1.59/1.00  --inst_sel_renew                        solver
% 1.59/1.00  --inst_lit_activity_flag                true
% 1.59/1.00  --inst_restr_to_given                   false
% 1.59/1.00  --inst_activity_threshold               500
% 1.59/1.00  --inst_out_proof                        true
% 1.59/1.00  
% 1.59/1.00  ------ Resolution Options
% 1.59/1.00  
% 1.59/1.00  --resolution_flag                       false
% 1.59/1.00  --res_lit_sel                           adaptive
% 1.59/1.00  --res_lit_sel_side                      none
% 1.59/1.00  --res_ordering                          kbo
% 1.59/1.00  --res_to_prop_solver                    active
% 1.59/1.00  --res_prop_simpl_new                    false
% 1.59/1.00  --res_prop_simpl_given                  true
% 1.59/1.00  --res_passive_queue_type                priority_queues
% 1.59/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.59/1.00  --res_passive_queues_freq               [15;5]
% 1.59/1.00  --res_forward_subs                      full
% 1.59/1.00  --res_backward_subs                     full
% 1.59/1.00  --res_forward_subs_resolution           true
% 1.59/1.00  --res_backward_subs_resolution          true
% 1.59/1.00  --res_orphan_elimination                true
% 1.59/1.00  --res_time_limit                        2.
% 1.59/1.00  --res_out_proof                         true
% 1.59/1.00  
% 1.59/1.00  ------ Superposition Options
% 1.59/1.00  
% 1.59/1.00  --superposition_flag                    true
% 1.59/1.00  --sup_passive_queue_type                priority_queues
% 1.59/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.59/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.59/1.00  --demod_completeness_check              fast
% 1.59/1.00  --demod_use_ground                      true
% 1.59/1.00  --sup_to_prop_solver                    passive
% 1.59/1.00  --sup_prop_simpl_new                    true
% 1.59/1.00  --sup_prop_simpl_given                  true
% 1.59/1.00  --sup_fun_splitting                     false
% 1.59/1.00  --sup_smt_interval                      50000
% 1.59/1.00  
% 1.59/1.00  ------ Superposition Simplification Setup
% 1.59/1.00  
% 1.59/1.00  --sup_indices_passive                   []
% 1.59/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.59/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.59/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.59/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.59/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.59/1.00  --sup_full_bw                           [BwDemod]
% 1.59/1.00  --sup_immed_triv                        [TrivRules]
% 1.59/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.59/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.59/1.00  --sup_immed_bw_main                     []
% 1.59/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.59/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.59/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.59/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.59/1.00  
% 1.59/1.00  ------ Combination Options
% 1.59/1.00  
% 1.59/1.00  --comb_res_mult                         3
% 1.59/1.00  --comb_sup_mult                         2
% 1.59/1.00  --comb_inst_mult                        10
% 1.59/1.00  
% 1.59/1.00  ------ Debug Options
% 1.59/1.00  
% 1.59/1.00  --dbg_backtrace                         false
% 1.59/1.00  --dbg_dump_prop_clauses                 false
% 1.59/1.00  --dbg_dump_prop_clauses_file            -
% 1.59/1.00  --dbg_out_stat                          false
% 1.59/1.00  
% 1.59/1.00  
% 1.59/1.00  
% 1.59/1.00  
% 1.59/1.00  ------ Proving...
% 1.59/1.00  
% 1.59/1.00  
% 1.59/1.00  % SZS status Theorem for theBenchmark.p
% 1.59/1.00  
% 1.59/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.59/1.00  
% 1.59/1.00  fof(f8,conjecture,(
% 1.59/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 1.59/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.59/1.00  
% 1.59/1.00  fof(f9,negated_conjecture,(
% 1.59/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 1.59/1.00    inference(negated_conjecture,[],[f8])).
% 1.59/1.00  
% 1.59/1.00  fof(f16,plain,(
% 1.59/1.00    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.59/1.00    inference(ennf_transformation,[],[f9])).
% 1.59/1.00  
% 1.59/1.00  fof(f17,plain,(
% 1.59/1.00    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.59/1.00    inference(flattening,[],[f16])).
% 1.59/1.00  
% 1.59/1.00  fof(f26,plain,(
% 1.59/1.00    ( ! [X0,X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (k1_tarski(sK4) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK4,X1) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 1.59/1.00    introduced(choice_axiom,[])).
% 1.59/1.00  
% 1.59/1.00  fof(f25,plain,(
% 1.59/1.00    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),sK3,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.59/1.00    introduced(choice_axiom,[])).
% 1.59/1.00  
% 1.59/1.00  fof(f24,plain,(
% 1.59/1.00    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2))),
% 1.59/1.00    introduced(choice_axiom,[])).
% 1.59/1.00  
% 1.59/1.00  fof(f27,plain,(
% 1.59/1.00    ((! [X3] : (k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2)),
% 1.59/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f26,f25,f24])).
% 1.59/1.00  
% 1.59/1.00  fof(f44,plain,(
% 1.59/1.00    m1_subset_1(sK4,u1_struct_0(sK2))),
% 1.59/1.00    inference(cnf_transformation,[],[f27])).
% 1.59/1.00  
% 1.59/1.00  fof(f5,axiom,(
% 1.59/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.59/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.59/1.00  
% 1.59/1.00  fof(f11,plain,(
% 1.59/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.59/1.00    inference(ennf_transformation,[],[f5])).
% 1.59/1.00  
% 1.59/1.00  fof(f12,plain,(
% 1.59/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.59/1.00    inference(flattening,[],[f11])).
% 1.59/1.00  
% 1.59/1.00  fof(f33,plain,(
% 1.59/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.59/1.00    inference(cnf_transformation,[],[f12])).
% 1.59/1.00  
% 1.59/1.00  fof(f42,plain,(
% 1.59/1.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.59/1.00    inference(cnf_transformation,[],[f27])).
% 1.59/1.00  
% 1.59/1.00  fof(f45,plain,(
% 1.59/1.00    r2_hidden(sK4,sK3)),
% 1.59/1.00    inference(cnf_transformation,[],[f27])).
% 1.59/1.00  
% 1.59/1.00  fof(f6,axiom,(
% 1.59/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.59/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.59/1.00  
% 1.59/1.00  fof(f13,plain,(
% 1.59/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.59/1.00    inference(ennf_transformation,[],[f6])).
% 1.59/1.00  
% 1.59/1.00  fof(f34,plain,(
% 1.59/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.59/1.00    inference(cnf_transformation,[],[f13])).
% 1.59/1.00  
% 1.59/1.00  fof(f3,axiom,(
% 1.59/1.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.59/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.59/1.00  
% 1.59/1.00  fof(f18,plain,(
% 1.59/1.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.59/1.00    inference(nnf_transformation,[],[f3])).
% 1.59/1.00  
% 1.59/1.00  fof(f31,plain,(
% 1.59/1.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.59/1.00    inference(cnf_transformation,[],[f18])).
% 1.59/1.00  
% 1.59/1.00  fof(f1,axiom,(
% 1.59/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.59/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.59/1.00  
% 1.59/1.00  fof(f28,plain,(
% 1.59/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.59/1.00    inference(cnf_transformation,[],[f1])).
% 1.59/1.00  
% 1.59/1.00  fof(f2,axiom,(
% 1.59/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.59/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.59/1.00  
% 1.59/1.00  fof(f29,plain,(
% 1.59/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.59/1.00    inference(cnf_transformation,[],[f2])).
% 1.59/1.00  
% 1.59/1.00  fof(f47,plain,(
% 1.59/1.00    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.59/1.00    inference(definition_unfolding,[],[f28,f29])).
% 1.59/1.00  
% 1.59/1.00  fof(f48,plain,(
% 1.59/1.00    ( ! [X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.59/1.00    inference(definition_unfolding,[],[f31,f47])).
% 1.59/1.00  
% 1.59/1.00  fof(f4,axiom,(
% 1.59/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.59/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.59/1.00  
% 1.59/1.00  fof(f10,plain,(
% 1.59/1.00    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.59/1.00    inference(ennf_transformation,[],[f4])).
% 1.59/1.00  
% 1.59/1.00  fof(f32,plain,(
% 1.59/1.00    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.59/1.00    inference(cnf_transformation,[],[f10])).
% 1.59/1.00  
% 1.59/1.00  fof(f50,plain,(
% 1.59/1.00    ( ! [X0,X1] : (m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.59/1.00    inference(definition_unfolding,[],[f32,f47])).
% 1.59/1.00  
% 1.59/1.00  fof(f7,axiom,(
% 1.59/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.59/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.59/1.00  
% 1.59/1.00  fof(f14,plain,(
% 1.59/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.59/1.00    inference(ennf_transformation,[],[f7])).
% 1.59/1.00  
% 1.59/1.00  fof(f15,plain,(
% 1.59/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.59/1.00    inference(flattening,[],[f14])).
% 1.59/1.00  
% 1.59/1.00  fof(f19,plain,(
% 1.59/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.59/1.00    inference(nnf_transformation,[],[f15])).
% 1.59/1.00  
% 1.59/1.00  fof(f20,plain,(
% 1.59/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.59/1.00    inference(rectify,[],[f19])).
% 1.59/1.00  
% 1.59/1.00  fof(f22,plain,(
% 1.59/1.00    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v3_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.59/1.00    introduced(choice_axiom,[])).
% 1.59/1.00  
% 1.59/1.00  fof(f21,plain,(
% 1.59/1.00    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.59/1.00    introduced(choice_axiom,[])).
% 1.59/1.00  
% 1.59/1.00  fof(f23,plain,(
% 1.59/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v3_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.59/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).
% 1.59/1.00  
% 1.59/1.00  fof(f37,plain,(
% 1.59/1.00    ( ! [X4,X0,X1] : (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.59/1.00    inference(cnf_transformation,[],[f23])).
% 1.59/1.00  
% 1.59/1.00  fof(f41,plain,(
% 1.59/1.00    l1_pre_topc(sK2)),
% 1.59/1.00    inference(cnf_transformation,[],[f27])).
% 1.59/1.00  
% 1.59/1.00  fof(f43,plain,(
% 1.59/1.00    v2_tex_2(sK3,sK2)),
% 1.59/1.00    inference(cnf_transformation,[],[f27])).
% 1.59/1.00  
% 1.59/1.00  fof(f46,plain,(
% 1.59/1.00    ( ! [X3] : (k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.59/1.00    inference(cnf_transformation,[],[f27])).
% 1.59/1.00  
% 1.59/1.00  fof(f51,plain,(
% 1.59/1.00    ( ! [X3] : (k1_enumset1(sK4,sK4,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.59/1.00    inference(definition_unfolding,[],[f46,f47])).
% 1.59/1.00  
% 1.59/1.00  fof(f36,plain,(
% 1.59/1.00    ( ! [X4,X0,X1] : (v3_pre_topc(sK1(X0,X1,X4),X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.59/1.00    inference(cnf_transformation,[],[f23])).
% 1.59/1.00  
% 1.59/1.00  fof(f35,plain,(
% 1.59/1.00    ( ! [X4,X0,X1] : (m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.59/1.00    inference(cnf_transformation,[],[f23])).
% 1.59/1.00  
% 1.59/1.00  cnf(c_13,negated_conjecture,
% 1.59/1.00      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 1.59/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_1825,negated_conjecture,
% 1.59/1.00      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 1.59/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2289,plain,
% 1.59/1.00      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 1.59/1.00      inference(predicate_to_equality,[status(thm)],[c_1825]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_3,plain,
% 1.59/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.59/1.00      inference(cnf_transformation,[],[f33]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_1829,plain,
% 1.59/1.00      ( ~ m1_subset_1(X0_44,X1_44)
% 1.59/1.00      | r2_hidden(X0_44,X1_44)
% 1.59/1.00      | v1_xboole_0(X1_44) ),
% 1.59/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2285,plain,
% 1.59/1.00      ( m1_subset_1(X0_44,X1_44) != iProver_top
% 1.59/1.00      | r2_hidden(X0_44,X1_44) = iProver_top
% 1.59/1.00      | v1_xboole_0(X1_44) = iProver_top ),
% 1.59/1.00      inference(predicate_to_equality,[status(thm)],[c_1829]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2661,plain,
% 1.59/1.00      ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
% 1.59/1.00      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 1.59/1.00      inference(superposition,[status(thm)],[c_2289,c_2285]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_15,negated_conjecture,
% 1.59/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.59/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_18,plain,
% 1.59/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.59/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_12,negated_conjecture,
% 1.59/1.00      ( r2_hidden(sK4,sK3) ),
% 1.59/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_21,plain,
% 1.59/1.00      ( r2_hidden(sK4,sK3) = iProver_top ),
% 1.59/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_4,plain,
% 1.59/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.59/1.00      | ~ r2_hidden(X2,X0)
% 1.59/1.00      | ~ v1_xboole_0(X1) ),
% 1.59/1.00      inference(cnf_transformation,[],[f34]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_1828,plain,
% 1.59/1.00      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 1.59/1.00      | ~ r2_hidden(X2_44,X0_44)
% 1.59/1.00      | ~ v1_xboole_0(X1_44) ),
% 1.59/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2488,plain,
% 1.59/1.00      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ r2_hidden(X1_44,X0_44)
% 1.59/1.00      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.59/1.00      inference(instantiation,[status(thm)],[c_1828]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2719,plain,
% 1.59/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ r2_hidden(X0_44,sK3)
% 1.59/1.00      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.59/1.00      inference(instantiation,[status(thm)],[c_2488]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2720,plain,
% 1.59/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.59/1.00      | r2_hidden(X0_44,sK3) != iProver_top
% 1.59/1.00      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 1.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2719]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2722,plain,
% 1.59/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.59/1.00      | r2_hidden(sK4,sK3) != iProver_top
% 1.59/1.00      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 1.59/1.00      inference(instantiation,[status(thm)],[c_2720]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2955,plain,
% 1.59/1.00      ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top ),
% 1.59/1.00      inference(global_propositional_subsumption,
% 1.59/1.00                [status(thm)],
% 1.59/1.00                [c_2661,c_18,c_21,c_2722]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_0,plain,
% 1.59/1.00      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_enumset1(X0,X0,X0),X1) ),
% 1.59/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_1832,plain,
% 1.59/1.00      ( ~ r2_hidden(X0_44,X1_44)
% 1.59/1.00      | r1_tarski(k1_enumset1(X0_44,X0_44,X0_44),X1_44) ),
% 1.59/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2282,plain,
% 1.59/1.00      ( r2_hidden(X0_44,X1_44) != iProver_top
% 1.59/1.00      | r1_tarski(k1_enumset1(X0_44,X0_44,X0_44),X1_44) = iProver_top ),
% 1.59/1.00      inference(predicate_to_equality,[status(thm)],[c_1832]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2,plain,
% 1.59/1.00      ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
% 1.59/1.00      | ~ r2_hidden(X0,X1) ),
% 1.59/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_1830,plain,
% 1.59/1.00      ( m1_subset_1(k1_enumset1(X0_44,X0_44,X0_44),k1_zfmisc_1(X1_44))
% 1.59/1.00      | ~ r2_hidden(X0_44,X1_44) ),
% 1.59/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2284,plain,
% 1.59/1.00      ( m1_subset_1(k1_enumset1(X0_44,X0_44,X0_44),k1_zfmisc_1(X1_44)) = iProver_top
% 1.59/1.00      | r2_hidden(X0_44,X1_44) != iProver_top ),
% 1.59/1.00      inference(predicate_to_equality,[status(thm)],[c_1830]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_1823,negated_conjecture,
% 1.59/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.59/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2291,plain,
% 1.59/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.59/1.00      inference(predicate_to_equality,[status(thm)],[c_1823]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_8,plain,
% 1.59/1.00      ( ~ v2_tex_2(X0,X1)
% 1.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.59/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.59/1.00      | ~ r1_tarski(X2,X0)
% 1.59/1.00      | ~ l1_pre_topc(X1)
% 1.59/1.00      | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2 ),
% 1.59/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_16,negated_conjecture,
% 1.59/1.00      ( l1_pre_topc(sK2) ),
% 1.59/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_488,plain,
% 1.59/1.00      ( ~ v2_tex_2(X0,X1)
% 1.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.59/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.59/1.00      | ~ r1_tarski(X2,X0)
% 1.59/1.00      | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2
% 1.59/1.00      | sK2 != X1 ),
% 1.59/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_489,plain,
% 1.59/1.00      ( ~ v2_tex_2(X0,sK2)
% 1.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ r1_tarski(X1,X0)
% 1.59/1.00      | k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,X1)) = X1 ),
% 1.59/1.00      inference(unflattening,[status(thm)],[c_488]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_1820,plain,
% 1.59/1.00      ( ~ v2_tex_2(X0_44,sK2)
% 1.59/1.00      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ r1_tarski(X1_44,X0_44)
% 1.59/1.00      | k9_subset_1(u1_struct_0(sK2),X0_44,sK1(sK2,X0_44,X1_44)) = X1_44 ),
% 1.59/1.00      inference(subtyping,[status(esa)],[c_489]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2294,plain,
% 1.59/1.00      ( k9_subset_1(u1_struct_0(sK2),X0_44,sK1(sK2,X0_44,X1_44)) = X1_44
% 1.59/1.00      | v2_tex_2(X0_44,sK2) != iProver_top
% 1.59/1.00      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.59/1.00      | m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.59/1.00      | r1_tarski(X1_44,X0_44) != iProver_top ),
% 1.59/1.00      inference(predicate_to_equality,[status(thm)],[c_1820]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2815,plain,
% 1.59/1.00      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0_44)) = X0_44
% 1.59/1.00      | v2_tex_2(sK3,sK2) != iProver_top
% 1.59/1.00      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.59/1.00      | r1_tarski(X0_44,sK3) != iProver_top ),
% 1.59/1.00      inference(superposition,[status(thm)],[c_2291,c_2294]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_14,negated_conjecture,
% 1.59/1.00      ( v2_tex_2(sK3,sK2) ),
% 1.59/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_19,plain,
% 1.59/1.00      ( v2_tex_2(sK3,sK2) = iProver_top ),
% 1.59/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2862,plain,
% 1.59/1.00      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0_44)) = X0_44
% 1.59/1.00      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.59/1.00      | r1_tarski(X0_44,sK3) != iProver_top ),
% 1.59/1.00      inference(global_propositional_subsumption,
% 1.59/1.00                [status(thm)],
% 1.59/1.00                [c_2815,c_19]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2873,plain,
% 1.59/1.00      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k1_enumset1(X0_44,X0_44,X0_44))) = k1_enumset1(X0_44,X0_44,X0_44)
% 1.59/1.00      | r2_hidden(X0_44,u1_struct_0(sK2)) != iProver_top
% 1.59/1.00      | r1_tarski(k1_enumset1(X0_44,X0_44,X0_44),sK3) != iProver_top ),
% 1.59/1.00      inference(superposition,[status(thm)],[c_2284,c_2862]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_3344,plain,
% 1.59/1.00      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k1_enumset1(X0_44,X0_44,X0_44))) = k1_enumset1(X0_44,X0_44,X0_44)
% 1.59/1.00      | r2_hidden(X0_44,u1_struct_0(sK2)) != iProver_top
% 1.59/1.00      | r2_hidden(X0_44,sK3) != iProver_top ),
% 1.59/1.00      inference(superposition,[status(thm)],[c_2282,c_2873]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_3759,plain,
% 1.59/1.00      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k1_enumset1(sK4,sK4,sK4))) = k1_enumset1(sK4,sK4,sK4)
% 1.59/1.00      | r2_hidden(sK4,sK3) != iProver_top ),
% 1.59/1.00      inference(superposition,[status(thm)],[c_2955,c_3344]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_131,plain,
% 1.59/1.00      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_enumset1(X0,X0,X0),X1) ),
% 1.59/1.00      inference(prop_impl,[status(thm)],[c_0]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_408,plain,
% 1.59/1.00      ( r1_tarski(k1_enumset1(X0,X0,X0),X1) | sK3 != X1 | sK4 != X0 ),
% 1.59/1.00      inference(resolution_lifted,[status(thm)],[c_131,c_12]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_409,plain,
% 1.59/1.00      ( r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3) ),
% 1.59/1.00      inference(unflattening,[status(thm)],[c_408]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2441,plain,
% 1.59/1.00      ( ~ v2_tex_2(sK3,sK2)
% 1.59/1.00      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ r1_tarski(X0_44,sK3)
% 1.59/1.00      | k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0_44)) = X0_44 ),
% 1.59/1.00      inference(instantiation,[status(thm)],[c_1820]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2525,plain,
% 1.59/1.00      ( ~ v2_tex_2(sK3,sK2)
% 1.59/1.00      | ~ m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3)
% 1.59/1.00      | k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k1_enumset1(sK4,sK4,sK4))) = k1_enumset1(sK4,sK4,sK4) ),
% 1.59/1.00      inference(instantiation,[status(thm)],[c_2441]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2600,plain,
% 1.59/1.00      ( m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ r2_hidden(sK4,u1_struct_0(sK2)) ),
% 1.59/1.00      inference(instantiation,[status(thm)],[c_1830]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2691,plain,
% 1.59/1.00      ( r2_hidden(sK4,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) ),
% 1.59/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2661]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2721,plain,
% 1.59/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ r2_hidden(sK4,sK3)
% 1.59/1.00      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.59/1.00      inference(instantiation,[status(thm)],[c_2719]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_3929,plain,
% 1.59/1.00      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k1_enumset1(sK4,sK4,sK4))) = k1_enumset1(sK4,sK4,sK4) ),
% 1.59/1.00      inference(global_propositional_subsumption,
% 1.59/1.00                [status(thm)],
% 1.59/1.00                [c_3759,c_15,c_14,c_12,c_409,c_2525,c_2600,c_2691,c_2721]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_11,negated_conjecture,
% 1.59/1.00      ( ~ v3_pre_topc(X0,sK2)
% 1.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | k1_enumset1(sK4,sK4,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X0) ),
% 1.59/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_1827,negated_conjecture,
% 1.59/1.00      ( ~ v3_pre_topc(X0_44,sK2)
% 1.59/1.00      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | k1_enumset1(sK4,sK4,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X0_44) ),
% 1.59/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2287,plain,
% 1.59/1.00      ( k1_enumset1(sK4,sK4,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X0_44)
% 1.59/1.00      | v3_pre_topc(X0_44,sK2) != iProver_top
% 1.59/1.00      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.59/1.00      inference(predicate_to_equality,[status(thm)],[c_1827]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_3932,plain,
% 1.59/1.00      ( v3_pre_topc(sK1(sK2,sK3,k1_enumset1(sK4,sK4,sK4)),sK2) != iProver_top
% 1.59/1.00      | m1_subset_1(sK1(sK2,sK3,k1_enumset1(sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.59/1.00      inference(superposition,[status(thm)],[c_3929,c_2287]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2601,plain,
% 1.59/1.00      ( m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.59/1.00      | r2_hidden(sK4,u1_struct_0(sK2)) != iProver_top ),
% 1.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2600]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_9,plain,
% 1.59/1.00      ( v3_pre_topc(sK1(X0,X1,X2),X0)
% 1.59/1.00      | ~ v2_tex_2(X1,X0)
% 1.59/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.59/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.59/1.00      | ~ r1_tarski(X2,X1)
% 1.59/1.00      | ~ l1_pre_topc(X0) ),
% 1.59/1.00      inference(cnf_transformation,[],[f36]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_446,plain,
% 1.59/1.00      ( v3_pre_topc(sK1(X0,X1,X2),X0)
% 1.59/1.00      | ~ v2_tex_2(X1,X0)
% 1.59/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.59/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.59/1.00      | ~ r1_tarski(X2,X1)
% 1.59/1.00      | sK2 != X0 ),
% 1.59/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_16]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_447,plain,
% 1.59/1.00      ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
% 1.59/1.00      | ~ v2_tex_2(X0,sK2)
% 1.59/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ r1_tarski(X1,X0) ),
% 1.59/1.00      inference(unflattening,[status(thm)],[c_446]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_1822,plain,
% 1.59/1.00      ( v3_pre_topc(sK1(sK2,X0_44,X1_44),sK2)
% 1.59/1.00      | ~ v2_tex_2(X0_44,sK2)
% 1.59/1.00      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ r1_tarski(X1_44,X0_44) ),
% 1.59/1.00      inference(subtyping,[status(esa)],[c_447]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2432,plain,
% 1.59/1.00      ( v3_pre_topc(sK1(sK2,sK3,X0_44),sK2)
% 1.59/1.00      | ~ v2_tex_2(sK3,sK2)
% 1.59/1.00      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ r1_tarski(X0_44,sK3) ),
% 1.59/1.00      inference(instantiation,[status(thm)],[c_1822]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2522,plain,
% 1.59/1.00      ( v3_pre_topc(sK1(sK2,sK3,k1_enumset1(sK4,sK4,sK4)),sK2)
% 1.59/1.00      | ~ v2_tex_2(sK3,sK2)
% 1.59/1.00      | ~ m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3) ),
% 1.59/1.00      inference(instantiation,[status(thm)],[c_2432]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2523,plain,
% 1.59/1.00      ( v3_pre_topc(sK1(sK2,sK3,k1_enumset1(sK4,sK4,sK4)),sK2) = iProver_top
% 1.59/1.00      | v2_tex_2(sK3,sK2) != iProver_top
% 1.59/1.00      | m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.59/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.59/1.00      | r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3) != iProver_top ),
% 1.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2522]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_10,plain,
% 1.59/1.00      ( ~ v2_tex_2(X0,X1)
% 1.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.59/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.59/1.00      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 1.59/1.00      | ~ r1_tarski(X2,X0)
% 1.59/1.00      | ~ l1_pre_topc(X1) ),
% 1.59/1.00      inference(cnf_transformation,[],[f35]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_467,plain,
% 1.59/1.00      ( ~ v2_tex_2(X0,X1)
% 1.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.59/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.59/1.00      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 1.59/1.00      | ~ r1_tarski(X2,X0)
% 1.59/1.00      | sK2 != X1 ),
% 1.59/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_16]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_468,plain,
% 1.59/1.00      ( ~ v2_tex_2(X0,sK2)
% 1.59/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ r1_tarski(X1,X0) ),
% 1.59/1.00      inference(unflattening,[status(thm)],[c_467]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_1821,plain,
% 1.59/1.00      ( ~ v2_tex_2(X0_44,sK2)
% 1.59/1.00      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | m1_subset_1(sK1(sK2,X0_44,X1_44),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ r1_tarski(X1_44,X0_44) ),
% 1.59/1.00      inference(subtyping,[status(esa)],[c_468]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2427,plain,
% 1.59/1.00      ( ~ v2_tex_2(sK3,sK2)
% 1.59/1.00      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | m1_subset_1(sK1(sK2,sK3,X0_44),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ r1_tarski(X0_44,sK3) ),
% 1.59/1.00      inference(instantiation,[status(thm)],[c_1821]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2519,plain,
% 1.59/1.00      ( ~ v2_tex_2(sK3,sK2)
% 1.59/1.00      | m1_subset_1(sK1(sK2,sK3,k1_enumset1(sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.59/1.00      | ~ r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3) ),
% 1.59/1.00      inference(instantiation,[status(thm)],[c_2427]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_2520,plain,
% 1.59/1.00      ( v2_tex_2(sK3,sK2) != iProver_top
% 1.59/1.00      | m1_subset_1(sK1(sK2,sK3,k1_enumset1(sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.59/1.00      | m1_subset_1(k1_enumset1(sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.59/1.00      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.59/1.00      | r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3) != iProver_top ),
% 1.59/1.00      inference(predicate_to_equality,[status(thm)],[c_2519]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(c_410,plain,
% 1.59/1.00      ( r1_tarski(k1_enumset1(sK4,sK4,sK4),sK3) = iProver_top ),
% 1.59/1.00      inference(predicate_to_equality,[status(thm)],[c_409]) ).
% 1.59/1.00  
% 1.59/1.00  cnf(contradiction,plain,
% 1.59/1.00      ( $false ),
% 1.59/1.00      inference(minisat,
% 1.59/1.00                [status(thm)],
% 1.59/1.00                [c_3932,c_2722,c_2661,c_2601,c_2523,c_2520,c_410,c_21,
% 1.59/1.00                 c_19,c_18]) ).
% 1.59/1.00  
% 1.59/1.00  
% 1.59/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.59/1.00  
% 1.59/1.00  ------                               Statistics
% 1.59/1.00  
% 1.59/1.00  ------ General
% 1.59/1.00  
% 1.59/1.00  abstr_ref_over_cycles:                  0
% 1.59/1.00  abstr_ref_under_cycles:                 0
% 1.59/1.00  gc_basic_clause_elim:                   0
% 1.59/1.00  forced_gc_time:                         0
% 1.59/1.00  parsing_time:                           0.007
% 1.59/1.00  unif_index_cands_time:                  0.
% 1.59/1.00  unif_index_add_time:                    0.
% 1.59/1.00  orderings_time:                         0.
% 1.59/1.00  out_proof_time:                         0.009
% 1.59/1.00  total_time:                             0.133
% 1.59/1.00  num_of_symbols:                         46
% 1.59/1.00  num_of_terms:                           2788
% 1.59/1.00  
% 1.59/1.00  ------ Preprocessing
% 1.59/1.00  
% 1.59/1.00  num_of_splits:                          0
% 1.59/1.00  num_of_split_atoms:                     0
% 1.59/1.00  num_of_reused_defs:                     0
% 1.59/1.00  num_eq_ax_congr_red:                    22
% 1.59/1.00  num_of_sem_filtered_clauses:            1
% 1.59/1.00  num_of_subtypes:                        2
% 1.59/1.00  monotx_restored_types:                  0
% 1.59/1.00  sat_num_of_epr_types:                   0
% 1.59/1.00  sat_num_of_non_cyclic_types:            0
% 1.59/1.00  sat_guarded_non_collapsed_types:        1
% 1.59/1.00  num_pure_diseq_elim:                    0
% 1.59/1.00  simp_replaced_by:                       0
% 1.59/1.00  res_preprocessed:                       86
% 1.59/1.00  prep_upred:                             0
% 1.59/1.00  prep_unflattend:                        72
% 1.59/1.00  smt_new_axioms:                         0
% 1.59/1.00  pred_elim_cands:                        6
% 1.59/1.00  pred_elim:                              1
% 1.59/1.00  pred_elim_cl:                           1
% 1.59/1.00  pred_elim_cycles:                       12
% 1.59/1.00  merged_defs:                            8
% 1.59/1.00  merged_defs_ncl:                        0
% 1.59/1.00  bin_hyper_res:                          8
% 1.59/1.00  prep_cycles:                            4
% 1.59/1.00  pred_elim_time:                         0.027
% 1.59/1.00  splitting_time:                         0.
% 1.59/1.00  sem_filter_time:                        0.
% 1.59/1.00  monotx_time:                            0.
% 1.59/1.00  subtype_inf_time:                       0.
% 1.59/1.00  
% 1.59/1.00  ------ Problem properties
% 1.59/1.00  
% 1.59/1.00  clauses:                                16
% 1.59/1.00  conjectures:                            5
% 1.59/1.00  epr:                                    3
% 1.59/1.00  horn:                                   13
% 1.59/1.00  ground:                                 4
% 1.59/1.00  unary:                                  4
% 1.59/1.00  binary:                                 3
% 1.59/1.00  lits:                                   45
% 1.59/1.00  lits_eq:                                3
% 1.59/1.00  fd_pure:                                0
% 1.59/1.00  fd_pseudo:                              0
% 1.59/1.00  fd_cond:                                0
% 1.59/1.00  fd_pseudo_cond:                         0
% 1.59/1.00  ac_symbols:                             0
% 1.59/1.00  
% 1.59/1.00  ------ Propositional Solver
% 1.59/1.00  
% 1.59/1.00  prop_solver_calls:                      29
% 1.59/1.00  prop_fast_solver_calls:                 955
% 1.59/1.00  smt_solver_calls:                       0
% 1.59/1.00  smt_fast_solver_calls:                  0
% 1.59/1.00  prop_num_of_clauses:                    939
% 1.59/1.00  prop_preprocess_simplified:             3985
% 1.59/1.00  prop_fo_subsumed:                       19
% 1.59/1.00  prop_solver_time:                       0.
% 1.59/1.00  smt_solver_time:                        0.
% 1.59/1.00  smt_fast_solver_time:                   0.
% 1.59/1.00  prop_fast_solver_time:                  0.
% 1.59/1.00  prop_unsat_core_time:                   0.
% 1.59/1.00  
% 1.59/1.00  ------ QBF
% 1.59/1.00  
% 1.59/1.00  qbf_q_res:                              0
% 1.59/1.00  qbf_num_tautologies:                    0
% 1.59/1.00  qbf_prep_cycles:                        0
% 1.59/1.00  
% 1.59/1.00  ------ BMC1
% 1.59/1.00  
% 1.59/1.00  bmc1_current_bound:                     -1
% 1.59/1.00  bmc1_last_solved_bound:                 -1
% 1.59/1.00  bmc1_unsat_core_size:                   -1
% 1.59/1.00  bmc1_unsat_core_parents_size:           -1
% 1.59/1.00  bmc1_merge_next_fun:                    0
% 1.59/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.59/1.00  
% 1.59/1.00  ------ Instantiation
% 1.59/1.00  
% 1.59/1.00  inst_num_of_clauses:                    288
% 1.59/1.00  inst_num_in_passive:                    63
% 1.59/1.00  inst_num_in_active:                     159
% 1.59/1.00  inst_num_in_unprocessed:                66
% 1.59/1.00  inst_num_of_loops:                      180
% 1.59/1.00  inst_num_of_learning_restarts:          0
% 1.59/1.00  inst_num_moves_active_passive:          16
% 1.59/1.00  inst_lit_activity:                      0
% 1.59/1.00  inst_lit_activity_moves:                0
% 1.59/1.00  inst_num_tautologies:                   0
% 1.59/1.00  inst_num_prop_implied:                  0
% 1.59/1.00  inst_num_existing_simplified:           0
% 1.59/1.00  inst_num_eq_res_simplified:             0
% 1.59/1.00  inst_num_child_elim:                    0
% 1.59/1.00  inst_num_of_dismatching_blockings:      9
% 1.59/1.00  inst_num_of_non_proper_insts:           253
% 1.59/1.00  inst_num_of_duplicates:                 0
% 1.59/1.00  inst_inst_num_from_inst_to_res:         0
% 1.59/1.00  inst_dismatching_checking_time:         0.
% 1.59/1.00  
% 1.59/1.00  ------ Resolution
% 1.59/1.00  
% 1.59/1.00  res_num_of_clauses:                     0
% 1.59/1.00  res_num_in_passive:                     0
% 1.59/1.00  res_num_in_active:                      0
% 1.59/1.00  res_num_of_loops:                       90
% 1.59/1.00  res_forward_subset_subsumed:            24
% 1.59/1.00  res_backward_subset_subsumed:           0
% 1.59/1.00  res_forward_subsumed:                   0
% 1.59/1.00  res_backward_subsumed:                  0
% 1.59/1.00  res_forward_subsumption_resolution:     2
% 1.59/1.00  res_backward_subsumption_resolution:    0
% 1.59/1.00  res_clause_to_clause_subsumption:       175
% 1.59/1.00  res_orphan_elimination:                 0
% 1.59/1.00  res_tautology_del:                      51
% 1.59/1.00  res_num_eq_res_simplified:              0
% 1.59/1.00  res_num_sel_changes:                    0
% 1.59/1.00  res_moves_from_active_to_pass:          0
% 1.59/1.00  
% 1.59/1.00  ------ Superposition
% 1.59/1.00  
% 1.59/1.00  sup_time_total:                         0.
% 1.59/1.00  sup_time_generating:                    0.
% 1.59/1.00  sup_time_sim_full:                      0.
% 1.59/1.00  sup_time_sim_immed:                     0.
% 1.59/1.00  
% 1.59/1.00  sup_num_of_clauses:                     41
% 1.59/1.00  sup_num_in_active:                      36
% 1.59/1.00  sup_num_in_passive:                     5
% 1.59/1.00  sup_num_of_loops:                       35
% 1.59/1.00  sup_fw_superposition:                   23
% 1.59/1.00  sup_bw_superposition:                   7
% 1.59/1.00  sup_immediate_simplified:               3
% 1.59/1.00  sup_given_eliminated:                   0
% 1.59/1.00  comparisons_done:                       0
% 1.59/1.00  comparisons_avoided:                    0
% 1.59/1.00  
% 1.59/1.00  ------ Simplifications
% 1.59/1.00  
% 1.59/1.00  
% 1.59/1.00  sim_fw_subset_subsumed:                 4
% 1.59/1.00  sim_bw_subset_subsumed:                 0
% 1.59/1.00  sim_fw_subsumed:                        0
% 1.59/1.00  sim_bw_subsumed:                        0
% 1.59/1.00  sim_fw_subsumption_res:                 0
% 1.59/1.00  sim_bw_subsumption_res:                 0
% 1.59/1.00  sim_tautology_del:                      1
% 1.59/1.00  sim_eq_tautology_del:                   0
% 1.59/1.00  sim_eq_res_simp:                        0
% 1.59/1.00  sim_fw_demodulated:                     0
% 1.59/1.00  sim_bw_demodulated:                     0
% 1.59/1.00  sim_light_normalised:                   0
% 1.59/1.00  sim_joinable_taut:                      0
% 1.59/1.00  sim_joinable_simp:                      0
% 1.59/1.00  sim_ac_normalised:                      0
% 1.59/1.00  sim_smt_subsumption:                    0
% 1.59/1.00  
%------------------------------------------------------------------------------
