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
% DateTime   : Thu Dec  3 12:26:00 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 447 expanded)
%              Number of clauses        :   67 ( 123 expanded)
%              Number of leaves         :   13 ( 127 expanded)
%              Depth                    :   22
%              Number of atoms          :  443 (2520 expanded)
%              Number of equality atoms :  119 ( 436 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v4_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f25])).

fof(f28,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
        & v4_pre_topc(sK3(X0,X1,X4),X0)
        & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
                    & v4_pre_topc(sK3(X0,X1,X4),X0)
                    & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f28,f27])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

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
                            & v4_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
                              & v4_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( k1_tarski(sK6) != k9_subset_1(u1_struct_0(X0),X1,X3)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK6,X1)
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ! [X3] :
                ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),sK5,X3)
                | ~ v4_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(X2,sK5)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & v2_tex_2(sK5,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),X1,X3)
                  | ~ v4_pre_topc(X3,sK4)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & v2_tex_2(X1,sK4)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ! [X3] :
        ( k1_tarski(sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X3)
        | ~ v4_pre_topc(X3,sK4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
    & r2_hidden(sK6,sK5)
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & v2_tex_2(sK5,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f14,f32,f31,f30])).

fof(f53,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_enumset1(X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f59])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_enumset1(X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f43,f59])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X3] :
      ( k1_tarski(sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X3)
      | ~ v4_pre_topc(X3,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X3] :
      ( k1_enumset1(sK6,sK6,sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X3)
      | ~ v4_pre_topc(X3,sK4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( v4_pre_topc(sK3(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_16,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_416,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_417,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK3(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_3068,plain,
    ( v2_tex_2(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK3(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3073,plain,
    ( r2_hidden(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_enumset1(X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3078,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k1_enumset1(X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3076,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3070,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_14,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,sK3(X1,X0,X2)) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_437,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | k9_subset_1(u1_struct_0(X1),X0,sK3(X1,X0,X2)) = X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_438,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK4),X0,sK3(sK4,X0,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_3067,plain,
    ( k9_subset_1(u1_struct_0(sK4),X0,sK3(sK4,X0,X1)) = X1
    | v2_tex_2(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_438])).

cnf(c_3379,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0
    | v2_tex_2(sK5,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3070,c_3067])).

cnf(c_24,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_726,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK4),X0,sK3(sK4,X0,X1)) = X1
    | sK5 != X0
    | sK4 != sK4 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_438])).

cnf(c_727,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X0,sK5)
    | k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_728,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_3826,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3379,c_24,c_728])).

cnf(c_3833,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0
    | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3076,c_3826])).

cnf(c_4424,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k1_enumset1(X0,X0,X0))) = k1_enumset1(X0,X0,X0)
    | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(k1_enumset1(X0,X0,X0),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3078,c_3833])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3075,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3664,plain,
    ( r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3070,c_3075])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_enumset1(X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3692,plain,
    ( r2_hidden(X0,sK5)
    | ~ r1_tarski(k1_enumset1(X0,X0,X0),sK5) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3693,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r1_tarski(k1_enumset1(X0,X0,X0),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3692])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3790,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,u1_struct_0(sK4))
    | ~ r1_tarski(X1,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_7253,plain,
    ( r2_hidden(X0,u1_struct_0(sK4))
    | ~ r2_hidden(X0,sK5)
    | ~ r1_tarski(sK5,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3790])).

cnf(c_7254,plain,
    ( r2_hidden(X0,u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7253])).

cnf(c_9135,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k1_enumset1(X0,X0,X0))) = k1_enumset1(X0,X0,X0)
    | r1_tarski(k1_enumset1(X0,X0,X0),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4424,c_3664,c_3693,c_7254])).

cnf(c_9145,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k1_enumset1(X0,X0,X0))) = k1_enumset1(X0,X0,X0)
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3078,c_9135])).

cnf(c_9270,plain,
    ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k1_enumset1(sK6,sK6,sK6))) = k1_enumset1(sK6,sK6,sK6) ),
    inference(superposition,[status(thm)],[c_3073,c_9145])).

cnf(c_17,negated_conjecture,
    ( ~ v4_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k1_enumset1(sK6,sK6,sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3074,plain,
    ( k1_enumset1(sK6,sK6,sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X0)
    | v4_pre_topc(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9315,plain,
    ( v4_pre_topc(sK3(sK4,sK5,k1_enumset1(sK6,sK6,sK6)),sK4) != iProver_top
    | m1_subset_1(sK3(sK4,sK5,k1_enumset1(sK6,sK6,sK6)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9270,c_3074])).

cnf(c_25,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_27,plain,
    ( r2_hidden(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3315,plain,
    ( ~ r2_hidden(X0,sK5)
    | r1_tarski(k1_enumset1(X0,X0,X0),sK5) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3702,plain,
    ( ~ r2_hidden(sK6,sK5)
    | r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_3315])).

cnf(c_3703,plain,
    ( r2_hidden(sK6,sK5) != iProver_top
    | r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3702])).

cnf(c_15,plain,
    ( v4_pre_topc(sK3(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X2,X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_395,plain,
    ( v4_pre_topc(sK3(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X2,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_396,plain,
    ( v4_pre_topc(sK3(sK4,X0,X1),sK4)
    | ~ v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_3251,plain,
    ( v4_pre_topc(sK3(sK4,sK5,X0),sK4)
    | ~ v2_tex_2(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_396])).

cnf(c_3314,plain,
    ( v4_pre_topc(sK3(sK4,sK5,k1_enumset1(X0,X0,X0)),sK4)
    | ~ v2_tex_2(sK5,sK4)
    | ~ m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(k1_enumset1(X0,X0,X0),sK5) ),
    inference(instantiation,[status(thm)],[c_3251])).

cnf(c_3886,plain,
    ( v4_pre_topc(sK3(sK4,sK5,k1_enumset1(sK6,sK6,sK6)),sK4)
    | ~ v2_tex_2(sK5,sK4)
    | ~ m1_subset_1(k1_enumset1(sK6,sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_3314])).

cnf(c_3887,plain,
    ( v4_pre_topc(sK3(sK4,sK5,k1_enumset1(sK6,sK6,sK6)),sK4) = iProver_top
    | v2_tex_2(sK5,sK4) != iProver_top
    | m1_subset_1(k1_enumset1(sK6,sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3886])).

cnf(c_3083,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4451,plain,
    ( r2_hidden(sK6,X0) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3073,c_3083])).

cnf(c_4490,plain,
    ( r2_hidden(sK6,u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3664,c_4451])).

cnf(c_3264,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3422,plain,
    ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(k1_enumset1(X0,X0,X0),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3264])).

cnf(c_4736,plain,
    ( m1_subset_1(k1_enumset1(sK6,sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(k1_enumset1(sK6,sK6,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3422])).

cnf(c_4737,plain,
    ( m1_subset_1(k1_enumset1(sK6,sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | r1_tarski(k1_enumset1(sK6,sK6,sK6),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4736])).

cnf(c_5221,plain,
    ( ~ r2_hidden(sK6,X0)
    | r1_tarski(k1_enumset1(sK6,sK6,sK6),X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8993,plain,
    ( ~ r2_hidden(sK6,u1_struct_0(sK4))
    | r1_tarski(k1_enumset1(sK6,sK6,sK6),u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_5221])).

cnf(c_8996,plain,
    ( r2_hidden(sK6,u1_struct_0(sK4)) != iProver_top
    | r1_tarski(k1_enumset1(sK6,sK6,sK6),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8993])).

cnf(c_9617,plain,
    ( m1_subset_1(sK3(sK4,sK5,k1_enumset1(sK6,sK6,sK6)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9315,c_24,c_25,c_27,c_3703,c_3887,c_4490,c_4737,c_8996])).

cnf(c_9623,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top
    | m1_subset_1(k1_enumset1(sK6,sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3068,c_9617])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9623,c_8996,c_4737,c_4490,c_3703,c_27,c_25,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.02/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/0.99  
% 3.02/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.02/0.99  
% 3.02/0.99  ------  iProver source info
% 3.02/0.99  
% 3.02/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.02/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.02/0.99  git: non_committed_changes: false
% 3.02/0.99  git: last_make_outside_of_git: false
% 3.02/0.99  
% 3.02/0.99  ------ 
% 3.02/0.99  
% 3.02/0.99  ------ Input Options
% 3.02/0.99  
% 3.02/0.99  --out_options                           all
% 3.02/0.99  --tptp_safe_out                         true
% 3.02/0.99  --problem_path                          ""
% 3.02/0.99  --include_path                          ""
% 3.02/0.99  --clausifier                            res/vclausify_rel
% 3.02/0.99  --clausifier_options                    --mode clausify
% 3.02/0.99  --stdin                                 false
% 3.02/0.99  --stats_out                             all
% 3.02/0.99  
% 3.02/0.99  ------ General Options
% 3.02/0.99  
% 3.02/0.99  --fof                                   false
% 3.02/0.99  --time_out_real                         305.
% 3.02/0.99  --time_out_virtual                      -1.
% 3.02/0.99  --symbol_type_check                     false
% 3.02/0.99  --clausify_out                          false
% 3.02/0.99  --sig_cnt_out                           false
% 3.02/0.99  --trig_cnt_out                          false
% 3.02/0.99  --trig_cnt_out_tolerance                1.
% 3.02/0.99  --trig_cnt_out_sk_spl                   false
% 3.02/0.99  --abstr_cl_out                          false
% 3.02/0.99  
% 3.02/0.99  ------ Global Options
% 3.02/0.99  
% 3.02/0.99  --schedule                              default
% 3.02/0.99  --add_important_lit                     false
% 3.02/0.99  --prop_solver_per_cl                    1000
% 3.02/0.99  --min_unsat_core                        false
% 3.02/0.99  --soft_assumptions                      false
% 3.02/0.99  --soft_lemma_size                       3
% 3.02/0.99  --prop_impl_unit_size                   0
% 3.02/0.99  --prop_impl_unit                        []
% 3.02/0.99  --share_sel_clauses                     true
% 3.02/0.99  --reset_solvers                         false
% 3.02/0.99  --bc_imp_inh                            [conj_cone]
% 3.02/0.99  --conj_cone_tolerance                   3.
% 3.02/0.99  --extra_neg_conj                        none
% 3.02/0.99  --large_theory_mode                     true
% 3.02/0.99  --prolific_symb_bound                   200
% 3.02/0.99  --lt_threshold                          2000
% 3.02/0.99  --clause_weak_htbl                      true
% 3.02/0.99  --gc_record_bc_elim                     false
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing Options
% 3.02/0.99  
% 3.02/0.99  --preprocessing_flag                    true
% 3.02/0.99  --time_out_prep_mult                    0.1
% 3.02/0.99  --splitting_mode                        input
% 3.02/0.99  --splitting_grd                         true
% 3.02/0.99  --splitting_cvd                         false
% 3.02/0.99  --splitting_cvd_svl                     false
% 3.02/0.99  --splitting_nvd                         32
% 3.02/0.99  --sub_typing                            true
% 3.02/0.99  --prep_gs_sim                           true
% 3.02/0.99  --prep_unflatten                        true
% 3.02/0.99  --prep_res_sim                          true
% 3.02/0.99  --prep_upred                            true
% 3.02/0.99  --prep_sem_filter                       exhaustive
% 3.02/0.99  --prep_sem_filter_out                   false
% 3.02/0.99  --pred_elim                             true
% 3.02/0.99  --res_sim_input                         true
% 3.02/0.99  --eq_ax_congr_red                       true
% 3.02/0.99  --pure_diseq_elim                       true
% 3.02/0.99  --brand_transform                       false
% 3.02/0.99  --non_eq_to_eq                          false
% 3.02/0.99  --prep_def_merge                        true
% 3.02/0.99  --prep_def_merge_prop_impl              false
% 3.02/0.99  --prep_def_merge_mbd                    true
% 3.02/0.99  --prep_def_merge_tr_red                 false
% 3.02/0.99  --prep_def_merge_tr_cl                  false
% 3.02/0.99  --smt_preprocessing                     true
% 3.02/0.99  --smt_ac_axioms                         fast
% 3.02/0.99  --preprocessed_out                      false
% 3.02/0.99  --preprocessed_stats                    false
% 3.02/0.99  
% 3.02/0.99  ------ Abstraction refinement Options
% 3.02/0.99  
% 3.02/0.99  --abstr_ref                             []
% 3.02/0.99  --abstr_ref_prep                        false
% 3.02/0.99  --abstr_ref_until_sat                   false
% 3.02/0.99  --abstr_ref_sig_restrict                funpre
% 3.02/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/0.99  --abstr_ref_under                       []
% 3.02/0.99  
% 3.02/0.99  ------ SAT Options
% 3.02/0.99  
% 3.02/0.99  --sat_mode                              false
% 3.02/0.99  --sat_fm_restart_options                ""
% 3.02/0.99  --sat_gr_def                            false
% 3.02/0.99  --sat_epr_types                         true
% 3.02/0.99  --sat_non_cyclic_types                  false
% 3.02/0.99  --sat_finite_models                     false
% 3.02/0.99  --sat_fm_lemmas                         false
% 3.02/0.99  --sat_fm_prep                           false
% 3.02/0.99  --sat_fm_uc_incr                        true
% 3.02/0.99  --sat_out_model                         small
% 3.02/0.99  --sat_out_clauses                       false
% 3.02/0.99  
% 3.02/0.99  ------ QBF Options
% 3.02/0.99  
% 3.02/0.99  --qbf_mode                              false
% 3.02/0.99  --qbf_elim_univ                         false
% 3.02/0.99  --qbf_dom_inst                          none
% 3.02/0.99  --qbf_dom_pre_inst                      false
% 3.02/0.99  --qbf_sk_in                             false
% 3.02/0.99  --qbf_pred_elim                         true
% 3.02/0.99  --qbf_split                             512
% 3.02/0.99  
% 3.02/0.99  ------ BMC1 Options
% 3.02/0.99  
% 3.02/0.99  --bmc1_incremental                      false
% 3.02/0.99  --bmc1_axioms                           reachable_all
% 3.02/0.99  --bmc1_min_bound                        0
% 3.02/0.99  --bmc1_max_bound                        -1
% 3.02/0.99  --bmc1_max_bound_default                -1
% 3.02/0.99  --bmc1_symbol_reachability              true
% 3.02/0.99  --bmc1_property_lemmas                  false
% 3.02/0.99  --bmc1_k_induction                      false
% 3.02/0.99  --bmc1_non_equiv_states                 false
% 3.02/0.99  --bmc1_deadlock                         false
% 3.02/0.99  --bmc1_ucm                              false
% 3.02/0.99  --bmc1_add_unsat_core                   none
% 3.02/0.99  --bmc1_unsat_core_children              false
% 3.02/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/0.99  --bmc1_out_stat                         full
% 3.02/0.99  --bmc1_ground_init                      false
% 3.02/0.99  --bmc1_pre_inst_next_state              false
% 3.02/0.99  --bmc1_pre_inst_state                   false
% 3.02/0.99  --bmc1_pre_inst_reach_state             false
% 3.02/0.99  --bmc1_out_unsat_core                   false
% 3.02/0.99  --bmc1_aig_witness_out                  false
% 3.02/0.99  --bmc1_verbose                          false
% 3.02/0.99  --bmc1_dump_clauses_tptp                false
% 3.02/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.02/0.99  --bmc1_dump_file                        -
% 3.02/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.02/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.02/0.99  --bmc1_ucm_extend_mode                  1
% 3.02/0.99  --bmc1_ucm_init_mode                    2
% 3.02/0.99  --bmc1_ucm_cone_mode                    none
% 3.02/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.02/0.99  --bmc1_ucm_relax_model                  4
% 3.02/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.02/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/0.99  --bmc1_ucm_layered_model                none
% 3.02/0.99  --bmc1_ucm_max_lemma_size               10
% 3.02/0.99  
% 3.02/0.99  ------ AIG Options
% 3.02/0.99  
% 3.02/0.99  --aig_mode                              false
% 3.02/0.99  
% 3.02/0.99  ------ Instantiation Options
% 3.02/0.99  
% 3.02/0.99  --instantiation_flag                    true
% 3.02/0.99  --inst_sos_flag                         false
% 3.02/0.99  --inst_sos_phase                        true
% 3.02/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel_side                     num_symb
% 3.02/0.99  --inst_solver_per_active                1400
% 3.02/0.99  --inst_solver_calls_frac                1.
% 3.02/0.99  --inst_passive_queue_type               priority_queues
% 3.02/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/0.99  --inst_passive_queues_freq              [25;2]
% 3.02/0.99  --inst_dismatching                      true
% 3.02/0.99  --inst_eager_unprocessed_to_passive     true
% 3.02/0.99  --inst_prop_sim_given                   true
% 3.02/0.99  --inst_prop_sim_new                     false
% 3.02/0.99  --inst_subs_new                         false
% 3.02/0.99  --inst_eq_res_simp                      false
% 3.02/0.99  --inst_subs_given                       false
% 3.02/0.99  --inst_orphan_elimination               true
% 3.02/0.99  --inst_learning_loop_flag               true
% 3.02/0.99  --inst_learning_start                   3000
% 3.02/0.99  --inst_learning_factor                  2
% 3.02/0.99  --inst_start_prop_sim_after_learn       3
% 3.02/0.99  --inst_sel_renew                        solver
% 3.02/0.99  --inst_lit_activity_flag                true
% 3.02/0.99  --inst_restr_to_given                   false
% 3.02/0.99  --inst_activity_threshold               500
% 3.02/0.99  --inst_out_proof                        true
% 3.02/0.99  
% 3.02/0.99  ------ Resolution Options
% 3.02/0.99  
% 3.02/0.99  --resolution_flag                       true
% 3.02/0.99  --res_lit_sel                           adaptive
% 3.02/0.99  --res_lit_sel_side                      none
% 3.02/0.99  --res_ordering                          kbo
% 3.02/0.99  --res_to_prop_solver                    active
% 3.02/0.99  --res_prop_simpl_new                    false
% 3.02/0.99  --res_prop_simpl_given                  true
% 3.02/0.99  --res_passive_queue_type                priority_queues
% 3.02/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/0.99  --res_passive_queues_freq               [15;5]
% 3.02/0.99  --res_forward_subs                      full
% 3.02/0.99  --res_backward_subs                     full
% 3.02/0.99  --res_forward_subs_resolution           true
% 3.02/0.99  --res_backward_subs_resolution          true
% 3.02/0.99  --res_orphan_elimination                true
% 3.02/0.99  --res_time_limit                        2.
% 3.02/0.99  --res_out_proof                         true
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Options
% 3.02/0.99  
% 3.02/0.99  --superposition_flag                    true
% 3.02/0.99  --sup_passive_queue_type                priority_queues
% 3.02/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.02/0.99  --demod_completeness_check              fast
% 3.02/0.99  --demod_use_ground                      true
% 3.02/0.99  --sup_to_prop_solver                    passive
% 3.02/0.99  --sup_prop_simpl_new                    true
% 3.02/0.99  --sup_prop_simpl_given                  true
% 3.02/0.99  --sup_fun_splitting                     false
% 3.02/0.99  --sup_smt_interval                      50000
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Simplification Setup
% 3.02/0.99  
% 3.02/0.99  --sup_indices_passive                   []
% 3.02/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_full_bw                           [BwDemod]
% 3.02/0.99  --sup_immed_triv                        [TrivRules]
% 3.02/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_immed_bw_main                     []
% 3.02/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  
% 3.02/0.99  ------ Combination Options
% 3.02/0.99  
% 3.02/0.99  --comb_res_mult                         3
% 3.02/0.99  --comb_sup_mult                         2
% 3.02/0.99  --comb_inst_mult                        10
% 3.02/0.99  
% 3.02/0.99  ------ Debug Options
% 3.02/0.99  
% 3.02/0.99  --dbg_backtrace                         false
% 3.02/0.99  --dbg_dump_prop_clauses                 false
% 3.02/0.99  --dbg_dump_prop_clauses_file            -
% 3.02/0.99  --dbg_out_stat                          false
% 3.02/0.99  ------ Parsing...
% 3.02/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.02/0.99  ------ Proving...
% 3.02/0.99  ------ Problem Properties 
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  clauses                                 22
% 3.02/0.99  conjectures                             5
% 3.02/0.99  EPR                                     3
% 3.02/0.99  Horn                                    18
% 3.02/0.99  unary                                   5
% 3.02/0.99  binary                                  7
% 3.02/0.99  lits                                    57
% 3.02/0.99  lits eq                                 8
% 3.02/0.99  fd_pure                                 0
% 3.02/0.99  fd_pseudo                               0
% 3.02/0.99  fd_cond                                 0
% 3.02/0.99  fd_pseudo_cond                          2
% 3.02/0.99  AC symbols                              0
% 3.02/0.99  
% 3.02/0.99  ------ Schedule dynamic 5 is on 
% 3.02/0.99  
% 3.02/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  ------ 
% 3.02/0.99  Current options:
% 3.02/0.99  ------ 
% 3.02/0.99  
% 3.02/0.99  ------ Input Options
% 3.02/0.99  
% 3.02/0.99  --out_options                           all
% 3.02/0.99  --tptp_safe_out                         true
% 3.02/0.99  --problem_path                          ""
% 3.02/0.99  --include_path                          ""
% 3.02/0.99  --clausifier                            res/vclausify_rel
% 3.02/0.99  --clausifier_options                    --mode clausify
% 3.02/0.99  --stdin                                 false
% 3.02/0.99  --stats_out                             all
% 3.02/0.99  
% 3.02/0.99  ------ General Options
% 3.02/0.99  
% 3.02/0.99  --fof                                   false
% 3.02/0.99  --time_out_real                         305.
% 3.02/0.99  --time_out_virtual                      -1.
% 3.02/0.99  --symbol_type_check                     false
% 3.02/0.99  --clausify_out                          false
% 3.02/0.99  --sig_cnt_out                           false
% 3.02/0.99  --trig_cnt_out                          false
% 3.02/0.99  --trig_cnt_out_tolerance                1.
% 3.02/0.99  --trig_cnt_out_sk_spl                   false
% 3.02/0.99  --abstr_cl_out                          false
% 3.02/0.99  
% 3.02/0.99  ------ Global Options
% 3.02/0.99  
% 3.02/0.99  --schedule                              default
% 3.02/0.99  --add_important_lit                     false
% 3.02/0.99  --prop_solver_per_cl                    1000
% 3.02/0.99  --min_unsat_core                        false
% 3.02/0.99  --soft_assumptions                      false
% 3.02/0.99  --soft_lemma_size                       3
% 3.02/0.99  --prop_impl_unit_size                   0
% 3.02/0.99  --prop_impl_unit                        []
% 3.02/0.99  --share_sel_clauses                     true
% 3.02/0.99  --reset_solvers                         false
% 3.02/0.99  --bc_imp_inh                            [conj_cone]
% 3.02/0.99  --conj_cone_tolerance                   3.
% 3.02/0.99  --extra_neg_conj                        none
% 3.02/0.99  --large_theory_mode                     true
% 3.02/0.99  --prolific_symb_bound                   200
% 3.02/0.99  --lt_threshold                          2000
% 3.02/0.99  --clause_weak_htbl                      true
% 3.02/0.99  --gc_record_bc_elim                     false
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing Options
% 3.02/0.99  
% 3.02/0.99  --preprocessing_flag                    true
% 3.02/0.99  --time_out_prep_mult                    0.1
% 3.02/0.99  --splitting_mode                        input
% 3.02/0.99  --splitting_grd                         true
% 3.02/0.99  --splitting_cvd                         false
% 3.02/0.99  --splitting_cvd_svl                     false
% 3.02/0.99  --splitting_nvd                         32
% 3.02/0.99  --sub_typing                            true
% 3.02/0.99  --prep_gs_sim                           true
% 3.02/0.99  --prep_unflatten                        true
% 3.02/0.99  --prep_res_sim                          true
% 3.02/0.99  --prep_upred                            true
% 3.02/0.99  --prep_sem_filter                       exhaustive
% 3.02/0.99  --prep_sem_filter_out                   false
% 3.02/0.99  --pred_elim                             true
% 3.02/0.99  --res_sim_input                         true
% 3.02/0.99  --eq_ax_congr_red                       true
% 3.02/0.99  --pure_diseq_elim                       true
% 3.02/0.99  --brand_transform                       false
% 3.02/0.99  --non_eq_to_eq                          false
% 3.02/0.99  --prep_def_merge                        true
% 3.02/0.99  --prep_def_merge_prop_impl              false
% 3.02/0.99  --prep_def_merge_mbd                    true
% 3.02/0.99  --prep_def_merge_tr_red                 false
% 3.02/0.99  --prep_def_merge_tr_cl                  false
% 3.02/0.99  --smt_preprocessing                     true
% 3.02/0.99  --smt_ac_axioms                         fast
% 3.02/0.99  --preprocessed_out                      false
% 3.02/0.99  --preprocessed_stats                    false
% 3.02/0.99  
% 3.02/0.99  ------ Abstraction refinement Options
% 3.02/0.99  
% 3.02/0.99  --abstr_ref                             []
% 3.02/0.99  --abstr_ref_prep                        false
% 3.02/0.99  --abstr_ref_until_sat                   false
% 3.02/0.99  --abstr_ref_sig_restrict                funpre
% 3.02/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/0.99  --abstr_ref_under                       []
% 3.02/0.99  
% 3.02/0.99  ------ SAT Options
% 3.02/0.99  
% 3.02/0.99  --sat_mode                              false
% 3.02/0.99  --sat_fm_restart_options                ""
% 3.02/0.99  --sat_gr_def                            false
% 3.02/0.99  --sat_epr_types                         true
% 3.02/0.99  --sat_non_cyclic_types                  false
% 3.02/0.99  --sat_finite_models                     false
% 3.02/0.99  --sat_fm_lemmas                         false
% 3.02/0.99  --sat_fm_prep                           false
% 3.02/0.99  --sat_fm_uc_incr                        true
% 3.02/0.99  --sat_out_model                         small
% 3.02/0.99  --sat_out_clauses                       false
% 3.02/0.99  
% 3.02/0.99  ------ QBF Options
% 3.02/0.99  
% 3.02/0.99  --qbf_mode                              false
% 3.02/0.99  --qbf_elim_univ                         false
% 3.02/0.99  --qbf_dom_inst                          none
% 3.02/0.99  --qbf_dom_pre_inst                      false
% 3.02/0.99  --qbf_sk_in                             false
% 3.02/0.99  --qbf_pred_elim                         true
% 3.02/0.99  --qbf_split                             512
% 3.02/0.99  
% 3.02/0.99  ------ BMC1 Options
% 3.02/0.99  
% 3.02/0.99  --bmc1_incremental                      false
% 3.02/0.99  --bmc1_axioms                           reachable_all
% 3.02/0.99  --bmc1_min_bound                        0
% 3.02/0.99  --bmc1_max_bound                        -1
% 3.02/0.99  --bmc1_max_bound_default                -1
% 3.02/0.99  --bmc1_symbol_reachability              true
% 3.02/0.99  --bmc1_property_lemmas                  false
% 3.02/0.99  --bmc1_k_induction                      false
% 3.02/0.99  --bmc1_non_equiv_states                 false
% 3.02/0.99  --bmc1_deadlock                         false
% 3.02/0.99  --bmc1_ucm                              false
% 3.02/0.99  --bmc1_add_unsat_core                   none
% 3.02/0.99  --bmc1_unsat_core_children              false
% 3.02/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/0.99  --bmc1_out_stat                         full
% 3.02/0.99  --bmc1_ground_init                      false
% 3.02/0.99  --bmc1_pre_inst_next_state              false
% 3.02/0.99  --bmc1_pre_inst_state                   false
% 3.02/0.99  --bmc1_pre_inst_reach_state             false
% 3.02/0.99  --bmc1_out_unsat_core                   false
% 3.02/0.99  --bmc1_aig_witness_out                  false
% 3.02/0.99  --bmc1_verbose                          false
% 3.02/0.99  --bmc1_dump_clauses_tptp                false
% 3.02/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.02/0.99  --bmc1_dump_file                        -
% 3.02/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.02/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.02/0.99  --bmc1_ucm_extend_mode                  1
% 3.02/0.99  --bmc1_ucm_init_mode                    2
% 3.02/0.99  --bmc1_ucm_cone_mode                    none
% 3.02/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.02/0.99  --bmc1_ucm_relax_model                  4
% 3.02/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.02/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/0.99  --bmc1_ucm_layered_model                none
% 3.02/0.99  --bmc1_ucm_max_lemma_size               10
% 3.02/0.99  
% 3.02/0.99  ------ AIG Options
% 3.02/0.99  
% 3.02/0.99  --aig_mode                              false
% 3.02/0.99  
% 3.02/0.99  ------ Instantiation Options
% 3.02/0.99  
% 3.02/0.99  --instantiation_flag                    true
% 3.02/0.99  --inst_sos_flag                         false
% 3.02/0.99  --inst_sos_phase                        true
% 3.02/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel_side                     none
% 3.02/0.99  --inst_solver_per_active                1400
% 3.02/0.99  --inst_solver_calls_frac                1.
% 3.02/0.99  --inst_passive_queue_type               priority_queues
% 3.02/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/0.99  --inst_passive_queues_freq              [25;2]
% 3.02/0.99  --inst_dismatching                      true
% 3.02/0.99  --inst_eager_unprocessed_to_passive     true
% 3.02/0.99  --inst_prop_sim_given                   true
% 3.02/0.99  --inst_prop_sim_new                     false
% 3.02/0.99  --inst_subs_new                         false
% 3.02/0.99  --inst_eq_res_simp                      false
% 3.02/0.99  --inst_subs_given                       false
% 3.02/0.99  --inst_orphan_elimination               true
% 3.02/0.99  --inst_learning_loop_flag               true
% 3.02/0.99  --inst_learning_start                   3000
% 3.02/0.99  --inst_learning_factor                  2
% 3.02/0.99  --inst_start_prop_sim_after_learn       3
% 3.02/0.99  --inst_sel_renew                        solver
% 3.02/0.99  --inst_lit_activity_flag                true
% 3.02/0.99  --inst_restr_to_given                   false
% 3.02/0.99  --inst_activity_threshold               500
% 3.02/0.99  --inst_out_proof                        true
% 3.02/0.99  
% 3.02/0.99  ------ Resolution Options
% 3.02/0.99  
% 3.02/0.99  --resolution_flag                       false
% 3.02/0.99  --res_lit_sel                           adaptive
% 3.02/0.99  --res_lit_sel_side                      none
% 3.02/0.99  --res_ordering                          kbo
% 3.02/0.99  --res_to_prop_solver                    active
% 3.02/0.99  --res_prop_simpl_new                    false
% 3.02/0.99  --res_prop_simpl_given                  true
% 3.02/0.99  --res_passive_queue_type                priority_queues
% 3.02/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/0.99  --res_passive_queues_freq               [15;5]
% 3.02/0.99  --res_forward_subs                      full
% 3.02/0.99  --res_backward_subs                     full
% 3.02/0.99  --res_forward_subs_resolution           true
% 3.02/0.99  --res_backward_subs_resolution          true
% 3.02/0.99  --res_orphan_elimination                true
% 3.02/0.99  --res_time_limit                        2.
% 3.02/0.99  --res_out_proof                         true
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Options
% 3.02/0.99  
% 3.02/0.99  --superposition_flag                    true
% 3.02/0.99  --sup_passive_queue_type                priority_queues
% 3.02/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.02/0.99  --demod_completeness_check              fast
% 3.02/0.99  --demod_use_ground                      true
% 3.02/0.99  --sup_to_prop_solver                    passive
% 3.02/0.99  --sup_prop_simpl_new                    true
% 3.02/0.99  --sup_prop_simpl_given                  true
% 3.02/0.99  --sup_fun_splitting                     false
% 3.02/0.99  --sup_smt_interval                      50000
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Simplification Setup
% 3.02/0.99  
% 3.02/0.99  --sup_indices_passive                   []
% 3.02/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_full_bw                           [BwDemod]
% 3.02/0.99  --sup_immed_triv                        [TrivRules]
% 3.02/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_immed_bw_main                     []
% 3.02/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  
% 3.02/0.99  ------ Combination Options
% 3.02/0.99  
% 3.02/0.99  --comb_res_mult                         3
% 3.02/0.99  --comb_sup_mult                         2
% 3.02/0.99  --comb_inst_mult                        10
% 3.02/0.99  
% 3.02/0.99  ------ Debug Options
% 3.02/0.99  
% 3.02/0.99  --dbg_backtrace                         false
% 3.02/0.99  --dbg_dump_prop_clauses                 false
% 3.02/0.99  --dbg_dump_prop_clauses_file            -
% 3.02/0.99  --dbg_out_stat                          false
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  ------ Proving...
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  % SZS status Theorem for theBenchmark.p
% 3.02/0.99  
% 3.02/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.02/0.99  
% 3.02/0.99  fof(f7,axiom,(
% 3.02/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f11,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.02/0.99    inference(ennf_transformation,[],[f7])).
% 3.02/0.99  
% 3.02/0.99  fof(f12,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.02/0.99    inference(flattening,[],[f11])).
% 3.02/0.99  
% 3.02/0.99  fof(f25,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.02/0.99    inference(nnf_transformation,[],[f12])).
% 3.02/0.99  
% 3.02/0.99  fof(f26,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.02/0.99    inference(rectify,[],[f25])).
% 3.02/0.99  
% 3.02/0.99  fof(f28,plain,(
% 3.02/0.99    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v4_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.02/0.99    introduced(choice_axiom,[])).
% 3.02/0.99  
% 3.02/0.99  fof(f27,plain,(
% 3.02/0.99    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.02/0.99    introduced(choice_axiom,[])).
% 3.02/0.99  
% 3.02/0.99  fof(f29,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v4_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f28,f27])).
% 3.02/0.99  
% 3.02/0.99  fof(f47,plain,(
% 3.02/0.99    ( ! [X4,X0,X1] : (m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f29])).
% 3.02/0.99  
% 3.02/0.99  fof(f8,conjecture,(
% 3.02/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f9,negated_conjecture,(
% 3.02/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 3.02/0.99    inference(negated_conjecture,[],[f8])).
% 3.02/0.99  
% 3.02/0.99  fof(f13,plain,(
% 3.02/0.99    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.02/0.99    inference(ennf_transformation,[],[f9])).
% 3.02/0.99  
% 3.02/0.99  fof(f14,plain,(
% 3.02/0.99    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.02/0.99    inference(flattening,[],[f13])).
% 3.02/0.99  
% 3.02/0.99  fof(f32,plain,(
% 3.02/0.99    ( ! [X0,X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (k1_tarski(sK6) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK6,X1) & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 3.02/0.99    introduced(choice_axiom,[])).
% 3.02/0.99  
% 3.02/0.99  fof(f31,plain,(
% 3.02/0.99    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),sK5,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,sK5) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(sK5,X0) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.02/0.99    introduced(choice_axiom,[])).
% 3.02/0.99  
% 3.02/0.99  fof(f30,plain,(
% 3.02/0.99    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK4),X1,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK4))) & v2_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4))),
% 3.02/0.99    introduced(choice_axiom,[])).
% 3.02/0.99  
% 3.02/0.99  fof(f33,plain,(
% 3.02/0.99    ((! [X3] : (k1_tarski(sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & r2_hidden(sK6,sK5) & m1_subset_1(sK6,u1_struct_0(sK4))) & v2_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4)),
% 3.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f14,f32,f31,f30])).
% 3.02/0.99  
% 3.02/0.99  fof(f53,plain,(
% 3.02/0.99    l1_pre_topc(sK4)),
% 3.02/0.99    inference(cnf_transformation,[],[f33])).
% 3.02/0.99  
% 3.02/0.99  fof(f57,plain,(
% 3.02/0.99    r2_hidden(sK6,sK5)),
% 3.02/0.99    inference(cnf_transformation,[],[f33])).
% 3.02/0.99  
% 3.02/0.99  fof(f5,axiom,(
% 3.02/0.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f23,plain,(
% 3.02/0.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.02/0.99    inference(nnf_transformation,[],[f5])).
% 3.02/0.99  
% 3.02/0.99  fof(f44,plain,(
% 3.02/0.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f23])).
% 3.02/0.99  
% 3.02/0.99  fof(f3,axiom,(
% 3.02/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f41,plain,(
% 3.02/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f3])).
% 3.02/0.99  
% 3.02/0.99  fof(f4,axiom,(
% 3.02/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f42,plain,(
% 3.02/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f4])).
% 3.02/0.99  
% 3.02/0.99  fof(f59,plain,(
% 3.02/0.99    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.02/0.99    inference(definition_unfolding,[],[f41,f42])).
% 3.02/0.99  
% 3.02/0.99  fof(f64,plain,(
% 3.02/0.99    ( ! [X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.02/0.99    inference(definition_unfolding,[],[f44,f59])).
% 3.02/0.99  
% 3.02/0.99  fof(f6,axiom,(
% 3.02/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f24,plain,(
% 3.02/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.02/0.99    inference(nnf_transformation,[],[f6])).
% 3.02/0.99  
% 3.02/0.99  fof(f46,plain,(
% 3.02/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f24])).
% 3.02/0.99  
% 3.02/0.99  fof(f54,plain,(
% 3.02/0.99    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 3.02/0.99    inference(cnf_transformation,[],[f33])).
% 3.02/0.99  
% 3.02/0.99  fof(f49,plain,(
% 3.02/0.99    ( ! [X4,X0,X1] : (k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f29])).
% 3.02/0.99  
% 3.02/0.99  fof(f55,plain,(
% 3.02/0.99    v2_tex_2(sK5,sK4)),
% 3.02/0.99    inference(cnf_transformation,[],[f33])).
% 3.02/0.99  
% 3.02/0.99  fof(f45,plain,(
% 3.02/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.02/0.99    inference(cnf_transformation,[],[f24])).
% 3.02/0.99  
% 3.02/0.99  fof(f43,plain,(
% 3.02/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f23])).
% 3.02/0.99  
% 3.02/0.99  fof(f65,plain,(
% 3.02/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_enumset1(X0,X0,X0),X1)) )),
% 3.02/0.99    inference(definition_unfolding,[],[f43,f59])).
% 3.02/0.99  
% 3.02/0.99  fof(f1,axiom,(
% 3.02/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f10,plain,(
% 3.02/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.02/0.99    inference(ennf_transformation,[],[f1])).
% 3.02/0.99  
% 3.02/0.99  fof(f15,plain,(
% 3.02/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.02/0.99    inference(nnf_transformation,[],[f10])).
% 3.02/0.99  
% 3.02/0.99  fof(f16,plain,(
% 3.02/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.02/0.99    inference(rectify,[],[f15])).
% 3.02/0.99  
% 3.02/0.99  fof(f17,plain,(
% 3.02/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.02/0.99    introduced(choice_axiom,[])).
% 3.02/0.99  
% 3.02/0.99  fof(f18,plain,(
% 3.02/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 3.02/0.99  
% 3.02/0.99  fof(f34,plain,(
% 3.02/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f18])).
% 3.02/0.99  
% 3.02/0.99  fof(f58,plain,(
% 3.02/0.99    ( ! [X3] : (k1_tarski(sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) )),
% 3.02/0.99    inference(cnf_transformation,[],[f33])).
% 3.02/0.99  
% 3.02/0.99  fof(f66,plain,(
% 3.02/0.99    ( ! [X3] : (k1_enumset1(sK6,sK6,sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X3) | ~v4_pre_topc(X3,sK4) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) )),
% 3.02/0.99    inference(definition_unfolding,[],[f58,f59])).
% 3.02/0.99  
% 3.02/0.99  fof(f48,plain,(
% 3.02/0.99    ( ! [X4,X0,X1] : (v4_pre_topc(sK3(X0,X1,X4),X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f29])).
% 3.02/0.99  
% 3.02/0.99  cnf(c_16,plain,
% 3.02/0.99      ( ~ v2_tex_2(X0,X1)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.99      | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.99      | ~ r1_tarski(X2,X0)
% 3.02/0.99      | ~ l1_pre_topc(X1) ),
% 3.02/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_22,negated_conjecture,
% 3.02/0.99      ( l1_pre_topc(sK4) ),
% 3.02/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_416,plain,
% 3.02/0.99      ( ~ v2_tex_2(X0,X1)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.99      | m1_subset_1(sK3(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.99      | ~ r1_tarski(X2,X0)
% 3.02/0.99      | sK4 != X1 ),
% 3.02/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_417,plain,
% 3.02/0.99      ( ~ v2_tex_2(X0,sK4)
% 3.02/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/0.99      | m1_subset_1(sK3(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/0.99      | ~ r1_tarski(X1,X0) ),
% 3.02/0.99      inference(unflattening,[status(thm)],[c_416]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3068,plain,
% 3.02/0.99      ( v2_tex_2(X0,sK4) != iProver_top
% 3.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.02/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.02/0.99      | m1_subset_1(sK3(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 3.02/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_18,negated_conjecture,
% 3.02/0.99      ( r2_hidden(sK6,sK5) ),
% 3.02/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3073,plain,
% 3.02/0.99      ( r2_hidden(sK6,sK5) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_7,plain,
% 3.02/0.99      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_enumset1(X0,X0,X0),X1) ),
% 3.02/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3078,plain,
% 3.02/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.02/0.99      | r1_tarski(k1_enumset1(X0,X0,X0),X1) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_9,plain,
% 3.02/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.02/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3076,plain,
% 3.02/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.02/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_21,negated_conjecture,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.02/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3070,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_14,plain,
% 3.02/0.99      ( ~ v2_tex_2(X0,X1)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.99      | ~ r1_tarski(X2,X0)
% 3.02/0.99      | ~ l1_pre_topc(X1)
% 3.02/0.99      | k9_subset_1(u1_struct_0(X1),X0,sK3(X1,X0,X2)) = X2 ),
% 3.02/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_437,plain,
% 3.02/0.99      ( ~ v2_tex_2(X0,X1)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.02/0.99      | ~ r1_tarski(X2,X0)
% 3.02/0.99      | k9_subset_1(u1_struct_0(X1),X0,sK3(X1,X0,X2)) = X2
% 3.02/0.99      | sK4 != X1 ),
% 3.02/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_438,plain,
% 3.02/0.99      ( ~ v2_tex_2(X0,sK4)
% 3.02/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/0.99      | ~ r1_tarski(X1,X0)
% 3.02/0.99      | k9_subset_1(u1_struct_0(sK4),X0,sK3(sK4,X0,X1)) = X1 ),
% 3.02/0.99      inference(unflattening,[status(thm)],[c_437]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3067,plain,
% 3.02/0.99      ( k9_subset_1(u1_struct_0(sK4),X0,sK3(sK4,X0,X1)) = X1
% 3.02/0.99      | v2_tex_2(X0,sK4) != iProver_top
% 3.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.02/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.02/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_438]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3379,plain,
% 3.02/0.99      ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0
% 3.02/0.99      | v2_tex_2(sK5,sK4) != iProver_top
% 3.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.02/0.99      | r1_tarski(X0,sK5) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_3070,c_3067]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_24,plain,
% 3.02/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_20,negated_conjecture,
% 3.02/0.99      ( v2_tex_2(sK5,sK4) ),
% 3.02/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_726,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/0.99      | ~ r1_tarski(X1,X0)
% 3.02/0.99      | k9_subset_1(u1_struct_0(sK4),X0,sK3(sK4,X0,X1)) = X1
% 3.02/0.99      | sK5 != X0
% 3.02/0.99      | sK4 != sK4 ),
% 3.02/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_438]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_727,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/0.99      | ~ r1_tarski(X0,sK5)
% 3.02/0.99      | k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0 ),
% 3.02/0.99      inference(unflattening,[status(thm)],[c_726]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_728,plain,
% 3.02/0.99      ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0
% 3.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.02/0.99      | r1_tarski(X0,sK5) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_727]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3826,plain,
% 3.02/0.99      ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0
% 3.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.02/0.99      | r1_tarski(X0,sK5) != iProver_top ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_3379,c_24,c_728]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3833,plain,
% 3.02/0.99      ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,X0)) = X0
% 3.02/0.99      | r1_tarski(X0,u1_struct_0(sK4)) != iProver_top
% 3.02/0.99      | r1_tarski(X0,sK5) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_3076,c_3826]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4424,plain,
% 3.02/0.99      ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k1_enumset1(X0,X0,X0))) = k1_enumset1(X0,X0,X0)
% 3.02/0.99      | r2_hidden(X0,u1_struct_0(sK4)) != iProver_top
% 3.02/0.99      | r1_tarski(k1_enumset1(X0,X0,X0),sK5) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_3078,c_3833]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_10,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.02/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3075,plain,
% 3.02/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.02/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3664,plain,
% 3.02/0.99      ( r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_3070,c_3075]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_8,plain,
% 3.02/0.99      ( r2_hidden(X0,X1) | ~ r1_tarski(k1_enumset1(X0,X0,X0),X1) ),
% 3.02/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3692,plain,
% 3.02/0.99      ( r2_hidden(X0,sK5) | ~ r1_tarski(k1_enumset1(X0,X0,X0),sK5) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3693,plain,
% 3.02/0.99      ( r2_hidden(X0,sK5) = iProver_top
% 3.02/0.99      | r1_tarski(k1_enumset1(X0,X0,X0),sK5) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_3692]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2,plain,
% 3.02/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.02/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3790,plain,
% 3.02/0.99      ( ~ r2_hidden(X0,X1)
% 3.02/0.99      | r2_hidden(X0,u1_struct_0(sK4))
% 3.02/0.99      | ~ r1_tarski(X1,u1_struct_0(sK4)) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_7253,plain,
% 3.02/0.99      ( r2_hidden(X0,u1_struct_0(sK4))
% 3.02/0.99      | ~ r2_hidden(X0,sK5)
% 3.02/0.99      | ~ r1_tarski(sK5,u1_struct_0(sK4)) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_3790]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_7254,plain,
% 3.02/0.99      ( r2_hidden(X0,u1_struct_0(sK4)) = iProver_top
% 3.02/0.99      | r2_hidden(X0,sK5) != iProver_top
% 3.02/0.99      | r1_tarski(sK5,u1_struct_0(sK4)) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_7253]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_9135,plain,
% 3.02/0.99      ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k1_enumset1(X0,X0,X0))) = k1_enumset1(X0,X0,X0)
% 3.02/0.99      | r1_tarski(k1_enumset1(X0,X0,X0),sK5) != iProver_top ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_4424,c_3664,c_3693,c_7254]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_9145,plain,
% 3.02/0.99      ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k1_enumset1(X0,X0,X0))) = k1_enumset1(X0,X0,X0)
% 3.02/0.99      | r2_hidden(X0,sK5) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_3078,c_9135]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_9270,plain,
% 3.02/0.99      ( k9_subset_1(u1_struct_0(sK4),sK5,sK3(sK4,sK5,k1_enumset1(sK6,sK6,sK6))) = k1_enumset1(sK6,sK6,sK6) ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_3073,c_9145]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_17,negated_conjecture,
% 3.02/0.99      ( ~ v4_pre_topc(X0,sK4)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/0.99      | k1_enumset1(sK6,sK6,sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3074,plain,
% 3.02/0.99      ( k1_enumset1(sK6,sK6,sK6) != k9_subset_1(u1_struct_0(sK4),sK5,X0)
% 3.02/0.99      | v4_pre_topc(X0,sK4) != iProver_top
% 3.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_9315,plain,
% 3.02/0.99      ( v4_pre_topc(sK3(sK4,sK5,k1_enumset1(sK6,sK6,sK6)),sK4) != iProver_top
% 3.02/0.99      | m1_subset_1(sK3(sK4,sK5,k1_enumset1(sK6,sK6,sK6)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_9270,c_3074]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_25,plain,
% 3.02/0.99      ( v2_tex_2(sK5,sK4) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_27,plain,
% 3.02/0.99      ( r2_hidden(sK6,sK5) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3315,plain,
% 3.02/0.99      ( ~ r2_hidden(X0,sK5) | r1_tarski(k1_enumset1(X0,X0,X0),sK5) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3702,plain,
% 3.02/0.99      ( ~ r2_hidden(sK6,sK5) | r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_3315]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3703,plain,
% 3.02/0.99      ( r2_hidden(sK6,sK5) != iProver_top
% 3.02/0.99      | r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_3702]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_15,plain,
% 3.02/0.99      ( v4_pre_topc(sK3(X0,X1,X2),X0)
% 3.02/0.99      | ~ v2_tex_2(X1,X0)
% 3.02/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/0.99      | ~ r1_tarski(X2,X1)
% 3.02/0.99      | ~ l1_pre_topc(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_395,plain,
% 3.02/0.99      ( v4_pre_topc(sK3(X0,X1,X2),X0)
% 3.02/0.99      | ~ v2_tex_2(X1,X0)
% 3.02/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.02/0.99      | ~ r1_tarski(X2,X1)
% 3.02/0.99      | sK4 != X0 ),
% 3.02/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_396,plain,
% 3.02/0.99      ( v4_pre_topc(sK3(sK4,X0,X1),sK4)
% 3.02/0.99      | ~ v2_tex_2(X0,sK4)
% 3.02/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/0.99      | ~ r1_tarski(X1,X0) ),
% 3.02/0.99      inference(unflattening,[status(thm)],[c_395]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3251,plain,
% 3.02/0.99      ( v4_pre_topc(sK3(sK4,sK5,X0),sK4)
% 3.02/0.99      | ~ v2_tex_2(sK5,sK4)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/0.99      | ~ r1_tarski(X0,sK5) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_396]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3314,plain,
% 3.02/0.99      ( v4_pre_topc(sK3(sK4,sK5,k1_enumset1(X0,X0,X0)),sK4)
% 3.02/0.99      | ~ v2_tex_2(sK5,sK4)
% 3.02/0.99      | ~ m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/0.99      | ~ r1_tarski(k1_enumset1(X0,X0,X0),sK5) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_3251]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3886,plain,
% 3.02/0.99      ( v4_pre_topc(sK3(sK4,sK5,k1_enumset1(sK6,sK6,sK6)),sK4)
% 3.02/0.99      | ~ v2_tex_2(sK5,sK4)
% 3.02/0.99      | ~ m1_subset_1(k1_enumset1(sK6,sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/0.99      | ~ r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_3314]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3887,plain,
% 3.02/0.99      ( v4_pre_topc(sK3(sK4,sK5,k1_enumset1(sK6,sK6,sK6)),sK4) = iProver_top
% 3.02/0.99      | v2_tex_2(sK5,sK4) != iProver_top
% 3.02/0.99      | m1_subset_1(k1_enumset1(sK6,sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.02/0.99      | r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_3886]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3083,plain,
% 3.02/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.02/0.99      | r2_hidden(X0,X2) = iProver_top
% 3.02/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4451,plain,
% 3.02/0.99      ( r2_hidden(sK6,X0) = iProver_top
% 3.02/0.99      | r1_tarski(sK5,X0) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_3073,c_3083]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4490,plain,
% 3.02/0.99      ( r2_hidden(sK6,u1_struct_0(sK4)) = iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_3664,c_4451]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3264,plain,
% 3.02/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/0.99      | ~ r1_tarski(X0,u1_struct_0(sK4)) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3422,plain,
% 3.02/0.99      ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/0.99      | ~ r1_tarski(k1_enumset1(X0,X0,X0),u1_struct_0(sK4)) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_3264]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4736,plain,
% 3.02/0.99      ( m1_subset_1(k1_enumset1(sK6,sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.02/0.99      | ~ r1_tarski(k1_enumset1(sK6,sK6,sK6),u1_struct_0(sK4)) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_3422]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4737,plain,
% 3.02/0.99      ( m1_subset_1(k1_enumset1(sK6,sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 3.02/0.99      | r1_tarski(k1_enumset1(sK6,sK6,sK6),u1_struct_0(sK4)) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_4736]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_5221,plain,
% 3.02/0.99      ( ~ r2_hidden(sK6,X0) | r1_tarski(k1_enumset1(sK6,sK6,sK6),X0) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_8993,plain,
% 3.02/0.99      ( ~ r2_hidden(sK6,u1_struct_0(sK4))
% 3.02/0.99      | r1_tarski(k1_enumset1(sK6,sK6,sK6),u1_struct_0(sK4)) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_5221]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_8996,plain,
% 3.02/0.99      ( r2_hidden(sK6,u1_struct_0(sK4)) != iProver_top
% 3.02/0.99      | r1_tarski(k1_enumset1(sK6,sK6,sK6),u1_struct_0(sK4)) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_8993]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_9617,plain,
% 3.02/0.99      ( m1_subset_1(sK3(sK4,sK5,k1_enumset1(sK6,sK6,sK6)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_9315,c_24,c_25,c_27,c_3703,c_3887,c_4490,c_4737,
% 3.02/0.99                 c_8996]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_9623,plain,
% 3.02/0.99      ( v2_tex_2(sK5,sK4) != iProver_top
% 3.02/0.99      | m1_subset_1(k1_enumset1(sK6,sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.02/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.02/0.99      | r1_tarski(k1_enumset1(sK6,sK6,sK6),sK5) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_3068,c_9617]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(contradiction,plain,
% 3.02/0.99      ( $false ),
% 3.02/0.99      inference(minisat,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_9623,c_8996,c_4737,c_4490,c_3703,c_27,c_25,c_24]) ).
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.02/0.99  
% 3.02/0.99  ------                               Statistics
% 3.02/0.99  
% 3.02/0.99  ------ General
% 3.02/0.99  
% 3.02/0.99  abstr_ref_over_cycles:                  0
% 3.02/0.99  abstr_ref_under_cycles:                 0
% 3.02/0.99  gc_basic_clause_elim:                   0
% 3.02/0.99  forced_gc_time:                         0
% 3.02/0.99  parsing_time:                           0.009
% 3.02/0.99  unif_index_cands_time:                  0.
% 3.02/0.99  unif_index_add_time:                    0.
% 3.02/0.99  orderings_time:                         0.
% 3.02/0.99  out_proof_time:                         0.008
% 3.02/0.99  total_time:                             0.248
% 3.02/0.99  num_of_symbols:                         48
% 3.02/0.99  num_of_terms:                           7036
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing
% 3.02/0.99  
% 3.02/0.99  num_of_splits:                          0
% 3.02/0.99  num_of_split_atoms:                     0
% 3.02/0.99  num_of_reused_defs:                     0
% 3.02/0.99  num_eq_ax_congr_red:                    26
% 3.02/0.99  num_of_sem_filtered_clauses:            1
% 3.02/0.99  num_of_subtypes:                        0
% 3.02/0.99  monotx_restored_types:                  0
% 3.02/0.99  sat_num_of_epr_types:                   0
% 3.02/0.99  sat_num_of_non_cyclic_types:            0
% 3.02/0.99  sat_guarded_non_collapsed_types:        0
% 3.02/0.99  num_pure_diseq_elim:                    0
% 3.02/0.99  simp_replaced_by:                       0
% 3.02/0.99  res_preprocessed:                       116
% 3.02/0.99  prep_upred:                             0
% 3.02/0.99  prep_unflattend:                        128
% 3.02/0.99  smt_new_axioms:                         0
% 3.02/0.99  pred_elim_cands:                        5
% 3.02/0.99  pred_elim:                              1
% 3.02/0.99  pred_elim_cl:                           1
% 3.02/0.99  pred_elim_cycles:                       8
% 3.02/0.99  merged_defs:                            16
% 3.02/0.99  merged_defs_ncl:                        0
% 3.02/0.99  bin_hyper_res:                          16
% 3.02/0.99  prep_cycles:                            4
% 3.02/0.99  pred_elim_time:                         0.034
% 3.02/0.99  splitting_time:                         0.
% 3.02/0.99  sem_filter_time:                        0.
% 3.02/0.99  monotx_time:                            0.
% 3.02/0.99  subtype_inf_time:                       0.
% 3.02/0.99  
% 3.02/0.99  ------ Problem properties
% 3.02/0.99  
% 3.02/0.99  clauses:                                22
% 3.02/0.99  conjectures:                            5
% 3.02/0.99  epr:                                    3
% 3.02/0.99  horn:                                   18
% 3.02/0.99  ground:                                 4
% 3.02/0.99  unary:                                  5
% 3.02/0.99  binary:                                 7
% 3.02/0.99  lits:                                   57
% 3.02/0.99  lits_eq:                                8
% 3.02/0.99  fd_pure:                                0
% 3.02/0.99  fd_pseudo:                              0
% 3.02/0.99  fd_cond:                                0
% 3.02/0.99  fd_pseudo_cond:                         2
% 3.02/0.99  ac_symbols:                             0
% 3.02/0.99  
% 3.02/0.99  ------ Propositional Solver
% 3.02/0.99  
% 3.02/0.99  prop_solver_calls:                      28
% 3.02/0.99  prop_fast_solver_calls:                 1335
% 3.02/0.99  smt_solver_calls:                       0
% 3.02/0.99  smt_fast_solver_calls:                  0
% 3.02/0.99  prop_num_of_clauses:                    2883
% 3.02/0.99  prop_preprocess_simplified:             7793
% 3.02/0.99  prop_fo_subsumed:                       16
% 3.02/0.99  prop_solver_time:                       0.
% 3.02/0.99  smt_solver_time:                        0.
% 3.02/0.99  smt_fast_solver_time:                   0.
% 3.02/0.99  prop_fast_solver_time:                  0.
% 3.02/0.99  prop_unsat_core_time:                   0.
% 3.02/0.99  
% 3.02/0.99  ------ QBF
% 3.02/0.99  
% 3.02/0.99  qbf_q_res:                              0
% 3.02/0.99  qbf_num_tautologies:                    0
% 3.02/0.99  qbf_prep_cycles:                        0
% 3.02/0.99  
% 3.02/0.99  ------ BMC1
% 3.02/0.99  
% 3.02/0.99  bmc1_current_bound:                     -1
% 3.02/0.99  bmc1_last_solved_bound:                 -1
% 3.02/0.99  bmc1_unsat_core_size:                   -1
% 3.02/0.99  bmc1_unsat_core_parents_size:           -1
% 3.02/0.99  bmc1_merge_next_fun:                    0
% 3.02/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.02/0.99  
% 3.02/0.99  ------ Instantiation
% 3.02/0.99  
% 3.02/0.99  inst_num_of_clauses:                    706
% 3.02/0.99  inst_num_in_passive:                    364
% 3.02/0.99  inst_num_in_active:                     266
% 3.02/0.99  inst_num_in_unprocessed:                77
% 3.02/0.99  inst_num_of_loops:                      390
% 3.02/0.99  inst_num_of_learning_restarts:          0
% 3.02/0.99  inst_num_moves_active_passive:          121
% 3.02/0.99  inst_lit_activity:                      0
% 3.02/0.99  inst_lit_activity_moves:                0
% 3.02/0.99  inst_num_tautologies:                   0
% 3.02/0.99  inst_num_prop_implied:                  0
% 3.02/0.99  inst_num_existing_simplified:           0
% 3.02/0.99  inst_num_eq_res_simplified:             0
% 3.02/0.99  inst_num_child_elim:                    0
% 3.02/0.99  inst_num_of_dismatching_blockings:      402
% 3.02/0.99  inst_num_of_non_proper_insts:           742
% 3.02/0.99  inst_num_of_duplicates:                 0
% 3.02/0.99  inst_inst_num_from_inst_to_res:         0
% 3.02/0.99  inst_dismatching_checking_time:         0.
% 3.02/0.99  
% 3.02/0.99  ------ Resolution
% 3.02/0.99  
% 3.02/0.99  res_num_of_clauses:                     0
% 3.02/0.99  res_num_in_passive:                     0
% 3.02/0.99  res_num_in_active:                      0
% 3.02/0.99  res_num_of_loops:                       120
% 3.02/0.99  res_forward_subset_subsumed:            66
% 3.02/0.99  res_backward_subset_subsumed:           2
% 3.02/0.99  res_forward_subsumed:                   0
% 3.02/0.99  res_backward_subsumed:                  0
% 3.02/0.99  res_forward_subsumption_resolution:     2
% 3.02/0.99  res_backward_subsumption_resolution:    0
% 3.02/0.99  res_clause_to_clause_subsumption:       1223
% 3.02/0.99  res_orphan_elimination:                 0
% 3.02/0.99  res_tautology_del:                      66
% 3.02/0.99  res_num_eq_res_simplified:              0
% 3.02/0.99  res_num_sel_changes:                    0
% 3.02/0.99  res_moves_from_active_to_pass:          0
% 3.02/0.99  
% 3.02/0.99  ------ Superposition
% 3.02/0.99  
% 3.02/0.99  sup_time_total:                         0.
% 3.02/0.99  sup_time_generating:                    0.
% 3.02/0.99  sup_time_sim_full:                      0.
% 3.02/0.99  sup_time_sim_immed:                     0.
% 3.02/0.99  
% 3.02/0.99  sup_num_of_clauses:                     154
% 3.02/0.99  sup_num_in_active:                      77
% 3.02/0.99  sup_num_in_passive:                     77
% 3.02/0.99  sup_num_of_loops:                       77
% 3.02/0.99  sup_fw_superposition:                   93
% 3.02/0.99  sup_bw_superposition:                   85
% 3.02/0.99  sup_immediate_simplified:               19
% 3.02/0.99  sup_given_eliminated:                   0
% 3.02/0.99  comparisons_done:                       0
% 3.02/0.99  comparisons_avoided:                    13
% 3.02/0.99  
% 3.02/0.99  ------ Simplifications
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  sim_fw_subset_subsumed:                 8
% 3.02/0.99  sim_bw_subset_subsumed:                 2
% 3.02/0.99  sim_fw_subsumed:                        8
% 3.02/0.99  sim_bw_subsumed:                        2
% 3.02/0.99  sim_fw_subsumption_res:                 0
% 3.02/0.99  sim_bw_subsumption_res:                 0
% 3.02/0.99  sim_tautology_del:                      9
% 3.02/0.99  sim_eq_tautology_del:                   1
% 3.02/0.99  sim_eq_res_simp:                        0
% 3.02/0.99  sim_fw_demodulated:                     0
% 3.02/0.99  sim_bw_demodulated:                     0
% 3.02/0.99  sim_light_normalised:                   0
% 3.02/0.99  sim_joinable_taut:                      0
% 3.02/0.99  sim_joinable_simp:                      0
% 3.02/0.99  sim_ac_normalised:                      0
% 3.02/0.99  sim_smt_subsumption:                    0
% 3.02/0.99  
%------------------------------------------------------------------------------
