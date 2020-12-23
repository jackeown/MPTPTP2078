%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:56 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 486 expanded)
%              Number of clauses        :   58 (  89 expanded)
%              Number of leaves         :   20 ( 145 expanded)
%              Depth                    :   19
%              Number of atoms          :  489 (2142 expanded)
%              Number of equality atoms :  146 ( 523 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( k1_tarski(sK5) != k9_subset_1(u1_struct_0(X0),X1,X3)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK5,X1)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
                ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),sK4,X3)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(X2,sK4)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & v2_tex_2(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
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
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK3),X1,X3)
                  | ~ v3_pre_topc(X3,sK3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & v2_tex_2(X1,sK3)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ! [X3] :
        ( k1_tarski(sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X3)
        | ~ v3_pre_topc(X3,sK3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
    & r2_hidden(sK5,sK4)
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f21,f35,f34,f33])).

fof(f65,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f67])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f68])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f70])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f71])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f73])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f31,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4
        & v3_pre_topc(sK2(X0,X1,X4),X0)
        & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK1(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4
                    & v3_pre_topc(sK2(X0,X1,X4),X0)
                    & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f31,f30])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f71])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f72])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f38,f72])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f78])).

fof(f66,plain,(
    ! [X3] :
      ( k1_tarski(sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X3)
      | ~ v3_pre_topc(X3,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    ! [X3] :
      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X3)
      | ~ v3_pre_topc(X3,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(definition_unfolding,[],[f66,f73])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( v3_pre_topc(sK2(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2266,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7,plain,
    ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2270,plain,
    ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2268,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2952,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2270,c_2268])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2263,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,sK2(X1,X0,X2)) = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_417,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | k9_subset_1(u1_struct_0(X1),X0,sK2(X1,X0,X2)) = X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_418,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK3),X0,sK2(sK3,X0,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_2260,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,sK2(sK3,X0,X1)) = X1
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_2527,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,X0)) = X0
    | v2_tex_2(sK4,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2263,c_2260])).

cnf(c_23,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_840,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK3),X0,sK2(sK3,X0,X1)) = X1
    | sK4 != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_418])).

cnf(c_841,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X0,sK4)
    | k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_840])).

cnf(c_842,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_841])).

cnf(c_3078,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2527,c_23,c_842])).

cnf(c_3085,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK4) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2270,c_3078])).

cnf(c_4598,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2952,c_3085])).

cnf(c_2678,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2263,c_2268])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2271,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2986,plain,
    ( k1_setfam_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,u1_struct_0(sK3))) = sK4 ),
    inference(superposition,[status(thm)],[c_2678,c_2271])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2273,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3859,plain,
    ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2986,c_2273])).

cnf(c_7831,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4598,c_3859])).

cnf(c_7843,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(superposition,[status(thm)],[c_2266,c_7831])).

cnf(c_16,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2267,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X0)
    | v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8012,plain,
    ( v3_pre_topc(sK2(sK3,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),sK3) != iProver_top
    | m1_subset_1(sK2(sK3,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7843,c_2267])).

cnf(c_4667,plain,
    ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X0,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4670,plain,
    ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4667])).

cnf(c_4672,plain,
    ( m1_subset_1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4670])).

cnf(c_3861,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3859])).

cnf(c_15,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_396,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_21])).

cnf(c_397,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_2446,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_397])).

cnf(c_2642,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ m1_subset_1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(sK2(sK3,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_2446])).

cnf(c_2646,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top
    | m1_subset_1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK2(sK3,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2642])).

cnf(c_14,plain,
    ( v3_pre_topc(sK2(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X2,X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_375,plain,
    ( v3_pre_topc(sK2(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X2,X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_376,plain,
    ( v3_pre_topc(sK2(sK3,X0,X1),sK3)
    | ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_2443,plain,
    ( v3_pre_topc(sK2(sK3,sK4,X0),sK3)
    | ~ v2_tex_2(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_376])).

cnf(c_2643,plain,
    ( v3_pre_topc(sK2(sK3,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),sK3)
    | ~ v2_tex_2(sK4,sK3)
    | ~ m1_subset_1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_2443])).

cnf(c_2644,plain,
    ( v3_pre_topc(sK2(sK3,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),sK3) = iProver_top
    | v2_tex_2(sK4,sK3) != iProver_top
    | m1_subset_1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2643])).

cnf(c_2507,plain,
    ( ~ m1_subset_1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_zfmisc_1(sK4))
    | r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2508,plain,
    ( m1_subset_1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_zfmisc_1(sK4)) != iProver_top
    | r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2507])).

cnf(c_2483,plain,
    ( m1_subset_1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_zfmisc_1(sK4))
    | ~ r2_hidden(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2484,plain,
    ( m1_subset_1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_zfmisc_1(sK4)) = iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2483])).

cnf(c_26,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_24,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8012,c_4672,c_3861,c_2646,c_2644,c_2508,c_2484,c_26,c_24,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.07/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/0.98  
% 3.07/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.07/0.98  
% 3.07/0.98  ------  iProver source info
% 3.07/0.98  
% 3.07/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.07/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.07/0.98  git: non_committed_changes: false
% 3.07/0.98  git: last_make_outside_of_git: false
% 3.07/0.98  
% 3.07/0.98  ------ 
% 3.07/0.98  
% 3.07/0.98  ------ Input Options
% 3.07/0.98  
% 3.07/0.98  --out_options                           all
% 3.07/0.98  --tptp_safe_out                         true
% 3.07/0.98  --problem_path                          ""
% 3.07/0.98  --include_path                          ""
% 3.07/0.98  --clausifier                            res/vclausify_rel
% 3.07/0.98  --clausifier_options                    --mode clausify
% 3.07/0.98  --stdin                                 false
% 3.07/0.98  --stats_out                             all
% 3.07/0.98  
% 3.07/0.98  ------ General Options
% 3.07/0.98  
% 3.07/0.98  --fof                                   false
% 3.07/0.98  --time_out_real                         305.
% 3.07/0.98  --time_out_virtual                      -1.
% 3.07/0.98  --symbol_type_check                     false
% 3.07/0.98  --clausify_out                          false
% 3.07/0.98  --sig_cnt_out                           false
% 3.07/0.98  --trig_cnt_out                          false
% 3.07/0.98  --trig_cnt_out_tolerance                1.
% 3.07/0.98  --trig_cnt_out_sk_spl                   false
% 3.07/0.98  --abstr_cl_out                          false
% 3.07/0.98  
% 3.07/0.98  ------ Global Options
% 3.07/0.98  
% 3.07/0.98  --schedule                              default
% 3.07/0.98  --add_important_lit                     false
% 3.07/0.98  --prop_solver_per_cl                    1000
% 3.07/0.98  --min_unsat_core                        false
% 3.07/0.98  --soft_assumptions                      false
% 3.07/0.98  --soft_lemma_size                       3
% 3.07/0.98  --prop_impl_unit_size                   0
% 3.07/0.98  --prop_impl_unit                        []
% 3.07/0.98  --share_sel_clauses                     true
% 3.07/0.98  --reset_solvers                         false
% 3.07/0.98  --bc_imp_inh                            [conj_cone]
% 3.07/0.98  --conj_cone_tolerance                   3.
% 3.07/0.98  --extra_neg_conj                        none
% 3.07/0.98  --large_theory_mode                     true
% 3.07/0.98  --prolific_symb_bound                   200
% 3.07/0.98  --lt_threshold                          2000
% 3.07/0.98  --clause_weak_htbl                      true
% 3.07/0.98  --gc_record_bc_elim                     false
% 3.07/0.98  
% 3.07/0.98  ------ Preprocessing Options
% 3.07/0.98  
% 3.07/0.98  --preprocessing_flag                    true
% 3.07/0.98  --time_out_prep_mult                    0.1
% 3.07/0.98  --splitting_mode                        input
% 3.07/0.98  --splitting_grd                         true
% 3.07/0.98  --splitting_cvd                         false
% 3.07/0.98  --splitting_cvd_svl                     false
% 3.07/0.98  --splitting_nvd                         32
% 3.07/0.98  --sub_typing                            true
% 3.07/0.98  --prep_gs_sim                           true
% 3.07/0.98  --prep_unflatten                        true
% 3.07/0.98  --prep_res_sim                          true
% 3.07/0.98  --prep_upred                            true
% 3.07/0.98  --prep_sem_filter                       exhaustive
% 3.07/0.98  --prep_sem_filter_out                   false
% 3.07/0.98  --pred_elim                             true
% 3.07/0.98  --res_sim_input                         true
% 3.07/0.98  --eq_ax_congr_red                       true
% 3.07/0.98  --pure_diseq_elim                       true
% 3.07/0.98  --brand_transform                       false
% 3.07/0.98  --non_eq_to_eq                          false
% 3.07/0.98  --prep_def_merge                        true
% 3.07/0.98  --prep_def_merge_prop_impl              false
% 3.07/0.98  --prep_def_merge_mbd                    true
% 3.07/0.98  --prep_def_merge_tr_red                 false
% 3.07/0.98  --prep_def_merge_tr_cl                  false
% 3.07/0.98  --smt_preprocessing                     true
% 3.07/0.98  --smt_ac_axioms                         fast
% 3.07/0.98  --preprocessed_out                      false
% 3.07/0.98  --preprocessed_stats                    false
% 3.07/0.98  
% 3.07/0.98  ------ Abstraction refinement Options
% 3.07/0.98  
% 3.07/0.98  --abstr_ref                             []
% 3.07/0.98  --abstr_ref_prep                        false
% 3.07/0.98  --abstr_ref_until_sat                   false
% 3.07/0.98  --abstr_ref_sig_restrict                funpre
% 3.07/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.07/0.98  --abstr_ref_under                       []
% 3.07/0.98  
% 3.07/0.98  ------ SAT Options
% 3.07/0.98  
% 3.07/0.98  --sat_mode                              false
% 3.07/0.98  --sat_fm_restart_options                ""
% 3.07/0.98  --sat_gr_def                            false
% 3.07/0.98  --sat_epr_types                         true
% 3.07/0.98  --sat_non_cyclic_types                  false
% 3.07/0.98  --sat_finite_models                     false
% 3.07/0.98  --sat_fm_lemmas                         false
% 3.07/0.98  --sat_fm_prep                           false
% 3.07/0.98  --sat_fm_uc_incr                        true
% 3.07/0.98  --sat_out_model                         small
% 3.07/0.98  --sat_out_clauses                       false
% 3.07/0.98  
% 3.07/0.98  ------ QBF Options
% 3.07/0.98  
% 3.07/0.98  --qbf_mode                              false
% 3.07/0.98  --qbf_elim_univ                         false
% 3.07/0.98  --qbf_dom_inst                          none
% 3.07/0.98  --qbf_dom_pre_inst                      false
% 3.07/0.98  --qbf_sk_in                             false
% 3.07/0.98  --qbf_pred_elim                         true
% 3.07/0.98  --qbf_split                             512
% 3.07/0.98  
% 3.07/0.98  ------ BMC1 Options
% 3.07/0.98  
% 3.07/0.98  --bmc1_incremental                      false
% 3.07/0.98  --bmc1_axioms                           reachable_all
% 3.07/0.98  --bmc1_min_bound                        0
% 3.07/0.98  --bmc1_max_bound                        -1
% 3.07/0.98  --bmc1_max_bound_default                -1
% 3.07/0.98  --bmc1_symbol_reachability              true
% 3.07/0.98  --bmc1_property_lemmas                  false
% 3.07/0.98  --bmc1_k_induction                      false
% 3.07/0.98  --bmc1_non_equiv_states                 false
% 3.07/0.98  --bmc1_deadlock                         false
% 3.07/0.98  --bmc1_ucm                              false
% 3.07/0.98  --bmc1_add_unsat_core                   none
% 3.07/0.98  --bmc1_unsat_core_children              false
% 3.07/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.07/0.98  --bmc1_out_stat                         full
% 3.07/0.98  --bmc1_ground_init                      false
% 3.07/0.98  --bmc1_pre_inst_next_state              false
% 3.07/0.98  --bmc1_pre_inst_state                   false
% 3.07/0.98  --bmc1_pre_inst_reach_state             false
% 3.07/0.98  --bmc1_out_unsat_core                   false
% 3.07/0.98  --bmc1_aig_witness_out                  false
% 3.07/0.98  --bmc1_verbose                          false
% 3.07/0.98  --bmc1_dump_clauses_tptp                false
% 3.07/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.07/0.98  --bmc1_dump_file                        -
% 3.07/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.07/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.07/0.98  --bmc1_ucm_extend_mode                  1
% 3.07/0.98  --bmc1_ucm_init_mode                    2
% 3.07/0.98  --bmc1_ucm_cone_mode                    none
% 3.07/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.07/0.98  --bmc1_ucm_relax_model                  4
% 3.07/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.07/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.07/0.98  --bmc1_ucm_layered_model                none
% 3.07/0.98  --bmc1_ucm_max_lemma_size               10
% 3.07/0.98  
% 3.07/0.98  ------ AIG Options
% 3.07/0.98  
% 3.07/0.98  --aig_mode                              false
% 3.07/0.98  
% 3.07/0.98  ------ Instantiation Options
% 3.07/0.98  
% 3.07/0.98  --instantiation_flag                    true
% 3.07/0.98  --inst_sos_flag                         false
% 3.07/0.98  --inst_sos_phase                        true
% 3.07/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.07/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.07/0.98  --inst_lit_sel_side                     num_symb
% 3.07/0.98  --inst_solver_per_active                1400
% 3.07/0.98  --inst_solver_calls_frac                1.
% 3.07/0.98  --inst_passive_queue_type               priority_queues
% 3.07/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.07/0.98  --inst_passive_queues_freq              [25;2]
% 3.07/0.98  --inst_dismatching                      true
% 3.07/0.98  --inst_eager_unprocessed_to_passive     true
% 3.07/0.98  --inst_prop_sim_given                   true
% 3.07/0.98  --inst_prop_sim_new                     false
% 3.07/0.98  --inst_subs_new                         false
% 3.07/0.98  --inst_eq_res_simp                      false
% 3.07/0.98  --inst_subs_given                       false
% 3.07/0.98  --inst_orphan_elimination               true
% 3.07/0.98  --inst_learning_loop_flag               true
% 3.07/0.98  --inst_learning_start                   3000
% 3.07/0.98  --inst_learning_factor                  2
% 3.07/0.98  --inst_start_prop_sim_after_learn       3
% 3.07/0.98  --inst_sel_renew                        solver
% 3.07/0.98  --inst_lit_activity_flag                true
% 3.07/0.98  --inst_restr_to_given                   false
% 3.07/0.98  --inst_activity_threshold               500
% 3.07/0.98  --inst_out_proof                        true
% 3.07/0.98  
% 3.07/0.98  ------ Resolution Options
% 3.07/0.98  
% 3.07/0.98  --resolution_flag                       true
% 3.07/0.98  --res_lit_sel                           adaptive
% 3.07/0.98  --res_lit_sel_side                      none
% 3.07/0.98  --res_ordering                          kbo
% 3.07/0.98  --res_to_prop_solver                    active
% 3.07/0.98  --res_prop_simpl_new                    false
% 3.07/0.98  --res_prop_simpl_given                  true
% 3.07/0.98  --res_passive_queue_type                priority_queues
% 3.07/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.07/0.98  --res_passive_queues_freq               [15;5]
% 3.07/0.98  --res_forward_subs                      full
% 3.07/0.98  --res_backward_subs                     full
% 3.07/0.98  --res_forward_subs_resolution           true
% 3.07/0.98  --res_backward_subs_resolution          true
% 3.07/0.98  --res_orphan_elimination                true
% 3.07/0.98  --res_time_limit                        2.
% 3.07/0.98  --res_out_proof                         true
% 3.07/0.98  
% 3.07/0.98  ------ Superposition Options
% 3.07/0.98  
% 3.07/0.98  --superposition_flag                    true
% 3.07/0.98  --sup_passive_queue_type                priority_queues
% 3.07/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.07/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.07/0.98  --demod_completeness_check              fast
% 3.07/0.98  --demod_use_ground                      true
% 3.07/0.98  --sup_to_prop_solver                    passive
% 3.07/0.98  --sup_prop_simpl_new                    true
% 3.07/0.98  --sup_prop_simpl_given                  true
% 3.07/0.98  --sup_fun_splitting                     false
% 3.07/0.98  --sup_smt_interval                      50000
% 3.07/0.98  
% 3.07/0.98  ------ Superposition Simplification Setup
% 3.07/0.98  
% 3.07/0.98  --sup_indices_passive                   []
% 3.07/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.07/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.98  --sup_full_bw                           [BwDemod]
% 3.07/0.98  --sup_immed_triv                        [TrivRules]
% 3.07/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.98  --sup_immed_bw_main                     []
% 3.07/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.07/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/0.98  
% 3.07/0.98  ------ Combination Options
% 3.07/0.98  
% 3.07/0.98  --comb_res_mult                         3
% 3.07/0.98  --comb_sup_mult                         2
% 3.07/0.98  --comb_inst_mult                        10
% 3.07/0.98  
% 3.07/0.98  ------ Debug Options
% 3.07/0.98  
% 3.07/0.98  --dbg_backtrace                         false
% 3.07/0.98  --dbg_dump_prop_clauses                 false
% 3.07/0.98  --dbg_dump_prop_clauses_file            -
% 3.07/0.98  --dbg_out_stat                          false
% 3.07/0.98  ------ Parsing...
% 3.07/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.07/0.98  
% 3.07/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.07/0.98  
% 3.07/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.07/0.98  
% 3.07/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.07/0.98  ------ Proving...
% 3.07/0.98  ------ Problem Properties 
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  clauses                                 21
% 3.07/0.98  conjectures                             5
% 3.07/0.98  EPR                                     2
% 3.07/0.98  Horn                                    17
% 3.07/0.98  unary                                   4
% 3.07/0.98  binary                                  6
% 3.07/0.98  lits                                    58
% 3.07/0.98  lits eq                                 7
% 3.07/0.98  fd_pure                                 0
% 3.07/0.98  fd_pseudo                               0
% 3.07/0.98  fd_cond                                 0
% 3.07/0.98  fd_pseudo_cond                          3
% 3.07/0.98  AC symbols                              0
% 3.07/0.98  
% 3.07/0.98  ------ Schedule dynamic 5 is on 
% 3.07/0.98  
% 3.07/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  ------ 
% 3.07/0.98  Current options:
% 3.07/0.98  ------ 
% 3.07/0.98  
% 3.07/0.98  ------ Input Options
% 3.07/0.98  
% 3.07/0.98  --out_options                           all
% 3.07/0.98  --tptp_safe_out                         true
% 3.07/0.98  --problem_path                          ""
% 3.07/0.98  --include_path                          ""
% 3.07/0.98  --clausifier                            res/vclausify_rel
% 3.07/0.98  --clausifier_options                    --mode clausify
% 3.07/0.98  --stdin                                 false
% 3.07/0.98  --stats_out                             all
% 3.07/0.98  
% 3.07/0.98  ------ General Options
% 3.07/0.98  
% 3.07/0.98  --fof                                   false
% 3.07/0.98  --time_out_real                         305.
% 3.07/0.98  --time_out_virtual                      -1.
% 3.07/0.98  --symbol_type_check                     false
% 3.07/0.98  --clausify_out                          false
% 3.07/0.98  --sig_cnt_out                           false
% 3.07/0.98  --trig_cnt_out                          false
% 3.07/0.98  --trig_cnt_out_tolerance                1.
% 3.07/0.98  --trig_cnt_out_sk_spl                   false
% 3.07/0.98  --abstr_cl_out                          false
% 3.07/0.98  
% 3.07/0.98  ------ Global Options
% 3.07/0.98  
% 3.07/0.98  --schedule                              default
% 3.07/0.98  --add_important_lit                     false
% 3.07/0.98  --prop_solver_per_cl                    1000
% 3.07/0.98  --min_unsat_core                        false
% 3.07/0.98  --soft_assumptions                      false
% 3.07/0.98  --soft_lemma_size                       3
% 3.07/0.98  --prop_impl_unit_size                   0
% 3.07/0.98  --prop_impl_unit                        []
% 3.07/0.98  --share_sel_clauses                     true
% 3.07/0.98  --reset_solvers                         false
% 3.07/0.98  --bc_imp_inh                            [conj_cone]
% 3.07/0.98  --conj_cone_tolerance                   3.
% 3.07/0.98  --extra_neg_conj                        none
% 3.07/0.98  --large_theory_mode                     true
% 3.07/0.98  --prolific_symb_bound                   200
% 3.07/0.98  --lt_threshold                          2000
% 3.07/0.98  --clause_weak_htbl                      true
% 3.07/0.98  --gc_record_bc_elim                     false
% 3.07/0.98  
% 3.07/0.98  ------ Preprocessing Options
% 3.07/0.98  
% 3.07/0.98  --preprocessing_flag                    true
% 3.07/0.98  --time_out_prep_mult                    0.1
% 3.07/0.98  --splitting_mode                        input
% 3.07/0.98  --splitting_grd                         true
% 3.07/0.98  --splitting_cvd                         false
% 3.07/0.98  --splitting_cvd_svl                     false
% 3.07/0.98  --splitting_nvd                         32
% 3.07/0.98  --sub_typing                            true
% 3.07/0.98  --prep_gs_sim                           true
% 3.07/0.98  --prep_unflatten                        true
% 3.07/0.98  --prep_res_sim                          true
% 3.07/0.98  --prep_upred                            true
% 3.07/0.98  --prep_sem_filter                       exhaustive
% 3.07/0.98  --prep_sem_filter_out                   false
% 3.07/0.98  --pred_elim                             true
% 3.07/0.98  --res_sim_input                         true
% 3.07/0.98  --eq_ax_congr_red                       true
% 3.07/0.98  --pure_diseq_elim                       true
% 3.07/0.98  --brand_transform                       false
% 3.07/0.98  --non_eq_to_eq                          false
% 3.07/0.98  --prep_def_merge                        true
% 3.07/0.98  --prep_def_merge_prop_impl              false
% 3.07/0.98  --prep_def_merge_mbd                    true
% 3.07/0.98  --prep_def_merge_tr_red                 false
% 3.07/0.98  --prep_def_merge_tr_cl                  false
% 3.07/0.98  --smt_preprocessing                     true
% 3.07/0.98  --smt_ac_axioms                         fast
% 3.07/0.98  --preprocessed_out                      false
% 3.07/0.98  --preprocessed_stats                    false
% 3.07/0.98  
% 3.07/0.98  ------ Abstraction refinement Options
% 3.07/0.98  
% 3.07/0.98  --abstr_ref                             []
% 3.07/0.98  --abstr_ref_prep                        false
% 3.07/0.98  --abstr_ref_until_sat                   false
% 3.07/0.98  --abstr_ref_sig_restrict                funpre
% 3.07/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.07/0.98  --abstr_ref_under                       []
% 3.07/0.98  
% 3.07/0.98  ------ SAT Options
% 3.07/0.98  
% 3.07/0.98  --sat_mode                              false
% 3.07/0.98  --sat_fm_restart_options                ""
% 3.07/0.98  --sat_gr_def                            false
% 3.07/0.98  --sat_epr_types                         true
% 3.07/0.98  --sat_non_cyclic_types                  false
% 3.07/0.98  --sat_finite_models                     false
% 3.07/0.98  --sat_fm_lemmas                         false
% 3.07/0.98  --sat_fm_prep                           false
% 3.07/0.98  --sat_fm_uc_incr                        true
% 3.07/0.98  --sat_out_model                         small
% 3.07/0.98  --sat_out_clauses                       false
% 3.07/0.98  
% 3.07/0.98  ------ QBF Options
% 3.07/0.98  
% 3.07/0.98  --qbf_mode                              false
% 3.07/0.98  --qbf_elim_univ                         false
% 3.07/0.98  --qbf_dom_inst                          none
% 3.07/0.98  --qbf_dom_pre_inst                      false
% 3.07/0.98  --qbf_sk_in                             false
% 3.07/0.98  --qbf_pred_elim                         true
% 3.07/0.98  --qbf_split                             512
% 3.07/0.98  
% 3.07/0.98  ------ BMC1 Options
% 3.07/0.98  
% 3.07/0.98  --bmc1_incremental                      false
% 3.07/0.98  --bmc1_axioms                           reachable_all
% 3.07/0.98  --bmc1_min_bound                        0
% 3.07/0.98  --bmc1_max_bound                        -1
% 3.07/0.98  --bmc1_max_bound_default                -1
% 3.07/0.98  --bmc1_symbol_reachability              true
% 3.07/0.98  --bmc1_property_lemmas                  false
% 3.07/0.98  --bmc1_k_induction                      false
% 3.07/0.98  --bmc1_non_equiv_states                 false
% 3.07/0.98  --bmc1_deadlock                         false
% 3.07/0.98  --bmc1_ucm                              false
% 3.07/0.98  --bmc1_add_unsat_core                   none
% 3.07/0.98  --bmc1_unsat_core_children              false
% 3.07/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.07/0.98  --bmc1_out_stat                         full
% 3.07/0.98  --bmc1_ground_init                      false
% 3.07/0.98  --bmc1_pre_inst_next_state              false
% 3.07/0.98  --bmc1_pre_inst_state                   false
% 3.07/0.98  --bmc1_pre_inst_reach_state             false
% 3.07/0.98  --bmc1_out_unsat_core                   false
% 3.07/0.98  --bmc1_aig_witness_out                  false
% 3.07/0.98  --bmc1_verbose                          false
% 3.07/0.98  --bmc1_dump_clauses_tptp                false
% 3.07/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.07/0.98  --bmc1_dump_file                        -
% 3.07/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.07/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.07/0.98  --bmc1_ucm_extend_mode                  1
% 3.07/0.98  --bmc1_ucm_init_mode                    2
% 3.07/0.98  --bmc1_ucm_cone_mode                    none
% 3.07/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.07/0.98  --bmc1_ucm_relax_model                  4
% 3.07/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.07/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.07/0.98  --bmc1_ucm_layered_model                none
% 3.07/0.98  --bmc1_ucm_max_lemma_size               10
% 3.07/0.98  
% 3.07/0.98  ------ AIG Options
% 3.07/0.98  
% 3.07/0.98  --aig_mode                              false
% 3.07/0.98  
% 3.07/0.98  ------ Instantiation Options
% 3.07/0.98  
% 3.07/0.98  --instantiation_flag                    true
% 3.07/0.98  --inst_sos_flag                         false
% 3.07/0.98  --inst_sos_phase                        true
% 3.07/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.07/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.07/0.98  --inst_lit_sel_side                     none
% 3.07/0.98  --inst_solver_per_active                1400
% 3.07/0.98  --inst_solver_calls_frac                1.
% 3.07/0.98  --inst_passive_queue_type               priority_queues
% 3.07/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.07/0.98  --inst_passive_queues_freq              [25;2]
% 3.07/0.98  --inst_dismatching                      true
% 3.07/0.98  --inst_eager_unprocessed_to_passive     true
% 3.07/0.98  --inst_prop_sim_given                   true
% 3.07/0.98  --inst_prop_sim_new                     false
% 3.07/0.98  --inst_subs_new                         false
% 3.07/0.98  --inst_eq_res_simp                      false
% 3.07/0.98  --inst_subs_given                       false
% 3.07/0.98  --inst_orphan_elimination               true
% 3.07/0.98  --inst_learning_loop_flag               true
% 3.07/0.98  --inst_learning_start                   3000
% 3.07/0.98  --inst_learning_factor                  2
% 3.07/0.98  --inst_start_prop_sim_after_learn       3
% 3.07/0.98  --inst_sel_renew                        solver
% 3.07/0.98  --inst_lit_activity_flag                true
% 3.07/0.98  --inst_restr_to_given                   false
% 3.07/0.98  --inst_activity_threshold               500
% 3.07/0.98  --inst_out_proof                        true
% 3.07/0.98  
% 3.07/0.98  ------ Resolution Options
% 3.07/0.98  
% 3.07/0.98  --resolution_flag                       false
% 3.07/0.98  --res_lit_sel                           adaptive
% 3.07/0.98  --res_lit_sel_side                      none
% 3.07/0.98  --res_ordering                          kbo
% 3.07/0.98  --res_to_prop_solver                    active
% 3.07/0.98  --res_prop_simpl_new                    false
% 3.07/0.98  --res_prop_simpl_given                  true
% 3.07/0.98  --res_passive_queue_type                priority_queues
% 3.07/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.07/0.98  --res_passive_queues_freq               [15;5]
% 3.07/0.98  --res_forward_subs                      full
% 3.07/0.98  --res_backward_subs                     full
% 3.07/0.98  --res_forward_subs_resolution           true
% 3.07/0.98  --res_backward_subs_resolution          true
% 3.07/0.98  --res_orphan_elimination                true
% 3.07/0.98  --res_time_limit                        2.
% 3.07/0.98  --res_out_proof                         true
% 3.07/0.98  
% 3.07/0.98  ------ Superposition Options
% 3.07/0.98  
% 3.07/0.98  --superposition_flag                    true
% 3.07/0.98  --sup_passive_queue_type                priority_queues
% 3.07/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.07/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.07/0.98  --demod_completeness_check              fast
% 3.07/0.98  --demod_use_ground                      true
% 3.07/0.98  --sup_to_prop_solver                    passive
% 3.07/0.98  --sup_prop_simpl_new                    true
% 3.07/0.98  --sup_prop_simpl_given                  true
% 3.07/0.98  --sup_fun_splitting                     false
% 3.07/0.98  --sup_smt_interval                      50000
% 3.07/0.98  
% 3.07/0.98  ------ Superposition Simplification Setup
% 3.07/0.98  
% 3.07/0.98  --sup_indices_passive                   []
% 3.07/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.07/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.98  --sup_full_bw                           [BwDemod]
% 3.07/0.98  --sup_immed_triv                        [TrivRules]
% 3.07/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.98  --sup_immed_bw_main                     []
% 3.07/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.07/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/0.98  
% 3.07/0.98  ------ Combination Options
% 3.07/0.98  
% 3.07/0.98  --comb_res_mult                         3
% 3.07/0.98  --comb_sup_mult                         2
% 3.07/0.98  --comb_inst_mult                        10
% 3.07/0.98  
% 3.07/0.98  ------ Debug Options
% 3.07/0.98  
% 3.07/0.98  --dbg_backtrace                         false
% 3.07/0.98  --dbg_dump_prop_clauses                 false
% 3.07/0.98  --dbg_dump_prop_clauses_file            -
% 3.07/0.98  --dbg_out_stat                          false
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  ------ Proving...
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  % SZS status Theorem for theBenchmark.p
% 3.07/0.98  
% 3.07/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.07/0.98  
% 3.07/0.98  fof(f14,conjecture,(
% 3.07/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f15,negated_conjecture,(
% 3.07/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 3.07/0.98    inference(negated_conjecture,[],[f14])).
% 3.07/0.98  
% 3.07/0.98  fof(f20,plain,(
% 3.07/0.98    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.07/0.98    inference(ennf_transformation,[],[f15])).
% 3.07/0.98  
% 3.07/0.98  fof(f21,plain,(
% 3.07/0.98    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.07/0.98    inference(flattening,[],[f20])).
% 3.07/0.98  
% 3.07/0.98  fof(f35,plain,(
% 3.07/0.98    ( ! [X0,X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (k1_tarski(sK5) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK5,X1) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 3.07/0.98    introduced(choice_axiom,[])).
% 3.07/0.98  
% 3.07/0.98  fof(f34,plain,(
% 3.07/0.98    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),sK4,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,sK4) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.07/0.98    introduced(choice_axiom,[])).
% 3.07/0.98  
% 3.07/0.98  fof(f33,plain,(
% 3.07/0.98    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK3),X1,X3) | ~v3_pre_topc(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK3))) & v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3))),
% 3.07/0.98    introduced(choice_axiom,[])).
% 3.07/0.98  
% 3.07/0.98  fof(f36,plain,(
% 3.07/0.98    ((! [X3] : (k1_tarski(sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X3) | ~v3_pre_topc(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) & r2_hidden(sK5,sK4) & m1_subset_1(sK5,u1_struct_0(sK3))) & v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3)),
% 3.07/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f21,f35,f34,f33])).
% 3.07/0.98  
% 3.07/0.98  fof(f65,plain,(
% 3.07/0.98    r2_hidden(sK5,sK4)),
% 3.07/0.98    inference(cnf_transformation,[],[f36])).
% 3.07/0.98  
% 3.07/0.98  fof(f10,axiom,(
% 3.07/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f17,plain,(
% 3.07/0.98    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 3.07/0.98    inference(ennf_transformation,[],[f10])).
% 3.07/0.98  
% 3.07/0.98  fof(f51,plain,(
% 3.07/0.98    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.07/0.98    inference(cnf_transformation,[],[f17])).
% 3.07/0.98  
% 3.07/0.98  fof(f3,axiom,(
% 3.07/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f44,plain,(
% 3.07/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.07/0.98    inference(cnf_transformation,[],[f3])).
% 3.07/0.98  
% 3.07/0.98  fof(f4,axiom,(
% 3.07/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f45,plain,(
% 3.07/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.07/0.98    inference(cnf_transformation,[],[f4])).
% 3.07/0.98  
% 3.07/0.98  fof(f5,axiom,(
% 3.07/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f46,plain,(
% 3.07/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.07/0.98    inference(cnf_transformation,[],[f5])).
% 3.07/0.98  
% 3.07/0.98  fof(f6,axiom,(
% 3.07/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f47,plain,(
% 3.07/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.07/0.98    inference(cnf_transformation,[],[f6])).
% 3.07/0.98  
% 3.07/0.98  fof(f7,axiom,(
% 3.07/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f48,plain,(
% 3.07/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.07/0.98    inference(cnf_transformation,[],[f7])).
% 3.07/0.98  
% 3.07/0.98  fof(f8,axiom,(
% 3.07/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f49,plain,(
% 3.07/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.07/0.98    inference(cnf_transformation,[],[f8])).
% 3.07/0.98  
% 3.07/0.98  fof(f9,axiom,(
% 3.07/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f50,plain,(
% 3.07/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.07/0.98    inference(cnf_transformation,[],[f9])).
% 3.07/0.98  
% 3.07/0.98  fof(f67,plain,(
% 3.07/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.07/0.98    inference(definition_unfolding,[],[f49,f50])).
% 3.07/0.98  
% 3.07/0.98  fof(f68,plain,(
% 3.07/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.07/0.98    inference(definition_unfolding,[],[f48,f67])).
% 3.07/0.98  
% 3.07/0.98  fof(f69,plain,(
% 3.07/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.07/0.98    inference(definition_unfolding,[],[f47,f68])).
% 3.07/0.98  
% 3.07/0.98  fof(f70,plain,(
% 3.07/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.07/0.98    inference(definition_unfolding,[],[f46,f69])).
% 3.07/0.98  
% 3.07/0.98  fof(f71,plain,(
% 3.07/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.07/0.98    inference(definition_unfolding,[],[f45,f70])).
% 3.07/0.98  
% 3.07/0.98  fof(f73,plain,(
% 3.07/0.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.07/0.98    inference(definition_unfolding,[],[f44,f71])).
% 3.07/0.98  
% 3.07/0.98  fof(f81,plain,(
% 3.07/0.98    ( ! [X0,X1] : (m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.07/0.98    inference(definition_unfolding,[],[f51,f73])).
% 3.07/0.98  
% 3.07/0.98  fof(f12,axiom,(
% 3.07/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f27,plain,(
% 3.07/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.07/0.98    inference(nnf_transformation,[],[f12])).
% 3.07/0.98  
% 3.07/0.98  fof(f53,plain,(
% 3.07/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.07/0.98    inference(cnf_transformation,[],[f27])).
% 3.07/0.98  
% 3.07/0.98  fof(f62,plain,(
% 3.07/0.98    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 3.07/0.98    inference(cnf_transformation,[],[f36])).
% 3.07/0.98  
% 3.07/0.98  fof(f13,axiom,(
% 3.07/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f18,plain,(
% 3.07/0.98    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.07/0.98    inference(ennf_transformation,[],[f13])).
% 3.07/0.98  
% 3.07/0.98  fof(f19,plain,(
% 3.07/0.98    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.07/0.98    inference(flattening,[],[f18])).
% 3.07/0.98  
% 3.07/0.98  fof(f28,plain,(
% 3.07/0.98    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.07/0.98    inference(nnf_transformation,[],[f19])).
% 3.07/0.98  
% 3.07/0.98  fof(f29,plain,(
% 3.07/0.98    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.07/0.98    inference(rectify,[],[f28])).
% 3.07/0.98  
% 3.07/0.98  fof(f31,plain,(
% 3.07/0.98    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 & v3_pre_topc(sK2(X0,X1,X4),X0) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.07/0.98    introduced(choice_axiom,[])).
% 3.07/0.98  
% 3.07/0.98  fof(f30,plain,(
% 3.07/0.98    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.07/0.98    introduced(choice_axiom,[])).
% 3.07/0.98  
% 3.07/0.98  fof(f32,plain,(
% 3.07/0.98    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 & v3_pre_topc(sK2(X0,X1,X4),X0) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.07/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f31,f30])).
% 3.07/0.98  
% 3.07/0.98  fof(f57,plain,(
% 3.07/0.98    ( ! [X4,X0,X1] : (k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.07/0.98    inference(cnf_transformation,[],[f32])).
% 3.07/0.98  
% 3.07/0.98  fof(f61,plain,(
% 3.07/0.98    l1_pre_topc(sK3)),
% 3.07/0.98    inference(cnf_transformation,[],[f36])).
% 3.07/0.98  
% 3.07/0.98  fof(f63,plain,(
% 3.07/0.98    v2_tex_2(sK4,sK3)),
% 3.07/0.98    inference(cnf_transformation,[],[f36])).
% 3.07/0.98  
% 3.07/0.98  fof(f2,axiom,(
% 3.07/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f16,plain,(
% 3.07/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.07/0.98    inference(ennf_transformation,[],[f2])).
% 3.07/0.98  
% 3.07/0.98  fof(f43,plain,(
% 3.07/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.07/0.98    inference(cnf_transformation,[],[f16])).
% 3.07/0.98  
% 3.07/0.98  fof(f11,axiom,(
% 3.07/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f52,plain,(
% 3.07/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.07/0.98    inference(cnf_transformation,[],[f11])).
% 3.07/0.98  
% 3.07/0.98  fof(f72,plain,(
% 3.07/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.07/0.98    inference(definition_unfolding,[],[f52,f71])).
% 3.07/0.98  
% 3.07/0.98  fof(f80,plain,(
% 3.07/0.98    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.07/0.98    inference(definition_unfolding,[],[f43,f72])).
% 3.07/0.98  
% 3.07/0.98  fof(f1,axiom,(
% 3.07/0.98    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f22,plain,(
% 3.07/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.07/0.98    inference(nnf_transformation,[],[f1])).
% 3.07/0.98  
% 3.07/0.98  fof(f23,plain,(
% 3.07/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.07/0.98    inference(flattening,[],[f22])).
% 3.07/0.98  
% 3.07/0.98  fof(f24,plain,(
% 3.07/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.07/0.98    inference(rectify,[],[f23])).
% 3.07/0.98  
% 3.07/0.98  fof(f25,plain,(
% 3.07/0.98    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.07/0.98    introduced(choice_axiom,[])).
% 3.07/0.98  
% 3.07/0.98  fof(f26,plain,(
% 3.07/0.98    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.07/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 3.07/0.98  
% 3.07/0.98  fof(f38,plain,(
% 3.07/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.07/0.98    inference(cnf_transformation,[],[f26])).
% 3.07/0.98  
% 3.07/0.98  fof(f78,plain,(
% 3.07/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.07/0.98    inference(definition_unfolding,[],[f38,f72])).
% 3.07/0.98  
% 3.07/0.98  fof(f84,plain,(
% 3.07/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.07/0.98    inference(equality_resolution,[],[f78])).
% 3.07/0.98  
% 3.07/0.98  fof(f66,plain,(
% 3.07/0.98    ( ! [X3] : (k1_tarski(sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X3) | ~v3_pre_topc(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 3.07/0.98    inference(cnf_transformation,[],[f36])).
% 3.07/0.98  
% 3.07/0.98  fof(f82,plain,(
% 3.07/0.98    ( ! [X3] : (k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X3) | ~v3_pre_topc(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) )),
% 3.07/0.98    inference(definition_unfolding,[],[f66,f73])).
% 3.07/0.98  
% 3.07/0.98  fof(f55,plain,(
% 3.07/0.98    ( ! [X4,X0,X1] : (m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.07/0.98    inference(cnf_transformation,[],[f32])).
% 3.07/0.98  
% 3.07/0.98  fof(f56,plain,(
% 3.07/0.98    ( ! [X4,X0,X1] : (v3_pre_topc(sK2(X0,X1,X4),X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.07/0.98    inference(cnf_transformation,[],[f32])).
% 3.07/0.98  
% 3.07/0.98  cnf(c_17,negated_conjecture,
% 3.07/0.98      ( r2_hidden(sK5,sK4) ),
% 3.07/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2266,plain,
% 3.07/0.98      ( r2_hidden(sK5,sK4) = iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_7,plain,
% 3.07/0.98      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
% 3.07/0.98      | ~ r2_hidden(X0,X1) ),
% 3.07/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2270,plain,
% 3.07/0.98      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 3.07/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_9,plain,
% 3.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.07/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2268,plain,
% 3.07/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.07/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2952,plain,
% 3.07/0.98      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 3.07/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.07/0.98      inference(superposition,[status(thm)],[c_2270,c_2268]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_20,negated_conjecture,
% 3.07/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.07/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2263,plain,
% 3.07/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_13,plain,
% 3.07/0.98      ( ~ v2_tex_2(X0,X1)
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | ~ r1_tarski(X2,X0)
% 3.07/0.98      | ~ l1_pre_topc(X1)
% 3.07/0.98      | k9_subset_1(u1_struct_0(X1),X0,sK2(X1,X0,X2)) = X2 ),
% 3.07/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_21,negated_conjecture,
% 3.07/0.98      ( l1_pre_topc(sK3) ),
% 3.07/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_417,plain,
% 3.07/0.98      ( ~ v2_tex_2(X0,X1)
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | ~ r1_tarski(X2,X0)
% 3.07/0.98      | k9_subset_1(u1_struct_0(X1),X0,sK2(X1,X0,X2)) = X2
% 3.07/0.98      | sK3 != X1 ),
% 3.07/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_418,plain,
% 3.07/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | ~ r1_tarski(X1,X0)
% 3.07/0.98      | k9_subset_1(u1_struct_0(sK3),X0,sK2(sK3,X0,X1)) = X1 ),
% 3.07/0.98      inference(unflattening,[status(thm)],[c_417]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2260,plain,
% 3.07/0.98      ( k9_subset_1(u1_struct_0(sK3),X0,sK2(sK3,X0,X1)) = X1
% 3.07/0.98      | v2_tex_2(X0,sK3) != iProver_top
% 3.07/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.07/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.07/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2527,plain,
% 3.07/0.98      ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,X0)) = X0
% 3.07/0.98      | v2_tex_2(sK4,sK3) != iProver_top
% 3.07/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.07/0.98      | r1_tarski(X0,sK4) != iProver_top ),
% 3.07/0.98      inference(superposition,[status(thm)],[c_2263,c_2260]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_23,plain,
% 3.07/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_19,negated_conjecture,
% 3.07/0.98      ( v2_tex_2(sK4,sK3) ),
% 3.07/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_840,plain,
% 3.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | ~ r1_tarski(X1,X0)
% 3.07/0.98      | k9_subset_1(u1_struct_0(sK3),X0,sK2(sK3,X0,X1)) = X1
% 3.07/0.98      | sK4 != X0
% 3.07/0.98      | sK3 != sK3 ),
% 3.07/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_418]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_841,plain,
% 3.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | ~ r1_tarski(X0,sK4)
% 3.07/0.98      | k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,X0)) = X0 ),
% 3.07/0.98      inference(unflattening,[status(thm)],[c_840]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_842,plain,
% 3.07/0.98      ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,X0)) = X0
% 3.07/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.07/0.98      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.07/0.98      | r1_tarski(X0,sK4) != iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_841]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_3078,plain,
% 3.07/0.98      ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,X0)) = X0
% 3.07/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.07/0.98      | r1_tarski(X0,sK4) != iProver_top ),
% 3.07/0.98      inference(global_propositional_subsumption,
% 3.07/0.98                [status(thm)],
% 3.07/0.98                [c_2527,c_23,c_842]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_3085,plain,
% 3.07/0.98      ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 3.07/0.98      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK4) != iProver_top
% 3.07/0.98      | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.07/0.98      inference(superposition,[status(thm)],[c_2270,c_3078]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_4598,plain,
% 3.07/0.98      ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 3.07/0.98      | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
% 3.07/0.98      | r2_hidden(X0,sK4) != iProver_top ),
% 3.07/0.98      inference(superposition,[status(thm)],[c_2952,c_3085]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2678,plain,
% 3.07/0.98      ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 3.07/0.98      inference(superposition,[status(thm)],[c_2263,c_2268]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_6,plain,
% 3.07/0.98      ( ~ r1_tarski(X0,X1)
% 3.07/0.98      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
% 3.07/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2271,plain,
% 3.07/0.98      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
% 3.07/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2986,plain,
% 3.07/0.98      ( k1_setfam_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,u1_struct_0(sK3))) = sK4 ),
% 3.07/0.98      inference(superposition,[status(thm)],[c_2678,c_2271]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_4,plain,
% 3.07/0.98      ( r2_hidden(X0,X1)
% 3.07/0.98      | ~ r2_hidden(X0,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 3.07/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2273,plain,
% 3.07/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.07/0.98      | r2_hidden(X0,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_3859,plain,
% 3.07/0.98      ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
% 3.07/0.98      | r2_hidden(X0,sK4) != iProver_top ),
% 3.07/0.98      inference(superposition,[status(thm)],[c_2986,c_2273]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_7831,plain,
% 3.07/0.98      ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 3.07/0.98      | r2_hidden(X0,sK4) != iProver_top ),
% 3.07/0.98      inference(global_propositional_subsumption,
% 3.07/0.98                [status(thm)],
% 3.07/0.98                [c_4598,c_3859]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_7843,plain,
% 3.07/0.98      ( k9_subset_1(u1_struct_0(sK3),sK4,sK2(sK3,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 3.07/0.98      inference(superposition,[status(thm)],[c_2266,c_7831]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_16,negated_conjecture,
% 3.07/0.98      ( ~ v3_pre_topc(X0,sK3)
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X0) ),
% 3.07/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2267,plain,
% 3.07/0.98      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k9_subset_1(u1_struct_0(sK3),sK4,X0)
% 3.07/0.98      | v3_pre_topc(X0,sK3) != iProver_top
% 3.07/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_8012,plain,
% 3.07/0.98      ( v3_pre_topc(sK2(sK3,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),sK3) != iProver_top
% 3.07/0.98      | m1_subset_1(sK2(sK3,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.07/0.98      inference(superposition,[status(thm)],[c_7843,c_2267]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_4667,plain,
% 3.07/0.98      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | ~ r2_hidden(X0,u1_struct_0(sK3)) ),
% 3.07/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_4670,plain,
% 3.07/0.98      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.07/0.98      | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_4667]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_4672,plain,
% 3.07/0.98      ( m1_subset_1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.07/0.98      | r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top ),
% 3.07/0.98      inference(instantiation,[status(thm)],[c_4670]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_3861,plain,
% 3.07/0.98      ( r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
% 3.07/0.98      | r2_hidden(sK5,sK4) != iProver_top ),
% 3.07/0.98      inference(instantiation,[status(thm)],[c_3859]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_15,plain,
% 3.07/0.98      ( ~ v2_tex_2(X0,X1)
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | ~ r1_tarski(X2,X0)
% 3.07/0.98      | ~ l1_pre_topc(X1) ),
% 3.07/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_396,plain,
% 3.07/0.98      ( ~ v2_tex_2(X0,X1)
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | ~ r1_tarski(X2,X0)
% 3.07/0.98      | sK3 != X1 ),
% 3.07/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_21]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_397,plain,
% 3.07/0.98      ( ~ v2_tex_2(X0,sK3)
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | m1_subset_1(sK2(sK3,X0,X1),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | ~ r1_tarski(X1,X0) ),
% 3.07/0.98      inference(unflattening,[status(thm)],[c_396]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2446,plain,
% 3.07/0.98      ( ~ v2_tex_2(sK4,sK3)
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | m1_subset_1(sK2(sK3,sK4,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | ~ r1_tarski(X0,sK4) ),
% 3.07/0.98      inference(instantiation,[status(thm)],[c_397]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2642,plain,
% 3.07/0.98      ( ~ v2_tex_2(sK4,sK3)
% 3.07/0.98      | ~ m1_subset_1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | m1_subset_1(sK2(sK3,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | ~ r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) ),
% 3.07/0.98      inference(instantiation,[status(thm)],[c_2446]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2646,plain,
% 3.07/0.98      ( v2_tex_2(sK4,sK3) != iProver_top
% 3.07/0.98      | m1_subset_1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.07/0.98      | m1_subset_1(sK2(sK3,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 3.07/0.98      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.07/0.98      | r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) != iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_2642]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_14,plain,
% 3.07/0.98      ( v3_pre_topc(sK2(X0,X1,X2),X0)
% 3.07/0.98      | ~ v2_tex_2(X1,X0)
% 3.07/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.07/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.07/0.98      | ~ r1_tarski(X2,X1)
% 3.07/0.98      | ~ l1_pre_topc(X0) ),
% 3.07/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_375,plain,
% 3.07/0.98      ( v3_pre_topc(sK2(X0,X1,X2),X0)
% 3.07/0.98      | ~ v2_tex_2(X1,X0)
% 3.07/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.07/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.07/0.98      | ~ r1_tarski(X2,X1)
% 3.07/0.98      | sK3 != X0 ),
% 3.07/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_376,plain,
% 3.07/0.98      ( v3_pre_topc(sK2(sK3,X0,X1),sK3)
% 3.07/0.98      | ~ v2_tex_2(X0,sK3)
% 3.07/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | ~ r1_tarski(X1,X0) ),
% 3.07/0.98      inference(unflattening,[status(thm)],[c_375]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2443,plain,
% 3.07/0.98      ( v3_pre_topc(sK2(sK3,sK4,X0),sK3)
% 3.07/0.98      | ~ v2_tex_2(sK4,sK3)
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | ~ r1_tarski(X0,sK4) ),
% 3.07/0.98      inference(instantiation,[status(thm)],[c_376]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2643,plain,
% 3.07/0.98      ( v3_pre_topc(sK2(sK3,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),sK3)
% 3.07/0.98      | ~ v2_tex_2(sK4,sK3)
% 3.07/0.98      | ~ m1_subset_1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.07/0.98      | ~ r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) ),
% 3.07/0.98      inference(instantiation,[status(thm)],[c_2443]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2644,plain,
% 3.07/0.98      ( v3_pre_topc(sK2(sK3,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),sK3) = iProver_top
% 3.07/0.98      | v2_tex_2(sK4,sK3) != iProver_top
% 3.07/0.98      | m1_subset_1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.07/0.98      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 3.07/0.98      | r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) != iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_2643]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2507,plain,
% 3.07/0.98      ( ~ m1_subset_1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_zfmisc_1(sK4))
% 3.07/0.98      | r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) ),
% 3.07/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2508,plain,
% 3.07/0.98      ( m1_subset_1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_zfmisc_1(sK4)) != iProver_top
% 3.07/0.98      | r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) = iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_2507]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2483,plain,
% 3.07/0.98      ( m1_subset_1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_zfmisc_1(sK4))
% 3.07/0.98      | ~ r2_hidden(sK5,sK4) ),
% 3.07/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2484,plain,
% 3.07/0.98      ( m1_subset_1(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k1_zfmisc_1(sK4)) = iProver_top
% 3.07/0.98      | r2_hidden(sK5,sK4) != iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_2483]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_26,plain,
% 3.07/0.98      ( r2_hidden(sK5,sK4) = iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_24,plain,
% 3.07/0.98      ( v2_tex_2(sK4,sK3) = iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(contradiction,plain,
% 3.07/0.98      ( $false ),
% 3.07/0.98      inference(minisat,
% 3.07/0.98                [status(thm)],
% 3.07/0.98                [c_8012,c_4672,c_3861,c_2646,c_2644,c_2508,c_2484,c_26,
% 3.07/0.98                 c_24,c_23]) ).
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.07/0.98  
% 3.07/0.98  ------                               Statistics
% 3.07/0.98  
% 3.07/0.98  ------ General
% 3.07/0.98  
% 3.07/0.98  abstr_ref_over_cycles:                  0
% 3.07/0.98  abstr_ref_under_cycles:                 0
% 3.07/0.98  gc_basic_clause_elim:                   0
% 3.07/0.98  forced_gc_time:                         0
% 3.07/0.98  parsing_time:                           0.009
% 3.07/0.98  unif_index_cands_time:                  0.
% 3.07/0.98  unif_index_add_time:                    0.
% 3.07/0.98  orderings_time:                         0.
% 3.07/0.98  out_proof_time:                         0.008
% 3.07/0.98  total_time:                             0.294
% 3.07/0.98  num_of_symbols:                         48
% 3.07/0.98  num_of_terms:                           6476
% 3.07/0.98  
% 3.07/0.98  ------ Preprocessing
% 3.07/0.98  
% 3.07/0.98  num_of_splits:                          0
% 3.07/0.98  num_of_split_atoms:                     0
% 3.07/0.98  num_of_reused_defs:                     0
% 3.07/0.98  num_eq_ax_congr_red:                    23
% 3.07/0.98  num_of_sem_filtered_clauses:            1
% 3.07/0.98  num_of_subtypes:                        0
% 3.07/0.98  monotx_restored_types:                  0
% 3.07/0.98  sat_num_of_epr_types:                   0
% 3.07/0.98  sat_num_of_non_cyclic_types:            0
% 3.07/0.98  sat_guarded_non_collapsed_types:        0
% 3.07/0.98  num_pure_diseq_elim:                    0
% 3.07/0.98  simp_replaced_by:                       0
% 3.07/0.98  res_preprocessed:                       114
% 3.07/0.98  prep_upred:                             0
% 3.07/0.98  prep_unflattend:                        58
% 3.07/0.98  smt_new_axioms:                         0
% 3.07/0.98  pred_elim_cands:                        5
% 3.07/0.98  pred_elim:                              1
% 3.07/0.98  pred_elim_cl:                           1
% 3.07/0.98  pred_elim_cycles:                       8
% 3.07/0.98  merged_defs:                            8
% 3.07/0.98  merged_defs_ncl:                        0
% 3.07/0.98  bin_hyper_res:                          8
% 3.07/0.98  prep_cycles:                            4
% 3.07/0.98  pred_elim_time:                         0.024
% 3.07/0.98  splitting_time:                         0.
% 3.07/0.98  sem_filter_time:                        0.
% 3.07/0.98  monotx_time:                            0.001
% 3.07/0.98  subtype_inf_time:                       0.
% 3.07/0.98  
% 3.07/0.98  ------ Problem properties
% 3.07/0.98  
% 3.07/0.98  clauses:                                21
% 3.07/0.98  conjectures:                            5
% 3.07/0.98  epr:                                    2
% 3.07/0.98  horn:                                   17
% 3.07/0.98  ground:                                 4
% 3.07/0.98  unary:                                  4
% 3.07/0.98  binary:                                 6
% 3.07/0.98  lits:                                   58
% 3.07/0.98  lits_eq:                                7
% 3.07/0.98  fd_pure:                                0
% 3.07/0.98  fd_pseudo:                              0
% 3.07/0.98  fd_cond:                                0
% 3.07/0.98  fd_pseudo_cond:                         3
% 3.07/0.98  ac_symbols:                             0
% 3.07/0.98  
% 3.07/0.98  ------ Propositional Solver
% 3.07/0.98  
% 3.07/0.98  prop_solver_calls:                      27
% 3.07/0.98  prop_fast_solver_calls:                 1231
% 3.07/0.98  smt_solver_calls:                       0
% 3.07/0.98  smt_fast_solver_calls:                  0
% 3.07/0.98  prop_num_of_clauses:                    2455
% 3.07/0.98  prop_preprocess_simplified:             7262
% 3.07/0.98  prop_fo_subsumed:                       12
% 3.07/0.98  prop_solver_time:                       0.
% 3.07/0.98  smt_solver_time:                        0.
% 3.07/0.98  smt_fast_solver_time:                   0.
% 3.07/0.98  prop_fast_solver_time:                  0.
% 3.07/0.98  prop_unsat_core_time:                   0.
% 3.07/0.98  
% 3.07/0.98  ------ QBF
% 3.07/0.98  
% 3.07/0.98  qbf_q_res:                              0
% 3.07/0.98  qbf_num_tautologies:                    0
% 3.07/0.98  qbf_prep_cycles:                        0
% 3.07/0.98  
% 3.07/0.98  ------ BMC1
% 3.07/0.98  
% 3.07/0.98  bmc1_current_bound:                     -1
% 3.07/0.98  bmc1_last_solved_bound:                 -1
% 3.07/0.98  bmc1_unsat_core_size:                   -1
% 3.07/0.98  bmc1_unsat_core_parents_size:           -1
% 3.07/0.98  bmc1_merge_next_fun:                    0
% 3.07/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.07/0.98  
% 3.07/0.98  ------ Instantiation
% 3.07/0.98  
% 3.07/0.98  inst_num_of_clauses:                    687
% 3.07/0.98  inst_num_in_passive:                    355
% 3.07/0.98  inst_num_in_active:                     283
% 3.07/0.98  inst_num_in_unprocessed:                49
% 3.07/0.98  inst_num_of_loops:                      350
% 3.07/0.98  inst_num_of_learning_restarts:          0
% 3.07/0.98  inst_num_moves_active_passive:          64
% 3.07/0.98  inst_lit_activity:                      0
% 3.07/0.98  inst_lit_activity_moves:                0
% 3.07/0.98  inst_num_tautologies:                   0
% 3.07/0.98  inst_num_prop_implied:                  0
% 3.07/0.98  inst_num_existing_simplified:           0
% 3.07/0.98  inst_num_eq_res_simplified:             0
% 3.07/0.98  inst_num_child_elim:                    0
% 3.07/0.98  inst_num_of_dismatching_blockings:      292
% 3.07/0.98  inst_num_of_non_proper_insts:           499
% 3.07/0.98  inst_num_of_duplicates:                 0
% 3.07/0.98  inst_inst_num_from_inst_to_res:         0
% 3.07/0.98  inst_dismatching_checking_time:         0.
% 3.07/0.98  
% 3.07/0.98  ------ Resolution
% 3.07/0.98  
% 3.07/0.98  res_num_of_clauses:                     0
% 3.07/0.98  res_num_in_passive:                     0
% 3.07/0.98  res_num_in_active:                      0
% 3.07/0.98  res_num_of_loops:                       118
% 3.07/0.98  res_forward_subset_subsumed:            50
% 3.07/0.98  res_backward_subset_subsumed:           0
% 3.07/0.98  res_forward_subsumed:                   0
% 3.07/0.98  res_backward_subsumed:                  0
% 3.07/0.98  res_forward_subsumption_resolution:     2
% 3.07/0.98  res_backward_subsumption_resolution:    0
% 3.07/0.98  res_clause_to_clause_subsumption:       990
% 3.07/0.98  res_orphan_elimination:                 0
% 3.07/0.98  res_tautology_del:                      59
% 3.07/0.98  res_num_eq_res_simplified:              0
% 3.07/0.98  res_num_sel_changes:                    0
% 3.07/0.98  res_moves_from_active_to_pass:          0
% 3.07/0.98  
% 3.07/0.98  ------ Superposition
% 3.07/0.98  
% 3.07/0.98  sup_time_total:                         0.
% 3.07/0.98  sup_time_generating:                    0.
% 3.07/0.98  sup_time_sim_full:                      0.
% 3.07/0.98  sup_time_sim_immed:                     0.
% 3.07/0.98  
% 3.07/0.98  sup_num_of_clauses:                     121
% 3.07/0.98  sup_num_in_active:                      69
% 3.07/0.98  sup_num_in_passive:                     52
% 3.07/0.98  sup_num_of_loops:                       68
% 3.07/0.98  sup_fw_superposition:                   89
% 3.07/0.98  sup_bw_superposition:                   55
% 3.07/0.98  sup_immediate_simplified:               14
% 3.07/0.98  sup_given_eliminated:                   0
% 3.07/0.98  comparisons_done:                       0
% 3.07/0.98  comparisons_avoided:                    0
% 3.07/0.98  
% 3.07/0.98  ------ Simplifications
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  sim_fw_subset_subsumed:                 8
% 3.07/0.98  sim_bw_subset_subsumed:                 0
% 3.07/0.98  sim_fw_subsumed:                        5
% 3.07/0.98  sim_bw_subsumed:                        0
% 3.07/0.98  sim_fw_subsumption_res:                 0
% 3.07/0.98  sim_bw_subsumption_res:                 0
% 3.07/0.98  sim_tautology_del:                      21
% 3.07/0.98  sim_eq_tautology_del:                   0
% 3.07/0.98  sim_eq_res_simp:                        3
% 3.07/0.98  sim_fw_demodulated:                     0
% 3.07/0.98  sim_bw_demodulated:                     0
% 3.07/0.98  sim_light_normalised:                   2
% 3.07/0.98  sim_joinable_taut:                      0
% 3.07/0.98  sim_joinable_simp:                      0
% 3.07/0.98  sim_ac_normalised:                      0
% 3.07/0.98  sim_smt_subsumption:                    0
% 3.07/0.98  
%------------------------------------------------------------------------------
