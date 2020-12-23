%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:05 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 306 expanded)
%              Number of clauses        :   63 (  87 expanded)
%              Number of leaves         :   12 (  86 expanded)
%              Depth                    :   21
%              Number of atoms          :  412 (1775 expanded)
%              Number of equality atoms :  112 ( 313 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

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
    inference(ennf_transformation,[],[f8])).

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

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3)
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( k1_tarski(sK4) != k9_subset_1(u1_struct_0(X0),X1,X3)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK4,X1)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
                ( k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),sK3,X3)
                | ~ v4_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(X2,sK3)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & v2_tex_2(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
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
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3)
                  | ~ v4_pre_topc(X3,sK2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & v2_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ! [X3] :
        ( k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3)
        | ~ v4_pre_topc(X3,sK2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
    & r2_hidden(sK4,sK3)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f23,f22,f21])).

fof(f41,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f43])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f6])).

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

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f19,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
        & v4_pre_topc(sK1(X0,X1,X4),X0)
        & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
                    & v4_pre_topc(sK1(X0,X1,X4),X0)
                    & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X3] :
      ( k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3)
      | ~ v4_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X3] :
      ( k2_enumset1(sK4,sK4,sK4,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3)
      | ~ v4_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( v4_pre_topc(sK1(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_11,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2028,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1,plain,
    ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2032,plain,
    ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2030,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2432,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2032,c_2030])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2025,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_318,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_319,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_318])).

cnf(c_2022,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,X1)) = X1
    | v2_tex_2(X0,sK2) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_2282,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0)) = X0
    | v2_tex_2(sK3,sK2) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2025,c_2022])).

cnf(c_13,negated_conjecture,
    ( v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_789,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),X1,sK1(sK2,X1,X0)) = X0
    | sK3 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_319])).

cnf(c_790,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_789])).

cnf(c_794,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK3)
    | k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_790,c_14])).

cnf(c_795,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_794])).

cnf(c_796,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0)) = X0
    | r1_tarski(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_795])).

cnf(c_2525,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0)) = X0
    | r1_tarski(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2282,c_796])).

cnf(c_2533,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X0)
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),sK3) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2032,c_2525])).

cnf(c_3153,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X0)
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2432,c_2533])).

cnf(c_2347,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2025,c_2030])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_121,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_158,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_0,c_121])).

cnf(c_2024,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_158])).

cnf(c_3084,plain,
    ( r2_hidden(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2347,c_2024])).

cnf(c_3951,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X0)
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3153,c_3084])).

cnf(c_3959,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_2028,c_3951])).

cnf(c_10,negated_conjecture,
    ( ~ v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_enumset1(sK4,sK4,sK4,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2029,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X0)
    | v4_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4016,plain,
    ( v4_pre_topc(sK1(sK2,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK2) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3959,c_2029])).

cnf(c_2332,plain,
    ( m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2333,plain,
    ( m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r2_hidden(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2332])).

cnf(c_2198,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK2))
    | r2_hidden(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_2297,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK2))
    | r2_hidden(sK4,u1_struct_0(sK2))
    | ~ r2_hidden(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_2198])).

cnf(c_2298,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2297])).

cnf(c_8,plain,
    ( v4_pre_topc(sK1(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ r1_tarski(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_390,plain,
    ( v4_pre_topc(sK1(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ r1_tarski(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_15])).

cnf(c_391,plain,
    ( v4_pre_topc(sK1(sK2,X0,X1),sK2)
    | ~ v2_tex_2(X0,sK2)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_2157,plain,
    ( v4_pre_topc(sK1(sK2,sK3,X0),sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ r1_tarski(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_391])).

cnf(c_2262,plain,
    ( v4_pre_topc(sK1(sK2,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
    | ~ m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_2157])).

cnf(c_2266,plain,
    ( v4_pre_topc(sK1(sK2,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK2) = iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top
    | r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3) != iProver_top
    | m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2262])).

cnf(c_9,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_297,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_15])).

cnf(c_298,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_2154,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ r1_tarski(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_298])).

cnf(c_2263,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
    | ~ m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_2154])).

cnf(c_2264,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3) != iProver_top
    | m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2263])).

cnf(c_2218,plain,
    ( r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
    | ~ m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2219,plain,
    ( r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3) = iProver_top
    | m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2218])).

cnf(c_2174,plain,
    ( m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(sK3))
    | ~ r2_hidden(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2175,plain,
    ( m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(sK3)) = iProver_top
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2174])).

cnf(c_2167,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2168,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2167])).

cnf(c_20,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_18,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_17,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4016,c_2333,c_2298,c_2266,c_2264,c_2219,c_2175,c_2168,c_20,c_18,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.68/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/0.98  
% 1.68/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.68/0.98  
% 1.68/0.98  ------  iProver source info
% 1.68/0.98  
% 1.68/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.68/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.68/0.98  git: non_committed_changes: false
% 1.68/0.98  git: last_make_outside_of_git: false
% 1.68/0.98  
% 1.68/0.98  ------ 
% 1.68/0.98  
% 1.68/0.98  ------ Input Options
% 1.68/0.98  
% 1.68/0.98  --out_options                           all
% 1.68/0.98  --tptp_safe_out                         true
% 1.68/0.98  --problem_path                          ""
% 1.68/0.98  --include_path                          ""
% 1.68/0.98  --clausifier                            res/vclausify_rel
% 1.68/0.98  --clausifier_options                    --mode clausify
% 1.68/0.98  --stdin                                 false
% 1.68/0.98  --stats_out                             all
% 1.68/0.98  
% 1.68/0.98  ------ General Options
% 1.68/0.98  
% 1.68/0.98  --fof                                   false
% 1.68/0.98  --time_out_real                         305.
% 1.68/0.98  --time_out_virtual                      -1.
% 1.68/0.98  --symbol_type_check                     false
% 1.68/0.98  --clausify_out                          false
% 1.68/0.98  --sig_cnt_out                           false
% 1.68/0.98  --trig_cnt_out                          false
% 1.68/0.98  --trig_cnt_out_tolerance                1.
% 1.68/0.98  --trig_cnt_out_sk_spl                   false
% 1.68/0.98  --abstr_cl_out                          false
% 1.68/0.98  
% 1.68/0.98  ------ Global Options
% 1.68/0.98  
% 1.68/0.98  --schedule                              default
% 1.68/0.98  --add_important_lit                     false
% 1.68/0.98  --prop_solver_per_cl                    1000
% 1.68/0.98  --min_unsat_core                        false
% 1.68/0.98  --soft_assumptions                      false
% 1.68/0.98  --soft_lemma_size                       3
% 1.68/0.98  --prop_impl_unit_size                   0
% 1.68/0.98  --prop_impl_unit                        []
% 1.68/0.98  --share_sel_clauses                     true
% 1.68/0.98  --reset_solvers                         false
% 1.68/0.98  --bc_imp_inh                            [conj_cone]
% 1.68/0.98  --conj_cone_tolerance                   3.
% 1.68/0.98  --extra_neg_conj                        none
% 1.68/0.98  --large_theory_mode                     true
% 1.68/0.98  --prolific_symb_bound                   200
% 1.68/0.98  --lt_threshold                          2000
% 1.68/0.98  --clause_weak_htbl                      true
% 1.68/0.98  --gc_record_bc_elim                     false
% 1.68/0.98  
% 1.68/0.98  ------ Preprocessing Options
% 1.68/0.98  
% 1.68/0.98  --preprocessing_flag                    true
% 1.68/0.98  --time_out_prep_mult                    0.1
% 1.68/0.98  --splitting_mode                        input
% 1.68/0.98  --splitting_grd                         true
% 1.68/0.98  --splitting_cvd                         false
% 1.68/0.98  --splitting_cvd_svl                     false
% 1.68/0.98  --splitting_nvd                         32
% 1.68/0.98  --sub_typing                            true
% 1.68/0.98  --prep_gs_sim                           true
% 1.68/0.98  --prep_unflatten                        true
% 1.68/0.98  --prep_res_sim                          true
% 1.68/0.98  --prep_upred                            true
% 1.68/0.98  --prep_sem_filter                       exhaustive
% 1.68/0.98  --prep_sem_filter_out                   false
% 1.68/0.98  --pred_elim                             true
% 1.68/0.98  --res_sim_input                         true
% 1.68/0.98  --eq_ax_congr_red                       true
% 1.68/0.98  --pure_diseq_elim                       true
% 1.68/0.98  --brand_transform                       false
% 1.68/0.98  --non_eq_to_eq                          false
% 1.68/0.98  --prep_def_merge                        true
% 1.68/0.98  --prep_def_merge_prop_impl              false
% 1.68/0.98  --prep_def_merge_mbd                    true
% 1.68/0.98  --prep_def_merge_tr_red                 false
% 1.68/0.98  --prep_def_merge_tr_cl                  false
% 1.68/0.98  --smt_preprocessing                     true
% 1.68/0.98  --smt_ac_axioms                         fast
% 1.68/0.98  --preprocessed_out                      false
% 1.68/0.98  --preprocessed_stats                    false
% 1.68/0.98  
% 1.68/0.98  ------ Abstraction refinement Options
% 1.68/0.98  
% 1.68/0.98  --abstr_ref                             []
% 1.68/0.98  --abstr_ref_prep                        false
% 1.68/0.98  --abstr_ref_until_sat                   false
% 1.68/0.98  --abstr_ref_sig_restrict                funpre
% 1.68/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.68/0.98  --abstr_ref_under                       []
% 1.68/0.98  
% 1.68/0.98  ------ SAT Options
% 1.68/0.98  
% 1.68/0.98  --sat_mode                              false
% 1.68/0.98  --sat_fm_restart_options                ""
% 1.68/0.98  --sat_gr_def                            false
% 1.68/0.98  --sat_epr_types                         true
% 1.68/0.98  --sat_non_cyclic_types                  false
% 1.68/0.98  --sat_finite_models                     false
% 1.68/0.98  --sat_fm_lemmas                         false
% 1.68/0.98  --sat_fm_prep                           false
% 1.68/0.98  --sat_fm_uc_incr                        true
% 1.68/0.98  --sat_out_model                         small
% 1.68/0.98  --sat_out_clauses                       false
% 1.68/0.98  
% 1.68/0.98  ------ QBF Options
% 1.68/0.98  
% 1.68/0.98  --qbf_mode                              false
% 1.68/0.98  --qbf_elim_univ                         false
% 1.68/0.98  --qbf_dom_inst                          none
% 1.68/0.98  --qbf_dom_pre_inst                      false
% 1.68/0.98  --qbf_sk_in                             false
% 1.68/0.98  --qbf_pred_elim                         true
% 1.68/0.98  --qbf_split                             512
% 1.68/0.98  
% 1.68/0.98  ------ BMC1 Options
% 1.68/0.98  
% 1.68/0.98  --bmc1_incremental                      false
% 1.68/0.98  --bmc1_axioms                           reachable_all
% 1.68/0.98  --bmc1_min_bound                        0
% 1.68/0.98  --bmc1_max_bound                        -1
% 1.68/0.98  --bmc1_max_bound_default                -1
% 1.68/0.98  --bmc1_symbol_reachability              true
% 1.68/0.98  --bmc1_property_lemmas                  false
% 1.68/0.98  --bmc1_k_induction                      false
% 1.68/0.98  --bmc1_non_equiv_states                 false
% 1.68/0.98  --bmc1_deadlock                         false
% 1.68/0.98  --bmc1_ucm                              false
% 1.68/0.98  --bmc1_add_unsat_core                   none
% 1.68/0.98  --bmc1_unsat_core_children              false
% 1.68/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.68/0.98  --bmc1_out_stat                         full
% 1.68/0.98  --bmc1_ground_init                      false
% 1.68/0.98  --bmc1_pre_inst_next_state              false
% 1.68/0.98  --bmc1_pre_inst_state                   false
% 1.68/0.98  --bmc1_pre_inst_reach_state             false
% 1.68/0.98  --bmc1_out_unsat_core                   false
% 1.68/0.98  --bmc1_aig_witness_out                  false
% 1.68/0.98  --bmc1_verbose                          false
% 1.68/0.98  --bmc1_dump_clauses_tptp                false
% 1.68/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.68/0.98  --bmc1_dump_file                        -
% 1.68/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.68/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.68/0.98  --bmc1_ucm_extend_mode                  1
% 1.68/0.98  --bmc1_ucm_init_mode                    2
% 1.68/0.98  --bmc1_ucm_cone_mode                    none
% 1.68/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.68/0.98  --bmc1_ucm_relax_model                  4
% 1.68/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.68/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.68/0.98  --bmc1_ucm_layered_model                none
% 1.68/0.98  --bmc1_ucm_max_lemma_size               10
% 1.68/0.98  
% 1.68/0.98  ------ AIG Options
% 1.68/0.98  
% 1.68/0.98  --aig_mode                              false
% 1.68/0.98  
% 1.68/0.98  ------ Instantiation Options
% 1.68/0.98  
% 1.68/0.98  --instantiation_flag                    true
% 1.68/0.98  --inst_sos_flag                         false
% 1.68/0.98  --inst_sos_phase                        true
% 1.68/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.68/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.68/0.98  --inst_lit_sel_side                     num_symb
% 1.68/0.98  --inst_solver_per_active                1400
% 1.68/0.98  --inst_solver_calls_frac                1.
% 1.68/0.98  --inst_passive_queue_type               priority_queues
% 1.68/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.68/0.98  --inst_passive_queues_freq              [25;2]
% 1.68/0.98  --inst_dismatching                      true
% 1.68/0.98  --inst_eager_unprocessed_to_passive     true
% 1.68/0.98  --inst_prop_sim_given                   true
% 1.68/0.98  --inst_prop_sim_new                     false
% 1.68/0.98  --inst_subs_new                         false
% 1.68/0.98  --inst_eq_res_simp                      false
% 1.68/0.98  --inst_subs_given                       false
% 1.68/0.98  --inst_orphan_elimination               true
% 1.68/0.98  --inst_learning_loop_flag               true
% 1.68/0.98  --inst_learning_start                   3000
% 1.68/0.98  --inst_learning_factor                  2
% 1.68/0.98  --inst_start_prop_sim_after_learn       3
% 1.68/0.98  --inst_sel_renew                        solver
% 1.68/0.98  --inst_lit_activity_flag                true
% 1.68/0.98  --inst_restr_to_given                   false
% 1.68/0.98  --inst_activity_threshold               500
% 1.68/0.98  --inst_out_proof                        true
% 1.68/0.98  
% 1.68/0.98  ------ Resolution Options
% 1.68/0.98  
% 1.68/0.98  --resolution_flag                       true
% 1.68/0.98  --res_lit_sel                           adaptive
% 1.68/0.98  --res_lit_sel_side                      none
% 1.68/0.98  --res_ordering                          kbo
% 1.68/0.98  --res_to_prop_solver                    active
% 1.68/0.98  --res_prop_simpl_new                    false
% 1.68/0.98  --res_prop_simpl_given                  true
% 1.68/0.98  --res_passive_queue_type                priority_queues
% 1.68/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.68/0.98  --res_passive_queues_freq               [15;5]
% 1.68/0.98  --res_forward_subs                      full
% 1.68/0.98  --res_backward_subs                     full
% 1.68/0.98  --res_forward_subs_resolution           true
% 1.68/0.98  --res_backward_subs_resolution          true
% 1.68/0.98  --res_orphan_elimination                true
% 1.68/0.98  --res_time_limit                        2.
% 1.68/0.98  --res_out_proof                         true
% 1.68/0.98  
% 1.68/0.98  ------ Superposition Options
% 1.68/0.98  
% 1.68/0.98  --superposition_flag                    true
% 1.68/0.98  --sup_passive_queue_type                priority_queues
% 1.68/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.68/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.68/0.98  --demod_completeness_check              fast
% 1.68/0.98  --demod_use_ground                      true
% 1.68/0.98  --sup_to_prop_solver                    passive
% 1.68/0.98  --sup_prop_simpl_new                    true
% 1.68/0.98  --sup_prop_simpl_given                  true
% 1.68/0.98  --sup_fun_splitting                     false
% 1.68/0.98  --sup_smt_interval                      50000
% 1.68/0.98  
% 1.68/0.98  ------ Superposition Simplification Setup
% 1.68/0.98  
% 1.68/0.98  --sup_indices_passive                   []
% 1.68/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.68/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.98  --sup_full_bw                           [BwDemod]
% 1.68/0.98  --sup_immed_triv                        [TrivRules]
% 1.68/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.68/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.98  --sup_immed_bw_main                     []
% 1.68/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.68/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.68/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.68/0.98  
% 1.68/0.98  ------ Combination Options
% 1.68/0.98  
% 1.68/0.98  --comb_res_mult                         3
% 1.68/0.98  --comb_sup_mult                         2
% 1.68/0.98  --comb_inst_mult                        10
% 1.68/0.98  
% 1.68/0.98  ------ Debug Options
% 1.68/0.98  
% 1.68/0.98  --dbg_backtrace                         false
% 1.68/0.98  --dbg_dump_prop_clauses                 false
% 1.68/0.98  --dbg_dump_prop_clauses_file            -
% 1.68/0.98  --dbg_out_stat                          false
% 1.68/0.98  ------ Parsing...
% 1.68/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.68/0.98  
% 1.68/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.68/0.98  
% 1.68/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.68/0.98  
% 1.68/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.68/0.98  ------ Proving...
% 1.68/0.98  ------ Problem Properties 
% 1.68/0.98  
% 1.68/0.98  
% 1.68/0.98  clauses                                 15
% 1.68/0.98  conjectures                             5
% 1.68/0.98  EPR                                     3
% 1.68/0.98  Horn                                    13
% 1.68/0.98  unary                                   4
% 1.68/0.98  binary                                  3
% 1.68/0.98  lits                                    42
% 1.68/0.98  lits eq                                 3
% 1.68/0.98  fd_pure                                 0
% 1.68/0.98  fd_pseudo                               0
% 1.68/0.98  fd_cond                                 0
% 1.68/0.98  fd_pseudo_cond                          0
% 1.68/0.98  AC symbols                              0
% 1.68/0.98  
% 1.68/0.98  ------ Schedule dynamic 5 is on 
% 1.68/0.98  
% 1.68/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.68/0.98  
% 1.68/0.98  
% 1.68/0.98  ------ 
% 1.68/0.98  Current options:
% 1.68/0.98  ------ 
% 1.68/0.98  
% 1.68/0.98  ------ Input Options
% 1.68/0.98  
% 1.68/0.98  --out_options                           all
% 1.68/0.98  --tptp_safe_out                         true
% 1.68/0.98  --problem_path                          ""
% 1.68/0.98  --include_path                          ""
% 1.68/0.98  --clausifier                            res/vclausify_rel
% 1.68/0.98  --clausifier_options                    --mode clausify
% 1.68/0.98  --stdin                                 false
% 1.68/0.98  --stats_out                             all
% 1.68/0.98  
% 1.68/0.98  ------ General Options
% 1.68/0.98  
% 1.68/0.98  --fof                                   false
% 1.68/0.98  --time_out_real                         305.
% 1.68/0.98  --time_out_virtual                      -1.
% 1.68/0.98  --symbol_type_check                     false
% 1.68/0.98  --clausify_out                          false
% 1.68/0.98  --sig_cnt_out                           false
% 1.68/0.98  --trig_cnt_out                          false
% 1.68/0.98  --trig_cnt_out_tolerance                1.
% 1.68/0.98  --trig_cnt_out_sk_spl                   false
% 1.68/0.98  --abstr_cl_out                          false
% 1.68/0.98  
% 1.68/0.98  ------ Global Options
% 1.68/0.98  
% 1.68/0.98  --schedule                              default
% 1.68/0.98  --add_important_lit                     false
% 1.68/0.98  --prop_solver_per_cl                    1000
% 1.68/0.98  --min_unsat_core                        false
% 1.68/0.98  --soft_assumptions                      false
% 1.68/0.98  --soft_lemma_size                       3
% 1.68/0.98  --prop_impl_unit_size                   0
% 1.68/0.98  --prop_impl_unit                        []
% 1.68/0.98  --share_sel_clauses                     true
% 1.68/0.98  --reset_solvers                         false
% 1.68/0.98  --bc_imp_inh                            [conj_cone]
% 1.68/0.98  --conj_cone_tolerance                   3.
% 1.68/0.98  --extra_neg_conj                        none
% 1.68/0.98  --large_theory_mode                     true
% 1.68/0.98  --prolific_symb_bound                   200
% 1.68/0.98  --lt_threshold                          2000
% 1.68/0.98  --clause_weak_htbl                      true
% 1.68/0.98  --gc_record_bc_elim                     false
% 1.68/0.98  
% 1.68/0.98  ------ Preprocessing Options
% 1.68/0.98  
% 1.68/0.98  --preprocessing_flag                    true
% 1.68/0.98  --time_out_prep_mult                    0.1
% 1.68/0.98  --splitting_mode                        input
% 1.68/0.98  --splitting_grd                         true
% 1.68/0.98  --splitting_cvd                         false
% 1.68/0.98  --splitting_cvd_svl                     false
% 1.68/0.98  --splitting_nvd                         32
% 1.68/0.98  --sub_typing                            true
% 1.68/0.98  --prep_gs_sim                           true
% 1.68/0.98  --prep_unflatten                        true
% 1.68/0.98  --prep_res_sim                          true
% 1.68/0.98  --prep_upred                            true
% 1.68/0.98  --prep_sem_filter                       exhaustive
% 1.68/0.98  --prep_sem_filter_out                   false
% 1.68/0.98  --pred_elim                             true
% 1.68/0.98  --res_sim_input                         true
% 1.68/0.98  --eq_ax_congr_red                       true
% 1.68/0.98  --pure_diseq_elim                       true
% 1.68/0.98  --brand_transform                       false
% 1.68/0.98  --non_eq_to_eq                          false
% 1.68/0.98  --prep_def_merge                        true
% 1.68/0.98  --prep_def_merge_prop_impl              false
% 1.68/0.98  --prep_def_merge_mbd                    true
% 1.68/0.98  --prep_def_merge_tr_red                 false
% 1.68/0.98  --prep_def_merge_tr_cl                  false
% 1.68/0.98  --smt_preprocessing                     true
% 1.68/0.98  --smt_ac_axioms                         fast
% 1.68/0.98  --preprocessed_out                      false
% 1.68/0.98  --preprocessed_stats                    false
% 1.68/0.98  
% 1.68/0.98  ------ Abstraction refinement Options
% 1.68/0.98  
% 1.68/0.98  --abstr_ref                             []
% 1.68/0.98  --abstr_ref_prep                        false
% 1.68/0.98  --abstr_ref_until_sat                   false
% 1.68/0.98  --abstr_ref_sig_restrict                funpre
% 1.68/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.68/0.98  --abstr_ref_under                       []
% 1.68/0.98  
% 1.68/0.98  ------ SAT Options
% 1.68/0.98  
% 1.68/0.98  --sat_mode                              false
% 1.68/0.98  --sat_fm_restart_options                ""
% 1.68/0.98  --sat_gr_def                            false
% 1.68/0.98  --sat_epr_types                         true
% 1.68/0.98  --sat_non_cyclic_types                  false
% 1.68/0.98  --sat_finite_models                     false
% 1.68/0.98  --sat_fm_lemmas                         false
% 1.68/0.98  --sat_fm_prep                           false
% 1.68/0.98  --sat_fm_uc_incr                        true
% 1.68/0.98  --sat_out_model                         small
% 1.68/0.98  --sat_out_clauses                       false
% 1.68/0.98  
% 1.68/0.98  ------ QBF Options
% 1.68/0.98  
% 1.68/0.98  --qbf_mode                              false
% 1.68/0.98  --qbf_elim_univ                         false
% 1.68/0.98  --qbf_dom_inst                          none
% 1.68/0.98  --qbf_dom_pre_inst                      false
% 1.68/0.98  --qbf_sk_in                             false
% 1.68/0.98  --qbf_pred_elim                         true
% 1.68/0.98  --qbf_split                             512
% 1.68/0.98  
% 1.68/0.98  ------ BMC1 Options
% 1.68/0.98  
% 1.68/0.98  --bmc1_incremental                      false
% 1.68/0.98  --bmc1_axioms                           reachable_all
% 1.68/0.98  --bmc1_min_bound                        0
% 1.68/0.98  --bmc1_max_bound                        -1
% 1.68/0.98  --bmc1_max_bound_default                -1
% 1.68/0.98  --bmc1_symbol_reachability              true
% 1.68/0.98  --bmc1_property_lemmas                  false
% 1.68/0.98  --bmc1_k_induction                      false
% 1.68/0.98  --bmc1_non_equiv_states                 false
% 1.68/0.98  --bmc1_deadlock                         false
% 1.68/0.98  --bmc1_ucm                              false
% 1.68/0.98  --bmc1_add_unsat_core                   none
% 1.68/0.98  --bmc1_unsat_core_children              false
% 1.68/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.68/0.98  --bmc1_out_stat                         full
% 1.68/0.98  --bmc1_ground_init                      false
% 1.68/0.98  --bmc1_pre_inst_next_state              false
% 1.68/0.98  --bmc1_pre_inst_state                   false
% 1.68/0.98  --bmc1_pre_inst_reach_state             false
% 1.68/0.98  --bmc1_out_unsat_core                   false
% 1.68/0.98  --bmc1_aig_witness_out                  false
% 1.68/0.98  --bmc1_verbose                          false
% 1.68/0.98  --bmc1_dump_clauses_tptp                false
% 1.68/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.68/0.98  --bmc1_dump_file                        -
% 1.68/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.68/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.68/0.98  --bmc1_ucm_extend_mode                  1
% 1.68/0.98  --bmc1_ucm_init_mode                    2
% 1.68/0.98  --bmc1_ucm_cone_mode                    none
% 1.68/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.68/0.98  --bmc1_ucm_relax_model                  4
% 1.68/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.68/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.68/0.98  --bmc1_ucm_layered_model                none
% 1.68/0.98  --bmc1_ucm_max_lemma_size               10
% 1.68/0.98  
% 1.68/0.98  ------ AIG Options
% 1.68/0.98  
% 1.68/0.98  --aig_mode                              false
% 1.68/0.98  
% 1.68/0.98  ------ Instantiation Options
% 1.68/0.98  
% 1.68/0.98  --instantiation_flag                    true
% 1.68/0.98  --inst_sos_flag                         false
% 1.68/0.98  --inst_sos_phase                        true
% 1.68/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.68/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.68/0.98  --inst_lit_sel_side                     none
% 1.68/0.98  --inst_solver_per_active                1400
% 1.68/0.98  --inst_solver_calls_frac                1.
% 1.68/0.98  --inst_passive_queue_type               priority_queues
% 1.68/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.68/0.98  --inst_passive_queues_freq              [25;2]
% 1.68/0.98  --inst_dismatching                      true
% 1.68/0.98  --inst_eager_unprocessed_to_passive     true
% 1.68/0.98  --inst_prop_sim_given                   true
% 1.68/0.98  --inst_prop_sim_new                     false
% 1.68/0.98  --inst_subs_new                         false
% 1.68/0.98  --inst_eq_res_simp                      false
% 1.68/0.98  --inst_subs_given                       false
% 1.68/0.98  --inst_orphan_elimination               true
% 1.68/0.98  --inst_learning_loop_flag               true
% 1.68/0.98  --inst_learning_start                   3000
% 1.68/0.98  --inst_learning_factor                  2
% 1.68/0.98  --inst_start_prop_sim_after_learn       3
% 1.68/0.98  --inst_sel_renew                        solver
% 1.68/0.98  --inst_lit_activity_flag                true
% 1.68/0.98  --inst_restr_to_given                   false
% 1.68/0.98  --inst_activity_threshold               500
% 1.68/0.98  --inst_out_proof                        true
% 1.68/0.98  
% 1.68/0.98  ------ Resolution Options
% 1.68/0.98  
% 1.68/0.98  --resolution_flag                       false
% 1.68/0.98  --res_lit_sel                           adaptive
% 1.68/0.98  --res_lit_sel_side                      none
% 1.68/0.98  --res_ordering                          kbo
% 1.68/0.98  --res_to_prop_solver                    active
% 1.68/0.98  --res_prop_simpl_new                    false
% 1.68/0.98  --res_prop_simpl_given                  true
% 1.68/0.98  --res_passive_queue_type                priority_queues
% 1.68/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.68/0.98  --res_passive_queues_freq               [15;5]
% 1.68/0.98  --res_forward_subs                      full
% 1.68/0.98  --res_backward_subs                     full
% 1.68/0.98  --res_forward_subs_resolution           true
% 1.68/0.98  --res_backward_subs_resolution          true
% 1.68/0.98  --res_orphan_elimination                true
% 1.68/0.98  --res_time_limit                        2.
% 1.68/0.98  --res_out_proof                         true
% 1.68/0.98  
% 1.68/0.98  ------ Superposition Options
% 1.68/0.98  
% 1.68/0.98  --superposition_flag                    true
% 1.68/0.98  --sup_passive_queue_type                priority_queues
% 1.68/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.68/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.68/0.98  --demod_completeness_check              fast
% 1.68/0.98  --demod_use_ground                      true
% 1.68/0.98  --sup_to_prop_solver                    passive
% 1.68/0.98  --sup_prop_simpl_new                    true
% 1.68/0.98  --sup_prop_simpl_given                  true
% 1.68/0.98  --sup_fun_splitting                     false
% 1.68/0.98  --sup_smt_interval                      50000
% 1.68/0.98  
% 1.68/0.98  ------ Superposition Simplification Setup
% 1.68/0.98  
% 1.68/0.98  --sup_indices_passive                   []
% 1.68/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.68/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.98  --sup_full_bw                           [BwDemod]
% 1.68/0.98  --sup_immed_triv                        [TrivRules]
% 1.68/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.68/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.99  --sup_immed_bw_main                     []
% 1.68/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.68/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.68/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.68/0.99  
% 1.68/0.99  ------ Combination Options
% 1.68/0.99  
% 1.68/0.99  --comb_res_mult                         3
% 1.68/0.99  --comb_sup_mult                         2
% 1.68/0.99  --comb_inst_mult                        10
% 1.68/0.99  
% 1.68/0.99  ------ Debug Options
% 1.68/0.99  
% 1.68/0.99  --dbg_backtrace                         false
% 1.68/0.99  --dbg_dump_prop_clauses                 false
% 1.68/0.99  --dbg_dump_prop_clauses_file            -
% 1.68/0.99  --dbg_out_stat                          false
% 1.68/0.99  
% 1.68/0.99  
% 1.68/0.99  
% 1.68/0.99  
% 1.68/0.99  ------ Proving...
% 1.68/0.99  
% 1.68/0.99  
% 1.68/0.99  % SZS status Theorem for theBenchmark.p
% 1.68/0.99  
% 1.68/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.68/0.99  
% 1.68/0.99  fof(f7,conjecture,(
% 1.68/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 1.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.99  
% 1.68/0.99  fof(f8,negated_conjecture,(
% 1.68/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 1.68/0.99    inference(negated_conjecture,[],[f7])).
% 1.68/0.99  
% 1.68/0.99  fof(f13,plain,(
% 1.68/0.99    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.68/0.99    inference(ennf_transformation,[],[f8])).
% 1.68/0.99  
% 1.68/0.99  fof(f14,plain,(
% 1.68/0.99    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.68/0.99    inference(flattening,[],[f13])).
% 1.68/0.99  
% 1.68/0.99  fof(f23,plain,(
% 1.68/0.99    ( ! [X0,X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (k1_tarski(sK4) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK4,X1) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 1.68/0.99    introduced(choice_axiom,[])).
% 1.68/0.99  
% 1.68/0.99  fof(f22,plain,(
% 1.68/0.99    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),sK3,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.68/0.99    introduced(choice_axiom,[])).
% 1.68/0.99  
% 1.68/0.99  fof(f21,plain,(
% 1.68/0.99    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3) | ~v4_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2))),
% 1.68/0.99    introduced(choice_axiom,[])).
% 1.68/0.99  
% 1.68/0.99  fof(f24,plain,(
% 1.68/0.99    ((! [X3] : (k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3) | ~v4_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2)),
% 1.68/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f23,f22,f21])).
% 1.68/0.99  
% 1.68/0.99  fof(f41,plain,(
% 1.68/0.99    r2_hidden(sK4,sK3)),
% 1.68/0.99    inference(cnf_transformation,[],[f24])).
% 1.68/0.99  
% 1.68/0.99  fof(f4,axiom,(
% 1.68/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.99  
% 1.68/0.99  fof(f10,plain,(
% 1.68/0.99    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.68/0.99    inference(ennf_transformation,[],[f4])).
% 1.68/0.99  
% 1.68/0.99  fof(f28,plain,(
% 1.68/0.99    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.68/0.99    inference(cnf_transformation,[],[f10])).
% 1.68/0.99  
% 1.68/0.99  fof(f1,axiom,(
% 1.68/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.99  
% 1.68/0.99  fof(f25,plain,(
% 1.68/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.68/0.99    inference(cnf_transformation,[],[f1])).
% 1.68/0.99  
% 1.68/0.99  fof(f2,axiom,(
% 1.68/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 1.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.99  
% 1.68/0.99  fof(f26,plain,(
% 1.68/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.68/0.99    inference(cnf_transformation,[],[f2])).
% 1.68/0.99  
% 1.68/0.99  fof(f43,plain,(
% 1.68/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.68/0.99    inference(definition_unfolding,[],[f25,f26])).
% 1.68/0.99  
% 1.68/0.99  fof(f44,plain,(
% 1.68/0.99    ( ! [X0,X1] : (m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.68/0.99    inference(definition_unfolding,[],[f28,f43])).
% 1.68/0.99  
% 1.68/0.99  fof(f5,axiom,(
% 1.68/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.99  
% 1.68/0.99  fof(f15,plain,(
% 1.68/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.68/0.99    inference(nnf_transformation,[],[f5])).
% 1.68/0.99  
% 1.68/0.99  fof(f29,plain,(
% 1.68/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.68/0.99    inference(cnf_transformation,[],[f15])).
% 1.68/0.99  
% 1.68/0.99  fof(f38,plain,(
% 1.68/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.68/0.99    inference(cnf_transformation,[],[f24])).
% 1.68/0.99  
% 1.68/0.99  fof(f6,axiom,(
% 1.68/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.99  
% 1.68/0.99  fof(f11,plain,(
% 1.68/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.68/0.99    inference(ennf_transformation,[],[f6])).
% 1.68/0.99  
% 1.68/0.99  fof(f12,plain,(
% 1.68/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.68/0.99    inference(flattening,[],[f11])).
% 1.68/0.99  
% 1.68/0.99  fof(f16,plain,(
% 1.68/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.68/0.99    inference(nnf_transformation,[],[f12])).
% 1.68/0.99  
% 1.68/0.99  fof(f17,plain,(
% 1.68/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.68/0.99    inference(rectify,[],[f16])).
% 1.68/0.99  
% 1.68/0.99  fof(f19,plain,(
% 1.68/0.99    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v4_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.68/0.99    introduced(choice_axiom,[])).
% 1.68/0.99  
% 1.68/0.99  fof(f18,plain,(
% 1.68/0.99    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.68/0.99    introduced(choice_axiom,[])).
% 1.68/0.99  
% 1.68/0.99  fof(f20,plain,(
% 1.68/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v4_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.68/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).
% 1.68/0.99  
% 1.68/0.99  fof(f33,plain,(
% 1.68/0.99    ( ! [X4,X0,X1] : (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.68/0.99    inference(cnf_transformation,[],[f20])).
% 1.68/0.99  
% 1.68/0.99  fof(f37,plain,(
% 1.68/0.99    l1_pre_topc(sK2)),
% 1.68/0.99    inference(cnf_transformation,[],[f24])).
% 1.68/0.99  
% 1.68/0.99  fof(f39,plain,(
% 1.68/0.99    v2_tex_2(sK3,sK2)),
% 1.68/0.99    inference(cnf_transformation,[],[f24])).
% 1.68/0.99  
% 1.68/0.99  fof(f3,axiom,(
% 1.68/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.68/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/0.99  
% 1.68/0.99  fof(f9,plain,(
% 1.68/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.68/0.99    inference(ennf_transformation,[],[f3])).
% 1.68/0.99  
% 1.68/0.99  fof(f27,plain,(
% 1.68/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.68/0.99    inference(cnf_transformation,[],[f9])).
% 1.68/0.99  
% 1.68/0.99  fof(f30,plain,(
% 1.68/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.68/0.99    inference(cnf_transformation,[],[f15])).
% 1.68/0.99  
% 1.68/0.99  fof(f42,plain,(
% 1.68/0.99    ( ! [X3] : (k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3) | ~v4_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.68/0.99    inference(cnf_transformation,[],[f24])).
% 1.68/0.99  
% 1.68/0.99  fof(f45,plain,(
% 1.68/0.99    ( ! [X3] : (k2_enumset1(sK4,sK4,sK4,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3) | ~v4_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.68/0.99    inference(definition_unfolding,[],[f42,f43])).
% 1.68/0.99  
% 1.68/0.99  fof(f32,plain,(
% 1.68/0.99    ( ! [X4,X0,X1] : (v4_pre_topc(sK1(X0,X1,X4),X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.68/0.99    inference(cnf_transformation,[],[f20])).
% 1.68/0.99  
% 1.68/0.99  fof(f31,plain,(
% 1.68/0.99    ( ! [X4,X0,X1] : (m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.68/0.99    inference(cnf_transformation,[],[f20])).
% 1.68/0.99  
% 1.68/0.99  cnf(c_11,negated_conjecture,
% 1.68/0.99      ( r2_hidden(sK4,sK3) ),
% 1.68/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2028,plain,
% 1.68/0.99      ( r2_hidden(sK4,sK3) = iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_1,plain,
% 1.68/0.99      ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1))
% 1.68/0.99      | ~ r2_hidden(X0,X1) ),
% 1.68/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2032,plain,
% 1.68/0.99      ( m1_subset_1(k2_enumset1(X0,X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 1.68/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_3,plain,
% 1.68/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.68/0.99      inference(cnf_transformation,[],[f29]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2030,plain,
% 1.68/0.99      ( r1_tarski(X0,X1) = iProver_top
% 1.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2432,plain,
% 1.68/0.99      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top
% 1.68/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 1.68/0.99      inference(superposition,[status(thm)],[c_2032,c_2030]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_14,negated_conjecture,
% 1.68/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.68/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2025,plain,
% 1.68/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_7,plain,
% 1.68/0.99      ( ~ v2_tex_2(X0,X1)
% 1.68/0.99      | ~ r1_tarski(X2,X0)
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ l1_pre_topc(X1)
% 1.68/0.99      | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2 ),
% 1.68/0.99      inference(cnf_transformation,[],[f33]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_15,negated_conjecture,
% 1.68/0.99      ( l1_pre_topc(sK2) ),
% 1.68/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_318,plain,
% 1.68/0.99      ( ~ v2_tex_2(X0,X1)
% 1.68/0.99      | ~ r1_tarski(X2,X0)
% 1.68/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2
% 1.68/0.99      | sK2 != X1 ),
% 1.68/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_15]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_319,plain,
% 1.68/0.99      ( ~ v2_tex_2(X0,sK2)
% 1.68/0.99      | ~ r1_tarski(X1,X0)
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.99      | k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,X1)) = X1 ),
% 1.68/0.99      inference(unflattening,[status(thm)],[c_318]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2022,plain,
% 1.68/0.99      ( k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,X1)) = X1
% 1.68/0.99      | v2_tex_2(X0,sK2) != iProver_top
% 1.68/0.99      | r1_tarski(X1,X0) != iProver_top
% 1.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.68/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_319]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2282,plain,
% 1.68/0.99      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0)) = X0
% 1.68/0.99      | v2_tex_2(sK3,sK2) != iProver_top
% 1.68/0.99      | r1_tarski(X0,sK3) != iProver_top
% 1.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.68/0.99      inference(superposition,[status(thm)],[c_2025,c_2022]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_13,negated_conjecture,
% 1.68/0.99      ( v2_tex_2(sK3,sK2) ),
% 1.68/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_789,plain,
% 1.68/0.99      ( ~ r1_tarski(X0,X1)
% 1.68/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.99      | k9_subset_1(u1_struct_0(sK2),X1,sK1(sK2,X1,X0)) = X0
% 1.68/0.99      | sK3 != X1
% 1.68/0.99      | sK2 != sK2 ),
% 1.68/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_319]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_790,plain,
% 1.68/0.99      ( ~ r1_tarski(X0,sK3)
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.99      | k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0)) = X0 ),
% 1.68/0.99      inference(unflattening,[status(thm)],[c_789]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_794,plain,
% 1.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.99      | ~ r1_tarski(X0,sK3)
% 1.68/0.99      | k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0)) = X0 ),
% 1.68/0.99      inference(global_propositional_subsumption,
% 1.68/0.99                [status(thm)],
% 1.68/0.99                [c_790,c_14]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_795,plain,
% 1.68/0.99      ( ~ r1_tarski(X0,sK3)
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.99      | k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0)) = X0 ),
% 1.68/0.99      inference(renaming,[status(thm)],[c_794]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_796,plain,
% 1.68/0.99      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0)) = X0
% 1.68/0.99      | r1_tarski(X0,sK3) != iProver_top
% 1.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_795]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2525,plain,
% 1.68/0.99      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,X0)) = X0
% 1.68/0.99      | r1_tarski(X0,sK3) != iProver_top
% 1.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.68/0.99      inference(global_propositional_subsumption,
% 1.68/0.99                [status(thm)],
% 1.68/0.99                [c_2282,c_796]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2533,plain,
% 1.68/0.99      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X0)
% 1.68/0.99      | r1_tarski(k2_enumset1(X0,X0,X0,X0),sK3) != iProver_top
% 1.68/0.99      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
% 1.68/0.99      inference(superposition,[status(thm)],[c_2032,c_2525]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_3153,plain,
% 1.68/0.99      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X0)
% 1.68/0.99      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
% 1.68/0.99      | r2_hidden(X0,sK3) != iProver_top ),
% 1.68/0.99      inference(superposition,[status(thm)],[c_2432,c_2533]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2347,plain,
% 1.68/0.99      ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
% 1.68/0.99      inference(superposition,[status(thm)],[c_2025,c_2030]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_0,plain,
% 1.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.68/0.99      | ~ r2_hidden(X2,X0)
% 1.68/0.99      | r2_hidden(X2,X1) ),
% 1.68/0.99      inference(cnf_transformation,[],[f27]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2,plain,
% 1.68/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.68/0.99      inference(cnf_transformation,[],[f30]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_121,plain,
% 1.68/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.68/0.99      inference(prop_impl,[status(thm)],[c_2]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_158,plain,
% 1.68/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 1.68/0.99      inference(bin_hyper_res,[status(thm)],[c_0,c_121]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2024,plain,
% 1.68/0.99      ( r1_tarski(X0,X1) != iProver_top
% 1.68/0.99      | r2_hidden(X2,X0) != iProver_top
% 1.68/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_158]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_3084,plain,
% 1.68/0.99      ( r2_hidden(X0,u1_struct_0(sK2)) = iProver_top
% 1.68/0.99      | r2_hidden(X0,sK3) != iProver_top ),
% 1.68/0.99      inference(superposition,[status(thm)],[c_2347,c_2024]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_3951,plain,
% 1.68/0.99      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X0)
% 1.68/0.99      | r2_hidden(X0,sK3) != iProver_top ),
% 1.68/0.99      inference(global_propositional_subsumption,
% 1.68/0.99                [status(thm)],
% 1.68/0.99                [c_3153,c_3084]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_3959,plain,
% 1.68/0.99      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k2_enumset1(sK4,sK4,sK4,sK4))) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 1.68/0.99      inference(superposition,[status(thm)],[c_2028,c_3951]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_10,negated_conjecture,
% 1.68/0.99      ( ~ v4_pre_topc(X0,sK2)
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.99      | k2_enumset1(sK4,sK4,sK4,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X0) ),
% 1.68/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2029,plain,
% 1.68/0.99      ( k2_enumset1(sK4,sK4,sK4,sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X0)
% 1.68/0.99      | v4_pre_topc(X0,sK2) != iProver_top
% 1.68/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_4016,plain,
% 1.68/0.99      ( v4_pre_topc(sK1(sK2,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK2) != iProver_top
% 1.68/0.99      | m1_subset_1(sK1(sK2,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.68/0.99      inference(superposition,[status(thm)],[c_3959,c_2029]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2332,plain,
% 1.68/0.99      ( m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.99      | ~ r2_hidden(sK4,u1_struct_0(sK2)) ),
% 1.68/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2333,plain,
% 1.68/0.99      ( m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.68/0.99      | r2_hidden(sK4,u1_struct_0(sK2)) != iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_2332]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2198,plain,
% 1.68/0.99      ( ~ r1_tarski(sK3,u1_struct_0(sK2))
% 1.68/0.99      | r2_hidden(X0,u1_struct_0(sK2))
% 1.68/0.99      | ~ r2_hidden(X0,sK3) ),
% 1.68/0.99      inference(instantiation,[status(thm)],[c_158]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2297,plain,
% 1.68/0.99      ( ~ r1_tarski(sK3,u1_struct_0(sK2))
% 1.68/0.99      | r2_hidden(sK4,u1_struct_0(sK2))
% 1.68/0.99      | ~ r2_hidden(sK4,sK3) ),
% 1.68/0.99      inference(instantiation,[status(thm)],[c_2198]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2298,plain,
% 1.68/0.99      ( r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top
% 1.68/0.99      | r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
% 1.68/0.99      | r2_hidden(sK4,sK3) != iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_2297]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_8,plain,
% 1.68/0.99      ( v4_pre_topc(sK1(X0,X1,X2),X0)
% 1.68/0.99      | ~ v2_tex_2(X1,X0)
% 1.68/0.99      | ~ r1_tarski(X2,X1)
% 1.68/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.68/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.68/0.99      | ~ l1_pre_topc(X0) ),
% 1.68/0.99      inference(cnf_transformation,[],[f32]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_390,plain,
% 1.68/0.99      ( v4_pre_topc(sK1(X0,X1,X2),X0)
% 1.68/0.99      | ~ v2_tex_2(X1,X0)
% 1.68/0.99      | ~ r1_tarski(X2,X1)
% 1.68/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.68/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.68/0.99      | sK2 != X0 ),
% 1.68/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_15]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_391,plain,
% 1.68/0.99      ( v4_pre_topc(sK1(sK2,X0,X1),sK2)
% 1.68/0.99      | ~ v2_tex_2(X0,sK2)
% 1.68/0.99      | ~ r1_tarski(X1,X0)
% 1.68/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.68/0.99      inference(unflattening,[status(thm)],[c_390]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2157,plain,
% 1.68/0.99      ( v4_pre_topc(sK1(sK2,sK3,X0),sK2)
% 1.68/0.99      | ~ v2_tex_2(sK3,sK2)
% 1.68/0.99      | ~ r1_tarski(X0,sK3)
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.68/0.99      inference(instantiation,[status(thm)],[c_391]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2262,plain,
% 1.68/0.99      ( v4_pre_topc(sK1(sK2,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK2)
% 1.68/0.99      | ~ v2_tex_2(sK3,sK2)
% 1.68/0.99      | ~ r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
% 1.68/0.99      | ~ m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.68/0.99      inference(instantiation,[status(thm)],[c_2157]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2266,plain,
% 1.68/0.99      ( v4_pre_topc(sK1(sK2,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),sK2) = iProver_top
% 1.68/0.99      | v2_tex_2(sK3,sK2) != iProver_top
% 1.68/0.99      | r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3) != iProver_top
% 1.68/0.99      | m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.68/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_2262]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_9,plain,
% 1.68/0.99      ( ~ v2_tex_2(X0,X1)
% 1.68/0.99      | ~ r1_tarski(X2,X0)
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ l1_pre_topc(X1) ),
% 1.68/0.99      inference(cnf_transformation,[],[f31]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_297,plain,
% 1.68/0.99      ( ~ v2_tex_2(X0,X1)
% 1.68/0.99      | ~ r1_tarski(X2,X0)
% 1.68/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 1.68/0.99      | sK2 != X1 ),
% 1.68/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_15]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_298,plain,
% 1.68/0.99      ( ~ v2_tex_2(X0,sK2)
% 1.68/0.99      | ~ r1_tarski(X1,X0)
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.99      | m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.68/0.99      inference(unflattening,[status(thm)],[c_297]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2154,plain,
% 1.68/0.99      ( ~ v2_tex_2(sK3,sK2)
% 1.68/0.99      | ~ r1_tarski(X0,sK3)
% 1.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.99      | m1_subset_1(sK1(sK2,sK3,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.68/0.99      inference(instantiation,[status(thm)],[c_298]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2263,plain,
% 1.68/0.99      ( ~ v2_tex_2(sK3,sK2)
% 1.68/0.99      | ~ r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
% 1.68/0.99      | ~ m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.99      | m1_subset_1(sK1(sK2,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.68/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.68/0.99      inference(instantiation,[status(thm)],[c_2154]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2264,plain,
% 1.68/0.99      ( v2_tex_2(sK3,sK2) != iProver_top
% 1.68/0.99      | r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3) != iProver_top
% 1.68/0.99      | m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.68/0.99      | m1_subset_1(sK1(sK2,sK3,k2_enumset1(sK4,sK4,sK4,sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.68/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_2263]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2218,plain,
% 1.68/0.99      ( r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3)
% 1.68/0.99      | ~ m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(sK3)) ),
% 1.68/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2219,plain,
% 1.68/0.99      ( r1_tarski(k2_enumset1(sK4,sK4,sK4,sK4),sK3) = iProver_top
% 1.68/0.99      | m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(sK3)) != iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_2218]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2174,plain,
% 1.68/0.99      ( m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(sK3))
% 1.68/0.99      | ~ r2_hidden(sK4,sK3) ),
% 1.68/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2175,plain,
% 1.68/0.99      ( m1_subset_1(k2_enumset1(sK4,sK4,sK4,sK4),k1_zfmisc_1(sK3)) = iProver_top
% 1.68/0.99      | r2_hidden(sK4,sK3) != iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_2174]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2167,plain,
% 1.68/0.99      ( r1_tarski(sK3,u1_struct_0(sK2))
% 1.68/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.68/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_2168,plain,
% 1.68/0.99      ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top
% 1.68/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_2167]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_20,plain,
% 1.68/0.99      ( r2_hidden(sK4,sK3) = iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_18,plain,
% 1.68/0.99      ( v2_tex_2(sK3,sK2) = iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(c_17,plain,
% 1.68/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.68/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.68/0.99  
% 1.68/0.99  cnf(contradiction,plain,
% 1.68/0.99      ( $false ),
% 1.68/0.99      inference(minisat,
% 1.68/0.99                [status(thm)],
% 1.68/0.99                [c_4016,c_2333,c_2298,c_2266,c_2264,c_2219,c_2175,c_2168,
% 1.68/0.99                 c_20,c_18,c_17]) ).
% 1.68/0.99  
% 1.68/0.99  
% 1.68/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.68/0.99  
% 1.68/0.99  ------                               Statistics
% 1.68/0.99  
% 1.68/0.99  ------ General
% 1.68/0.99  
% 1.68/0.99  abstr_ref_over_cycles:                  0
% 1.68/0.99  abstr_ref_under_cycles:                 0
% 1.68/0.99  gc_basic_clause_elim:                   0
% 1.68/0.99  forced_gc_time:                         0
% 1.68/0.99  parsing_time:                           0.008
% 1.68/0.99  unif_index_cands_time:                  0.
% 1.68/0.99  unif_index_add_time:                    0.
% 1.68/0.99  orderings_time:                         0.
% 1.68/0.99  out_proof_time:                         0.007
% 1.68/0.99  total_time:                             0.136
% 1.68/0.99  num_of_symbols:                         46
% 1.68/0.99  num_of_terms:                           2248
% 1.68/0.99  
% 1.68/0.99  ------ Preprocessing
% 1.68/0.99  
% 1.68/0.99  num_of_splits:                          0
% 1.68/0.99  num_of_split_atoms:                     0
% 1.68/0.99  num_of_reused_defs:                     0
% 1.68/0.99  num_eq_ax_congr_red:                    14
% 1.68/0.99  num_of_sem_filtered_clauses:            1
% 1.68/0.99  num_of_subtypes:                        0
% 1.68/0.99  monotx_restored_types:                  0
% 1.68/0.99  sat_num_of_epr_types:                   0
% 1.68/0.99  sat_num_of_non_cyclic_types:            0
% 1.68/0.99  sat_guarded_non_collapsed_types:        0
% 1.68/0.99  num_pure_diseq_elim:                    0
% 1.68/0.99  simp_replaced_by:                       0
% 1.68/0.99  res_preprocessed:                       88
% 1.68/0.99  prep_upred:                             0
% 1.68/0.99  prep_unflattend:                        58
% 1.68/0.99  smt_new_axioms:                         0
% 1.68/0.99  pred_elim_cands:                        5
% 1.68/0.99  pred_elim:                              1
% 1.68/0.99  pred_elim_cl:                           1
% 1.68/0.99  pred_elim_cycles:                       8
% 1.68/0.99  merged_defs:                            8
% 1.68/0.99  merged_defs_ncl:                        0
% 1.68/0.99  bin_hyper_res:                          9
% 1.68/0.99  prep_cycles:                            4
% 1.68/0.99  pred_elim_time:                         0.025
% 1.68/0.99  splitting_time:                         0.
% 1.68/0.99  sem_filter_time:                        0.
% 1.68/0.99  monotx_time:                            0.001
% 1.68/0.99  subtype_inf_time:                       0.
% 1.68/0.99  
% 1.68/0.99  ------ Problem properties
% 1.68/0.99  
% 1.68/0.99  clauses:                                15
% 1.68/0.99  conjectures:                            5
% 1.68/0.99  epr:                                    3
% 1.68/0.99  horn:                                   13
% 1.68/0.99  ground:                                 4
% 1.68/0.99  unary:                                  4
% 1.68/0.99  binary:                                 3
% 1.68/0.99  lits:                                   42
% 1.68/0.99  lits_eq:                                3
% 1.68/0.99  fd_pure:                                0
% 1.68/0.99  fd_pseudo:                              0
% 1.68/0.99  fd_cond:                                0
% 1.68/0.99  fd_pseudo_cond:                         0
% 1.68/0.99  ac_symbols:                             0
% 1.68/0.99  
% 1.68/0.99  ------ Propositional Solver
% 1.68/0.99  
% 1.68/0.99  prop_solver_calls:                      28
% 1.68/0.99  prop_fast_solver_calls:                 981
% 1.68/0.99  smt_solver_calls:                       0
% 1.68/0.99  smt_fast_solver_calls:                  0
% 1.68/0.99  prop_num_of_clauses:                    932
% 1.68/0.99  prop_preprocess_simplified:             3582
% 1.68/0.99  prop_fo_subsumed:                       12
% 1.68/0.99  prop_solver_time:                       0.
% 1.68/0.99  smt_solver_time:                        0.
% 1.68/0.99  smt_fast_solver_time:                   0.
% 1.68/0.99  prop_fast_solver_time:                  0.
% 1.68/0.99  prop_unsat_core_time:                   0.
% 1.68/0.99  
% 1.68/0.99  ------ QBF
% 1.68/0.99  
% 1.68/0.99  qbf_q_res:                              0
% 1.68/0.99  qbf_num_tautologies:                    0
% 1.68/0.99  qbf_prep_cycles:                        0
% 1.68/0.99  
% 1.68/0.99  ------ BMC1
% 1.68/0.99  
% 1.68/0.99  bmc1_current_bound:                     -1
% 1.68/0.99  bmc1_last_solved_bound:                 -1
% 1.68/0.99  bmc1_unsat_core_size:                   -1
% 1.68/0.99  bmc1_unsat_core_parents_size:           -1
% 1.68/0.99  bmc1_merge_next_fun:                    0
% 1.68/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.68/0.99  
% 1.68/0.99  ------ Instantiation
% 1.68/0.99  
% 1.68/0.99  inst_num_of_clauses:                    264
% 1.68/0.99  inst_num_in_passive:                    22
% 1.68/0.99  inst_num_in_active:                     220
% 1.68/0.99  inst_num_in_unprocessed:                22
% 1.68/0.99  inst_num_of_loops:                      240
% 1.68/0.99  inst_num_of_learning_restarts:          0
% 1.68/0.99  inst_num_moves_active_passive:          15
% 1.68/0.99  inst_lit_activity:                      0
% 1.68/0.99  inst_lit_activity_moves:                0
% 1.68/0.99  inst_num_tautologies:                   0
% 1.68/0.99  inst_num_prop_implied:                  0
% 1.68/0.99  inst_num_existing_simplified:           0
% 1.68/0.99  inst_num_eq_res_simplified:             0
% 1.68/0.99  inst_num_child_elim:                    0
% 1.68/0.99  inst_num_of_dismatching_blockings:      31
% 1.68/0.99  inst_num_of_non_proper_insts:           236
% 1.68/0.99  inst_num_of_duplicates:                 0
% 1.68/0.99  inst_inst_num_from_inst_to_res:         0
% 1.68/0.99  inst_dismatching_checking_time:         0.
% 1.68/0.99  
% 1.68/0.99  ------ Resolution
% 1.68/0.99  
% 1.68/0.99  res_num_of_clauses:                     0
% 1.68/0.99  res_num_in_passive:                     0
% 1.68/0.99  res_num_in_active:                      0
% 1.68/0.99  res_num_of_loops:                       92
% 1.68/0.99  res_forward_subset_subsumed:            37
% 1.68/0.99  res_backward_subset_subsumed:           0
% 1.68/0.99  res_forward_subsumed:                   0
% 1.68/0.99  res_backward_subsumed:                  0
% 1.68/0.99  res_forward_subsumption_resolution:     2
% 1.68/0.99  res_backward_subsumption_resolution:    0
% 1.68/0.99  res_clause_to_clause_subsumption:       493
% 1.68/0.99  res_orphan_elimination:                 0
% 1.68/0.99  res_tautology_del:                      68
% 1.68/0.99  res_num_eq_res_simplified:              0
% 1.68/0.99  res_num_sel_changes:                    0
% 1.68/0.99  res_moves_from_active_to_pass:          0
% 1.68/0.99  
% 1.68/0.99  ------ Superposition
% 1.68/0.99  
% 1.68/0.99  sup_time_total:                         0.
% 1.68/0.99  sup_time_generating:                    0.
% 1.68/0.99  sup_time_sim_full:                      0.
% 1.68/0.99  sup_time_sim_immed:                     0.
% 1.68/0.99  
% 1.68/0.99  sup_num_of_clauses:                     61
% 1.68/0.99  sup_num_in_active:                      47
% 1.68/0.99  sup_num_in_passive:                     14
% 1.68/0.99  sup_num_of_loops:                       46
% 1.68/0.99  sup_fw_superposition:                   28
% 1.68/0.99  sup_bw_superposition:                   32
% 1.68/0.99  sup_immediate_simplified:               4
% 1.68/0.99  sup_given_eliminated:                   0
% 1.68/0.99  comparisons_done:                       0
% 1.68/0.99  comparisons_avoided:                    0
% 1.68/0.99  
% 1.68/0.99  ------ Simplifications
% 1.68/0.99  
% 1.68/0.99  
% 1.68/0.99  sim_fw_subset_subsumed:                 3
% 1.68/0.99  sim_bw_subset_subsumed:                 0
% 1.68/0.99  sim_fw_subsumed:                        2
% 1.68/0.99  sim_bw_subsumed:                        0
% 1.68/0.99  sim_fw_subsumption_res:                 0
% 1.68/0.99  sim_bw_subsumption_res:                 0
% 1.68/0.99  sim_tautology_del:                      5
% 1.68/0.99  sim_eq_tautology_del:                   0
% 1.68/0.99  sim_eq_res_simp:                        0
% 1.68/0.99  sim_fw_demodulated:                     0
% 1.68/0.99  sim_bw_demodulated:                     0
% 1.68/0.99  sim_light_normalised:                   0
% 1.68/0.99  sim_joinable_taut:                      0
% 1.68/0.99  sim_joinable_simp:                      0
% 1.68/0.99  sim_ac_normalised:                      0
% 1.68/0.99  sim_smt_subsumption:                    0
% 1.68/0.99  
%------------------------------------------------------------------------------
