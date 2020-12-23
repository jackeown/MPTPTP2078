%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:58 EST 2020

% Result     : Theorem 1.24s
% Output     : CNFRefutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 212 expanded)
%              Number of clauses        :   60 (  74 expanded)
%              Number of leaves         :   10 (  56 expanded)
%              Depth                    :   20
%              Number of atoms          :  419 (1363 expanded)
%              Number of equality atoms :  103 ( 229 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f21,plain,(
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

fof(f20,plain,(
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

fof(f19,plain,
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

fof(f22,plain,
    ( ! [X3] :
        ( k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3)
        | ~ v3_pre_topc(X3,sK2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
    & r2_hidden(sK4,sK3)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f21,f20,f19])).

fof(f37,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f17,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
        & v3_pre_topc(sK1(X0,X1,X4),X0)
        & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17,f16])).

fof(f29,plain,(
    ! [X4,X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    ! [X3] :
      ( k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3)
      | ~ v3_pre_topc(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f27,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    ! [X4,X0,X1] :
      ( v3_pre_topc(sK1(X0,X1,X4),X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_11,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1486,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1760,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1486])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1483,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1763,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1483])).

cnf(c_3,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1488,plain,
    ( m1_subset_1(k1_tarski(X0_43),k1_zfmisc_1(X1_43))
    | ~ r2_hidden(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1758,plain,
    ( m1_subset_1(k1_tarski(X0_43),k1_zfmisc_1(X1_43)) = iProver_top
    | r2_hidden(X0_43,X1_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1488])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_121,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_7,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_338,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_339,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_508,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X2,X3)
    | X0 != X3
    | k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,X1)) = X1
    | k1_tarski(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_121,c_339])).

cnf(c_509,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,k1_tarski(X1))) = k1_tarski(X1) ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_1480,plain,
    ( ~ v2_tex_2(X0_43,sK2)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_tarski(X1_43),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1_43,X0_43)
    | k9_subset_1(u1_struct_0(sK2),X0_43,sK1(sK2,X0_43,k1_tarski(X1_43))) = k1_tarski(X1_43) ),
    inference(subtyping,[status(esa)],[c_509])).

cnf(c_1766,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0_43,sK1(sK2,X0_43,k1_tarski(X1_43))) = k1_tarski(X1_43)
    | v2_tex_2(X0_43,sK2) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k1_tarski(X1_43),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1_43,X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1480])).

cnf(c_2328,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0_43,sK1(sK2,X0_43,k1_tarski(X1_43))) = k1_tarski(X1_43)
    | v2_tex_2(X0_43,sK2) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1_43,X0_43) != iProver_top
    | r2_hidden(X1_43,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1758,c_1766])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1489,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | ~ r2_hidden(X2_43,X0_43)
    | r2_hidden(X2_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1757,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
    | r2_hidden(X2_43,X0_43) != iProver_top
    | r2_hidden(X2_43,X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1489])).

cnf(c_2407,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0_43,sK1(sK2,X0_43,k1_tarski(X1_43))) = k1_tarski(X1_43)
    | v2_tex_2(X0_43,sK2) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1_43,X0_43) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2328,c_1757])).

cnf(c_2411,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k1_tarski(X0_43))) = k1_tarski(X0_43)
    | v2_tex_2(sK3,sK2) != iProver_top
    | r2_hidden(X0_43,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1763,c_2407])).

cnf(c_13,negated_conjecture,
    ( v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_18,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2521,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k1_tarski(X0_43))) = k1_tarski(X0_43)
    | r2_hidden(X0_43,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2411,c_18])).

cnf(c_2529,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k1_tarski(sK4))) = k1_tarski(sK4) ),
    inference(superposition,[status(thm)],[c_1760,c_2521])).

cnf(c_10,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1487,negated_conjecture,
    ( ~ v3_pre_topc(X0_43,sK2)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X0_43) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1759,plain,
    ( k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X0_43)
    | v3_pre_topc(X0_43,sK2) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1487])).

cnf(c_2531,plain,
    ( v3_pre_topc(sK1(sK2,sK3,k1_tarski(sK4)),sK2) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2529,c_1759])).

cnf(c_1885,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0_43))
    | r2_hidden(sK4,X0_43)
    | ~ r2_hidden(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_2051,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK4,u1_struct_0(sK2))
    | ~ r2_hidden(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1885])).

cnf(c_2052,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2051])).

cnf(c_9,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_317,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_15])).

cnf(c_318,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_529,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X2,X3)
    | X0 != X3
    | k1_tarski(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_121,c_318])).

cnf(c_530,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0,k1_tarski(X1)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0) ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_1479,plain,
    ( ~ v2_tex_2(X0_43,sK2)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0_43,k1_tarski(X1_43)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_tarski(X1_43),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_530])).

cnf(c_1962,plain,
    ( ~ v2_tex_2(X0_43,sK2)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0_43,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK4,X0_43) ),
    inference(instantiation,[status(thm)],[c_1479])).

cnf(c_1970,plain,
    ( v2_tex_2(X0_43,sK2) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK1(sK2,X0_43,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK4,X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1962])).

cnf(c_1972,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1970])).

cnf(c_8,plain,
    ( v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X2,X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_296,plain,
    ( v3_pre_topc(sK1(X0,X1,X2),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(X2,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_15])).

cnf(c_297,plain,
    ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
    | ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_550,plain,
    ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
    | ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X2,X3)
    | X0 != X3
    | k1_tarski(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_121,c_297])).

cnf(c_551,plain,
    ( v3_pre_topc(sK1(sK2,X0,k1_tarski(X1)),sK2)
    | ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0) ),
    inference(unflattening,[status(thm)],[c_550])).

cnf(c_1478,plain,
    ( v3_pre_topc(sK1(sK2,X0_43,k1_tarski(X1_43)),sK2)
    | ~ v2_tex_2(X0_43,sK2)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_tarski(X1_43),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_551])).

cnf(c_1963,plain,
    ( v3_pre_topc(sK1(sK2,X0_43,k1_tarski(sK4)),sK2)
    | ~ v2_tex_2(X0_43,sK2)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK4,X0_43) ),
    inference(instantiation,[status(thm)],[c_1478])).

cnf(c_1966,plain,
    ( v3_pre_topc(sK1(sK2,X0_43,k1_tarski(sK4)),sK2) = iProver_top
    | v2_tex_2(X0_43,sK2) != iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK4,X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1963])).

cnf(c_1968,plain,
    ( v3_pre_topc(sK1(sK2,sK3,k1_tarski(sK4)),sK2) = iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1966])).

cnf(c_1913,plain,
    ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(X0_43))
    | ~ r2_hidden(sK4,X0_43) ),
    inference(instantiation,[status(thm)],[c_1488])).

cnf(c_1960,plain,
    ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1913])).

cnf(c_1964,plain,
    ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r2_hidden(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1960])).

cnf(c_20,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_17,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2531,c_2052,c_1972,c_1968,c_1964,c_20,c_18,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:23:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.24/0.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.24/0.95  
% 1.24/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.24/0.95  
% 1.24/0.95  ------  iProver source info
% 1.24/0.95  
% 1.24/0.95  git: date: 2020-06-30 10:37:57 +0100
% 1.24/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.24/0.95  git: non_committed_changes: false
% 1.24/0.95  git: last_make_outside_of_git: false
% 1.24/0.95  
% 1.24/0.95  ------ 
% 1.24/0.95  
% 1.24/0.95  ------ Input Options
% 1.24/0.95  
% 1.24/0.95  --out_options                           all
% 1.24/0.95  --tptp_safe_out                         true
% 1.24/0.95  --problem_path                          ""
% 1.24/0.95  --include_path                          ""
% 1.24/0.95  --clausifier                            res/vclausify_rel
% 1.24/0.95  --clausifier_options                    --mode clausify
% 1.24/0.95  --stdin                                 false
% 1.24/0.95  --stats_out                             all
% 1.24/0.95  
% 1.24/0.95  ------ General Options
% 1.24/0.95  
% 1.24/0.95  --fof                                   false
% 1.24/0.95  --time_out_real                         305.
% 1.24/0.95  --time_out_virtual                      -1.
% 1.24/0.95  --symbol_type_check                     false
% 1.24/0.95  --clausify_out                          false
% 1.24/0.95  --sig_cnt_out                           false
% 1.24/0.95  --trig_cnt_out                          false
% 1.24/0.95  --trig_cnt_out_tolerance                1.
% 1.24/0.95  --trig_cnt_out_sk_spl                   false
% 1.24/0.95  --abstr_cl_out                          false
% 1.24/0.95  
% 1.24/0.95  ------ Global Options
% 1.24/0.95  
% 1.24/0.95  --schedule                              default
% 1.24/0.95  --add_important_lit                     false
% 1.24/0.95  --prop_solver_per_cl                    1000
% 1.24/0.95  --min_unsat_core                        false
% 1.24/0.95  --soft_assumptions                      false
% 1.24/0.95  --soft_lemma_size                       3
% 1.24/0.95  --prop_impl_unit_size                   0
% 1.24/0.95  --prop_impl_unit                        []
% 1.24/0.95  --share_sel_clauses                     true
% 1.24/0.95  --reset_solvers                         false
% 1.24/0.95  --bc_imp_inh                            [conj_cone]
% 1.24/0.95  --conj_cone_tolerance                   3.
% 1.24/0.95  --extra_neg_conj                        none
% 1.24/0.95  --large_theory_mode                     true
% 1.24/0.95  --prolific_symb_bound                   200
% 1.24/0.95  --lt_threshold                          2000
% 1.24/0.95  --clause_weak_htbl                      true
% 1.24/0.95  --gc_record_bc_elim                     false
% 1.24/0.95  
% 1.24/0.95  ------ Preprocessing Options
% 1.24/0.95  
% 1.24/0.95  --preprocessing_flag                    true
% 1.24/0.95  --time_out_prep_mult                    0.1
% 1.24/0.95  --splitting_mode                        input
% 1.24/0.95  --splitting_grd                         true
% 1.24/0.95  --splitting_cvd                         false
% 1.24/0.95  --splitting_cvd_svl                     false
% 1.24/0.95  --splitting_nvd                         32
% 1.24/0.95  --sub_typing                            true
% 1.24/0.95  --prep_gs_sim                           true
% 1.24/0.95  --prep_unflatten                        true
% 1.24/0.95  --prep_res_sim                          true
% 1.24/0.95  --prep_upred                            true
% 1.24/0.95  --prep_sem_filter                       exhaustive
% 1.24/0.95  --prep_sem_filter_out                   false
% 1.24/0.95  --pred_elim                             true
% 1.24/0.95  --res_sim_input                         true
% 1.24/0.95  --eq_ax_congr_red                       true
% 1.24/0.95  --pure_diseq_elim                       true
% 1.24/0.95  --brand_transform                       false
% 1.24/0.95  --non_eq_to_eq                          false
% 1.24/0.95  --prep_def_merge                        true
% 1.24/0.95  --prep_def_merge_prop_impl              false
% 1.24/0.95  --prep_def_merge_mbd                    true
% 1.24/0.95  --prep_def_merge_tr_red                 false
% 1.24/0.95  --prep_def_merge_tr_cl                  false
% 1.24/0.95  --smt_preprocessing                     true
% 1.24/0.95  --smt_ac_axioms                         fast
% 1.24/0.95  --preprocessed_out                      false
% 1.24/0.95  --preprocessed_stats                    false
% 1.24/0.95  
% 1.24/0.95  ------ Abstraction refinement Options
% 1.24/0.95  
% 1.24/0.95  --abstr_ref                             []
% 1.24/0.95  --abstr_ref_prep                        false
% 1.24/0.95  --abstr_ref_until_sat                   false
% 1.24/0.95  --abstr_ref_sig_restrict                funpre
% 1.24/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 1.24/0.95  --abstr_ref_under                       []
% 1.24/0.95  
% 1.24/0.95  ------ SAT Options
% 1.24/0.95  
% 1.24/0.95  --sat_mode                              false
% 1.24/0.95  --sat_fm_restart_options                ""
% 1.24/0.95  --sat_gr_def                            false
% 1.24/0.95  --sat_epr_types                         true
% 1.24/0.95  --sat_non_cyclic_types                  false
% 1.24/0.95  --sat_finite_models                     false
% 1.24/0.95  --sat_fm_lemmas                         false
% 1.24/0.95  --sat_fm_prep                           false
% 1.24/0.95  --sat_fm_uc_incr                        true
% 1.24/0.95  --sat_out_model                         small
% 1.24/0.95  --sat_out_clauses                       false
% 1.24/0.95  
% 1.24/0.95  ------ QBF Options
% 1.24/0.95  
% 1.24/0.95  --qbf_mode                              false
% 1.24/0.95  --qbf_elim_univ                         false
% 1.24/0.95  --qbf_dom_inst                          none
% 1.24/0.95  --qbf_dom_pre_inst                      false
% 1.24/0.95  --qbf_sk_in                             false
% 1.24/0.95  --qbf_pred_elim                         true
% 1.24/0.95  --qbf_split                             512
% 1.24/0.95  
% 1.24/0.95  ------ BMC1 Options
% 1.24/0.95  
% 1.24/0.95  --bmc1_incremental                      false
% 1.24/0.95  --bmc1_axioms                           reachable_all
% 1.24/0.95  --bmc1_min_bound                        0
% 1.24/0.95  --bmc1_max_bound                        -1
% 1.24/0.95  --bmc1_max_bound_default                -1
% 1.24/0.95  --bmc1_symbol_reachability              true
% 1.24/0.95  --bmc1_property_lemmas                  false
% 1.24/0.95  --bmc1_k_induction                      false
% 1.24/0.95  --bmc1_non_equiv_states                 false
% 1.24/0.95  --bmc1_deadlock                         false
% 1.24/0.95  --bmc1_ucm                              false
% 1.24/0.95  --bmc1_add_unsat_core                   none
% 1.24/0.95  --bmc1_unsat_core_children              false
% 1.24/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 1.24/0.95  --bmc1_out_stat                         full
% 1.24/0.95  --bmc1_ground_init                      false
% 1.24/0.95  --bmc1_pre_inst_next_state              false
% 1.24/0.95  --bmc1_pre_inst_state                   false
% 1.24/0.95  --bmc1_pre_inst_reach_state             false
% 1.24/0.95  --bmc1_out_unsat_core                   false
% 1.24/0.95  --bmc1_aig_witness_out                  false
% 1.24/0.95  --bmc1_verbose                          false
% 1.24/0.95  --bmc1_dump_clauses_tptp                false
% 1.24/0.95  --bmc1_dump_unsat_core_tptp             false
% 1.24/0.95  --bmc1_dump_file                        -
% 1.24/0.95  --bmc1_ucm_expand_uc_limit              128
% 1.24/0.95  --bmc1_ucm_n_expand_iterations          6
% 1.24/0.95  --bmc1_ucm_extend_mode                  1
% 1.24/0.95  --bmc1_ucm_init_mode                    2
% 1.24/0.95  --bmc1_ucm_cone_mode                    none
% 1.24/0.95  --bmc1_ucm_reduced_relation_type        0
% 1.24/0.95  --bmc1_ucm_relax_model                  4
% 1.24/0.95  --bmc1_ucm_full_tr_after_sat            true
% 1.24/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 1.24/0.95  --bmc1_ucm_layered_model                none
% 1.24/0.95  --bmc1_ucm_max_lemma_size               10
% 1.24/0.95  
% 1.24/0.95  ------ AIG Options
% 1.24/0.95  
% 1.24/0.95  --aig_mode                              false
% 1.24/0.95  
% 1.24/0.95  ------ Instantiation Options
% 1.24/0.95  
% 1.24/0.95  --instantiation_flag                    true
% 1.24/0.95  --inst_sos_flag                         false
% 1.24/0.95  --inst_sos_phase                        true
% 1.24/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.24/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.24/0.95  --inst_lit_sel_side                     num_symb
% 1.24/0.95  --inst_solver_per_active                1400
% 1.24/0.95  --inst_solver_calls_frac                1.
% 1.24/0.95  --inst_passive_queue_type               priority_queues
% 1.24/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.24/0.95  --inst_passive_queues_freq              [25;2]
% 1.24/0.95  --inst_dismatching                      true
% 1.24/0.95  --inst_eager_unprocessed_to_passive     true
% 1.24/0.95  --inst_prop_sim_given                   true
% 1.24/0.95  --inst_prop_sim_new                     false
% 1.24/0.95  --inst_subs_new                         false
% 1.24/0.95  --inst_eq_res_simp                      false
% 1.24/0.95  --inst_subs_given                       false
% 1.24/0.95  --inst_orphan_elimination               true
% 1.24/0.95  --inst_learning_loop_flag               true
% 1.24/0.95  --inst_learning_start                   3000
% 1.24/0.95  --inst_learning_factor                  2
% 1.24/0.95  --inst_start_prop_sim_after_learn       3
% 1.24/0.95  --inst_sel_renew                        solver
% 1.24/0.95  --inst_lit_activity_flag                true
% 1.24/0.95  --inst_restr_to_given                   false
% 1.24/0.95  --inst_activity_threshold               500
% 1.24/0.95  --inst_out_proof                        true
% 1.24/0.95  
% 1.24/0.95  ------ Resolution Options
% 1.24/0.95  
% 1.24/0.95  --resolution_flag                       true
% 1.24/0.95  --res_lit_sel                           adaptive
% 1.24/0.95  --res_lit_sel_side                      none
% 1.24/0.95  --res_ordering                          kbo
% 1.24/0.95  --res_to_prop_solver                    active
% 1.24/0.95  --res_prop_simpl_new                    false
% 1.24/0.95  --res_prop_simpl_given                  true
% 1.24/0.95  --res_passive_queue_type                priority_queues
% 1.24/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.24/0.95  --res_passive_queues_freq               [15;5]
% 1.24/0.95  --res_forward_subs                      full
% 1.24/0.95  --res_backward_subs                     full
% 1.24/0.95  --res_forward_subs_resolution           true
% 1.24/0.95  --res_backward_subs_resolution          true
% 1.24/0.95  --res_orphan_elimination                true
% 1.24/0.95  --res_time_limit                        2.
% 1.24/0.95  --res_out_proof                         true
% 1.24/0.95  
% 1.24/0.95  ------ Superposition Options
% 1.24/0.95  
% 1.24/0.95  --superposition_flag                    true
% 1.24/0.95  --sup_passive_queue_type                priority_queues
% 1.24/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.24/0.95  --sup_passive_queues_freq               [8;1;4]
% 1.24/0.95  --demod_completeness_check              fast
% 1.24/0.95  --demod_use_ground                      true
% 1.24/0.95  --sup_to_prop_solver                    passive
% 1.24/0.95  --sup_prop_simpl_new                    true
% 1.24/0.95  --sup_prop_simpl_given                  true
% 1.24/0.95  --sup_fun_splitting                     false
% 1.24/0.95  --sup_smt_interval                      50000
% 1.24/0.95  
% 1.24/0.95  ------ Superposition Simplification Setup
% 1.24/0.95  
% 1.24/0.95  --sup_indices_passive                   []
% 1.24/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.24/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.24/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.24/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 1.24/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.24/0.95  --sup_full_bw                           [BwDemod]
% 1.24/0.95  --sup_immed_triv                        [TrivRules]
% 1.24/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.24/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.24/0.95  --sup_immed_bw_main                     []
% 1.24/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.24/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 1.24/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.24/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.24/0.95  
% 1.24/0.95  ------ Combination Options
% 1.24/0.95  
% 1.24/0.95  --comb_res_mult                         3
% 1.24/0.95  --comb_sup_mult                         2
% 1.24/0.95  --comb_inst_mult                        10
% 1.24/0.95  
% 1.24/0.95  ------ Debug Options
% 1.24/0.95  
% 1.24/0.95  --dbg_backtrace                         false
% 1.24/0.95  --dbg_dump_prop_clauses                 false
% 1.24/0.95  --dbg_dump_prop_clauses_file            -
% 1.24/0.95  --dbg_out_stat                          false
% 1.24/0.95  ------ Parsing...
% 1.24/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.24/0.95  
% 1.24/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.24/0.95  
% 1.24/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.24/0.95  
% 1.24/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.24/0.95  ------ Proving...
% 1.24/0.95  ------ Problem Properties 
% 1.24/0.95  
% 1.24/0.95  
% 1.24/0.95  clauses                                 13
% 1.24/0.95  conjectures                             5
% 1.24/0.95  EPR                                     2
% 1.24/0.95  Horn                                    11
% 1.24/0.95  unary                                   4
% 1.24/0.95  binary                                  1
% 1.24/0.95  lits                                    39
% 1.24/0.95  lits eq                                 4
% 1.24/0.95  fd_pure                                 0
% 1.24/0.95  fd_pseudo                               0
% 1.24/0.95  fd_cond                                 0
% 1.24/0.95  fd_pseudo_cond                          0
% 1.24/0.95  AC symbols                              0
% 1.24/0.95  
% 1.24/0.95  ------ Schedule dynamic 5 is on 
% 1.24/0.95  
% 1.24/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.24/0.95  
% 1.24/0.95  
% 1.24/0.95  ------ 
% 1.24/0.95  Current options:
% 1.24/0.95  ------ 
% 1.24/0.95  
% 1.24/0.95  ------ Input Options
% 1.24/0.95  
% 1.24/0.95  --out_options                           all
% 1.24/0.95  --tptp_safe_out                         true
% 1.24/0.95  --problem_path                          ""
% 1.24/0.95  --include_path                          ""
% 1.24/0.95  --clausifier                            res/vclausify_rel
% 1.24/0.95  --clausifier_options                    --mode clausify
% 1.24/0.95  --stdin                                 false
% 1.24/0.95  --stats_out                             all
% 1.24/0.95  
% 1.24/0.95  ------ General Options
% 1.24/0.95  
% 1.24/0.95  --fof                                   false
% 1.24/0.95  --time_out_real                         305.
% 1.24/0.95  --time_out_virtual                      -1.
% 1.24/0.95  --symbol_type_check                     false
% 1.24/0.95  --clausify_out                          false
% 1.24/0.95  --sig_cnt_out                           false
% 1.24/0.95  --trig_cnt_out                          false
% 1.24/0.95  --trig_cnt_out_tolerance                1.
% 1.24/0.95  --trig_cnt_out_sk_spl                   false
% 1.24/0.95  --abstr_cl_out                          false
% 1.24/0.95  
% 1.24/0.95  ------ Global Options
% 1.24/0.95  
% 1.24/0.95  --schedule                              default
% 1.24/0.95  --add_important_lit                     false
% 1.24/0.95  --prop_solver_per_cl                    1000
% 1.24/0.95  --min_unsat_core                        false
% 1.24/0.95  --soft_assumptions                      false
% 1.24/0.95  --soft_lemma_size                       3
% 1.24/0.95  --prop_impl_unit_size                   0
% 1.24/0.95  --prop_impl_unit                        []
% 1.24/0.95  --share_sel_clauses                     true
% 1.24/0.95  --reset_solvers                         false
% 1.24/0.95  --bc_imp_inh                            [conj_cone]
% 1.24/0.95  --conj_cone_tolerance                   3.
% 1.24/0.95  --extra_neg_conj                        none
% 1.24/0.95  --large_theory_mode                     true
% 1.24/0.95  --prolific_symb_bound                   200
% 1.24/0.95  --lt_threshold                          2000
% 1.24/0.95  --clause_weak_htbl                      true
% 1.24/0.95  --gc_record_bc_elim                     false
% 1.24/0.95  
% 1.24/0.95  ------ Preprocessing Options
% 1.24/0.95  
% 1.24/0.95  --preprocessing_flag                    true
% 1.24/0.95  --time_out_prep_mult                    0.1
% 1.24/0.95  --splitting_mode                        input
% 1.24/0.95  --splitting_grd                         true
% 1.24/0.95  --splitting_cvd                         false
% 1.24/0.95  --splitting_cvd_svl                     false
% 1.24/0.95  --splitting_nvd                         32
% 1.24/0.95  --sub_typing                            true
% 1.24/0.95  --prep_gs_sim                           true
% 1.24/0.95  --prep_unflatten                        true
% 1.24/0.95  --prep_res_sim                          true
% 1.24/0.95  --prep_upred                            true
% 1.24/0.95  --prep_sem_filter                       exhaustive
% 1.24/0.95  --prep_sem_filter_out                   false
% 1.24/0.95  --pred_elim                             true
% 1.24/0.95  --res_sim_input                         true
% 1.24/0.95  --eq_ax_congr_red                       true
% 1.24/0.95  --pure_diseq_elim                       true
% 1.24/0.95  --brand_transform                       false
% 1.24/0.95  --non_eq_to_eq                          false
% 1.24/0.95  --prep_def_merge                        true
% 1.24/0.95  --prep_def_merge_prop_impl              false
% 1.24/0.95  --prep_def_merge_mbd                    true
% 1.24/0.95  --prep_def_merge_tr_red                 false
% 1.24/0.95  --prep_def_merge_tr_cl                  false
% 1.24/0.95  --smt_preprocessing                     true
% 1.24/0.95  --smt_ac_axioms                         fast
% 1.24/0.95  --preprocessed_out                      false
% 1.24/0.95  --preprocessed_stats                    false
% 1.24/0.95  
% 1.24/0.95  ------ Abstraction refinement Options
% 1.24/0.95  
% 1.24/0.95  --abstr_ref                             []
% 1.24/0.95  --abstr_ref_prep                        false
% 1.24/0.95  --abstr_ref_until_sat                   false
% 1.24/0.95  --abstr_ref_sig_restrict                funpre
% 1.24/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 1.24/0.95  --abstr_ref_under                       []
% 1.24/0.95  
% 1.24/0.95  ------ SAT Options
% 1.24/0.95  
% 1.24/0.95  --sat_mode                              false
% 1.24/0.95  --sat_fm_restart_options                ""
% 1.24/0.95  --sat_gr_def                            false
% 1.24/0.95  --sat_epr_types                         true
% 1.24/0.95  --sat_non_cyclic_types                  false
% 1.24/0.95  --sat_finite_models                     false
% 1.24/0.95  --sat_fm_lemmas                         false
% 1.24/0.95  --sat_fm_prep                           false
% 1.24/0.95  --sat_fm_uc_incr                        true
% 1.24/0.95  --sat_out_model                         small
% 1.24/0.95  --sat_out_clauses                       false
% 1.24/0.95  
% 1.24/0.95  ------ QBF Options
% 1.24/0.95  
% 1.24/0.95  --qbf_mode                              false
% 1.24/0.95  --qbf_elim_univ                         false
% 1.24/0.95  --qbf_dom_inst                          none
% 1.24/0.95  --qbf_dom_pre_inst                      false
% 1.24/0.95  --qbf_sk_in                             false
% 1.24/0.95  --qbf_pred_elim                         true
% 1.24/0.95  --qbf_split                             512
% 1.24/0.95  
% 1.24/0.95  ------ BMC1 Options
% 1.24/0.95  
% 1.24/0.95  --bmc1_incremental                      false
% 1.24/0.95  --bmc1_axioms                           reachable_all
% 1.24/0.95  --bmc1_min_bound                        0
% 1.24/0.95  --bmc1_max_bound                        -1
% 1.24/0.95  --bmc1_max_bound_default                -1
% 1.24/0.95  --bmc1_symbol_reachability              true
% 1.24/0.95  --bmc1_property_lemmas                  false
% 1.24/0.95  --bmc1_k_induction                      false
% 1.24/0.95  --bmc1_non_equiv_states                 false
% 1.24/0.95  --bmc1_deadlock                         false
% 1.24/0.95  --bmc1_ucm                              false
% 1.24/0.95  --bmc1_add_unsat_core                   none
% 1.24/0.95  --bmc1_unsat_core_children              false
% 1.24/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 1.24/0.95  --bmc1_out_stat                         full
% 1.24/0.95  --bmc1_ground_init                      false
% 1.24/0.95  --bmc1_pre_inst_next_state              false
% 1.24/0.95  --bmc1_pre_inst_state                   false
% 1.24/0.95  --bmc1_pre_inst_reach_state             false
% 1.24/0.95  --bmc1_out_unsat_core                   false
% 1.24/0.95  --bmc1_aig_witness_out                  false
% 1.24/0.95  --bmc1_verbose                          false
% 1.24/0.95  --bmc1_dump_clauses_tptp                false
% 1.24/0.95  --bmc1_dump_unsat_core_tptp             false
% 1.24/0.95  --bmc1_dump_file                        -
% 1.24/0.95  --bmc1_ucm_expand_uc_limit              128
% 1.24/0.95  --bmc1_ucm_n_expand_iterations          6
% 1.24/0.95  --bmc1_ucm_extend_mode                  1
% 1.24/0.95  --bmc1_ucm_init_mode                    2
% 1.24/0.95  --bmc1_ucm_cone_mode                    none
% 1.24/0.95  --bmc1_ucm_reduced_relation_type        0
% 1.24/0.95  --bmc1_ucm_relax_model                  4
% 1.24/0.95  --bmc1_ucm_full_tr_after_sat            true
% 1.24/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 1.24/0.95  --bmc1_ucm_layered_model                none
% 1.24/0.95  --bmc1_ucm_max_lemma_size               10
% 1.24/0.95  
% 1.24/0.95  ------ AIG Options
% 1.24/0.95  
% 1.24/0.95  --aig_mode                              false
% 1.24/0.95  
% 1.24/0.95  ------ Instantiation Options
% 1.24/0.95  
% 1.24/0.95  --instantiation_flag                    true
% 1.24/0.95  --inst_sos_flag                         false
% 1.24/0.95  --inst_sos_phase                        true
% 1.24/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.24/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.24/0.95  --inst_lit_sel_side                     none
% 1.24/0.95  --inst_solver_per_active                1400
% 1.24/0.95  --inst_solver_calls_frac                1.
% 1.24/0.95  --inst_passive_queue_type               priority_queues
% 1.24/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.24/0.95  --inst_passive_queues_freq              [25;2]
% 1.24/0.95  --inst_dismatching                      true
% 1.24/0.95  --inst_eager_unprocessed_to_passive     true
% 1.24/0.95  --inst_prop_sim_given                   true
% 1.24/0.95  --inst_prop_sim_new                     false
% 1.24/0.95  --inst_subs_new                         false
% 1.24/0.95  --inst_eq_res_simp                      false
% 1.24/0.95  --inst_subs_given                       false
% 1.24/0.95  --inst_orphan_elimination               true
% 1.24/0.95  --inst_learning_loop_flag               true
% 1.24/0.95  --inst_learning_start                   3000
% 1.24/0.95  --inst_learning_factor                  2
% 1.24/0.95  --inst_start_prop_sim_after_learn       3
% 1.24/0.95  --inst_sel_renew                        solver
% 1.24/0.95  --inst_lit_activity_flag                true
% 1.24/0.95  --inst_restr_to_given                   false
% 1.24/0.95  --inst_activity_threshold               500
% 1.24/0.95  --inst_out_proof                        true
% 1.24/0.95  
% 1.24/0.95  ------ Resolution Options
% 1.24/0.95  
% 1.24/0.95  --resolution_flag                       false
% 1.24/0.95  --res_lit_sel                           adaptive
% 1.24/0.95  --res_lit_sel_side                      none
% 1.24/0.95  --res_ordering                          kbo
% 1.24/0.95  --res_to_prop_solver                    active
% 1.24/0.95  --res_prop_simpl_new                    false
% 1.24/0.95  --res_prop_simpl_given                  true
% 1.24/0.95  --res_passive_queue_type                priority_queues
% 1.24/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.24/0.95  --res_passive_queues_freq               [15;5]
% 1.24/0.95  --res_forward_subs                      full
% 1.24/0.95  --res_backward_subs                     full
% 1.24/0.95  --res_forward_subs_resolution           true
% 1.24/0.95  --res_backward_subs_resolution          true
% 1.24/0.95  --res_orphan_elimination                true
% 1.24/0.95  --res_time_limit                        2.
% 1.24/0.95  --res_out_proof                         true
% 1.24/0.95  
% 1.24/0.95  ------ Superposition Options
% 1.24/0.95  
% 1.24/0.95  --superposition_flag                    true
% 1.24/0.95  --sup_passive_queue_type                priority_queues
% 1.24/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.24/0.95  --sup_passive_queues_freq               [8;1;4]
% 1.24/0.95  --demod_completeness_check              fast
% 1.24/0.95  --demod_use_ground                      true
% 1.24/0.95  --sup_to_prop_solver                    passive
% 1.24/0.95  --sup_prop_simpl_new                    true
% 1.24/0.95  --sup_prop_simpl_given                  true
% 1.24/0.95  --sup_fun_splitting                     false
% 1.24/0.95  --sup_smt_interval                      50000
% 1.24/0.95  
% 1.24/0.95  ------ Superposition Simplification Setup
% 1.24/0.95  
% 1.24/0.95  --sup_indices_passive                   []
% 1.24/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.24/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.24/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.24/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 1.24/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.24/0.95  --sup_full_bw                           [BwDemod]
% 1.24/0.95  --sup_immed_triv                        [TrivRules]
% 1.24/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.24/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.24/0.95  --sup_immed_bw_main                     []
% 1.24/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.24/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 1.24/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.24/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.24/0.95  
% 1.24/0.95  ------ Combination Options
% 1.24/0.95  
% 1.24/0.95  --comb_res_mult                         3
% 1.24/0.95  --comb_sup_mult                         2
% 1.24/0.95  --comb_inst_mult                        10
% 1.24/0.95  
% 1.24/0.95  ------ Debug Options
% 1.24/0.95  
% 1.24/0.95  --dbg_backtrace                         false
% 1.24/0.95  --dbg_dump_prop_clauses                 false
% 1.24/0.95  --dbg_dump_prop_clauses_file            -
% 1.24/0.95  --dbg_out_stat                          false
% 1.24/0.95  
% 1.24/0.95  
% 1.24/0.95  
% 1.24/0.95  
% 1.24/0.95  ------ Proving...
% 1.24/0.95  
% 1.24/0.95  
% 1.24/0.95  % SZS status Theorem for theBenchmark.p
% 1.24/0.95  
% 1.24/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 1.24/0.95  
% 1.24/0.95  fof(f5,conjecture,(
% 1.24/0.95    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 1.24/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.24/0.95  
% 1.24/0.95  fof(f6,negated_conjecture,(
% 1.24/0.95    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,X3) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 1.24/0.95    inference(negated_conjecture,[],[f5])).
% 1.24/0.95  
% 1.24/0.95  fof(f11,plain,(
% 1.24/0.95    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.24/0.95    inference(ennf_transformation,[],[f6])).
% 1.24/0.95  
% 1.24/0.95  fof(f12,plain,(
% 1.24/0.95    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.24/0.95    inference(flattening,[],[f11])).
% 1.24/0.95  
% 1.24/0.95  fof(f21,plain,(
% 1.24/0.95    ( ! [X0,X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (k1_tarski(sK4) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK4,X1) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 1.24/0.95    introduced(choice_axiom,[])).
% 1.24/0.95  
% 1.24/0.95  fof(f20,plain,(
% 1.24/0.95    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),sK3,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.24/0.95    introduced(choice_axiom,[])).
% 1.24/0.95  
% 1.24/0.95  fof(f19,plain,(
% 1.24/0.95    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(X0),X1,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK2),X1,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2))),
% 1.24/0.95    introduced(choice_axiom,[])).
% 1.24/0.95  
% 1.24/0.95  fof(f22,plain,(
% 1.24/0.95    ((! [X3] : (k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2)),
% 1.24/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f21,f20,f19])).
% 1.24/0.95  
% 1.24/0.95  fof(f37,plain,(
% 1.24/0.95    r2_hidden(sK4,sK3)),
% 1.24/0.95    inference(cnf_transformation,[],[f22])).
% 1.24/0.95  
% 1.24/0.95  fof(f34,plain,(
% 1.24/0.95    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.24/0.95    inference(cnf_transformation,[],[f22])).
% 1.24/0.95  
% 1.24/0.95  fof(f3,axiom,(
% 1.24/0.95    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.24/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.24/0.95  
% 1.24/0.95  fof(f8,plain,(
% 1.24/0.95    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.24/0.95    inference(ennf_transformation,[],[f3])).
% 1.24/0.95  
% 1.24/0.95  fof(f26,plain,(
% 1.24/0.95    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.24/0.95    inference(cnf_transformation,[],[f8])).
% 1.24/0.95  
% 1.24/0.95  fof(f1,axiom,(
% 1.24/0.95    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.24/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.24/0.95  
% 1.24/0.95  fof(f13,plain,(
% 1.24/0.95    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.24/0.95    inference(nnf_transformation,[],[f1])).
% 1.24/0.95  
% 1.24/0.95  fof(f24,plain,(
% 1.24/0.95    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.24/0.95    inference(cnf_transformation,[],[f13])).
% 1.24/0.95  
% 1.24/0.95  fof(f4,axiom,(
% 1.24/0.95    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.24/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.24/0.95  
% 1.24/0.95  fof(f9,plain,(
% 1.24/0.96    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.24/0.96    inference(ennf_transformation,[],[f4])).
% 1.24/0.96  
% 1.24/0.96  fof(f10,plain,(
% 1.24/0.96    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.24/0.96    inference(flattening,[],[f9])).
% 1.24/0.96  
% 1.24/0.96  fof(f14,plain,(
% 1.24/0.96    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.24/0.96    inference(nnf_transformation,[],[f10])).
% 1.24/0.96  
% 1.24/0.96  fof(f15,plain,(
% 1.24/0.96    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.24/0.96    inference(rectify,[],[f14])).
% 1.24/0.96  
% 1.24/0.96  fof(f17,plain,(
% 1.24/0.96    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v3_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.24/0.96    introduced(choice_axiom,[])).
% 1.24/0.96  
% 1.24/0.96  fof(f16,plain,(
% 1.24/0.96    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.24/0.96    introduced(choice_axiom,[])).
% 1.24/0.96  
% 1.24/0.96  fof(f18,plain,(
% 1.24/0.96    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v3_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.24/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17,f16])).
% 1.24/0.96  
% 1.24/0.96  fof(f29,plain,(
% 1.24/0.96    ( ! [X4,X0,X1] : (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.24/0.96    inference(cnf_transformation,[],[f18])).
% 1.24/0.96  
% 1.24/0.96  fof(f33,plain,(
% 1.24/0.96    l1_pre_topc(sK2)),
% 1.24/0.96    inference(cnf_transformation,[],[f22])).
% 1.24/0.96  
% 1.24/0.96  fof(f2,axiom,(
% 1.24/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.24/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.24/0.96  
% 1.24/0.96  fof(f7,plain,(
% 1.24/0.96    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.24/0.96    inference(ennf_transformation,[],[f2])).
% 1.24/0.96  
% 1.24/0.96  fof(f25,plain,(
% 1.24/0.96    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.24/0.96    inference(cnf_transformation,[],[f7])).
% 1.24/0.96  
% 1.24/0.96  fof(f35,plain,(
% 1.24/0.96    v2_tex_2(sK3,sK2)),
% 1.24/0.96    inference(cnf_transformation,[],[f22])).
% 1.24/0.96  
% 1.24/0.96  fof(f38,plain,(
% 1.24/0.96    ( ! [X3] : (k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X3) | ~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 1.24/0.96    inference(cnf_transformation,[],[f22])).
% 1.24/0.96  
% 1.24/0.96  fof(f27,plain,(
% 1.24/0.96    ( ! [X4,X0,X1] : (m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.24/0.96    inference(cnf_transformation,[],[f18])).
% 1.24/0.96  
% 1.24/0.96  fof(f28,plain,(
% 1.24/0.96    ( ! [X4,X0,X1] : (v3_pre_topc(sK1(X0,X1,X4),X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.24/0.96    inference(cnf_transformation,[],[f18])).
% 1.24/0.96  
% 1.24/0.96  cnf(c_11,negated_conjecture,
% 1.24/0.96      ( r2_hidden(sK4,sK3) ),
% 1.24/0.96      inference(cnf_transformation,[],[f37]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1486,negated_conjecture,
% 1.24/0.96      ( r2_hidden(sK4,sK3) ),
% 1.24/0.96      inference(subtyping,[status(esa)],[c_11]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1760,plain,
% 1.24/0.96      ( r2_hidden(sK4,sK3) = iProver_top ),
% 1.24/0.96      inference(predicate_to_equality,[status(thm)],[c_1486]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_14,negated_conjecture,
% 1.24/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.24/0.96      inference(cnf_transformation,[],[f34]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1483,negated_conjecture,
% 1.24/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.24/0.96      inference(subtyping,[status(esa)],[c_14]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1763,plain,
% 1.24/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.24/0.96      inference(predicate_to_equality,[status(thm)],[c_1483]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_3,plain,
% 1.24/0.96      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~ r2_hidden(X0,X1) ),
% 1.24/0.96      inference(cnf_transformation,[],[f26]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1488,plain,
% 1.24/0.96      ( m1_subset_1(k1_tarski(X0_43),k1_zfmisc_1(X1_43))
% 1.24/0.96      | ~ r2_hidden(X0_43,X1_43) ),
% 1.24/0.96      inference(subtyping,[status(esa)],[c_3]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1758,plain,
% 1.24/0.96      ( m1_subset_1(k1_tarski(X0_43),k1_zfmisc_1(X1_43)) = iProver_top
% 1.24/0.96      | r2_hidden(X0_43,X1_43) != iProver_top ),
% 1.24/0.96      inference(predicate_to_equality,[status(thm)],[c_1488]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_0,plain,
% 1.24/0.96      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 1.24/0.96      inference(cnf_transformation,[],[f24]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_121,plain,
% 1.24/0.96      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 1.24/0.96      inference(prop_impl,[status(thm)],[c_0]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_7,plain,
% 1.24/0.96      ( ~ v2_tex_2(X0,X1)
% 1.24/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.24/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.24/0.96      | ~ r1_tarski(X2,X0)
% 1.24/0.96      | ~ l1_pre_topc(X1)
% 1.24/0.96      | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2 ),
% 1.24/0.96      inference(cnf_transformation,[],[f29]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_15,negated_conjecture,
% 1.24/0.96      ( l1_pre_topc(sK2) ),
% 1.24/0.96      inference(cnf_transformation,[],[f33]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_338,plain,
% 1.24/0.96      ( ~ v2_tex_2(X0,X1)
% 1.24/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.24/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.24/0.96      | ~ r1_tarski(X2,X0)
% 1.24/0.96      | k9_subset_1(u1_struct_0(X1),X0,sK1(X1,X0,X2)) = X2
% 1.24/0.96      | sK2 != X1 ),
% 1.24/0.96      inference(resolution_lifted,[status(thm)],[c_7,c_15]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_339,plain,
% 1.24/0.96      ( ~ v2_tex_2(X0,sK2)
% 1.24/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ r1_tarski(X1,X0)
% 1.24/0.96      | k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,X1)) = X1 ),
% 1.24/0.96      inference(unflattening,[status(thm)],[c_338]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_508,plain,
% 1.24/0.96      ( ~ v2_tex_2(X0,sK2)
% 1.24/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ r2_hidden(X2,X3)
% 1.24/0.96      | X0 != X3
% 1.24/0.96      | k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,X1)) = X1
% 1.24/0.96      | k1_tarski(X2) != X1 ),
% 1.24/0.96      inference(resolution_lifted,[status(thm)],[c_121,c_339]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_509,plain,
% 1.24/0.96      ( ~ v2_tex_2(X0,sK2)
% 1.24/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ r2_hidden(X1,X0)
% 1.24/0.96      | k9_subset_1(u1_struct_0(sK2),X0,sK1(sK2,X0,k1_tarski(X1))) = k1_tarski(X1) ),
% 1.24/0.96      inference(unflattening,[status(thm)],[c_508]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1480,plain,
% 1.24/0.96      ( ~ v2_tex_2(X0_43,sK2)
% 1.24/0.96      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ m1_subset_1(k1_tarski(X1_43),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ r2_hidden(X1_43,X0_43)
% 1.24/0.96      | k9_subset_1(u1_struct_0(sK2),X0_43,sK1(sK2,X0_43,k1_tarski(X1_43))) = k1_tarski(X1_43) ),
% 1.24/0.96      inference(subtyping,[status(esa)],[c_509]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1766,plain,
% 1.24/0.96      ( k9_subset_1(u1_struct_0(sK2),X0_43,sK1(sK2,X0_43,k1_tarski(X1_43))) = k1_tarski(X1_43)
% 1.24/0.96      | v2_tex_2(X0_43,sK2) != iProver_top
% 1.24/0.96      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.24/0.96      | m1_subset_1(k1_tarski(X1_43),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.24/0.96      | r2_hidden(X1_43,X0_43) != iProver_top ),
% 1.24/0.96      inference(predicate_to_equality,[status(thm)],[c_1480]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_2328,plain,
% 1.24/0.96      ( k9_subset_1(u1_struct_0(sK2),X0_43,sK1(sK2,X0_43,k1_tarski(X1_43))) = k1_tarski(X1_43)
% 1.24/0.96      | v2_tex_2(X0_43,sK2) != iProver_top
% 1.24/0.96      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.24/0.96      | r2_hidden(X1_43,X0_43) != iProver_top
% 1.24/0.96      | r2_hidden(X1_43,u1_struct_0(sK2)) != iProver_top ),
% 1.24/0.96      inference(superposition,[status(thm)],[c_1758,c_1766]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_2,plain,
% 1.24/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.24/0.96      | ~ r2_hidden(X2,X0)
% 1.24/0.96      | r2_hidden(X2,X1) ),
% 1.24/0.96      inference(cnf_transformation,[],[f25]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1489,plain,
% 1.24/0.96      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 1.24/0.96      | ~ r2_hidden(X2_43,X0_43)
% 1.24/0.96      | r2_hidden(X2_43,X1_43) ),
% 1.24/0.96      inference(subtyping,[status(esa)],[c_2]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1757,plain,
% 1.24/0.96      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
% 1.24/0.96      | r2_hidden(X2_43,X0_43) != iProver_top
% 1.24/0.96      | r2_hidden(X2_43,X1_43) = iProver_top ),
% 1.24/0.96      inference(predicate_to_equality,[status(thm)],[c_1489]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_2407,plain,
% 1.24/0.96      ( k9_subset_1(u1_struct_0(sK2),X0_43,sK1(sK2,X0_43,k1_tarski(X1_43))) = k1_tarski(X1_43)
% 1.24/0.96      | v2_tex_2(X0_43,sK2) != iProver_top
% 1.24/0.96      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.24/0.96      | r2_hidden(X1_43,X0_43) != iProver_top ),
% 1.24/0.96      inference(forward_subsumption_resolution,
% 1.24/0.96                [status(thm)],
% 1.24/0.96                [c_2328,c_1757]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_2411,plain,
% 1.24/0.96      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k1_tarski(X0_43))) = k1_tarski(X0_43)
% 1.24/0.96      | v2_tex_2(sK3,sK2) != iProver_top
% 1.24/0.96      | r2_hidden(X0_43,sK3) != iProver_top ),
% 1.24/0.96      inference(superposition,[status(thm)],[c_1763,c_2407]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_13,negated_conjecture,
% 1.24/0.96      ( v2_tex_2(sK3,sK2) ),
% 1.24/0.96      inference(cnf_transformation,[],[f35]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_18,plain,
% 1.24/0.96      ( v2_tex_2(sK3,sK2) = iProver_top ),
% 1.24/0.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_2521,plain,
% 1.24/0.96      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k1_tarski(X0_43))) = k1_tarski(X0_43)
% 1.24/0.96      | r2_hidden(X0_43,sK3) != iProver_top ),
% 1.24/0.96      inference(global_propositional_subsumption,
% 1.24/0.96                [status(thm)],
% 1.24/0.96                [c_2411,c_18]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_2529,plain,
% 1.24/0.96      ( k9_subset_1(u1_struct_0(sK2),sK3,sK1(sK2,sK3,k1_tarski(sK4))) = k1_tarski(sK4) ),
% 1.24/0.96      inference(superposition,[status(thm)],[c_1760,c_2521]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_10,negated_conjecture,
% 1.24/0.96      ( ~ v3_pre_topc(X0,sK2)
% 1.24/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X0) ),
% 1.24/0.96      inference(cnf_transformation,[],[f38]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1487,negated_conjecture,
% 1.24/0.96      ( ~ v3_pre_topc(X0_43,sK2)
% 1.24/0.96      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X0_43) ),
% 1.24/0.96      inference(subtyping,[status(esa)],[c_10]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1759,plain,
% 1.24/0.96      ( k1_tarski(sK4) != k9_subset_1(u1_struct_0(sK2),sK3,X0_43)
% 1.24/0.96      | v3_pre_topc(X0_43,sK2) != iProver_top
% 1.24/0.96      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.24/0.96      inference(predicate_to_equality,[status(thm)],[c_1487]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_2531,plain,
% 1.24/0.96      ( v3_pre_topc(sK1(sK2,sK3,k1_tarski(sK4)),sK2) != iProver_top
% 1.24/0.96      | m1_subset_1(sK1(sK2,sK3,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.24/0.96      inference(superposition,[status(thm)],[c_2529,c_1759]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1885,plain,
% 1.24/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0_43))
% 1.24/0.96      | r2_hidden(sK4,X0_43)
% 1.24/0.96      | ~ r2_hidden(sK4,sK3) ),
% 1.24/0.96      inference(instantiation,[status(thm)],[c_1489]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_2051,plain,
% 1.24/0.96      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | r2_hidden(sK4,u1_struct_0(sK2))
% 1.24/0.96      | ~ r2_hidden(sK4,sK3) ),
% 1.24/0.96      inference(instantiation,[status(thm)],[c_1885]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_2052,plain,
% 1.24/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.24/0.96      | r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
% 1.24/0.96      | r2_hidden(sK4,sK3) != iProver_top ),
% 1.24/0.96      inference(predicate_to_equality,[status(thm)],[c_2051]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_9,plain,
% 1.24/0.96      ( ~ v2_tex_2(X0,X1)
% 1.24/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.24/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.24/0.96      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 1.24/0.96      | ~ r1_tarski(X2,X0)
% 1.24/0.96      | ~ l1_pre_topc(X1) ),
% 1.24/0.96      inference(cnf_transformation,[],[f27]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_317,plain,
% 1.24/0.96      ( ~ v2_tex_2(X0,X1)
% 1.24/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.24/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.24/0.96      | m1_subset_1(sK1(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 1.24/0.96      | ~ r1_tarski(X2,X0)
% 1.24/0.96      | sK2 != X1 ),
% 1.24/0.96      inference(resolution_lifted,[status(thm)],[c_9,c_15]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_318,plain,
% 1.24/0.96      ( ~ v2_tex_2(X0,sK2)
% 1.24/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ r1_tarski(X1,X0) ),
% 1.24/0.96      inference(unflattening,[status(thm)],[c_317]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_529,plain,
% 1.24/0.96      ( ~ v2_tex_2(X0,sK2)
% 1.24/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | m1_subset_1(sK1(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ r2_hidden(X2,X3)
% 1.24/0.96      | X0 != X3
% 1.24/0.96      | k1_tarski(X2) != X1 ),
% 1.24/0.96      inference(resolution_lifted,[status(thm)],[c_121,c_318]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_530,plain,
% 1.24/0.96      ( ~ v2_tex_2(X0,sK2)
% 1.24/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | m1_subset_1(sK1(sK2,X0,k1_tarski(X1)),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ r2_hidden(X1,X0) ),
% 1.24/0.96      inference(unflattening,[status(thm)],[c_529]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1479,plain,
% 1.24/0.96      ( ~ v2_tex_2(X0_43,sK2)
% 1.24/0.96      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | m1_subset_1(sK1(sK2,X0_43,k1_tarski(X1_43)),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ m1_subset_1(k1_tarski(X1_43),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ r2_hidden(X1_43,X0_43) ),
% 1.24/0.96      inference(subtyping,[status(esa)],[c_530]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1962,plain,
% 1.24/0.96      ( ~ v2_tex_2(X0_43,sK2)
% 1.24/0.96      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | m1_subset_1(sK1(sK2,X0_43,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ r2_hidden(sK4,X0_43) ),
% 1.24/0.96      inference(instantiation,[status(thm)],[c_1479]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1970,plain,
% 1.24/0.96      ( v2_tex_2(X0_43,sK2) != iProver_top
% 1.24/0.96      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.24/0.96      | m1_subset_1(sK1(sK2,X0_43,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.24/0.96      | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.24/0.96      | r2_hidden(sK4,X0_43) != iProver_top ),
% 1.24/0.96      inference(predicate_to_equality,[status(thm)],[c_1962]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1972,plain,
% 1.24/0.96      ( v2_tex_2(sK3,sK2) != iProver_top
% 1.24/0.96      | m1_subset_1(sK1(sK2,sK3,k1_tarski(sK4)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.24/0.96      | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.24/0.96      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.24/0.96      | r2_hidden(sK4,sK3) != iProver_top ),
% 1.24/0.96      inference(instantiation,[status(thm)],[c_1970]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_8,plain,
% 1.24/0.96      ( v3_pre_topc(sK1(X0,X1,X2),X0)
% 1.24/0.96      | ~ v2_tex_2(X1,X0)
% 1.24/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.24/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.24/0.96      | ~ r1_tarski(X2,X1)
% 1.24/0.96      | ~ l1_pre_topc(X0) ),
% 1.24/0.96      inference(cnf_transformation,[],[f28]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_296,plain,
% 1.24/0.96      ( v3_pre_topc(sK1(X0,X1,X2),X0)
% 1.24/0.96      | ~ v2_tex_2(X1,X0)
% 1.24/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.24/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.24/0.96      | ~ r1_tarski(X2,X1)
% 1.24/0.96      | sK2 != X0 ),
% 1.24/0.96      inference(resolution_lifted,[status(thm)],[c_8,c_15]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_297,plain,
% 1.24/0.96      ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
% 1.24/0.96      | ~ v2_tex_2(X0,sK2)
% 1.24/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ r1_tarski(X1,X0) ),
% 1.24/0.96      inference(unflattening,[status(thm)],[c_296]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_550,plain,
% 1.24/0.96      ( v3_pre_topc(sK1(sK2,X0,X1),sK2)
% 1.24/0.96      | ~ v2_tex_2(X0,sK2)
% 1.24/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ r2_hidden(X2,X3)
% 1.24/0.96      | X0 != X3
% 1.24/0.96      | k1_tarski(X2) != X1 ),
% 1.24/0.96      inference(resolution_lifted,[status(thm)],[c_121,c_297]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_551,plain,
% 1.24/0.96      ( v3_pre_topc(sK1(sK2,X0,k1_tarski(X1)),sK2)
% 1.24/0.96      | ~ v2_tex_2(X0,sK2)
% 1.24/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ r2_hidden(X1,X0) ),
% 1.24/0.96      inference(unflattening,[status(thm)],[c_550]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1478,plain,
% 1.24/0.96      ( v3_pre_topc(sK1(sK2,X0_43,k1_tarski(X1_43)),sK2)
% 1.24/0.96      | ~ v2_tex_2(X0_43,sK2)
% 1.24/0.96      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ m1_subset_1(k1_tarski(X1_43),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ r2_hidden(X1_43,X0_43) ),
% 1.24/0.96      inference(subtyping,[status(esa)],[c_551]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1963,plain,
% 1.24/0.96      ( v3_pre_topc(sK1(sK2,X0_43,k1_tarski(sK4)),sK2)
% 1.24/0.96      | ~ v2_tex_2(X0_43,sK2)
% 1.24/0.96      | ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ r2_hidden(sK4,X0_43) ),
% 1.24/0.96      inference(instantiation,[status(thm)],[c_1478]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1966,plain,
% 1.24/0.96      ( v3_pre_topc(sK1(sK2,X0_43,k1_tarski(sK4)),sK2) = iProver_top
% 1.24/0.96      | v2_tex_2(X0_43,sK2) != iProver_top
% 1.24/0.96      | m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.24/0.96      | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.24/0.96      | r2_hidden(sK4,X0_43) != iProver_top ),
% 1.24/0.96      inference(predicate_to_equality,[status(thm)],[c_1963]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1968,plain,
% 1.24/0.96      ( v3_pre_topc(sK1(sK2,sK3,k1_tarski(sK4)),sK2) = iProver_top
% 1.24/0.96      | v2_tex_2(sK3,sK2) != iProver_top
% 1.24/0.96      | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.24/0.96      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.24/0.96      | r2_hidden(sK4,sK3) != iProver_top ),
% 1.24/0.96      inference(instantiation,[status(thm)],[c_1966]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1913,plain,
% 1.24/0.96      ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(X0_43))
% 1.24/0.96      | ~ r2_hidden(sK4,X0_43) ),
% 1.24/0.96      inference(instantiation,[status(thm)],[c_1488]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1960,plain,
% 1.24/0.96      ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.24/0.96      | ~ r2_hidden(sK4,u1_struct_0(sK2)) ),
% 1.24/0.96      inference(instantiation,[status(thm)],[c_1913]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_1964,plain,
% 1.24/0.96      ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.24/0.96      | r2_hidden(sK4,u1_struct_0(sK2)) != iProver_top ),
% 1.24/0.96      inference(predicate_to_equality,[status(thm)],[c_1960]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_20,plain,
% 1.24/0.96      ( r2_hidden(sK4,sK3) = iProver_top ),
% 1.24/0.96      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(c_17,plain,
% 1.24/0.96      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.24/0.96      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.24/0.96  
% 1.24/0.96  cnf(contradiction,plain,
% 1.24/0.96      ( $false ),
% 1.24/0.96      inference(minisat,
% 1.24/0.96                [status(thm)],
% 1.24/0.96                [c_2531,c_2052,c_1972,c_1968,c_1964,c_20,c_18,c_17]) ).
% 1.24/0.96  
% 1.24/0.96  
% 1.24/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 1.24/0.96  
% 1.24/0.96  ------                               Statistics
% 1.24/0.96  
% 1.24/0.96  ------ General
% 1.24/0.96  
% 1.24/0.96  abstr_ref_over_cycles:                  0
% 1.24/0.96  abstr_ref_under_cycles:                 0
% 1.24/0.96  gc_basic_clause_elim:                   0
% 1.24/0.96  forced_gc_time:                         0
% 1.24/0.96  parsing_time:                           0.009
% 1.24/0.96  unif_index_cands_time:                  0.
% 1.24/0.96  unif_index_add_time:                    0.
% 1.24/0.96  orderings_time:                         0.
% 1.24/0.96  out_proof_time:                         0.009
% 1.24/0.96  total_time:                             0.106
% 1.24/0.96  num_of_symbols:                         45
% 1.24/0.96  num_of_terms:                           1701
% 1.24/0.96  
% 1.24/0.96  ------ Preprocessing
% 1.24/0.96  
% 1.24/0.96  num_of_splits:                          0
% 1.24/0.96  num_of_split_atoms:                     0
% 1.24/0.96  num_of_reused_defs:                     0
% 1.24/0.96  num_eq_ax_congr_red:                    15
% 1.24/0.96  num_of_sem_filtered_clauses:            1
% 1.24/0.96  num_of_subtypes:                        2
% 1.24/0.96  monotx_restored_types:                  0
% 1.24/0.96  sat_num_of_epr_types:                   0
% 1.24/0.96  sat_num_of_non_cyclic_types:            0
% 1.24/0.96  sat_guarded_non_collapsed_types:        0
% 1.24/0.96  num_pure_diseq_elim:                    0
% 1.24/0.96  simp_replaced_by:                       0
% 1.24/0.96  res_preprocessed:                       76
% 1.24/0.96  prep_upred:                             0
% 1.24/0.96  prep_unflattend:                        41
% 1.24/0.96  smt_new_axioms:                         0
% 1.24/0.96  pred_elim_cands:                        4
% 1.24/0.96  pred_elim:                              2
% 1.24/0.96  pred_elim_cl:                           3
% 1.24/0.96  pred_elim_cycles:                       8
% 1.24/0.96  merged_defs:                            2
% 1.24/0.96  merged_defs_ncl:                        0
% 1.24/0.96  bin_hyper_res:                          2
% 1.24/0.96  prep_cycles:                            4
% 1.24/0.96  pred_elim_time:                         0.029
% 1.24/0.96  splitting_time:                         0.
% 1.24/0.96  sem_filter_time:                        0.
% 1.24/0.96  monotx_time:                            0.
% 1.24/0.96  subtype_inf_time:                       0.
% 1.24/0.96  
% 1.24/0.96  ------ Problem properties
% 1.24/0.96  
% 1.24/0.96  clauses:                                13
% 1.24/0.96  conjectures:                            5
% 1.24/0.96  epr:                                    2
% 1.24/0.96  horn:                                   11
% 1.24/0.96  ground:                                 4
% 1.24/0.96  unary:                                  4
% 1.24/0.96  binary:                                 1
% 1.24/0.96  lits:                                   39
% 1.24/0.96  lits_eq:                                4
% 1.24/0.96  fd_pure:                                0
% 1.24/0.96  fd_pseudo:                              0
% 1.24/0.96  fd_cond:                                0
% 1.24/0.96  fd_pseudo_cond:                         0
% 1.24/0.96  ac_symbols:                             0
% 1.24/0.96  
% 1.24/0.96  ------ Propositional Solver
% 1.24/0.96  
% 1.24/0.96  prop_solver_calls:                      27
% 1.24/0.96  prop_fast_solver_calls:                 795
% 1.24/0.96  smt_solver_calls:                       0
% 1.24/0.96  smt_fast_solver_calls:                  0
% 1.24/0.96  prop_num_of_clauses:                    465
% 1.24/0.96  prop_preprocess_simplified:             2541
% 1.24/0.96  prop_fo_subsumed:                       12
% 1.24/0.96  prop_solver_time:                       0.
% 1.24/0.96  smt_solver_time:                        0.
% 1.24/0.96  smt_fast_solver_time:                   0.
% 1.24/0.96  prop_fast_solver_time:                  0.
% 1.24/0.96  prop_unsat_core_time:                   0.
% 1.24/0.96  
% 1.24/0.96  ------ QBF
% 1.24/0.96  
% 1.24/0.96  qbf_q_res:                              0
% 1.24/0.96  qbf_num_tautologies:                    0
% 1.24/0.96  qbf_prep_cycles:                        0
% 1.24/0.96  
% 1.24/0.96  ------ BMC1
% 1.24/0.96  
% 1.24/0.96  bmc1_current_bound:                     -1
% 1.24/0.96  bmc1_last_solved_bound:                 -1
% 1.24/0.96  bmc1_unsat_core_size:                   -1
% 1.24/0.96  bmc1_unsat_core_parents_size:           -1
% 1.24/0.96  bmc1_merge_next_fun:                    0
% 1.24/0.96  bmc1_unsat_core_clauses_time:           0.
% 1.24/0.96  
% 1.24/0.96  ------ Instantiation
% 1.24/0.96  
% 1.24/0.96  inst_num_of_clauses:                    111
% 1.24/0.96  inst_num_in_passive:                    7
% 1.24/0.96  inst_num_in_active:                     92
% 1.24/0.96  inst_num_in_unprocessed:                12
% 1.24/0.96  inst_num_of_loops:                      100
% 1.24/0.96  inst_num_of_learning_restarts:          0
% 1.24/0.96  inst_num_moves_active_passive:          4
% 1.24/0.96  inst_lit_activity:                      0
% 1.24/0.96  inst_lit_activity_moves:                0
% 1.24/0.96  inst_num_tautologies:                   0
% 1.24/0.96  inst_num_prop_implied:                  0
% 1.24/0.96  inst_num_existing_simplified:           0
% 1.24/0.96  inst_num_eq_res_simplified:             0
% 1.24/0.96  inst_num_child_elim:                    0
% 1.24/0.96  inst_num_of_dismatching_blockings:      27
% 1.24/0.96  inst_num_of_non_proper_insts:           117
% 1.24/0.96  inst_num_of_duplicates:                 0
% 1.24/0.96  inst_inst_num_from_inst_to_res:         0
% 1.24/0.96  inst_dismatching_checking_time:         0.
% 1.24/0.96  
% 1.24/0.96  ------ Resolution
% 1.24/0.96  
% 1.24/0.96  res_num_of_clauses:                     0
% 1.24/0.96  res_num_in_passive:                     0
% 1.24/0.96  res_num_in_active:                      0
% 1.24/0.96  res_num_of_loops:                       80
% 1.24/0.96  res_forward_subset_subsumed:            22
% 1.24/0.96  res_backward_subset_subsumed:           0
% 1.24/0.96  res_forward_subsumed:                   0
% 1.24/0.96  res_backward_subsumed:                  0
% 1.24/0.96  res_forward_subsumption_resolution:     3
% 1.24/0.96  res_backward_subsumption_resolution:    0
% 1.24/0.96  res_clause_to_clause_subsumption:       151
% 1.24/0.96  res_orphan_elimination:                 0
% 1.24/0.96  res_tautology_del:                      31
% 1.24/0.96  res_num_eq_res_simplified:              0
% 1.24/0.96  res_num_sel_changes:                    0
% 1.24/0.96  res_moves_from_active_to_pass:          0
% 1.24/0.96  
% 1.24/0.96  ------ Superposition
% 1.24/0.96  
% 1.24/0.96  sup_time_total:                         0.
% 1.24/0.96  sup_time_generating:                    0.
% 1.24/0.96  sup_time_sim_full:                      0.
% 1.24/0.96  sup_time_sim_immed:                     0.
% 1.24/0.96  
% 1.24/0.96  sup_num_of_clauses:                     27
% 1.24/0.96  sup_num_in_active:                      20
% 1.24/0.96  sup_num_in_passive:                     7
% 1.24/0.96  sup_num_of_loops:                       19
% 1.24/0.96  sup_fw_superposition:                   11
% 1.24/0.96  sup_bw_superposition:                   5
% 1.24/0.96  sup_immediate_simplified:               1
% 1.24/0.96  sup_given_eliminated:                   0
% 1.24/0.96  comparisons_done:                       0
% 1.24/0.96  comparisons_avoided:                    0
% 1.24/0.96  
% 1.24/0.96  ------ Simplifications
% 1.24/0.96  
% 1.24/0.96  
% 1.24/0.96  sim_fw_subset_subsumed:                 2
% 1.24/0.96  sim_bw_subset_subsumed:                 0
% 1.24/0.96  sim_fw_subsumed:                        0
% 1.24/0.96  sim_bw_subsumed:                        0
% 1.24/0.96  sim_fw_subsumption_res:                 1
% 1.24/0.96  sim_bw_subsumption_res:                 0
% 1.24/0.96  sim_tautology_del:                      0
% 1.24/0.96  sim_eq_tautology_del:                   0
% 1.24/0.96  sim_eq_res_simp:                        0
% 1.24/0.96  sim_fw_demodulated:                     0
% 1.24/0.96  sim_bw_demodulated:                     0
% 1.24/0.96  sim_light_normalised:                   0
% 1.24/0.96  sim_joinable_taut:                      0
% 1.24/0.96  sim_joinable_simp:                      0
% 1.24/0.96  sim_ac_normalised:                      0
% 1.24/0.96  sim_smt_subsumption:                    0
% 1.24/0.96  
%------------------------------------------------------------------------------
