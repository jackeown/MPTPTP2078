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
% DateTime   : Thu Dec  3 12:26:17 EST 2020

% Result     : Theorem 1.21s
% Output     : CNFRefutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 256 expanded)
%              Number of clauses        :   53 (  76 expanded)
%              Number of leaves         :   15 (  62 expanded)
%              Depth                    :   28
%              Number of atoms          :  337 (1171 expanded)
%              Number of equality atoms :   75 ( 112 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( ~ v2_tex_2(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK3)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f32,f31])).

fof(f52,plain,(
    ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(nnf_transformation,[],[f21])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f29,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4
        & v4_pre_topc(sK2(X0,X1,X4),X0)
        & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK1(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4
                    & v4_pre_topc(sK2(X0,X1,X4),X0)
                    & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f29,f28])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f50,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f24])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_14,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_9,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_429,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK1(X1,X0),X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_430,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK1(sK3,X0),X0) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_570,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 != X1
    | sK1(sK3,X0) != X2
    | k2_xboole_0(X2,X1) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_430])).

cnf(c_571,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_xboole_0(sK1(sK3,X0),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_637,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_xboole_0(sK1(sK3,X0),X0) = X0
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_571])).

cnf(c_638,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | k2_xboole_0(sK1(sK3,sK4),sK4) = sK4 ),
    inference(unflattening,[status(thm)],[c_637])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_640,plain,
    ( k2_xboole_0(sK1(sK3,sK4),sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_638,c_15])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_16,negated_conjecture,
    ( v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_251,plain,
    ( sK4 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_16])).

cnf(c_252,plain,
    ( k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_251])).

cnf(c_707,plain,
    ( k2_xboole_0(sK1(sK3,k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_640,c_252])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_712,plain,
    ( sK1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_707,c_3])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_7,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_203,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_204,plain,
    ( v4_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_208,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v4_pre_topc(X0,sK3)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_204,c_17])).

cnf(c_209,plain,
    ( v4_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_228,plain,
    ( v4_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_209])).

cnf(c_229,plain,
    ( v4_pre_topc(k1_xboole_0,sK3)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_228])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_235,plain,
    ( v4_pre_topc(k1_xboole_0,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_229,c_6])).

cnf(c_8,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_444,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_445,plain,
    ( v2_tex_2(X0,sK3)
    | ~ v4_pre_topc(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_595,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0)
    | sK3 != sK3
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_235,c_445])).

cnf(c_596,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X0,k1_xboole_0) != sK1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_292,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0)
    | sK3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_235])).

cnf(c_293,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | k9_subset_1(u1_struct_0(sK3),X0,k1_xboole_0) != sK1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_297,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_tex_2(X0,sK3)
    | k9_subset_1(u1_struct_0(sK3),X0,k1_xboole_0) != sK1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_293,c_17])).

cnf(c_298,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X0,k1_xboole_0) != sK1(sK3,X0) ),
    inference(renaming,[status(thm)],[c_297])).

cnf(c_311,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X0,k1_xboole_0) != sK1(sK3,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_298,c_6])).

cnf(c_598,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_tex_2(X0,sK3)
    | k9_subset_1(u1_struct_0(sK3),X0,k1_xboole_0) != sK1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_596,c_311])).

cnf(c_599,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X0,k1_xboole_0) != sK1(sK3,X0) ),
    inference(renaming,[status(thm)],[c_598])).

cnf(c_664,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X0,k1_xboole_0) != sK1(sK3,X0)
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_599])).

cnf(c_665,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),sK4,k1_xboole_0) != sK1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_664])).

cnf(c_667,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k1_xboole_0) != sK1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_665,c_15])).

cnf(c_708,plain,
    ( k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) != sK1(sK3,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_667,c_252])).

cnf(c_4,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_677,plain,
    ( k9_subset_1(X0,X1,X1) = X1
    | k1_zfmisc_1(X0) != X2
    | sK0(X2) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_5])).

cnf(c_678,plain,
    ( k9_subset_1(X0,X1,X1) = X1 ),
    inference(unflattening,[status(thm)],[c_677])).

cnf(c_709,plain,
    ( sK1(sK3,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_708,c_678])).

cnf(c_714,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_712,c_709])).

cnf(c_716,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_714])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:14:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.21/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.21/1.03  
% 1.21/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.21/1.03  
% 1.21/1.03  ------  iProver source info
% 1.21/1.03  
% 1.21/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.21/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.21/1.03  git: non_committed_changes: false
% 1.21/1.03  git: last_make_outside_of_git: false
% 1.21/1.03  
% 1.21/1.03  ------ 
% 1.21/1.03  
% 1.21/1.03  ------ Input Options
% 1.21/1.03  
% 1.21/1.03  --out_options                           all
% 1.21/1.03  --tptp_safe_out                         true
% 1.21/1.03  --problem_path                          ""
% 1.21/1.03  --include_path                          ""
% 1.21/1.03  --clausifier                            res/vclausify_rel
% 1.21/1.03  --clausifier_options                    --mode clausify
% 1.21/1.03  --stdin                                 false
% 1.21/1.03  --stats_out                             all
% 1.21/1.03  
% 1.21/1.03  ------ General Options
% 1.21/1.03  
% 1.21/1.03  --fof                                   false
% 1.21/1.03  --time_out_real                         305.
% 1.21/1.03  --time_out_virtual                      -1.
% 1.21/1.03  --symbol_type_check                     false
% 1.21/1.03  --clausify_out                          false
% 1.21/1.03  --sig_cnt_out                           false
% 1.21/1.03  --trig_cnt_out                          false
% 1.21/1.03  --trig_cnt_out_tolerance                1.
% 1.21/1.03  --trig_cnt_out_sk_spl                   false
% 1.21/1.03  --abstr_cl_out                          false
% 1.21/1.03  
% 1.21/1.03  ------ Global Options
% 1.21/1.03  
% 1.21/1.03  --schedule                              default
% 1.21/1.03  --add_important_lit                     false
% 1.21/1.03  --prop_solver_per_cl                    1000
% 1.21/1.03  --min_unsat_core                        false
% 1.21/1.03  --soft_assumptions                      false
% 1.21/1.03  --soft_lemma_size                       3
% 1.21/1.03  --prop_impl_unit_size                   0
% 1.21/1.03  --prop_impl_unit                        []
% 1.21/1.03  --share_sel_clauses                     true
% 1.21/1.03  --reset_solvers                         false
% 1.21/1.03  --bc_imp_inh                            [conj_cone]
% 1.21/1.03  --conj_cone_tolerance                   3.
% 1.21/1.03  --extra_neg_conj                        none
% 1.21/1.03  --large_theory_mode                     true
% 1.21/1.03  --prolific_symb_bound                   200
% 1.21/1.03  --lt_threshold                          2000
% 1.21/1.03  --clause_weak_htbl                      true
% 1.21/1.03  --gc_record_bc_elim                     false
% 1.21/1.03  
% 1.21/1.03  ------ Preprocessing Options
% 1.21/1.03  
% 1.21/1.03  --preprocessing_flag                    true
% 1.21/1.03  --time_out_prep_mult                    0.1
% 1.21/1.03  --splitting_mode                        input
% 1.21/1.03  --splitting_grd                         true
% 1.21/1.03  --splitting_cvd                         false
% 1.21/1.03  --splitting_cvd_svl                     false
% 1.21/1.03  --splitting_nvd                         32
% 1.21/1.03  --sub_typing                            true
% 1.21/1.03  --prep_gs_sim                           true
% 1.21/1.03  --prep_unflatten                        true
% 1.21/1.03  --prep_res_sim                          true
% 1.21/1.03  --prep_upred                            true
% 1.21/1.03  --prep_sem_filter                       exhaustive
% 1.21/1.03  --prep_sem_filter_out                   false
% 1.21/1.03  --pred_elim                             true
% 1.21/1.03  --res_sim_input                         true
% 1.21/1.03  --eq_ax_congr_red                       true
% 1.21/1.03  --pure_diseq_elim                       true
% 1.21/1.03  --brand_transform                       false
% 1.21/1.03  --non_eq_to_eq                          false
% 1.21/1.03  --prep_def_merge                        true
% 1.21/1.03  --prep_def_merge_prop_impl              false
% 1.21/1.03  --prep_def_merge_mbd                    true
% 1.21/1.03  --prep_def_merge_tr_red                 false
% 1.21/1.03  --prep_def_merge_tr_cl                  false
% 1.21/1.03  --smt_preprocessing                     true
% 1.21/1.03  --smt_ac_axioms                         fast
% 1.21/1.03  --preprocessed_out                      false
% 1.21/1.03  --preprocessed_stats                    false
% 1.21/1.03  
% 1.21/1.03  ------ Abstraction refinement Options
% 1.21/1.03  
% 1.21/1.03  --abstr_ref                             []
% 1.21/1.03  --abstr_ref_prep                        false
% 1.21/1.03  --abstr_ref_until_sat                   false
% 1.21/1.03  --abstr_ref_sig_restrict                funpre
% 1.21/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.21/1.03  --abstr_ref_under                       []
% 1.21/1.03  
% 1.21/1.03  ------ SAT Options
% 1.21/1.03  
% 1.21/1.03  --sat_mode                              false
% 1.21/1.03  --sat_fm_restart_options                ""
% 1.21/1.03  --sat_gr_def                            false
% 1.21/1.03  --sat_epr_types                         true
% 1.21/1.03  --sat_non_cyclic_types                  false
% 1.21/1.03  --sat_finite_models                     false
% 1.21/1.03  --sat_fm_lemmas                         false
% 1.21/1.03  --sat_fm_prep                           false
% 1.21/1.03  --sat_fm_uc_incr                        true
% 1.21/1.03  --sat_out_model                         small
% 1.21/1.03  --sat_out_clauses                       false
% 1.21/1.03  
% 1.21/1.03  ------ QBF Options
% 1.21/1.03  
% 1.21/1.03  --qbf_mode                              false
% 1.21/1.03  --qbf_elim_univ                         false
% 1.21/1.03  --qbf_dom_inst                          none
% 1.21/1.03  --qbf_dom_pre_inst                      false
% 1.21/1.03  --qbf_sk_in                             false
% 1.21/1.03  --qbf_pred_elim                         true
% 1.21/1.03  --qbf_split                             512
% 1.21/1.03  
% 1.21/1.03  ------ BMC1 Options
% 1.21/1.03  
% 1.21/1.03  --bmc1_incremental                      false
% 1.21/1.03  --bmc1_axioms                           reachable_all
% 1.21/1.03  --bmc1_min_bound                        0
% 1.21/1.03  --bmc1_max_bound                        -1
% 1.21/1.03  --bmc1_max_bound_default                -1
% 1.21/1.03  --bmc1_symbol_reachability              true
% 1.21/1.03  --bmc1_property_lemmas                  false
% 1.21/1.03  --bmc1_k_induction                      false
% 1.21/1.03  --bmc1_non_equiv_states                 false
% 1.21/1.03  --bmc1_deadlock                         false
% 1.21/1.03  --bmc1_ucm                              false
% 1.21/1.03  --bmc1_add_unsat_core                   none
% 1.21/1.03  --bmc1_unsat_core_children              false
% 1.21/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.21/1.03  --bmc1_out_stat                         full
% 1.21/1.03  --bmc1_ground_init                      false
% 1.21/1.03  --bmc1_pre_inst_next_state              false
% 1.21/1.03  --bmc1_pre_inst_state                   false
% 1.21/1.03  --bmc1_pre_inst_reach_state             false
% 1.21/1.03  --bmc1_out_unsat_core                   false
% 1.21/1.03  --bmc1_aig_witness_out                  false
% 1.21/1.03  --bmc1_verbose                          false
% 1.21/1.03  --bmc1_dump_clauses_tptp                false
% 1.21/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.21/1.03  --bmc1_dump_file                        -
% 1.21/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.21/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.21/1.03  --bmc1_ucm_extend_mode                  1
% 1.21/1.03  --bmc1_ucm_init_mode                    2
% 1.21/1.03  --bmc1_ucm_cone_mode                    none
% 1.21/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.21/1.03  --bmc1_ucm_relax_model                  4
% 1.21/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.21/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.21/1.03  --bmc1_ucm_layered_model                none
% 1.21/1.03  --bmc1_ucm_max_lemma_size               10
% 1.21/1.03  
% 1.21/1.03  ------ AIG Options
% 1.21/1.03  
% 1.21/1.03  --aig_mode                              false
% 1.21/1.03  
% 1.21/1.03  ------ Instantiation Options
% 1.21/1.03  
% 1.21/1.03  --instantiation_flag                    true
% 1.21/1.03  --inst_sos_flag                         false
% 1.21/1.03  --inst_sos_phase                        true
% 1.21/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.21/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.21/1.03  --inst_lit_sel_side                     num_symb
% 1.21/1.03  --inst_solver_per_active                1400
% 1.21/1.03  --inst_solver_calls_frac                1.
% 1.21/1.03  --inst_passive_queue_type               priority_queues
% 1.21/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.21/1.03  --inst_passive_queues_freq              [25;2]
% 1.21/1.03  --inst_dismatching                      true
% 1.21/1.03  --inst_eager_unprocessed_to_passive     true
% 1.21/1.03  --inst_prop_sim_given                   true
% 1.21/1.03  --inst_prop_sim_new                     false
% 1.21/1.03  --inst_subs_new                         false
% 1.21/1.03  --inst_eq_res_simp                      false
% 1.21/1.03  --inst_subs_given                       false
% 1.21/1.03  --inst_orphan_elimination               true
% 1.21/1.03  --inst_learning_loop_flag               true
% 1.21/1.03  --inst_learning_start                   3000
% 1.21/1.03  --inst_learning_factor                  2
% 1.21/1.03  --inst_start_prop_sim_after_learn       3
% 1.21/1.03  --inst_sel_renew                        solver
% 1.21/1.03  --inst_lit_activity_flag                true
% 1.21/1.03  --inst_restr_to_given                   false
% 1.21/1.03  --inst_activity_threshold               500
% 1.21/1.03  --inst_out_proof                        true
% 1.21/1.03  
% 1.21/1.03  ------ Resolution Options
% 1.21/1.03  
% 1.21/1.03  --resolution_flag                       true
% 1.21/1.03  --res_lit_sel                           adaptive
% 1.21/1.03  --res_lit_sel_side                      none
% 1.21/1.03  --res_ordering                          kbo
% 1.21/1.03  --res_to_prop_solver                    active
% 1.21/1.03  --res_prop_simpl_new                    false
% 1.21/1.03  --res_prop_simpl_given                  true
% 1.21/1.03  --res_passive_queue_type                priority_queues
% 1.21/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.21/1.03  --res_passive_queues_freq               [15;5]
% 1.21/1.03  --res_forward_subs                      full
% 1.21/1.03  --res_backward_subs                     full
% 1.21/1.03  --res_forward_subs_resolution           true
% 1.21/1.03  --res_backward_subs_resolution          true
% 1.21/1.03  --res_orphan_elimination                true
% 1.21/1.03  --res_time_limit                        2.
% 1.21/1.03  --res_out_proof                         true
% 1.21/1.03  
% 1.21/1.03  ------ Superposition Options
% 1.21/1.03  
% 1.21/1.03  --superposition_flag                    true
% 1.21/1.03  --sup_passive_queue_type                priority_queues
% 1.21/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.21/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.21/1.03  --demod_completeness_check              fast
% 1.21/1.03  --demod_use_ground                      true
% 1.21/1.03  --sup_to_prop_solver                    passive
% 1.21/1.03  --sup_prop_simpl_new                    true
% 1.21/1.03  --sup_prop_simpl_given                  true
% 1.21/1.03  --sup_fun_splitting                     false
% 1.21/1.03  --sup_smt_interval                      50000
% 1.21/1.03  
% 1.21/1.03  ------ Superposition Simplification Setup
% 1.21/1.03  
% 1.21/1.03  --sup_indices_passive                   []
% 1.21/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.21/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/1.03  --sup_full_bw                           [BwDemod]
% 1.21/1.03  --sup_immed_triv                        [TrivRules]
% 1.21/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.21/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/1.03  --sup_immed_bw_main                     []
% 1.21/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.21/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.21/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.21/1.03  
% 1.21/1.03  ------ Combination Options
% 1.21/1.03  
% 1.21/1.03  --comb_res_mult                         3
% 1.21/1.03  --comb_sup_mult                         2
% 1.21/1.03  --comb_inst_mult                        10
% 1.21/1.03  
% 1.21/1.03  ------ Debug Options
% 1.21/1.03  
% 1.21/1.03  --dbg_backtrace                         false
% 1.21/1.03  --dbg_dump_prop_clauses                 false
% 1.21/1.03  --dbg_dump_prop_clauses_file            -
% 1.21/1.03  --dbg_out_stat                          false
% 1.21/1.03  ------ Parsing...
% 1.21/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.21/1.03  
% 1.21/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.21/1.03  
% 1.21/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.21/1.03  
% 1.21/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 1.21/1.03  ------ Proving...
% 1.21/1.03  ------ Problem Properties 
% 1.21/1.03  
% 1.21/1.03  
% 1.21/1.03  clauses                                 6
% 1.21/1.03  conjectures                             0
% 1.21/1.03  EPR                                     1
% 1.21/1.03  Horn                                    6
% 1.21/1.03  unary                                   6
% 1.21/1.03  binary                                  0
% 1.21/1.03  lits                                    6
% 1.21/1.03  lits eq                                 6
% 1.21/1.03  fd_pure                                 0
% 1.21/1.03  fd_pseudo                               0
% 1.21/1.03  fd_cond                                 0
% 1.21/1.03  fd_pseudo_cond                          0
% 1.21/1.03  AC symbols                              0
% 1.21/1.03  
% 1.21/1.03  ------ Schedule UEQ
% 1.21/1.03  
% 1.21/1.03  ------ pure equality problem: resolution off 
% 1.21/1.03  
% 1.21/1.03  ------ Option_UEQ Time Limit: Unbounded
% 1.21/1.03  
% 1.21/1.03  
% 1.21/1.03  ------ 
% 1.21/1.03  Current options:
% 1.21/1.03  ------ 
% 1.21/1.03  
% 1.21/1.03  ------ Input Options
% 1.21/1.03  
% 1.21/1.03  --out_options                           all
% 1.21/1.03  --tptp_safe_out                         true
% 1.21/1.03  --problem_path                          ""
% 1.21/1.03  --include_path                          ""
% 1.21/1.03  --clausifier                            res/vclausify_rel
% 1.21/1.03  --clausifier_options                    --mode clausify
% 1.21/1.03  --stdin                                 false
% 1.21/1.03  --stats_out                             all
% 1.21/1.03  
% 1.21/1.03  ------ General Options
% 1.21/1.03  
% 1.21/1.03  --fof                                   false
% 1.21/1.03  --time_out_real                         305.
% 1.21/1.03  --time_out_virtual                      -1.
% 1.21/1.03  --symbol_type_check                     false
% 1.21/1.03  --clausify_out                          false
% 1.21/1.03  --sig_cnt_out                           false
% 1.21/1.03  --trig_cnt_out                          false
% 1.21/1.03  --trig_cnt_out_tolerance                1.
% 1.21/1.03  --trig_cnt_out_sk_spl                   false
% 1.21/1.03  --abstr_cl_out                          false
% 1.21/1.03  
% 1.21/1.03  ------ Global Options
% 1.21/1.03  
% 1.21/1.03  --schedule                              default
% 1.21/1.03  --add_important_lit                     false
% 1.21/1.03  --prop_solver_per_cl                    1000
% 1.21/1.03  --min_unsat_core                        false
% 1.21/1.03  --soft_assumptions                      false
% 1.21/1.03  --soft_lemma_size                       3
% 1.21/1.03  --prop_impl_unit_size                   0
% 1.21/1.03  --prop_impl_unit                        []
% 1.21/1.03  --share_sel_clauses                     true
% 1.21/1.03  --reset_solvers                         false
% 1.21/1.03  --bc_imp_inh                            [conj_cone]
% 1.21/1.03  --conj_cone_tolerance                   3.
% 1.21/1.03  --extra_neg_conj                        none
% 1.21/1.03  --large_theory_mode                     true
% 1.21/1.03  --prolific_symb_bound                   200
% 1.21/1.03  --lt_threshold                          2000
% 1.21/1.03  --clause_weak_htbl                      true
% 1.21/1.03  --gc_record_bc_elim                     false
% 1.21/1.03  
% 1.21/1.03  ------ Preprocessing Options
% 1.21/1.03  
% 1.21/1.03  --preprocessing_flag                    true
% 1.21/1.03  --time_out_prep_mult                    0.1
% 1.21/1.03  --splitting_mode                        input
% 1.21/1.03  --splitting_grd                         true
% 1.21/1.03  --splitting_cvd                         false
% 1.21/1.03  --splitting_cvd_svl                     false
% 1.21/1.03  --splitting_nvd                         32
% 1.21/1.03  --sub_typing                            true
% 1.21/1.03  --prep_gs_sim                           true
% 1.21/1.03  --prep_unflatten                        true
% 1.21/1.03  --prep_res_sim                          true
% 1.21/1.03  --prep_upred                            true
% 1.21/1.03  --prep_sem_filter                       exhaustive
% 1.21/1.03  --prep_sem_filter_out                   false
% 1.21/1.03  --pred_elim                             true
% 1.21/1.03  --res_sim_input                         true
% 1.21/1.03  --eq_ax_congr_red                       true
% 1.21/1.03  --pure_diseq_elim                       true
% 1.21/1.03  --brand_transform                       false
% 1.21/1.03  --non_eq_to_eq                          false
% 1.21/1.03  --prep_def_merge                        true
% 1.21/1.03  --prep_def_merge_prop_impl              false
% 1.21/1.03  --prep_def_merge_mbd                    true
% 1.21/1.03  --prep_def_merge_tr_red                 false
% 1.21/1.03  --prep_def_merge_tr_cl                  false
% 1.21/1.03  --smt_preprocessing                     true
% 1.21/1.03  --smt_ac_axioms                         fast
% 1.21/1.03  --preprocessed_out                      false
% 1.21/1.03  --preprocessed_stats                    false
% 1.21/1.03  
% 1.21/1.03  ------ Abstraction refinement Options
% 1.21/1.03  
% 1.21/1.03  --abstr_ref                             []
% 1.21/1.03  --abstr_ref_prep                        false
% 1.21/1.03  --abstr_ref_until_sat                   false
% 1.21/1.03  --abstr_ref_sig_restrict                funpre
% 1.21/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.21/1.03  --abstr_ref_under                       []
% 1.21/1.03  
% 1.21/1.03  ------ SAT Options
% 1.21/1.03  
% 1.21/1.03  --sat_mode                              false
% 1.21/1.03  --sat_fm_restart_options                ""
% 1.21/1.03  --sat_gr_def                            false
% 1.21/1.03  --sat_epr_types                         true
% 1.21/1.03  --sat_non_cyclic_types                  false
% 1.21/1.03  --sat_finite_models                     false
% 1.21/1.03  --sat_fm_lemmas                         false
% 1.21/1.03  --sat_fm_prep                           false
% 1.21/1.03  --sat_fm_uc_incr                        true
% 1.21/1.03  --sat_out_model                         small
% 1.21/1.03  --sat_out_clauses                       false
% 1.21/1.03  
% 1.21/1.03  ------ QBF Options
% 1.21/1.03  
% 1.21/1.03  --qbf_mode                              false
% 1.21/1.03  --qbf_elim_univ                         false
% 1.21/1.03  --qbf_dom_inst                          none
% 1.21/1.03  --qbf_dom_pre_inst                      false
% 1.21/1.03  --qbf_sk_in                             false
% 1.21/1.03  --qbf_pred_elim                         true
% 1.21/1.03  --qbf_split                             512
% 1.21/1.03  
% 1.21/1.03  ------ BMC1 Options
% 1.21/1.03  
% 1.21/1.03  --bmc1_incremental                      false
% 1.21/1.03  --bmc1_axioms                           reachable_all
% 1.21/1.03  --bmc1_min_bound                        0
% 1.21/1.03  --bmc1_max_bound                        -1
% 1.21/1.03  --bmc1_max_bound_default                -1
% 1.21/1.03  --bmc1_symbol_reachability              true
% 1.21/1.03  --bmc1_property_lemmas                  false
% 1.21/1.03  --bmc1_k_induction                      false
% 1.21/1.03  --bmc1_non_equiv_states                 false
% 1.21/1.03  --bmc1_deadlock                         false
% 1.21/1.03  --bmc1_ucm                              false
% 1.21/1.03  --bmc1_add_unsat_core                   none
% 1.21/1.03  --bmc1_unsat_core_children              false
% 1.21/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.21/1.03  --bmc1_out_stat                         full
% 1.21/1.03  --bmc1_ground_init                      false
% 1.21/1.03  --bmc1_pre_inst_next_state              false
% 1.21/1.03  --bmc1_pre_inst_state                   false
% 1.21/1.03  --bmc1_pre_inst_reach_state             false
% 1.21/1.03  --bmc1_out_unsat_core                   false
% 1.21/1.03  --bmc1_aig_witness_out                  false
% 1.21/1.03  --bmc1_verbose                          false
% 1.21/1.03  --bmc1_dump_clauses_tptp                false
% 1.21/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.21/1.03  --bmc1_dump_file                        -
% 1.21/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.21/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.21/1.03  --bmc1_ucm_extend_mode                  1
% 1.21/1.03  --bmc1_ucm_init_mode                    2
% 1.21/1.03  --bmc1_ucm_cone_mode                    none
% 1.21/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.21/1.03  --bmc1_ucm_relax_model                  4
% 1.21/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.21/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.21/1.03  --bmc1_ucm_layered_model                none
% 1.21/1.03  --bmc1_ucm_max_lemma_size               10
% 1.21/1.03  
% 1.21/1.03  ------ AIG Options
% 1.21/1.03  
% 1.21/1.03  --aig_mode                              false
% 1.21/1.03  
% 1.21/1.03  ------ Instantiation Options
% 1.21/1.03  
% 1.21/1.03  --instantiation_flag                    false
% 1.21/1.03  --inst_sos_flag                         false
% 1.21/1.03  --inst_sos_phase                        true
% 1.21/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.21/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.21/1.03  --inst_lit_sel_side                     num_symb
% 1.21/1.03  --inst_solver_per_active                1400
% 1.21/1.03  --inst_solver_calls_frac                1.
% 1.21/1.03  --inst_passive_queue_type               priority_queues
% 1.21/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.21/1.03  --inst_passive_queues_freq              [25;2]
% 1.21/1.03  --inst_dismatching                      true
% 1.21/1.03  --inst_eager_unprocessed_to_passive     true
% 1.21/1.03  --inst_prop_sim_given                   true
% 1.21/1.03  --inst_prop_sim_new                     false
% 1.21/1.03  --inst_subs_new                         false
% 1.21/1.03  --inst_eq_res_simp                      false
% 1.21/1.03  --inst_subs_given                       false
% 1.21/1.03  --inst_orphan_elimination               true
% 1.21/1.03  --inst_learning_loop_flag               true
% 1.21/1.03  --inst_learning_start                   3000
% 1.21/1.03  --inst_learning_factor                  2
% 1.21/1.03  --inst_start_prop_sim_after_learn       3
% 1.21/1.03  --inst_sel_renew                        solver
% 1.21/1.03  --inst_lit_activity_flag                true
% 1.21/1.03  --inst_restr_to_given                   false
% 1.21/1.03  --inst_activity_threshold               500
% 1.21/1.03  --inst_out_proof                        true
% 1.21/1.03  
% 1.21/1.03  ------ Resolution Options
% 1.21/1.03  
% 1.21/1.03  --resolution_flag                       false
% 1.21/1.03  --res_lit_sel                           adaptive
% 1.21/1.03  --res_lit_sel_side                      none
% 1.21/1.03  --res_ordering                          kbo
% 1.21/1.03  --res_to_prop_solver                    active
% 1.21/1.03  --res_prop_simpl_new                    false
% 1.21/1.03  --res_prop_simpl_given                  true
% 1.21/1.03  --res_passive_queue_type                priority_queues
% 1.21/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.21/1.03  --res_passive_queues_freq               [15;5]
% 1.21/1.03  --res_forward_subs                      full
% 1.21/1.03  --res_backward_subs                     full
% 1.21/1.03  --res_forward_subs_resolution           true
% 1.21/1.03  --res_backward_subs_resolution          true
% 1.21/1.03  --res_orphan_elimination                true
% 1.21/1.03  --res_time_limit                        2.
% 1.21/1.03  --res_out_proof                         true
% 1.21/1.03  
% 1.21/1.03  ------ Superposition Options
% 1.21/1.03  
% 1.21/1.03  --superposition_flag                    true
% 1.21/1.03  --sup_passive_queue_type                priority_queues
% 1.21/1.03  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.21/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.21/1.03  --demod_completeness_check              fast
% 1.21/1.03  --demod_use_ground                      true
% 1.21/1.03  --sup_to_prop_solver                    active
% 1.21/1.03  --sup_prop_simpl_new                    false
% 1.21/1.03  --sup_prop_simpl_given                  false
% 1.21/1.03  --sup_fun_splitting                     true
% 1.21/1.03  --sup_smt_interval                      10000
% 1.21/1.03  
% 1.21/1.03  ------ Superposition Simplification Setup
% 1.21/1.03  
% 1.21/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 1.21/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 1.21/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 1.21/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/1.03  --sup_full_triv                         [TrivRules]
% 1.21/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 1.21/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 1.21/1.03  --sup_immed_triv                        [TrivRules]
% 1.21/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.21/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 1.21/1.03  --sup_immed_bw_main                     []
% 1.21/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 1.21/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.21/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 1.21/1.03  --sup_input_bw                          [BwDemod;BwSubsumption]
% 1.21/1.03  
% 1.21/1.03  ------ Combination Options
% 1.21/1.03  
% 1.21/1.03  --comb_res_mult                         1
% 1.21/1.03  --comb_sup_mult                         1
% 1.21/1.03  --comb_inst_mult                        1000000
% 1.21/1.03  
% 1.21/1.03  ------ Debug Options
% 1.21/1.03  
% 1.21/1.03  --dbg_backtrace                         false
% 1.21/1.03  --dbg_dump_prop_clauses                 false
% 1.21/1.03  --dbg_dump_prop_clauses_file            -
% 1.21/1.03  --dbg_out_stat                          false
% 1.21/1.03  
% 1.21/1.03  
% 1.21/1.03  
% 1.21/1.03  
% 1.21/1.03  ------ Proving...
% 1.21/1.03  
% 1.21/1.03  
% 1.21/1.03  % SZS status Theorem for theBenchmark.p
% 1.21/1.03  
% 1.21/1.03   Resolution empty clause
% 1.21/1.03  
% 1.21/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.21/1.03  
% 1.21/1.03  fof(f11,conjecture,(
% 1.21/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.21/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.03  
% 1.21/1.03  fof(f12,negated_conjecture,(
% 1.21/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.21/1.03    inference(negated_conjecture,[],[f11])).
% 1.21/1.03  
% 1.21/1.03  fof(f13,plain,(
% 1.21/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 1.21/1.03    inference(pure_predicate_removal,[],[f12])).
% 1.21/1.03  
% 1.21/1.03  fof(f22,plain,(
% 1.21/1.03    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.21/1.03    inference(ennf_transformation,[],[f13])).
% 1.21/1.03  
% 1.21/1.03  fof(f23,plain,(
% 1.21/1.03    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.21/1.03    inference(flattening,[],[f22])).
% 1.21/1.03  
% 1.21/1.03  fof(f32,plain,(
% 1.21/1.03    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK4))) )),
% 1.21/1.03    introduced(choice_axiom,[])).
% 1.21/1.03  
% 1.21/1.03  fof(f31,plain,(
% 1.21/1.03    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))),
% 1.21/1.03    introduced(choice_axiom,[])).
% 1.21/1.03  
% 1.21/1.03  fof(f33,plain,(
% 1.21/1.03    (~v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)),
% 1.21/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f32,f31])).
% 1.21/1.03  
% 1.21/1.03  fof(f52,plain,(
% 1.21/1.03    ~v2_tex_2(sK4,sK3)),
% 1.21/1.03    inference(cnf_transformation,[],[f33])).
% 1.21/1.03  
% 1.21/1.03  fof(f3,axiom,(
% 1.21/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.21/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.03  
% 1.21/1.03  fof(f16,plain,(
% 1.21/1.03    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.21/1.03    inference(ennf_transformation,[],[f3])).
% 1.21/1.03  
% 1.21/1.03  fof(f36,plain,(
% 1.21/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.21/1.03    inference(cnf_transformation,[],[f16])).
% 1.21/1.03  
% 1.21/1.03  fof(f10,axiom,(
% 1.21/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.21/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.03  
% 1.21/1.03  fof(f20,plain,(
% 1.21/1.03    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.21/1.03    inference(ennf_transformation,[],[f10])).
% 1.21/1.03  
% 1.21/1.03  fof(f21,plain,(
% 1.21/1.03    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.21/1.03    inference(flattening,[],[f20])).
% 1.21/1.03  
% 1.21/1.03  fof(f26,plain,(
% 1.21/1.03    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.21/1.03    inference(nnf_transformation,[],[f21])).
% 1.21/1.03  
% 1.21/1.03  fof(f27,plain,(
% 1.21/1.03    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.21/1.03    inference(rectify,[],[f26])).
% 1.21/1.03  
% 1.21/1.03  fof(f29,plain,(
% 1.21/1.03    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 & v4_pre_topc(sK2(X0,X1,X4),X0) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.21/1.03    introduced(choice_axiom,[])).
% 1.21/1.03  
% 1.21/1.03  fof(f28,plain,(
% 1.21/1.03    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.21/1.03    introduced(choice_axiom,[])).
% 1.21/1.03  
% 1.21/1.03  fof(f30,plain,(
% 1.21/1.03    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 & v4_pre_topc(sK2(X0,X1,X4),X0) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.21/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f29,f28])).
% 1.21/1.03  
% 1.21/1.03  fof(f46,plain,(
% 1.21/1.03    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.21/1.03    inference(cnf_transformation,[],[f30])).
% 1.21/1.03  
% 1.21/1.03  fof(f49,plain,(
% 1.21/1.03    l1_pre_topc(sK3)),
% 1.21/1.03    inference(cnf_transformation,[],[f33])).
% 1.21/1.03  
% 1.21/1.03  fof(f51,plain,(
% 1.21/1.03    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.21/1.03    inference(cnf_transformation,[],[f33])).
% 1.21/1.03  
% 1.21/1.03  fof(f2,axiom,(
% 1.21/1.03    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.21/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.03  
% 1.21/1.03  fof(f15,plain,(
% 1.21/1.03    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.21/1.03    inference(ennf_transformation,[],[f2])).
% 1.21/1.03  
% 1.21/1.03  fof(f35,plain,(
% 1.21/1.03    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.21/1.03    inference(cnf_transformation,[],[f15])).
% 1.21/1.03  
% 1.21/1.03  fof(f50,plain,(
% 1.21/1.03    v1_xboole_0(sK4)),
% 1.21/1.03    inference(cnf_transformation,[],[f33])).
% 1.21/1.03  
% 1.21/1.03  fof(f4,axiom,(
% 1.21/1.03    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.21/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.03  
% 1.21/1.03  fof(f37,plain,(
% 1.21/1.03    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.21/1.03    inference(cnf_transformation,[],[f4])).
% 1.21/1.03  
% 1.21/1.03  fof(f1,axiom,(
% 1.21/1.03    v1_xboole_0(k1_xboole_0)),
% 1.21/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.03  
% 1.21/1.03  fof(f34,plain,(
% 1.21/1.03    v1_xboole_0(k1_xboole_0)),
% 1.21/1.03    inference(cnf_transformation,[],[f1])).
% 1.21/1.03  
% 1.21/1.03  fof(f9,axiom,(
% 1.21/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 1.21/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.03  
% 1.21/1.03  fof(f18,plain,(
% 1.21/1.03    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.21/1.03    inference(ennf_transformation,[],[f9])).
% 1.21/1.03  
% 1.21/1.03  fof(f19,plain,(
% 1.21/1.03    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.21/1.03    inference(flattening,[],[f18])).
% 1.21/1.03  
% 1.21/1.03  fof(f41,plain,(
% 1.21/1.03    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.21/1.03    inference(cnf_transformation,[],[f19])).
% 1.21/1.03  
% 1.21/1.03  fof(f48,plain,(
% 1.21/1.03    v2_pre_topc(sK3)),
% 1.21/1.03    inference(cnf_transformation,[],[f33])).
% 1.21/1.03  
% 1.21/1.03  fof(f7,axiom,(
% 1.21/1.03    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.21/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.03  
% 1.21/1.03  fof(f40,plain,(
% 1.21/1.03    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.21/1.03    inference(cnf_transformation,[],[f7])).
% 1.21/1.03  
% 1.21/1.03  fof(f47,plain,(
% 1.21/1.03    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.21/1.03    inference(cnf_transformation,[],[f30])).
% 1.21/1.03  
% 1.21/1.03  fof(f5,axiom,(
% 1.21/1.03    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 1.21/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.03  
% 1.21/1.03  fof(f24,plain,(
% 1.21/1.03    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 1.21/1.03    introduced(choice_axiom,[])).
% 1.21/1.03  
% 1.21/1.03  fof(f25,plain,(
% 1.21/1.03    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 1.21/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f24])).
% 1.21/1.03  
% 1.21/1.03  fof(f38,plain,(
% 1.21/1.03    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 1.21/1.03    inference(cnf_transformation,[],[f25])).
% 1.21/1.03  
% 1.21/1.03  fof(f6,axiom,(
% 1.21/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 1.21/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.21/1.03  
% 1.21/1.03  fof(f17,plain,(
% 1.21/1.03    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.21/1.03    inference(ennf_transformation,[],[f6])).
% 1.21/1.03  
% 1.21/1.03  fof(f39,plain,(
% 1.21/1.03    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.21/1.03    inference(cnf_transformation,[],[f17])).
% 1.21/1.03  
% 1.21/1.03  cnf(c_14,negated_conjecture,
% 1.21/1.03      ( ~ v2_tex_2(sK4,sK3) ),
% 1.21/1.03      inference(cnf_transformation,[],[f52]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_2,plain,
% 1.21/1.03      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 1.21/1.03      inference(cnf_transformation,[],[f36]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_9,plain,
% 1.21/1.03      ( v2_tex_2(X0,X1)
% 1.21/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.21/1.03      | r1_tarski(sK1(X1,X0),X0)
% 1.21/1.03      | ~ l1_pre_topc(X1) ),
% 1.21/1.03      inference(cnf_transformation,[],[f46]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_17,negated_conjecture,
% 1.21/1.03      ( l1_pre_topc(sK3) ),
% 1.21/1.03      inference(cnf_transformation,[],[f49]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_429,plain,
% 1.21/1.03      ( v2_tex_2(X0,X1)
% 1.21/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.21/1.03      | r1_tarski(sK1(X1,X0),X0)
% 1.21/1.03      | sK3 != X1 ),
% 1.21/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_430,plain,
% 1.21/1.03      ( v2_tex_2(X0,sK3)
% 1.21/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | r1_tarski(sK1(sK3,X0),X0) ),
% 1.21/1.03      inference(unflattening,[status(thm)],[c_429]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_570,plain,
% 1.21/1.03      ( v2_tex_2(X0,sK3)
% 1.21/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | X0 != X1
% 1.21/1.03      | sK1(sK3,X0) != X2
% 1.21/1.03      | k2_xboole_0(X2,X1) = X1 ),
% 1.21/1.03      inference(resolution_lifted,[status(thm)],[c_2,c_430]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_571,plain,
% 1.21/1.03      ( v2_tex_2(X0,sK3)
% 1.21/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | k2_xboole_0(sK1(sK3,X0),X0) = X0 ),
% 1.21/1.03      inference(unflattening,[status(thm)],[c_570]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_637,plain,
% 1.21/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | k2_xboole_0(sK1(sK3,X0),X0) = X0
% 1.21/1.03      | sK3 != sK3
% 1.21/1.03      | sK4 != X0 ),
% 1.21/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_571]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_638,plain,
% 1.21/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | k2_xboole_0(sK1(sK3,sK4),sK4) = sK4 ),
% 1.21/1.03      inference(unflattening,[status(thm)],[c_637]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_15,negated_conjecture,
% 1.21/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.21/1.03      inference(cnf_transformation,[],[f51]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_640,plain,
% 1.21/1.03      ( k2_xboole_0(sK1(sK3,sK4),sK4) = sK4 ),
% 1.21/1.03      inference(global_propositional_subsumption,[status(thm)],[c_638,c_15]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_1,plain,
% 1.21/1.03      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.21/1.03      inference(cnf_transformation,[],[f35]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_16,negated_conjecture,
% 1.21/1.03      ( v1_xboole_0(sK4) ),
% 1.21/1.03      inference(cnf_transformation,[],[f50]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_251,plain,
% 1.21/1.03      ( sK4 != X0 | k1_xboole_0 = X0 ),
% 1.21/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_16]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_252,plain,
% 1.21/1.03      ( k1_xboole_0 = sK4 ),
% 1.21/1.03      inference(unflattening,[status(thm)],[c_251]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_707,plain,
% 1.21/1.03      ( k2_xboole_0(sK1(sK3,k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 1.21/1.03      inference(light_normalisation,[status(thm)],[c_640,c_252]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_3,plain,
% 1.21/1.03      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.21/1.03      inference(cnf_transformation,[],[f37]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_712,plain,
% 1.21/1.03      ( sK1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 1.21/1.03      inference(superposition,[status(thm)],[c_707,c_3]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_0,plain,
% 1.21/1.03      ( v1_xboole_0(k1_xboole_0) ),
% 1.21/1.03      inference(cnf_transformation,[],[f34]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_7,plain,
% 1.21/1.03      ( v4_pre_topc(X0,X1)
% 1.21/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.21/1.03      | ~ v2_pre_topc(X1)
% 1.21/1.03      | ~ l1_pre_topc(X1)
% 1.21/1.03      | ~ v1_xboole_0(X0) ),
% 1.21/1.03      inference(cnf_transformation,[],[f41]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_18,negated_conjecture,
% 1.21/1.03      ( v2_pre_topc(sK3) ),
% 1.21/1.03      inference(cnf_transformation,[],[f48]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_203,plain,
% 1.21/1.03      ( v4_pre_topc(X0,X1)
% 1.21/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.21/1.03      | ~ l1_pre_topc(X1)
% 1.21/1.03      | ~ v1_xboole_0(X0)
% 1.21/1.03      | sK3 != X1 ),
% 1.21/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_204,plain,
% 1.21/1.03      ( v4_pre_topc(X0,sK3)
% 1.21/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | ~ l1_pre_topc(sK3)
% 1.21/1.03      | ~ v1_xboole_0(X0) ),
% 1.21/1.03      inference(unflattening,[status(thm)],[c_203]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_208,plain,
% 1.21/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | v4_pre_topc(X0,sK3)
% 1.21/1.03      | ~ v1_xboole_0(X0) ),
% 1.21/1.03      inference(global_propositional_subsumption,[status(thm)],[c_204,c_17]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_209,plain,
% 1.21/1.03      ( v4_pre_topc(X0,sK3)
% 1.21/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | ~ v1_xboole_0(X0) ),
% 1.21/1.03      inference(renaming,[status(thm)],[c_208]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_228,plain,
% 1.21/1.03      ( v4_pre_topc(X0,sK3)
% 1.21/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | k1_xboole_0 != X0 ),
% 1.21/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_209]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_229,plain,
% 1.21/1.03      ( v4_pre_topc(k1_xboole_0,sK3)
% 1.21/1.03      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.21/1.03      inference(unflattening,[status(thm)],[c_228]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_6,plain,
% 1.21/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.21/1.03      inference(cnf_transformation,[],[f40]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_235,plain,
% 1.21/1.03      ( v4_pre_topc(k1_xboole_0,sK3) ),
% 1.21/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_229,c_6]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_8,plain,
% 1.21/1.03      ( v2_tex_2(X0,X1)
% 1.21/1.03      | ~ v4_pre_topc(X2,X1)
% 1.21/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.21/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.21/1.03      | ~ l1_pre_topc(X1)
% 1.21/1.03      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0) ),
% 1.21/1.03      inference(cnf_transformation,[],[f47]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_444,plain,
% 1.21/1.03      ( v2_tex_2(X0,X1)
% 1.21/1.03      | ~ v4_pre_topc(X2,X1)
% 1.21/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.21/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.21/1.03      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0)
% 1.21/1.03      | sK3 != X1 ),
% 1.21/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_445,plain,
% 1.21/1.03      ( v2_tex_2(X0,sK3)
% 1.21/1.03      | ~ v4_pre_topc(X1,sK3)
% 1.21/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0) ),
% 1.21/1.03      inference(unflattening,[status(thm)],[c_444]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_595,plain,
% 1.21/1.03      ( v2_tex_2(X0,sK3)
% 1.21/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0)
% 1.21/1.03      | sK3 != sK3
% 1.21/1.03      | k1_xboole_0 != X1 ),
% 1.21/1.03      inference(resolution_lifted,[status(thm)],[c_235,c_445]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_596,plain,
% 1.21/1.03      ( v2_tex_2(X0,sK3)
% 1.21/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | k9_subset_1(u1_struct_0(sK3),X0,k1_xboole_0) != sK1(sK3,X0) ),
% 1.21/1.03      inference(unflattening,[status(thm)],[c_595]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_292,plain,
% 1.21/1.03      ( v2_tex_2(X0,X1)
% 1.21/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.21/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.21/1.03      | ~ l1_pre_topc(X1)
% 1.21/1.03      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0)
% 1.21/1.03      | sK3 != X1
% 1.21/1.03      | k1_xboole_0 != X2 ),
% 1.21/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_235]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_293,plain,
% 1.21/1.03      ( v2_tex_2(X0,sK3)
% 1.21/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | ~ l1_pre_topc(sK3)
% 1.21/1.03      | k9_subset_1(u1_struct_0(sK3),X0,k1_xboole_0) != sK1(sK3,X0) ),
% 1.21/1.03      inference(unflattening,[status(thm)],[c_292]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_297,plain,
% 1.21/1.03      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | v2_tex_2(X0,sK3)
% 1.21/1.03      | k9_subset_1(u1_struct_0(sK3),X0,k1_xboole_0) != sK1(sK3,X0) ),
% 1.21/1.03      inference(global_propositional_subsumption,[status(thm)],[c_293,c_17]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_298,plain,
% 1.21/1.03      ( v2_tex_2(X0,sK3)
% 1.21/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | k9_subset_1(u1_struct_0(sK3),X0,k1_xboole_0) != sK1(sK3,X0) ),
% 1.21/1.03      inference(renaming,[status(thm)],[c_297]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_311,plain,
% 1.21/1.03      ( v2_tex_2(X0,sK3)
% 1.21/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | k9_subset_1(u1_struct_0(sK3),X0,k1_xboole_0) != sK1(sK3,X0) ),
% 1.21/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_298,c_6]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_598,plain,
% 1.21/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | v2_tex_2(X0,sK3)
% 1.21/1.03      | k9_subset_1(u1_struct_0(sK3),X0,k1_xboole_0) != sK1(sK3,X0) ),
% 1.21/1.03      inference(global_propositional_subsumption,[status(thm)],[c_596,c_311]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_599,plain,
% 1.21/1.03      ( v2_tex_2(X0,sK3)
% 1.21/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | k9_subset_1(u1_struct_0(sK3),X0,k1_xboole_0) != sK1(sK3,X0) ),
% 1.21/1.03      inference(renaming,[status(thm)],[c_598]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_664,plain,
% 1.21/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | k9_subset_1(u1_struct_0(sK3),X0,k1_xboole_0) != sK1(sK3,X0)
% 1.21/1.03      | sK3 != sK3
% 1.21/1.03      | sK4 != X0 ),
% 1.21/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_599]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_665,plain,
% 1.21/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.21/1.03      | k9_subset_1(u1_struct_0(sK3),sK4,k1_xboole_0) != sK1(sK3,sK4) ),
% 1.21/1.03      inference(unflattening,[status(thm)],[c_664]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_667,plain,
% 1.21/1.03      ( k9_subset_1(u1_struct_0(sK3),sK4,k1_xboole_0) != sK1(sK3,sK4) ),
% 1.21/1.03      inference(global_propositional_subsumption,[status(thm)],[c_665,c_15]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_708,plain,
% 1.21/1.03      ( k9_subset_1(u1_struct_0(sK3),k1_xboole_0,k1_xboole_0) != sK1(sK3,k1_xboole_0) ),
% 1.21/1.03      inference(light_normalisation,[status(thm)],[c_667,c_252]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_4,plain,
% 1.21/1.03      ( m1_subset_1(sK0(X0),X0) ),
% 1.21/1.03      inference(cnf_transformation,[],[f38]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_5,plain,
% 1.21/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k9_subset_1(X1,X2,X2) = X2 ),
% 1.21/1.03      inference(cnf_transformation,[],[f39]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_677,plain,
% 1.21/1.03      ( k9_subset_1(X0,X1,X1) = X1 | k1_zfmisc_1(X0) != X2 | sK0(X2) != X3 ),
% 1.21/1.03      inference(resolution_lifted,[status(thm)],[c_4,c_5]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_678,plain,
% 1.21/1.03      ( k9_subset_1(X0,X1,X1) = X1 ),
% 1.21/1.03      inference(unflattening,[status(thm)],[c_677]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_709,plain,
% 1.21/1.03      ( sK1(sK3,k1_xboole_0) != k1_xboole_0 ),
% 1.21/1.03      inference(demodulation,[status(thm)],[c_708,c_678]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_714,plain,
% 1.21/1.03      ( k1_xboole_0 != k1_xboole_0 ),
% 1.21/1.03      inference(demodulation,[status(thm)],[c_712,c_709]) ).
% 1.21/1.03  
% 1.21/1.03  cnf(c_716,plain,
% 1.21/1.03      ( $false ),
% 1.21/1.03      inference(equality_resolution_simp,[status(thm)],[c_714]) ).
% 1.21/1.03  
% 1.21/1.03  
% 1.21/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.21/1.03  
% 1.21/1.03  ------                               Statistics
% 1.21/1.03  
% 1.21/1.03  ------ General
% 1.21/1.03  
% 1.21/1.03  abstr_ref_over_cycles:                  0
% 1.21/1.03  abstr_ref_under_cycles:                 0
% 1.21/1.03  gc_basic_clause_elim:                   0
% 1.21/1.03  forced_gc_time:                         0
% 1.21/1.03  parsing_time:                           0.007
% 1.21/1.03  unif_index_cands_time:                  0.
% 1.21/1.03  unif_index_add_time:                    0.
% 1.21/1.03  orderings_time:                         0.
% 1.21/1.03  out_proof_time:                         0.01
% 1.21/1.03  total_time:                             0.055
% 1.21/1.03  num_of_symbols:                         48
% 1.21/1.03  num_of_terms:                           723
% 1.21/1.03  
% 1.21/1.03  ------ Preprocessing
% 1.21/1.03  
% 1.21/1.03  num_of_splits:                          0
% 1.21/1.03  num_of_split_atoms:                     0
% 1.21/1.03  num_of_reused_defs:                     0
% 1.21/1.03  num_eq_ax_congr_red:                    10
% 1.21/1.03  num_of_sem_filtered_clauses:            0
% 1.21/1.03  num_of_subtypes:                        0
% 1.21/1.03  monotx_restored_types:                  0
% 1.21/1.03  sat_num_of_epr_types:                   0
% 1.21/1.03  sat_num_of_non_cyclic_types:            0
% 1.21/1.03  sat_guarded_non_collapsed_types:        0
% 1.21/1.03  num_pure_diseq_elim:                    0
% 1.21/1.03  simp_replaced_by:                       0
% 1.21/1.03  res_preprocessed:                       37
% 1.21/1.03  prep_upred:                             0
% 1.21/1.03  prep_unflattend:                        39
% 1.21/1.03  smt_new_axioms:                         0
% 1.21/1.03  pred_elim_cands:                        0
% 1.21/1.03  pred_elim:                              7
% 1.21/1.03  pred_elim_cl:                           13
% 1.21/1.03  pred_elim_cycles:                       10
% 1.21/1.03  merged_defs:                            0
% 1.21/1.03  merged_defs_ncl:                        0
% 1.21/1.03  bin_hyper_res:                          0
% 1.21/1.03  prep_cycles:                            3
% 1.21/1.03  pred_elim_time:                         0.01
% 1.21/1.03  splitting_time:                         0.
% 1.21/1.03  sem_filter_time:                        0.
% 1.21/1.03  monotx_time:                            0.
% 1.21/1.03  subtype_inf_time:                       0.
% 1.21/1.03  
% 1.21/1.03  ------ Problem properties
% 1.21/1.03  
% 1.21/1.03  clauses:                                6
% 1.21/1.03  conjectures:                            0
% 1.21/1.03  epr:                                    1
% 1.21/1.03  horn:                                   6
% 1.21/1.03  ground:                                 4
% 1.21/1.03  unary:                                  6
% 1.21/1.03  binary:                                 0
% 1.21/1.03  lits:                                   6
% 1.21/1.03  lits_eq:                                6
% 1.21/1.03  fd_pure:                                0
% 1.21/1.03  fd_pseudo:                              0
% 1.21/1.03  fd_cond:                                0
% 1.21/1.03  fd_pseudo_cond:                         0
% 1.21/1.03  ac_symbols:                             0
% 1.21/1.03  
% 1.21/1.03  ------ Propositional Solver
% 1.21/1.03  
% 1.21/1.03  prop_solver_calls:                      17
% 1.21/1.03  prop_fast_solver_calls:                 277
% 1.21/1.03  smt_solver_calls:                       0
% 1.21/1.03  smt_fast_solver_calls:                  0
% 1.21/1.03  prop_num_of_clauses:                    157
% 1.21/1.03  prop_preprocess_simplified:             823
% 1.21/1.03  prop_fo_subsumed:                       13
% 1.21/1.03  prop_solver_time:                       0.
% 1.21/1.03  smt_solver_time:                        0.
% 1.21/1.03  smt_fast_solver_time:                   0.
% 1.21/1.03  prop_fast_solver_time:                  0.
% 1.21/1.03  prop_unsat_core_time:                   0.
% 1.21/1.03  
% 1.21/1.03  ------ QBF
% 1.21/1.03  
% 1.21/1.03  qbf_q_res:                              0
% 1.21/1.03  qbf_num_tautologies:                    0
% 1.21/1.03  qbf_prep_cycles:                        0
% 1.21/1.03  
% 1.21/1.03  ------ BMC1
% 1.21/1.03  
% 1.21/1.03  bmc1_current_bound:                     -1
% 1.21/1.03  bmc1_last_solved_bound:                 -1
% 1.21/1.03  bmc1_unsat_core_size:                   -1
% 1.21/1.03  bmc1_unsat_core_parents_size:           -1
% 1.21/1.03  bmc1_merge_next_fun:                    0
% 1.21/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.21/1.03  
% 1.21/1.03  ------ Instantiation
% 1.21/1.03  
% 1.21/1.03  inst_num_of_clauses:                    0
% 1.21/1.03  inst_num_in_passive:                    0
% 1.21/1.03  inst_num_in_active:                     0
% 1.21/1.03  inst_num_in_unprocessed:                0
% 1.21/1.03  inst_num_of_loops:                      0
% 1.21/1.03  inst_num_of_learning_restarts:          0
% 1.21/1.03  inst_num_moves_active_passive:          0
% 1.21/1.03  inst_lit_activity:                      0
% 1.21/1.03  inst_lit_activity_moves:                0
% 1.21/1.03  inst_num_tautologies:                   0
% 1.21/1.03  inst_num_prop_implied:                  0
% 1.21/1.03  inst_num_existing_simplified:           0
% 1.21/1.03  inst_num_eq_res_simplified:             0
% 1.21/1.03  inst_num_child_elim:                    0
% 1.21/1.03  inst_num_of_dismatching_blockings:      0
% 1.21/1.03  inst_num_of_non_proper_insts:           0
% 1.21/1.03  inst_num_of_duplicates:                 0
% 1.21/1.03  inst_inst_num_from_inst_to_res:         0
% 1.21/1.03  inst_dismatching_checking_time:         0.
% 1.21/1.03  
% 1.21/1.03  ------ Resolution
% 1.21/1.03  
% 1.21/1.03  res_num_of_clauses:                     0
% 1.21/1.03  res_num_in_passive:                     0
% 1.21/1.03  res_num_in_active:                      0
% 1.21/1.03  res_num_of_loops:                       40
% 1.21/1.03  res_forward_subset_subsumed:            3
% 1.21/1.03  res_backward_subset_subsumed:           0
% 1.21/1.03  res_forward_subsumed:                   0
% 1.21/1.03  res_backward_subsumed:                  0
% 1.21/1.03  res_forward_subsumption_resolution:     4
% 1.21/1.03  res_backward_subsumption_resolution:    0
% 1.21/1.03  res_clause_to_clause_subsumption:       35
% 1.21/1.03  res_orphan_elimination:                 0
% 1.21/1.03  res_tautology_del:                      4
% 1.21/1.03  res_num_eq_res_simplified:              0
% 1.21/1.03  res_num_sel_changes:                    0
% 1.21/1.03  res_moves_from_active_to_pass:          0
% 1.21/1.03  
% 1.21/1.03  ------ Superposition
% 1.21/1.03  
% 1.21/1.03  sup_time_total:                         0.
% 1.21/1.03  sup_time_generating:                    0.
% 1.21/1.03  sup_time_sim_full:                      0.
% 1.21/1.03  sup_time_sim_immed:                     0.
% 1.21/1.03  
% 1.21/1.03  sup_num_of_clauses:                     4
% 1.21/1.03  sup_num_in_active:                      2
% 1.21/1.03  sup_num_in_passive:                     2
% 1.21/1.03  sup_num_of_loops:                       4
% 1.21/1.03  sup_fw_superposition:                   1
% 1.21/1.03  sup_bw_superposition:                   1
% 1.21/1.03  sup_immediate_simplified:               0
% 1.21/1.03  sup_given_eliminated:                   0
% 1.21/1.03  comparisons_done:                       0
% 1.21/1.03  comparisons_avoided:                    0
% 1.21/1.03  
% 1.21/1.03  ------ Simplifications
% 1.21/1.03  
% 1.21/1.03  
% 1.21/1.03  sim_fw_subset_subsumed:                 0
% 1.21/1.03  sim_bw_subset_subsumed:                 0
% 1.21/1.03  sim_fw_subsumed:                        1
% 1.21/1.03  sim_bw_subsumed:                        0
% 1.21/1.03  sim_fw_subsumption_res:                 0
% 1.21/1.03  sim_bw_subsumption_res:                 0
% 1.21/1.03  sim_tautology_del:                      0
% 1.21/1.03  sim_eq_tautology_del:                   0
% 1.21/1.03  sim_eq_res_simp:                        0
% 1.21/1.03  sim_fw_demodulated:                     2
% 1.21/1.03  sim_bw_demodulated:                     2
% 1.21/1.03  sim_light_normalised:                   3
% 1.21/1.03  sim_joinable_taut:                      0
% 1.21/1.03  sim_joinable_simp:                      0
% 1.21/1.03  sim_ac_normalised:                      0
% 1.21/1.03  sim_smt_subsumption:                    0
% 1.21/1.03  
%------------------------------------------------------------------------------
