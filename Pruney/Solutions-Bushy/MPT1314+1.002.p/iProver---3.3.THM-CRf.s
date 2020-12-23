%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1314+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:26 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 444 expanded)
%              Number of clauses        :   65 ( 137 expanded)
%              Number of leaves         :   15 ( 138 expanded)
%              Depth                    :   20
%              Number of atoms          :  334 (2215 expanded)
%              Number of equality atoms :   97 ( 427 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v3_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f31,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v3_pre_topc(X3,X2)
          & X1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ~ v3_pre_topc(sK4,X2)
        & sK4 = X1
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ v3_pre_topc(X3,X2)
              & X1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
          & v3_pre_topc(X1,X0)
          & m1_pre_topc(X2,X0) )
     => ( ? [X3] :
            ( ~ v3_pre_topc(X3,sK3)
            & X1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
        & v3_pre_topc(X1,X0)
        & m1_pre_topc(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ v3_pre_topc(X3,X2)
                & sK2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
            & v3_pre_topc(sK2,X0)
            & m1_pre_topc(X2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v3_pre_topc(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
                & v3_pre_topc(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,sK1)
              & m1_pre_topc(X2,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ v3_pre_topc(sK4,sK3)
    & sK2 = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v3_pre_topc(sK2,sK1)
    & m1_pre_topc(sK3,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f23,f31,f30,f29,f28])).

fof(f49,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK0(X0,X1,X2),k2_struct_0(X1)) = X2
        & v3_pre_topc(sK0(X0,X1,X2),X0)
        & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK0(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v3_pre_topc(sK0(X0,X1,X2),X0)
                    & m1_subset_1(sK0(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    sK2 = sK4 ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    ~ v3_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_493,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_744,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_493])).

cnf(c_3,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_0,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_227,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_3,c_0])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_244,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_16])).

cnf(c_245,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_247,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_245,c_18])).

cnf(c_373,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_227,c_247])).

cnf(c_374,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_483,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(subtyping,[status(esa)],[c_374])).

cnf(c_765,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_744,c_483])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_202,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_xboole_0(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_11,c_6])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | k3_xboole_0(X0_44,X1_44) = X0_44 ),
    inference(subtyping,[status(esa)],[c_202])).

cnf(c_747,plain,
    ( k3_xboole_0(X0_44,X1_44) = X0_44
    | m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_490])).

cnf(c_1594,plain,
    ( k3_xboole_0(sK4,k2_struct_0(sK3)) = sK4 ),
    inference(superposition,[status(thm)],[c_765,c_747])).

cnf(c_1,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_216,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_3,c_1])).

cnf(c_378,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_216,c_247])).

cnf(c_379,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_482,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_379])).

cnf(c_753,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_482])).

cnf(c_774,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_753,c_483])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_496,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | k9_subset_1(X1_44,X2_44,X0_44) = k3_xboole_0(X2_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_742,plain,
    ( k9_subset_1(X0_44,X1_44,X2_44) = k3_xboole_0(X1_44,X2_44)
    | m1_subset_1(X2_44,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_496])).

cnf(c_1416,plain,
    ( k9_subset_1(k2_struct_0(sK3),X0_44,k2_struct_0(sK3)) = k3_xboole_0(X0_44,k2_struct_0(sK3)) ),
    inference(superposition,[status(thm)],[c_774,c_742])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_497,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | m1_subset_1(k9_subset_1(X1_44,X2_44,X0_44),k1_zfmisc_1(X1_44)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_741,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
    | m1_subset_1(k9_subset_1(X1_44,X2_44,X0_44),k1_zfmisc_1(X1_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_497])).

cnf(c_7,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_255,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_16])).

cnf(c_256,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | v3_pre_topc(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_255])).

cnf(c_260,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),sK3)
    | ~ v3_pre_topc(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_256,c_18])).

cnf(c_261,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | v3_pre_topc(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_260])).

cnf(c_489,plain,
    ( ~ v3_pre_topc(X0_44,sK1)
    | v3_pre_topc(k9_subset_1(u1_struct_0(sK3),X0_44,k2_struct_0(sK3)),sK3)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0_44,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_261])).

cnf(c_748,plain,
    ( v3_pre_topc(X0_44,sK1) != iProver_top
    | v3_pre_topc(k9_subset_1(u1_struct_0(sK3),X0_44,k2_struct_0(sK3)),sK3) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0_44,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_361,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_227,c_18])).

cnf(c_362,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_485,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_362])).

cnf(c_810,plain,
    ( v3_pre_topc(X0_44,sK1) != iProver_top
    | v3_pre_topc(k9_subset_1(k2_struct_0(sK3),X0_44,k2_struct_0(sK3)),sK3) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(k9_subset_1(k2_struct_0(sK3),X0_44,k2_struct_0(sK3)),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_748,c_483,c_485])).

cnf(c_1410,plain,
    ( v3_pre_topc(X0_44,sK1) != iProver_top
    | v3_pre_topc(k9_subset_1(k2_struct_0(sK3),X0_44,k2_struct_0(sK3)),sK3) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_741,c_810])).

cnf(c_1581,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v3_pre_topc(k9_subset_1(k2_struct_0(sK3),X0_44,k2_struct_0(sK3)),sK3) = iProver_top
    | v3_pre_topc(X0_44,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1410,c_774])).

cnf(c_1582,plain,
    ( v3_pre_topc(X0_44,sK1) != iProver_top
    | v3_pre_topc(k9_subset_1(k2_struct_0(sK3),X0_44,k2_struct_0(sK3)),sK3) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1581])).

cnf(c_1734,plain,
    ( v3_pre_topc(X0_44,sK1) != iProver_top
    | v3_pre_topc(k3_xboole_0(X0_44,k2_struct_0(sK3)),sK3) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1416,c_1582])).

cnf(c_2688,plain,
    ( v3_pre_topc(sK4,sK1) != iProver_top
    | v3_pre_topc(sK4,sK3) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1594,c_1734])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_491,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_746,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_13,negated_conjecture,
    ( sK2 = sK4 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_494,negated_conjecture,
    ( sK2 = sK4 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_768,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_746,c_485,c_494])).

cnf(c_15,negated_conjecture,
    ( v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_492,negated_conjecture,
    ( v3_pre_topc(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_745,plain,
    ( v3_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_756,plain,
    ( v3_pre_topc(sK4,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_745,c_494])).

cnf(c_12,negated_conjecture,
    ( ~ v3_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_24,plain,
    ( v3_pre_topc(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2688,c_768,c_756,c_24])).


%------------------------------------------------------------------------------
