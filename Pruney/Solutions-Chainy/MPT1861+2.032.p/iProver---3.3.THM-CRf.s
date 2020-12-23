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
% DateTime   : Thu Dec  3 12:25:53 EST 2020

% Result     : Theorem 19.69s
% Output     : CNFRefutation 19.69s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 584 expanded)
%              Number of clauses        :  103 ( 243 expanded)
%              Number of leaves         :   17 ( 136 expanded)
%              Depth                    :   17
%              Number of atoms          :  394 (1939 expanded)
%              Number of equality atoms :  141 ( 274 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK0(X0),X0)
      & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f21])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f33,f31])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0] : ~ v1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & ( v2_tex_2(X2,X0)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK3),X0)
        & ( v2_tex_2(sK3,X0)
          | v2_tex_2(X1,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),sK2,X2),X0)
            & ( v2_tex_2(X2,X0)
              | v2_tex_2(sK2,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK1),X1,X2),sK1)
              & ( v2_tex_2(X2,sK1)
                | v2_tex_2(X1,sK1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1)
    & ( v2_tex_2(sK3,sK1)
      | v2_tex_2(sK2,sK1) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f27,f26,f25])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,
    ( v2_tex_2(sK3,sK1)
    | v2_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_5,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_725,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_723,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1217,plain,
    ( r1_tarski(sK0(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_725,c_723])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_122,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_123,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_122])).

cnf(c_151,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_123])).

cnf(c_717,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_151])).

cnf(c_1716,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK0(X1))) = k9_subset_1(X1,X0,sK0(X1)) ),
    inference(superposition,[status(thm)],[c_1217,c_717])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_150,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_123])).

cnf(c_718,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_150])).

cnf(c_3104,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_718,c_723])).

cnf(c_5025,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,sK0(X1))),X1) = iProver_top
    | r1_tarski(sK0(X1),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1716,c_3104])).

cnf(c_4,plain,
    ( ~ v1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_8,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_154,plain,
    ( v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_123])).

cnf(c_221,plain,
    ( ~ r1_tarski(X0,X1)
    | X1 != X2
    | X1 = X0
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_154])).

cnf(c_222,plain,
    ( ~ r1_tarski(sK0(X0),X0)
    | X0 = sK0(X0) ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_716,plain,
    ( X0 = sK0(X0)
    | r1_tarski(sK0(X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_223,plain,
    ( X0 = sK0(X0)
    | r1_tarski(sK0(X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_222])).

cnf(c_15515,plain,
    ( X0 = sK0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_716,c_223,c_1217])).

cnf(c_57496,plain,
    ( r1_tarski(X0,X0) != iProver_top
    | r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5025,c_15515])).

cnf(c_15525,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15515,c_1217])).

cnf(c_57498,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_57496,c_15525])).

cnf(c_57499,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_57498])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_726,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_57565,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_57499,c_726])).

cnf(c_0,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_727,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5007,plain,
    ( r1_tarski(k9_subset_1(X0,X1,sK0(X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1716,c_727])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_720,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_724,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_10,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_238,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_239,plain,
    ( ~ v2_tex_2(X0,sK1)
    | v2_tex_2(X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_238])).

cnf(c_715,plain,
    ( v2_tex_2(X0,sK1) != iProver_top
    | v2_tex_2(X1,sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_239])).

cnf(c_1308,plain,
    ( v2_tex_2(X0,sK1) != iProver_top
    | v2_tex_2(X1,sK1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_724,c_715])).

cnf(c_2049,plain,
    ( v2_tex_2(X0,sK1) != iProver_top
    | v2_tex_2(sK3,sK1) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_720,c_1308])).

cnf(c_5375,plain,
    ( v2_tex_2(k9_subset_1(X0,u1_struct_0(sK1),sK0(X0)),sK1) != iProver_top
    | v2_tex_2(sK3,sK1) = iProver_top
    | r1_tarski(sK3,k9_subset_1(X0,u1_struct_0(sK1),sK0(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5007,c_2049])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_17,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_18,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,negated_conjecture,
    ( v2_tex_2(sK3,sK1)
    | v2_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_19,plain,
    ( v2_tex_2(sK3,sK1) = iProver_top
    | v2_tex_2(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_833,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_973,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_833])).

cnf(c_974,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_973])).

cnf(c_386,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1157,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_386])).

cnf(c_1352,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK1))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k9_subset_1(u1_struct_0(sK1),sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_151])).

cnf(c_1218,plain,
    ( r1_tarski(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_720,c_723])).

cnf(c_1314,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK3)) = k9_subset_1(u1_struct_0(sK1),X0,sK3) ),
    inference(superposition,[status(thm)],[c_1218,c_717])).

cnf(c_11,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_722,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1412,plain,
    ( v2_tex_2(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1314,c_722])).

cnf(c_392,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_776,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | X2 != X0
    | k1_zfmisc_1(u1_struct_0(sK1)) != X1 ),
    inference(instantiation,[status(thm)],[c_392])).

cnf(c_920,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | X1 != X0
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_776])).

cnf(c_1374,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK1),X1,X2),k1_zfmisc_1(u1_struct_0(sK1)))
    | X0 != k9_subset_1(u1_struct_0(sK1),X1,X2)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_920])).

cnf(c_1976,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK1),X1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | X0 != k9_subset_1(u1_struct_0(sK1),X1,sK3)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1374])).

cnf(c_2277,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k9_subset_1(u1_struct_0(sK1),sK2,sK3)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1976])).

cnf(c_2278,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k9_subset_1(u1_struct_0(sK1),sK2,sK3)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2277])).

cnf(c_2004,plain,
    ( v2_tex_2(X0,sK1)
    | ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_239])).

cnf(c_2173,plain,
    ( v2_tex_2(k4_xboole_0(sK2,k4_xboole_0(sK2,X0)),sK1)
    | ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(k4_xboole_0(sK2,k4_xboole_0(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,X0)),sK2) ),
    inference(instantiation,[status(thm)],[c_2004])).

cnf(c_4061,plain,
    ( v2_tex_2(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK1)
    | ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK2) ),
    inference(instantiation,[status(thm)],[c_2173])).

cnf(c_4063,plain,
    ( v2_tex_2(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK1) = iProver_top
    | v2_tex_2(sK2,sK1) != iProver_top
    | m1_subset_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4061])).

cnf(c_1245,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK1),X0,X1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_150])).

cnf(c_1823,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK1),X0,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1245])).

cnf(c_4566,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1823])).

cnf(c_4567,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | r1_tarski(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4566])).

cnf(c_1422,plain,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,X0)),sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5722,plain,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK2) ),
    inference(instantiation,[status(thm)],[c_1422])).

cnf(c_5723,plain,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5722])).

cnf(c_5971,plain,
    ( v2_tex_2(sK3,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5375,c_17,c_13,c_18,c_19,c_973,c_974,c_1157,c_1352,c_1412,c_2278,c_4063,c_4567,c_5723])).

cnf(c_1006,plain,
    ( v2_tex_2(X0,sK1) = iProver_top
    | v2_tex_2(sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_720,c_715])).

cnf(c_1307,plain,
    ( v2_tex_2(X0,sK1) = iProver_top
    | v2_tex_2(sK3,sK1) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_724,c_1006])).

cnf(c_839,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK1))
    | r1_tarski(X0,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1024,plain,
    ( r1_tarski(X0,u1_struct_0(sK1))
    | ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_839])).

cnf(c_1025,plain,
    ( r1_tarski(X0,u1_struct_0(sK1)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1024])).

cnf(c_1569,plain,
    ( v2_tex_2(sK3,sK1) != iProver_top
    | v2_tex_2(X0,sK1) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1307,c_18,c_974,c_1025])).

cnf(c_1570,plain,
    ( v2_tex_2(X0,sK1) = iProver_top
    | v2_tex_2(sK3,sK1) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_1569])).

cnf(c_5975,plain,
    ( v2_tex_2(X0,sK1) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5971,c_1570])).

cnf(c_57874,plain,
    ( v2_tex_2(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sK1) = iProver_top
    | r1_tarski(X1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_57565,c_5975])).

cnf(c_63405,plain,
    ( r1_tarski(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_57874,c_1412])).

cnf(c_389,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_887,plain,
    ( ~ r1_tarski(X0,sK3)
    | r1_tarski(X1,sK3)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_1767,plain,
    ( r1_tarski(X0,sK3)
    | ~ r1_tarski(sK0(sK3),sK3)
    | X0 != sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_887])).

cnf(c_2396,plain,
    ( ~ r1_tarski(sK0(sK3),sK3)
    | r1_tarski(sK3,sK3)
    | sK3 != sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_1767])).

cnf(c_2397,plain,
    ( sK3 != sK0(sK3)
    | r1_tarski(sK0(sK3),sK3) != iProver_top
    | r1_tarski(sK3,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2396])).

cnf(c_1348,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1349,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1348])).

cnf(c_1332,plain,
    ( ~ r1_tarski(sK0(sK3),sK3)
    | sK3 = sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_882,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1109,plain,
    ( ~ m1_subset_1(sK0(sK3),k1_zfmisc_1(sK3))
    | r1_tarski(sK0(sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_882])).

cnf(c_1110,plain,
    ( m1_subset_1(sK0(sK3),k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(sK0(sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1109])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_63405,c_2397,c_1349,c_1348,c_1332,c_1110,c_1109])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.69/3.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.69/3.04  
% 19.69/3.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.69/3.04  
% 19.69/3.04  ------  iProver source info
% 19.69/3.04  
% 19.69/3.04  git: date: 2020-06-30 10:37:57 +0100
% 19.69/3.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.69/3.04  git: non_committed_changes: false
% 19.69/3.04  git: last_make_outside_of_git: false
% 19.69/3.04  
% 19.69/3.04  ------ 
% 19.69/3.04  
% 19.69/3.04  ------ Input Options
% 19.69/3.04  
% 19.69/3.04  --out_options                           all
% 19.69/3.04  --tptp_safe_out                         true
% 19.69/3.04  --problem_path                          ""
% 19.69/3.04  --include_path                          ""
% 19.69/3.04  --clausifier                            res/vclausify_rel
% 19.69/3.04  --clausifier_options                    ""
% 19.69/3.04  --stdin                                 false
% 19.69/3.04  --stats_out                             all
% 19.69/3.04  
% 19.69/3.04  ------ General Options
% 19.69/3.04  
% 19.69/3.04  --fof                                   false
% 19.69/3.04  --time_out_real                         305.
% 19.69/3.04  --time_out_virtual                      -1.
% 19.69/3.04  --symbol_type_check                     false
% 19.69/3.04  --clausify_out                          false
% 19.69/3.04  --sig_cnt_out                           false
% 19.69/3.04  --trig_cnt_out                          false
% 19.69/3.04  --trig_cnt_out_tolerance                1.
% 19.69/3.04  --trig_cnt_out_sk_spl                   false
% 19.69/3.04  --abstr_cl_out                          false
% 19.69/3.04  
% 19.69/3.04  ------ Global Options
% 19.69/3.04  
% 19.69/3.04  --schedule                              default
% 19.69/3.04  --add_important_lit                     false
% 19.69/3.04  --prop_solver_per_cl                    1000
% 19.69/3.04  --min_unsat_core                        false
% 19.69/3.04  --soft_assumptions                      false
% 19.69/3.04  --soft_lemma_size                       3
% 19.69/3.04  --prop_impl_unit_size                   0
% 19.69/3.04  --prop_impl_unit                        []
% 19.69/3.04  --share_sel_clauses                     true
% 19.69/3.04  --reset_solvers                         false
% 19.69/3.04  --bc_imp_inh                            [conj_cone]
% 19.69/3.04  --conj_cone_tolerance                   3.
% 19.69/3.04  --extra_neg_conj                        none
% 19.69/3.04  --large_theory_mode                     true
% 19.69/3.04  --prolific_symb_bound                   200
% 19.69/3.04  --lt_threshold                          2000
% 19.69/3.04  --clause_weak_htbl                      true
% 19.69/3.04  --gc_record_bc_elim                     false
% 19.69/3.04  
% 19.69/3.04  ------ Preprocessing Options
% 19.69/3.04  
% 19.69/3.04  --preprocessing_flag                    true
% 19.69/3.04  --time_out_prep_mult                    0.1
% 19.69/3.04  --splitting_mode                        input
% 19.69/3.04  --splitting_grd                         true
% 19.69/3.04  --splitting_cvd                         false
% 19.69/3.04  --splitting_cvd_svl                     false
% 19.69/3.04  --splitting_nvd                         32
% 19.69/3.04  --sub_typing                            true
% 19.69/3.04  --prep_gs_sim                           true
% 19.69/3.04  --prep_unflatten                        true
% 19.69/3.04  --prep_res_sim                          true
% 19.69/3.04  --prep_upred                            true
% 19.69/3.04  --prep_sem_filter                       exhaustive
% 19.69/3.04  --prep_sem_filter_out                   false
% 19.69/3.04  --pred_elim                             true
% 19.69/3.04  --res_sim_input                         true
% 19.69/3.04  --eq_ax_congr_red                       true
% 19.69/3.04  --pure_diseq_elim                       true
% 19.69/3.04  --brand_transform                       false
% 19.69/3.04  --non_eq_to_eq                          false
% 19.69/3.04  --prep_def_merge                        true
% 19.69/3.04  --prep_def_merge_prop_impl              false
% 19.69/3.04  --prep_def_merge_mbd                    true
% 19.69/3.04  --prep_def_merge_tr_red                 false
% 19.69/3.04  --prep_def_merge_tr_cl                  false
% 19.69/3.04  --smt_preprocessing                     true
% 19.69/3.04  --smt_ac_axioms                         fast
% 19.69/3.04  --preprocessed_out                      false
% 19.69/3.04  --preprocessed_stats                    false
% 19.69/3.04  
% 19.69/3.04  ------ Abstraction refinement Options
% 19.69/3.04  
% 19.69/3.04  --abstr_ref                             []
% 19.69/3.04  --abstr_ref_prep                        false
% 19.69/3.04  --abstr_ref_until_sat                   false
% 19.69/3.04  --abstr_ref_sig_restrict                funpre
% 19.69/3.04  --abstr_ref_af_restrict_to_split_sk     false
% 19.69/3.04  --abstr_ref_under                       []
% 19.69/3.04  
% 19.69/3.04  ------ SAT Options
% 19.69/3.04  
% 19.69/3.04  --sat_mode                              false
% 19.69/3.04  --sat_fm_restart_options                ""
% 19.69/3.04  --sat_gr_def                            false
% 19.69/3.04  --sat_epr_types                         true
% 19.69/3.04  --sat_non_cyclic_types                  false
% 19.69/3.04  --sat_finite_models                     false
% 19.69/3.04  --sat_fm_lemmas                         false
% 19.69/3.04  --sat_fm_prep                           false
% 19.69/3.04  --sat_fm_uc_incr                        true
% 19.69/3.04  --sat_out_model                         small
% 19.69/3.04  --sat_out_clauses                       false
% 19.69/3.04  
% 19.69/3.04  ------ QBF Options
% 19.69/3.04  
% 19.69/3.04  --qbf_mode                              false
% 19.69/3.04  --qbf_elim_univ                         false
% 19.69/3.04  --qbf_dom_inst                          none
% 19.69/3.04  --qbf_dom_pre_inst                      false
% 19.69/3.04  --qbf_sk_in                             false
% 19.69/3.04  --qbf_pred_elim                         true
% 19.69/3.04  --qbf_split                             512
% 19.69/3.04  
% 19.69/3.04  ------ BMC1 Options
% 19.69/3.04  
% 19.69/3.04  --bmc1_incremental                      false
% 19.69/3.04  --bmc1_axioms                           reachable_all
% 19.69/3.04  --bmc1_min_bound                        0
% 19.69/3.04  --bmc1_max_bound                        -1
% 19.69/3.04  --bmc1_max_bound_default                -1
% 19.69/3.04  --bmc1_symbol_reachability              true
% 19.69/3.04  --bmc1_property_lemmas                  false
% 19.69/3.04  --bmc1_k_induction                      false
% 19.69/3.04  --bmc1_non_equiv_states                 false
% 19.69/3.04  --bmc1_deadlock                         false
% 19.69/3.04  --bmc1_ucm                              false
% 19.69/3.04  --bmc1_add_unsat_core                   none
% 19.69/3.04  --bmc1_unsat_core_children              false
% 19.69/3.04  --bmc1_unsat_core_extrapolate_axioms    false
% 19.69/3.04  --bmc1_out_stat                         full
% 19.69/3.04  --bmc1_ground_init                      false
% 19.69/3.04  --bmc1_pre_inst_next_state              false
% 19.69/3.04  --bmc1_pre_inst_state                   false
% 19.69/3.04  --bmc1_pre_inst_reach_state             false
% 19.69/3.04  --bmc1_out_unsat_core                   false
% 19.69/3.04  --bmc1_aig_witness_out                  false
% 19.69/3.04  --bmc1_verbose                          false
% 19.69/3.04  --bmc1_dump_clauses_tptp                false
% 19.69/3.04  --bmc1_dump_unsat_core_tptp             false
% 19.69/3.04  --bmc1_dump_file                        -
% 19.69/3.04  --bmc1_ucm_expand_uc_limit              128
% 19.69/3.04  --bmc1_ucm_n_expand_iterations          6
% 19.69/3.04  --bmc1_ucm_extend_mode                  1
% 19.69/3.04  --bmc1_ucm_init_mode                    2
% 19.69/3.04  --bmc1_ucm_cone_mode                    none
% 19.69/3.04  --bmc1_ucm_reduced_relation_type        0
% 19.69/3.04  --bmc1_ucm_relax_model                  4
% 19.69/3.04  --bmc1_ucm_full_tr_after_sat            true
% 19.69/3.04  --bmc1_ucm_expand_neg_assumptions       false
% 19.69/3.04  --bmc1_ucm_layered_model                none
% 19.69/3.04  --bmc1_ucm_max_lemma_size               10
% 19.69/3.04  
% 19.69/3.04  ------ AIG Options
% 19.69/3.04  
% 19.69/3.04  --aig_mode                              false
% 19.69/3.04  
% 19.69/3.04  ------ Instantiation Options
% 19.69/3.04  
% 19.69/3.04  --instantiation_flag                    true
% 19.69/3.04  --inst_sos_flag                         true
% 19.69/3.04  --inst_sos_phase                        true
% 19.69/3.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.69/3.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.69/3.04  --inst_lit_sel_side                     num_symb
% 19.69/3.04  --inst_solver_per_active                1400
% 19.69/3.04  --inst_solver_calls_frac                1.
% 19.69/3.04  --inst_passive_queue_type               priority_queues
% 19.69/3.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.69/3.04  --inst_passive_queues_freq              [25;2]
% 19.69/3.04  --inst_dismatching                      true
% 19.69/3.04  --inst_eager_unprocessed_to_passive     true
% 19.69/3.04  --inst_prop_sim_given                   true
% 19.69/3.04  --inst_prop_sim_new                     false
% 19.69/3.04  --inst_subs_new                         false
% 19.69/3.04  --inst_eq_res_simp                      false
% 19.69/3.04  --inst_subs_given                       false
% 19.69/3.04  --inst_orphan_elimination               true
% 19.69/3.04  --inst_learning_loop_flag               true
% 19.69/3.04  --inst_learning_start                   3000
% 19.69/3.04  --inst_learning_factor                  2
% 19.69/3.04  --inst_start_prop_sim_after_learn       3
% 19.69/3.04  --inst_sel_renew                        solver
% 19.69/3.04  --inst_lit_activity_flag                true
% 19.69/3.04  --inst_restr_to_given                   false
% 19.69/3.04  --inst_activity_threshold               500
% 19.69/3.04  --inst_out_proof                        true
% 19.69/3.04  
% 19.69/3.04  ------ Resolution Options
% 19.69/3.04  
% 19.69/3.04  --resolution_flag                       true
% 19.69/3.04  --res_lit_sel                           adaptive
% 19.69/3.04  --res_lit_sel_side                      none
% 19.69/3.04  --res_ordering                          kbo
% 19.69/3.04  --res_to_prop_solver                    active
% 19.69/3.04  --res_prop_simpl_new                    false
% 19.69/3.04  --res_prop_simpl_given                  true
% 19.69/3.04  --res_passive_queue_type                priority_queues
% 19.69/3.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.69/3.04  --res_passive_queues_freq               [15;5]
% 19.69/3.04  --res_forward_subs                      full
% 19.69/3.04  --res_backward_subs                     full
% 19.69/3.04  --res_forward_subs_resolution           true
% 19.69/3.04  --res_backward_subs_resolution          true
% 19.69/3.04  --res_orphan_elimination                true
% 19.69/3.04  --res_time_limit                        2.
% 19.69/3.04  --res_out_proof                         true
% 19.69/3.04  
% 19.69/3.04  ------ Superposition Options
% 19.69/3.04  
% 19.69/3.04  --superposition_flag                    true
% 19.69/3.04  --sup_passive_queue_type                priority_queues
% 19.69/3.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.69/3.04  --sup_passive_queues_freq               [8;1;4]
% 19.69/3.04  --demod_completeness_check              fast
% 19.69/3.04  --demod_use_ground                      true
% 19.69/3.04  --sup_to_prop_solver                    passive
% 19.69/3.04  --sup_prop_simpl_new                    true
% 19.69/3.04  --sup_prop_simpl_given                  true
% 19.69/3.04  --sup_fun_splitting                     true
% 19.69/3.04  --sup_smt_interval                      50000
% 19.69/3.04  
% 19.69/3.04  ------ Superposition Simplification Setup
% 19.69/3.04  
% 19.69/3.04  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.69/3.04  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.69/3.04  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.69/3.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.69/3.04  --sup_full_triv                         [TrivRules;PropSubs]
% 19.69/3.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.69/3.04  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.69/3.04  --sup_immed_triv                        [TrivRules]
% 19.69/3.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.69/3.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.69/3.04  --sup_immed_bw_main                     []
% 19.69/3.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.69/3.04  --sup_input_triv                        [Unflattening;TrivRules]
% 19.69/3.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.69/3.04  --sup_input_bw                          []
% 19.69/3.04  
% 19.69/3.04  ------ Combination Options
% 19.69/3.04  
% 19.69/3.04  --comb_res_mult                         3
% 19.69/3.04  --comb_sup_mult                         2
% 19.69/3.04  --comb_inst_mult                        10
% 19.69/3.04  
% 19.69/3.04  ------ Debug Options
% 19.69/3.04  
% 19.69/3.04  --dbg_backtrace                         false
% 19.69/3.04  --dbg_dump_prop_clauses                 false
% 19.69/3.04  --dbg_dump_prop_clauses_file            -
% 19.69/3.04  --dbg_out_stat                          false
% 19.69/3.04  ------ Parsing...
% 19.69/3.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.69/3.04  
% 19.69/3.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 19.69/3.04  
% 19.69/3.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.69/3.04  
% 19.69/3.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.69/3.04  ------ Proving...
% 19.69/3.04  ------ Problem Properties 
% 19.69/3.04  
% 19.69/3.04  
% 19.69/3.04  clauses                                 13
% 19.69/3.04  conjectures                             4
% 19.69/3.04  EPR                                     2
% 19.69/3.04  Horn                                    12
% 19.69/3.04  unary                                   5
% 19.69/3.04  binary                                  6
% 19.69/3.04  lits                                    25
% 19.69/3.04  lits eq                                 2
% 19.69/3.04  fd_pure                                 0
% 19.69/3.04  fd_pseudo                               0
% 19.69/3.04  fd_cond                                 0
% 19.69/3.04  fd_pseudo_cond                          0
% 19.69/3.04  AC symbols                              0
% 19.69/3.04  
% 19.69/3.04  ------ Schedule dynamic 5 is on 
% 19.69/3.04  
% 19.69/3.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.69/3.04  
% 19.69/3.04  
% 19.69/3.04  ------ 
% 19.69/3.04  Current options:
% 19.69/3.04  ------ 
% 19.69/3.04  
% 19.69/3.04  ------ Input Options
% 19.69/3.04  
% 19.69/3.04  --out_options                           all
% 19.69/3.04  --tptp_safe_out                         true
% 19.69/3.04  --problem_path                          ""
% 19.69/3.04  --include_path                          ""
% 19.69/3.04  --clausifier                            res/vclausify_rel
% 19.69/3.04  --clausifier_options                    ""
% 19.69/3.04  --stdin                                 false
% 19.69/3.04  --stats_out                             all
% 19.69/3.04  
% 19.69/3.04  ------ General Options
% 19.69/3.04  
% 19.69/3.04  --fof                                   false
% 19.69/3.04  --time_out_real                         305.
% 19.69/3.04  --time_out_virtual                      -1.
% 19.69/3.04  --symbol_type_check                     false
% 19.69/3.04  --clausify_out                          false
% 19.69/3.04  --sig_cnt_out                           false
% 19.69/3.04  --trig_cnt_out                          false
% 19.69/3.04  --trig_cnt_out_tolerance                1.
% 19.69/3.04  --trig_cnt_out_sk_spl                   false
% 19.69/3.04  --abstr_cl_out                          false
% 19.69/3.04  
% 19.69/3.04  ------ Global Options
% 19.69/3.04  
% 19.69/3.04  --schedule                              default
% 19.69/3.04  --add_important_lit                     false
% 19.69/3.04  --prop_solver_per_cl                    1000
% 19.69/3.04  --min_unsat_core                        false
% 19.69/3.04  --soft_assumptions                      false
% 19.69/3.04  --soft_lemma_size                       3
% 19.69/3.04  --prop_impl_unit_size                   0
% 19.69/3.04  --prop_impl_unit                        []
% 19.69/3.04  --share_sel_clauses                     true
% 19.69/3.04  --reset_solvers                         false
% 19.69/3.04  --bc_imp_inh                            [conj_cone]
% 19.69/3.04  --conj_cone_tolerance                   3.
% 19.69/3.04  --extra_neg_conj                        none
% 19.69/3.04  --large_theory_mode                     true
% 19.69/3.04  --prolific_symb_bound                   200
% 19.69/3.04  --lt_threshold                          2000
% 19.69/3.04  --clause_weak_htbl                      true
% 19.69/3.04  --gc_record_bc_elim                     false
% 19.69/3.04  
% 19.69/3.04  ------ Preprocessing Options
% 19.69/3.04  
% 19.69/3.04  --preprocessing_flag                    true
% 19.69/3.04  --time_out_prep_mult                    0.1
% 19.69/3.04  --splitting_mode                        input
% 19.69/3.04  --splitting_grd                         true
% 19.69/3.04  --splitting_cvd                         false
% 19.69/3.04  --splitting_cvd_svl                     false
% 19.69/3.04  --splitting_nvd                         32
% 19.69/3.04  --sub_typing                            true
% 19.69/3.04  --prep_gs_sim                           true
% 19.69/3.04  --prep_unflatten                        true
% 19.69/3.04  --prep_res_sim                          true
% 19.69/3.04  --prep_upred                            true
% 19.69/3.04  --prep_sem_filter                       exhaustive
% 19.69/3.04  --prep_sem_filter_out                   false
% 19.69/3.04  --pred_elim                             true
% 19.69/3.04  --res_sim_input                         true
% 19.69/3.04  --eq_ax_congr_red                       true
% 19.69/3.04  --pure_diseq_elim                       true
% 19.69/3.04  --brand_transform                       false
% 19.69/3.04  --non_eq_to_eq                          false
% 19.69/3.04  --prep_def_merge                        true
% 19.69/3.04  --prep_def_merge_prop_impl              false
% 19.69/3.04  --prep_def_merge_mbd                    true
% 19.69/3.04  --prep_def_merge_tr_red                 false
% 19.69/3.04  --prep_def_merge_tr_cl                  false
% 19.69/3.04  --smt_preprocessing                     true
% 19.69/3.04  --smt_ac_axioms                         fast
% 19.69/3.04  --preprocessed_out                      false
% 19.69/3.04  --preprocessed_stats                    false
% 19.69/3.04  
% 19.69/3.04  ------ Abstraction refinement Options
% 19.69/3.04  
% 19.69/3.04  --abstr_ref                             []
% 19.69/3.04  --abstr_ref_prep                        false
% 19.69/3.04  --abstr_ref_until_sat                   false
% 19.69/3.04  --abstr_ref_sig_restrict                funpre
% 19.69/3.04  --abstr_ref_af_restrict_to_split_sk     false
% 19.69/3.04  --abstr_ref_under                       []
% 19.69/3.04  
% 19.69/3.04  ------ SAT Options
% 19.69/3.04  
% 19.69/3.04  --sat_mode                              false
% 19.69/3.04  --sat_fm_restart_options                ""
% 19.69/3.04  --sat_gr_def                            false
% 19.69/3.04  --sat_epr_types                         true
% 19.69/3.04  --sat_non_cyclic_types                  false
% 19.69/3.04  --sat_finite_models                     false
% 19.69/3.04  --sat_fm_lemmas                         false
% 19.69/3.04  --sat_fm_prep                           false
% 19.69/3.04  --sat_fm_uc_incr                        true
% 19.69/3.04  --sat_out_model                         small
% 19.69/3.04  --sat_out_clauses                       false
% 19.69/3.04  
% 19.69/3.04  ------ QBF Options
% 19.69/3.04  
% 19.69/3.04  --qbf_mode                              false
% 19.69/3.04  --qbf_elim_univ                         false
% 19.69/3.04  --qbf_dom_inst                          none
% 19.69/3.04  --qbf_dom_pre_inst                      false
% 19.69/3.04  --qbf_sk_in                             false
% 19.69/3.04  --qbf_pred_elim                         true
% 19.69/3.04  --qbf_split                             512
% 19.69/3.04  
% 19.69/3.04  ------ BMC1 Options
% 19.69/3.04  
% 19.69/3.04  --bmc1_incremental                      false
% 19.69/3.04  --bmc1_axioms                           reachable_all
% 19.69/3.04  --bmc1_min_bound                        0
% 19.69/3.04  --bmc1_max_bound                        -1
% 19.69/3.04  --bmc1_max_bound_default                -1
% 19.69/3.04  --bmc1_symbol_reachability              true
% 19.69/3.04  --bmc1_property_lemmas                  false
% 19.69/3.04  --bmc1_k_induction                      false
% 19.69/3.04  --bmc1_non_equiv_states                 false
% 19.69/3.04  --bmc1_deadlock                         false
% 19.69/3.04  --bmc1_ucm                              false
% 19.69/3.04  --bmc1_add_unsat_core                   none
% 19.69/3.04  --bmc1_unsat_core_children              false
% 19.69/3.04  --bmc1_unsat_core_extrapolate_axioms    false
% 19.69/3.04  --bmc1_out_stat                         full
% 19.69/3.04  --bmc1_ground_init                      false
% 19.69/3.04  --bmc1_pre_inst_next_state              false
% 19.69/3.04  --bmc1_pre_inst_state                   false
% 19.69/3.04  --bmc1_pre_inst_reach_state             false
% 19.69/3.04  --bmc1_out_unsat_core                   false
% 19.69/3.04  --bmc1_aig_witness_out                  false
% 19.69/3.04  --bmc1_verbose                          false
% 19.69/3.04  --bmc1_dump_clauses_tptp                false
% 19.69/3.04  --bmc1_dump_unsat_core_tptp             false
% 19.69/3.04  --bmc1_dump_file                        -
% 19.69/3.04  --bmc1_ucm_expand_uc_limit              128
% 19.69/3.04  --bmc1_ucm_n_expand_iterations          6
% 19.69/3.04  --bmc1_ucm_extend_mode                  1
% 19.69/3.04  --bmc1_ucm_init_mode                    2
% 19.69/3.04  --bmc1_ucm_cone_mode                    none
% 19.69/3.04  --bmc1_ucm_reduced_relation_type        0
% 19.69/3.04  --bmc1_ucm_relax_model                  4
% 19.69/3.04  --bmc1_ucm_full_tr_after_sat            true
% 19.69/3.04  --bmc1_ucm_expand_neg_assumptions       false
% 19.69/3.04  --bmc1_ucm_layered_model                none
% 19.69/3.04  --bmc1_ucm_max_lemma_size               10
% 19.69/3.04  
% 19.69/3.04  ------ AIG Options
% 19.69/3.04  
% 19.69/3.04  --aig_mode                              false
% 19.69/3.04  
% 19.69/3.04  ------ Instantiation Options
% 19.69/3.04  
% 19.69/3.04  --instantiation_flag                    true
% 19.69/3.04  --inst_sos_flag                         true
% 19.69/3.04  --inst_sos_phase                        true
% 19.69/3.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.69/3.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.69/3.04  --inst_lit_sel_side                     none
% 19.69/3.04  --inst_solver_per_active                1400
% 19.69/3.04  --inst_solver_calls_frac                1.
% 19.69/3.04  --inst_passive_queue_type               priority_queues
% 19.69/3.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.69/3.04  --inst_passive_queues_freq              [25;2]
% 19.69/3.04  --inst_dismatching                      true
% 19.69/3.04  --inst_eager_unprocessed_to_passive     true
% 19.69/3.04  --inst_prop_sim_given                   true
% 19.69/3.04  --inst_prop_sim_new                     false
% 19.69/3.04  --inst_subs_new                         false
% 19.69/3.04  --inst_eq_res_simp                      false
% 19.69/3.04  --inst_subs_given                       false
% 19.69/3.04  --inst_orphan_elimination               true
% 19.69/3.04  --inst_learning_loop_flag               true
% 19.69/3.04  --inst_learning_start                   3000
% 19.69/3.04  --inst_learning_factor                  2
% 19.69/3.04  --inst_start_prop_sim_after_learn       3
% 19.69/3.04  --inst_sel_renew                        solver
% 19.69/3.04  --inst_lit_activity_flag                true
% 19.69/3.04  --inst_restr_to_given                   false
% 19.69/3.04  --inst_activity_threshold               500
% 19.69/3.04  --inst_out_proof                        true
% 19.69/3.04  
% 19.69/3.04  ------ Resolution Options
% 19.69/3.04  
% 19.69/3.04  --resolution_flag                       false
% 19.69/3.04  --res_lit_sel                           adaptive
% 19.69/3.04  --res_lit_sel_side                      none
% 19.69/3.04  --res_ordering                          kbo
% 19.69/3.04  --res_to_prop_solver                    active
% 19.69/3.04  --res_prop_simpl_new                    false
% 19.69/3.04  --res_prop_simpl_given                  true
% 19.69/3.04  --res_passive_queue_type                priority_queues
% 19.69/3.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.69/3.04  --res_passive_queues_freq               [15;5]
% 19.69/3.04  --res_forward_subs                      full
% 19.69/3.04  --res_backward_subs                     full
% 19.69/3.04  --res_forward_subs_resolution           true
% 19.69/3.04  --res_backward_subs_resolution          true
% 19.69/3.04  --res_orphan_elimination                true
% 19.69/3.04  --res_time_limit                        2.
% 19.69/3.04  --res_out_proof                         true
% 19.69/3.04  
% 19.69/3.04  ------ Superposition Options
% 19.69/3.04  
% 19.69/3.04  --superposition_flag                    true
% 19.69/3.04  --sup_passive_queue_type                priority_queues
% 19.69/3.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.69/3.04  --sup_passive_queues_freq               [8;1;4]
% 19.69/3.04  --demod_completeness_check              fast
% 19.69/3.04  --demod_use_ground                      true
% 19.69/3.04  --sup_to_prop_solver                    passive
% 19.69/3.04  --sup_prop_simpl_new                    true
% 19.69/3.04  --sup_prop_simpl_given                  true
% 19.69/3.04  --sup_fun_splitting                     true
% 19.69/3.04  --sup_smt_interval                      50000
% 19.69/3.04  
% 19.69/3.04  ------ Superposition Simplification Setup
% 19.69/3.04  
% 19.69/3.04  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.69/3.04  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.69/3.04  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.69/3.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.69/3.04  --sup_full_triv                         [TrivRules;PropSubs]
% 19.69/3.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.69/3.04  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.69/3.04  --sup_immed_triv                        [TrivRules]
% 19.69/3.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.69/3.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.69/3.04  --sup_immed_bw_main                     []
% 19.69/3.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.69/3.04  --sup_input_triv                        [Unflattening;TrivRules]
% 19.69/3.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.69/3.04  --sup_input_bw                          []
% 19.69/3.04  
% 19.69/3.04  ------ Combination Options
% 19.69/3.04  
% 19.69/3.04  --comb_res_mult                         3
% 19.69/3.04  --comb_sup_mult                         2
% 19.69/3.04  --comb_inst_mult                        10
% 19.69/3.04  
% 19.69/3.04  ------ Debug Options
% 19.69/3.04  
% 19.69/3.04  --dbg_backtrace                         false
% 19.69/3.04  --dbg_dump_prop_clauses                 false
% 19.69/3.04  --dbg_dump_prop_clauses_file            -
% 19.69/3.04  --dbg_out_stat                          false
% 19.69/3.04  
% 19.69/3.04  
% 19.69/3.04  
% 19.69/3.04  
% 19.69/3.04  ------ Proving...
% 19.69/3.04  
% 19.69/3.04  
% 19.69/3.04  % SZS status Theorem for theBenchmark.p
% 19.69/3.04  
% 19.69/3.04  % SZS output start CNFRefutation for theBenchmark.p
% 19.69/3.04  
% 19.69/3.04  fof(f6,axiom,(
% 19.69/3.04    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.69/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.69/3.04  
% 19.69/3.04  fof(f21,plain,(
% 19.69/3.04    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0))))),
% 19.69/3.04    introduced(choice_axiom,[])).
% 19.69/3.04  
% 19.69/3.04  fof(f22,plain,(
% 19.69/3.04    ! [X0] : (~v1_subset_1(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)))),
% 19.69/3.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f21])).
% 19.69/3.04  
% 19.69/3.04  fof(f34,plain,(
% 19.69/3.04    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(X0))) )),
% 19.69/3.04    inference(cnf_transformation,[],[f22])).
% 19.69/3.04  
% 19.69/3.04  fof(f7,axiom,(
% 19.69/3.04    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.69/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.69/3.04  
% 19.69/3.04  fof(f23,plain,(
% 19.69/3.04    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 19.69/3.04    inference(nnf_transformation,[],[f7])).
% 19.69/3.04  
% 19.69/3.04  fof(f36,plain,(
% 19.69/3.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.69/3.04    inference(cnf_transformation,[],[f23])).
% 19.69/3.04  
% 19.69/3.04  fof(f5,axiom,(
% 19.69/3.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 19.69/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.69/3.04  
% 19.69/3.04  fof(f15,plain,(
% 19.69/3.04    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 19.69/3.04    inference(ennf_transformation,[],[f5])).
% 19.69/3.04  
% 19.69/3.04  fof(f33,plain,(
% 19.69/3.04    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 19.69/3.04    inference(cnf_transformation,[],[f15])).
% 19.69/3.04  
% 19.69/3.04  fof(f3,axiom,(
% 19.69/3.04    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 19.69/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.69/3.04  
% 19.69/3.04  fof(f31,plain,(
% 19.69/3.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 19.69/3.04    inference(cnf_transformation,[],[f3])).
% 19.69/3.04  
% 19.69/3.04  fof(f47,plain,(
% 19.69/3.04    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 19.69/3.04    inference(definition_unfolding,[],[f33,f31])).
% 19.69/3.04  
% 19.69/3.04  fof(f37,plain,(
% 19.69/3.04    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 19.69/3.04    inference(cnf_transformation,[],[f23])).
% 19.69/3.04  
% 19.69/3.04  fof(f4,axiom,(
% 19.69/3.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 19.69/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.69/3.04  
% 19.69/3.04  fof(f14,plain,(
% 19.69/3.04    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 19.69/3.04    inference(ennf_transformation,[],[f4])).
% 19.69/3.04  
% 19.69/3.04  fof(f32,plain,(
% 19.69/3.04    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 19.69/3.04    inference(cnf_transformation,[],[f14])).
% 19.69/3.04  
% 19.69/3.04  fof(f35,plain,(
% 19.69/3.04    ( ! [X0] : (~v1_subset_1(sK0(X0),X0)) )),
% 19.69/3.04    inference(cnf_transformation,[],[f22])).
% 19.69/3.04  
% 19.69/3.04  fof(f8,axiom,(
% 19.69/3.04    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 19.69/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.69/3.04  
% 19.69/3.04  fof(f16,plain,(
% 19.69/3.04    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.69/3.04    inference(ennf_transformation,[],[f8])).
% 19.69/3.04  
% 19.69/3.04  fof(f24,plain,(
% 19.69/3.04    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.69/3.04    inference(nnf_transformation,[],[f16])).
% 19.69/3.04  
% 19.69/3.04  fof(f39,plain,(
% 19.69/3.04    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.69/3.04    inference(cnf_transformation,[],[f24])).
% 19.69/3.04  
% 19.69/3.04  fof(f2,axiom,(
% 19.69/3.04    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 19.69/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.69/3.04  
% 19.69/3.04  fof(f12,plain,(
% 19.69/3.04    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 19.69/3.04    inference(ennf_transformation,[],[f2])).
% 19.69/3.04  
% 19.69/3.04  fof(f13,plain,(
% 19.69/3.04    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 19.69/3.04    inference(flattening,[],[f12])).
% 19.69/3.04  
% 19.69/3.04  fof(f30,plain,(
% 19.69/3.04    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 19.69/3.04    inference(cnf_transformation,[],[f13])).
% 19.69/3.04  
% 19.69/3.04  fof(f1,axiom,(
% 19.69/3.04    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 19.69/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.69/3.04  
% 19.69/3.04  fof(f29,plain,(
% 19.69/3.04    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 19.69/3.04    inference(cnf_transformation,[],[f1])).
% 19.69/3.04  
% 19.69/3.04  fof(f46,plain,(
% 19.69/3.04    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 19.69/3.04    inference(definition_unfolding,[],[f29,f31])).
% 19.69/3.04  
% 19.69/3.04  fof(f10,conjecture,(
% 19.69/3.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 19.69/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.69/3.04  
% 19.69/3.04  fof(f11,negated_conjecture,(
% 19.69/3.04    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 19.69/3.04    inference(negated_conjecture,[],[f10])).
% 19.69/3.04  
% 19.69/3.04  fof(f19,plain,(
% 19.69/3.04    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 19.69/3.04    inference(ennf_transformation,[],[f11])).
% 19.69/3.04  
% 19.69/3.04  fof(f20,plain,(
% 19.69/3.04    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 19.69/3.04    inference(flattening,[],[f19])).
% 19.69/3.04  
% 19.69/3.04  fof(f27,plain,(
% 19.69/3.04    ( ! [X0,X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,sK3),X0) & (v2_tex_2(sK3,X0) | v2_tex_2(X1,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.69/3.04    introduced(choice_axiom,[])).
% 19.69/3.04  
% 19.69/3.04  fof(f26,plain,(
% 19.69/3.04    ( ! [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),sK2,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(sK2,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.69/3.04    introduced(choice_axiom,[])).
% 19.69/3.04  
% 19.69/3.04  fof(f25,plain,(
% 19.69/3.04    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK1),X1,X2),sK1) & (v2_tex_2(X2,sK1) | v2_tex_2(X1,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1))),
% 19.69/3.04    introduced(choice_axiom,[])).
% 19.69/3.04  
% 19.69/3.04  fof(f28,plain,(
% 19.69/3.04    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1) & (v2_tex_2(sK3,sK1) | v2_tex_2(sK2,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1)),
% 19.69/3.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f27,f26,f25])).
% 19.69/3.04  
% 19.69/3.04  fof(f43,plain,(
% 19.69/3.04    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 19.69/3.04    inference(cnf_transformation,[],[f28])).
% 19.69/3.04  
% 19.69/3.04  fof(f9,axiom,(
% 19.69/3.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 19.69/3.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.69/3.04  
% 19.69/3.04  fof(f17,plain,(
% 19.69/3.04    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.69/3.04    inference(ennf_transformation,[],[f9])).
% 19.69/3.04  
% 19.69/3.04  fof(f18,plain,(
% 19.69/3.04    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.69/3.04    inference(flattening,[],[f17])).
% 19.69/3.04  
% 19.69/3.04  fof(f40,plain,(
% 19.69/3.04    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.69/3.04    inference(cnf_transformation,[],[f18])).
% 19.69/3.04  
% 19.69/3.04  fof(f41,plain,(
% 19.69/3.04    l1_pre_topc(sK1)),
% 19.69/3.04    inference(cnf_transformation,[],[f28])).
% 19.69/3.04  
% 19.69/3.04  fof(f42,plain,(
% 19.69/3.04    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 19.69/3.04    inference(cnf_transformation,[],[f28])).
% 19.69/3.04  
% 19.69/3.04  fof(f44,plain,(
% 19.69/3.04    v2_tex_2(sK3,sK1) | v2_tex_2(sK2,sK1)),
% 19.69/3.04    inference(cnf_transformation,[],[f28])).
% 19.69/3.04  
% 19.69/3.04  fof(f45,plain,(
% 19.69/3.04    ~v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1)),
% 19.69/3.04    inference(cnf_transformation,[],[f28])).
% 19.69/3.04  
% 19.69/3.04  cnf(c_5,plain,
% 19.69/3.04      ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
% 19.69/3.04      inference(cnf_transformation,[],[f34]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_725,plain,
% 19.69/3.04      ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_7,plain,
% 19.69/3.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 19.69/3.04      inference(cnf_transformation,[],[f36]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_723,plain,
% 19.69/3.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 19.69/3.04      | r1_tarski(X0,X1) = iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1217,plain,
% 19.69/3.04      ( r1_tarski(sK0(X0),X0) = iProver_top ),
% 19.69/3.04      inference(superposition,[status(thm)],[c_725,c_723]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_3,plain,
% 19.69/3.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.69/3.04      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 19.69/3.04      inference(cnf_transformation,[],[f47]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_6,plain,
% 19.69/3.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.69/3.04      inference(cnf_transformation,[],[f37]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_122,plain,
% 19.69/3.04      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.69/3.04      inference(prop_impl,[status(thm)],[c_6]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_123,plain,
% 19.69/3.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.69/3.04      inference(renaming,[status(thm)],[c_122]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_151,plain,
% 19.69/3.04      ( ~ r1_tarski(X0,X1)
% 19.69/3.04      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 19.69/3.04      inference(bin_hyper_res,[status(thm)],[c_3,c_123]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_717,plain,
% 19.69/3.04      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 19.69/3.04      | r1_tarski(X1,X2) != iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_151]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1716,plain,
% 19.69/3.04      ( k4_xboole_0(X0,k4_xboole_0(X0,sK0(X1))) = k9_subset_1(X1,X0,sK0(X1)) ),
% 19.69/3.04      inference(superposition,[status(thm)],[c_1217,c_717]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_2,plain,
% 19.69/3.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.69/3.04      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 19.69/3.04      inference(cnf_transformation,[],[f32]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_150,plain,
% 19.69/3.04      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 19.69/3.04      | ~ r1_tarski(X2,X0) ),
% 19.69/3.04      inference(bin_hyper_res,[status(thm)],[c_2,c_123]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_718,plain,
% 19.69/3.04      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 19.69/3.04      | r1_tarski(X2,X0) != iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_150]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_3104,plain,
% 19.69/3.04      ( r1_tarski(X0,X1) != iProver_top
% 19.69/3.04      | r1_tarski(k9_subset_1(X1,X2,X0),X1) = iProver_top ),
% 19.69/3.04      inference(superposition,[status(thm)],[c_718,c_723]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_5025,plain,
% 19.69/3.04      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,sK0(X1))),X1) = iProver_top
% 19.69/3.04      | r1_tarski(sK0(X1),X1) != iProver_top ),
% 19.69/3.04      inference(superposition,[status(thm)],[c_1716,c_3104]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_4,plain,
% 19.69/3.04      ( ~ v1_subset_1(sK0(X0),X0) ),
% 19.69/3.04      inference(cnf_transformation,[],[f35]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_8,plain,
% 19.69/3.04      ( v1_subset_1(X0,X1)
% 19.69/3.04      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.69/3.04      | X0 = X1 ),
% 19.69/3.04      inference(cnf_transformation,[],[f39]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_154,plain,
% 19.69/3.04      ( v1_subset_1(X0,X1) | ~ r1_tarski(X0,X1) | X0 = X1 ),
% 19.69/3.04      inference(bin_hyper_res,[status(thm)],[c_8,c_123]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_221,plain,
% 19.69/3.04      ( ~ r1_tarski(X0,X1) | X1 != X2 | X1 = X0 | sK0(X2) != X0 ),
% 19.69/3.04      inference(resolution_lifted,[status(thm)],[c_4,c_154]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_222,plain,
% 19.69/3.04      ( ~ r1_tarski(sK0(X0),X0) | X0 = sK0(X0) ),
% 19.69/3.04      inference(unflattening,[status(thm)],[c_221]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_716,plain,
% 19.69/3.04      ( X0 = sK0(X0) | r1_tarski(sK0(X0),X0) != iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_223,plain,
% 19.69/3.04      ( X0 = sK0(X0) | r1_tarski(sK0(X0),X0) != iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_222]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_15515,plain,
% 19.69/3.04      ( X0 = sK0(X0) ),
% 19.69/3.04      inference(global_propositional_subsumption,
% 19.69/3.04                [status(thm)],
% 19.69/3.04                [c_716,c_223,c_1217]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_57496,plain,
% 19.69/3.04      ( r1_tarski(X0,X0) != iProver_top
% 19.69/3.04      | r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) = iProver_top ),
% 19.69/3.04      inference(demodulation,[status(thm)],[c_5025,c_15515]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_15525,plain,
% 19.69/3.04      ( r1_tarski(X0,X0) = iProver_top ),
% 19.69/3.04      inference(demodulation,[status(thm)],[c_15515,c_1217]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_57498,plain,
% 19.69/3.04      ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) = iProver_top ),
% 19.69/3.04      inference(global_propositional_subsumption,
% 19.69/3.04                [status(thm)],
% 19.69/3.04                [c_57496,c_15525]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_57499,plain,
% 19.69/3.04      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 19.69/3.04      inference(renaming,[status(thm)],[c_57498]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1,plain,
% 19.69/3.04      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 19.69/3.04      inference(cnf_transformation,[],[f30]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_726,plain,
% 19.69/3.04      ( r1_tarski(X0,X1) != iProver_top
% 19.69/3.04      | r1_tarski(X1,X2) != iProver_top
% 19.69/3.04      | r1_tarski(X0,X2) = iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_57565,plain,
% 19.69/3.04      ( r1_tarski(X0,X1) != iProver_top
% 19.69/3.04      | r1_tarski(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X1) = iProver_top ),
% 19.69/3.04      inference(superposition,[status(thm)],[c_57499,c_726]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_0,plain,
% 19.69/3.04      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 19.69/3.04      inference(cnf_transformation,[],[f46]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_727,plain,
% 19.69/3.04      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_5007,plain,
% 19.69/3.04      ( r1_tarski(k9_subset_1(X0,X1,sK0(X0)),X1) = iProver_top ),
% 19.69/3.04      inference(superposition,[status(thm)],[c_1716,c_727]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_13,negated_conjecture,
% 19.69/3.04      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 19.69/3.04      inference(cnf_transformation,[],[f43]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_720,plain,
% 19.69/3.04      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_724,plain,
% 19.69/3.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 19.69/3.04      | r1_tarski(X0,X1) != iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_10,plain,
% 19.69/3.04      ( ~ v2_tex_2(X0,X1)
% 19.69/3.04      | v2_tex_2(X2,X1)
% 19.69/3.04      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.69/3.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.69/3.04      | ~ r1_tarski(X2,X0)
% 19.69/3.04      | ~ l1_pre_topc(X1) ),
% 19.69/3.04      inference(cnf_transformation,[],[f40]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_15,negated_conjecture,
% 19.69/3.04      ( l1_pre_topc(sK1) ),
% 19.69/3.04      inference(cnf_transformation,[],[f41]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_238,plain,
% 19.69/3.04      ( ~ v2_tex_2(X0,X1)
% 19.69/3.04      | v2_tex_2(X2,X1)
% 19.69/3.04      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.69/3.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.69/3.04      | ~ r1_tarski(X2,X0)
% 19.69/3.04      | sK1 != X1 ),
% 19.69/3.04      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_239,plain,
% 19.69/3.04      ( ~ v2_tex_2(X0,sK1)
% 19.69/3.04      | v2_tex_2(X1,sK1)
% 19.69/3.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | ~ r1_tarski(X1,X0) ),
% 19.69/3.04      inference(unflattening,[status(thm)],[c_238]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_715,plain,
% 19.69/3.04      ( v2_tex_2(X0,sK1) != iProver_top
% 19.69/3.04      | v2_tex_2(X1,sK1) = iProver_top
% 19.69/3.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.69/3.04      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.69/3.04      | r1_tarski(X1,X0) != iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_239]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1308,plain,
% 19.69/3.04      ( v2_tex_2(X0,sK1) != iProver_top
% 19.69/3.04      | v2_tex_2(X1,sK1) = iProver_top
% 19.69/3.04      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.69/3.04      | r1_tarski(X1,X0) != iProver_top
% 19.69/3.04      | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
% 19.69/3.04      inference(superposition,[status(thm)],[c_724,c_715]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_2049,plain,
% 19.69/3.04      ( v2_tex_2(X0,sK1) != iProver_top
% 19.69/3.04      | v2_tex_2(sK3,sK1) = iProver_top
% 19.69/3.04      | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top
% 19.69/3.04      | r1_tarski(sK3,X0) != iProver_top ),
% 19.69/3.04      inference(superposition,[status(thm)],[c_720,c_1308]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_5375,plain,
% 19.69/3.04      ( v2_tex_2(k9_subset_1(X0,u1_struct_0(sK1),sK0(X0)),sK1) != iProver_top
% 19.69/3.04      | v2_tex_2(sK3,sK1) = iProver_top
% 19.69/3.04      | r1_tarski(sK3,k9_subset_1(X0,u1_struct_0(sK1),sK0(X0))) != iProver_top ),
% 19.69/3.04      inference(superposition,[status(thm)],[c_5007,c_2049]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_14,negated_conjecture,
% 19.69/3.04      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 19.69/3.04      inference(cnf_transformation,[],[f42]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_17,plain,
% 19.69/3.04      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_18,plain,
% 19.69/3.04      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_12,negated_conjecture,
% 19.69/3.04      ( v2_tex_2(sK3,sK1) | v2_tex_2(sK2,sK1) ),
% 19.69/3.04      inference(cnf_transformation,[],[f44]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_19,plain,
% 19.69/3.04      ( v2_tex_2(sK3,sK1) = iProver_top
% 19.69/3.04      | v2_tex_2(sK2,sK1) = iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_833,plain,
% 19.69/3.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | r1_tarski(X0,u1_struct_0(sK1)) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_7]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_973,plain,
% 19.69/3.04      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | r1_tarski(sK3,u1_struct_0(sK1)) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_833]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_974,plain,
% 19.69/3.04      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.69/3.04      | r1_tarski(sK3,u1_struct_0(sK1)) = iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_973]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_386,plain,( X0 = X0 ),theory(equality) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1157,plain,
% 19.69/3.04      ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_386]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1352,plain,
% 19.69/3.04      ( ~ r1_tarski(sK3,u1_struct_0(sK1))
% 19.69/3.04      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k9_subset_1(u1_struct_0(sK1),sK2,sK3) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_151]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1218,plain,
% 19.69/3.04      ( r1_tarski(sK3,u1_struct_0(sK1)) = iProver_top ),
% 19.69/3.04      inference(superposition,[status(thm)],[c_720,c_723]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1314,plain,
% 19.69/3.04      ( k4_xboole_0(X0,k4_xboole_0(X0,sK3)) = k9_subset_1(u1_struct_0(sK1),X0,sK3) ),
% 19.69/3.04      inference(superposition,[status(thm)],[c_1218,c_717]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_11,negated_conjecture,
% 19.69/3.04      ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1) ),
% 19.69/3.04      inference(cnf_transformation,[],[f45]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_722,plain,
% 19.69/3.04      ( v2_tex_2(k9_subset_1(u1_struct_0(sK1),sK2,sK3),sK1) != iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1412,plain,
% 19.69/3.04      ( v2_tex_2(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK1) != iProver_top ),
% 19.69/3.04      inference(demodulation,[status(thm)],[c_1314,c_722]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_392,plain,
% 19.69/3.04      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.69/3.04      theory(equality) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_776,plain,
% 19.69/3.04      ( ~ m1_subset_1(X0,X1)
% 19.69/3.04      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | X2 != X0
% 19.69/3.04      | k1_zfmisc_1(u1_struct_0(sK1)) != X1 ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_392]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_920,plain,
% 19.69/3.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | X1 != X0
% 19.69/3.04      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_776]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1374,plain,
% 19.69/3.04      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK1),X1,X2),k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | X0 != k9_subset_1(u1_struct_0(sK1),X1,X2)
% 19.69/3.04      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_920]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1976,plain,
% 19.69/3.04      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK1),X1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | X0 != k9_subset_1(u1_struct_0(sK1),X1,sK3)
% 19.69/3.04      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_1374]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_2277,plain,
% 19.69/3.04      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | m1_subset_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k9_subset_1(u1_struct_0(sK1),sK2,sK3)
% 19.69/3.04      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_1976]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_2278,plain,
% 19.69/3.04      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k9_subset_1(u1_struct_0(sK1),sK2,sK3)
% 19.69/3.04      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 19.69/3.04      | m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.69/3.04      | m1_subset_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_2277]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_2004,plain,
% 19.69/3.04      ( v2_tex_2(X0,sK1)
% 19.69/3.04      | ~ v2_tex_2(sK2,sK1)
% 19.69/3.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | ~ r1_tarski(X0,sK2) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_239]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_2173,plain,
% 19.69/3.04      ( v2_tex_2(k4_xboole_0(sK2,k4_xboole_0(sK2,X0)),sK1)
% 19.69/3.04      | ~ v2_tex_2(sK2,sK1)
% 19.69/3.04      | ~ m1_subset_1(k4_xboole_0(sK2,k4_xboole_0(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | ~ r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,X0)),sK2) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_2004]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_4061,plain,
% 19.69/3.04      ( v2_tex_2(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK1)
% 19.69/3.04      | ~ v2_tex_2(sK2,sK1)
% 19.69/3.04      | ~ m1_subset_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | ~ r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK2) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_2173]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_4063,plain,
% 19.69/3.04      ( v2_tex_2(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK1) = iProver_top
% 19.69/3.04      | v2_tex_2(sK2,sK1) != iProver_top
% 19.69/3.04      | m1_subset_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.69/3.04      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.69/3.04      | r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK2) != iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_4061]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1245,plain,
% 19.69/3.04      ( m1_subset_1(k9_subset_1(u1_struct_0(sK1),X0,X1),k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | ~ r1_tarski(X1,u1_struct_0(sK1)) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_150]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1823,plain,
% 19.69/3.04      ( m1_subset_1(k9_subset_1(u1_struct_0(sK1),X0,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | ~ r1_tarski(sK3,u1_struct_0(sK1)) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_1245]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_4566,plain,
% 19.69/3.04      ( m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 19.69/3.04      | ~ r1_tarski(sK3,u1_struct_0(sK1)) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_1823]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_4567,plain,
% 19.69/3.04      ( m1_subset_1(k9_subset_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 19.69/3.04      | r1_tarski(sK3,u1_struct_0(sK1)) != iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_4566]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1422,plain,
% 19.69/3.04      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,X0)),sK2) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_0]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_5722,plain,
% 19.69/3.04      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK2) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_1422]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_5723,plain,
% 19.69/3.04      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK2) = iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_5722]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_5971,plain,
% 19.69/3.04      ( v2_tex_2(sK3,sK1) = iProver_top ),
% 19.69/3.04      inference(global_propositional_subsumption,
% 19.69/3.04                [status(thm)],
% 19.69/3.04                [c_5375,c_17,c_13,c_18,c_19,c_973,c_974,c_1157,c_1352,
% 19.69/3.04                 c_1412,c_2278,c_4063,c_4567,c_5723]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1006,plain,
% 19.69/3.04      ( v2_tex_2(X0,sK1) = iProver_top
% 19.69/3.04      | v2_tex_2(sK3,sK1) != iProver_top
% 19.69/3.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.69/3.04      | r1_tarski(X0,sK3) != iProver_top ),
% 19.69/3.04      inference(superposition,[status(thm)],[c_720,c_715]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1307,plain,
% 19.69/3.04      ( v2_tex_2(X0,sK1) = iProver_top
% 19.69/3.04      | v2_tex_2(sK3,sK1) != iProver_top
% 19.69/3.04      | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top
% 19.69/3.04      | r1_tarski(X0,sK3) != iProver_top ),
% 19.69/3.04      inference(superposition,[status(thm)],[c_724,c_1006]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_839,plain,
% 19.69/3.04      ( ~ r1_tarski(X0,X1)
% 19.69/3.04      | ~ r1_tarski(X1,u1_struct_0(sK1))
% 19.69/3.04      | r1_tarski(X0,u1_struct_0(sK1)) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_1]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1024,plain,
% 19.69/3.04      ( r1_tarski(X0,u1_struct_0(sK1))
% 19.69/3.04      | ~ r1_tarski(X0,sK3)
% 19.69/3.04      | ~ r1_tarski(sK3,u1_struct_0(sK1)) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_839]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1025,plain,
% 19.69/3.04      ( r1_tarski(X0,u1_struct_0(sK1)) = iProver_top
% 19.69/3.04      | r1_tarski(X0,sK3) != iProver_top
% 19.69/3.04      | r1_tarski(sK3,u1_struct_0(sK1)) != iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_1024]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1569,plain,
% 19.69/3.04      ( v2_tex_2(sK3,sK1) != iProver_top
% 19.69/3.04      | v2_tex_2(X0,sK1) = iProver_top
% 19.69/3.04      | r1_tarski(X0,sK3) != iProver_top ),
% 19.69/3.04      inference(global_propositional_subsumption,
% 19.69/3.04                [status(thm)],
% 19.69/3.04                [c_1307,c_18,c_974,c_1025]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1570,plain,
% 19.69/3.04      ( v2_tex_2(X0,sK1) = iProver_top
% 19.69/3.04      | v2_tex_2(sK3,sK1) != iProver_top
% 19.69/3.04      | r1_tarski(X0,sK3) != iProver_top ),
% 19.69/3.04      inference(renaming,[status(thm)],[c_1569]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_5975,plain,
% 19.69/3.04      ( v2_tex_2(X0,sK1) = iProver_top
% 19.69/3.04      | r1_tarski(X0,sK3) != iProver_top ),
% 19.69/3.04      inference(superposition,[status(thm)],[c_5971,c_1570]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_57874,plain,
% 19.69/3.04      ( v2_tex_2(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sK1) = iProver_top
% 19.69/3.04      | r1_tarski(X1,sK3) != iProver_top ),
% 19.69/3.04      inference(superposition,[status(thm)],[c_57565,c_5975]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_63405,plain,
% 19.69/3.04      ( r1_tarski(sK3,sK3) != iProver_top ),
% 19.69/3.04      inference(superposition,[status(thm)],[c_57874,c_1412]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_389,plain,
% 19.69/3.04      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 19.69/3.04      theory(equality) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_887,plain,
% 19.69/3.04      ( ~ r1_tarski(X0,sK3) | r1_tarski(X1,sK3) | X1 != X0 ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_389]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1767,plain,
% 19.69/3.04      ( r1_tarski(X0,sK3) | ~ r1_tarski(sK0(sK3),sK3) | X0 != sK0(sK3) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_887]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_2396,plain,
% 19.69/3.04      ( ~ r1_tarski(sK0(sK3),sK3)
% 19.69/3.04      | r1_tarski(sK3,sK3)
% 19.69/3.04      | sK3 != sK0(sK3) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_1767]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_2397,plain,
% 19.69/3.04      ( sK3 != sK0(sK3)
% 19.69/3.04      | r1_tarski(sK0(sK3),sK3) != iProver_top
% 19.69/3.04      | r1_tarski(sK3,sK3) = iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_2396]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1348,plain,
% 19.69/3.04      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(sK3)) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_5]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1349,plain,
% 19.69/3.04      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(sK3)) = iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_1348]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1332,plain,
% 19.69/3.04      ( ~ r1_tarski(sK0(sK3),sK3) | sK3 = sK0(sK3) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_222]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_882,plain,
% 19.69/3.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3)) | r1_tarski(X0,sK3) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_7]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1109,plain,
% 19.69/3.04      ( ~ m1_subset_1(sK0(sK3),k1_zfmisc_1(sK3))
% 19.69/3.04      | r1_tarski(sK0(sK3),sK3) ),
% 19.69/3.04      inference(instantiation,[status(thm)],[c_882]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(c_1110,plain,
% 19.69/3.04      ( m1_subset_1(sK0(sK3),k1_zfmisc_1(sK3)) != iProver_top
% 19.69/3.04      | r1_tarski(sK0(sK3),sK3) = iProver_top ),
% 19.69/3.04      inference(predicate_to_equality,[status(thm)],[c_1109]) ).
% 19.69/3.04  
% 19.69/3.04  cnf(contradiction,plain,
% 19.69/3.04      ( $false ),
% 19.69/3.04      inference(minisat,
% 19.69/3.04                [status(thm)],
% 19.69/3.04                [c_63405,c_2397,c_1349,c_1348,c_1332,c_1110,c_1109]) ).
% 19.69/3.04  
% 19.69/3.04  
% 19.69/3.04  % SZS output end CNFRefutation for theBenchmark.p
% 19.69/3.04  
% 19.69/3.04  ------                               Statistics
% 19.69/3.04  
% 19.69/3.04  ------ General
% 19.69/3.04  
% 19.69/3.04  abstr_ref_over_cycles:                  0
% 19.69/3.04  abstr_ref_under_cycles:                 0
% 19.69/3.04  gc_basic_clause_elim:                   0
% 19.69/3.04  forced_gc_time:                         0
% 19.69/3.04  parsing_time:                           0.012
% 19.69/3.04  unif_index_cands_time:                  0.
% 19.69/3.04  unif_index_add_time:                    0.
% 19.69/3.04  orderings_time:                         0.
% 19.69/3.04  out_proof_time:                         0.019
% 19.69/3.04  total_time:                             2.375
% 19.69/3.04  num_of_symbols:                         44
% 19.69/3.04  num_of_terms:                           104542
% 19.69/3.04  
% 19.69/3.04  ------ Preprocessing
% 19.69/3.04  
% 19.69/3.04  num_of_splits:                          0
% 19.69/3.04  num_of_split_atoms:                     0
% 19.69/3.04  num_of_reused_defs:                     0
% 19.69/3.04  num_eq_ax_congr_red:                    10
% 19.69/3.04  num_of_sem_filtered_clauses:            1
% 19.69/3.04  num_of_subtypes:                        0
% 19.69/3.04  monotx_restored_types:                  0
% 19.69/3.04  sat_num_of_epr_types:                   0
% 19.69/3.04  sat_num_of_non_cyclic_types:            0
% 19.69/3.04  sat_guarded_non_collapsed_types:        0
% 19.69/3.04  num_pure_diseq_elim:                    0
% 19.69/3.04  simp_replaced_by:                       0
% 19.69/3.04  res_preprocessed:                       74
% 19.69/3.04  prep_upred:                             0
% 19.69/3.04  prep_unflattend:                        5
% 19.69/3.04  smt_new_axioms:                         0
% 19.69/3.04  pred_elim_cands:                        3
% 19.69/3.04  pred_elim:                              2
% 19.69/3.04  pred_elim_cl:                           3
% 19.69/3.04  pred_elim_cycles:                       4
% 19.69/3.04  merged_defs:                            8
% 19.69/3.04  merged_defs_ncl:                        0
% 19.69/3.04  bin_hyper_res:                          11
% 19.69/3.04  prep_cycles:                            4
% 19.69/3.04  pred_elim_time:                         0.001
% 19.69/3.04  splitting_time:                         0.
% 19.69/3.04  sem_filter_time:                        0.
% 19.69/3.04  monotx_time:                            0.001
% 19.69/3.04  subtype_inf_time:                       0.
% 19.69/3.04  
% 19.69/3.04  ------ Problem properties
% 19.69/3.04  
% 19.69/3.04  clauses:                                13
% 19.69/3.04  conjectures:                            4
% 19.69/3.04  epr:                                    2
% 19.69/3.04  horn:                                   12
% 19.69/3.04  ground:                                 4
% 19.69/3.04  unary:                                  5
% 19.69/3.04  binary:                                 6
% 19.69/3.04  lits:                                   25
% 19.69/3.04  lits_eq:                                2
% 19.69/3.04  fd_pure:                                0
% 19.69/3.04  fd_pseudo:                              0
% 19.69/3.04  fd_cond:                                0
% 19.69/3.04  fd_pseudo_cond:                         0
% 19.69/3.04  ac_symbols:                             0
% 19.69/3.04  
% 19.69/3.04  ------ Propositional Solver
% 19.69/3.04  
% 19.69/3.04  prop_solver_calls:                      41
% 19.69/3.04  prop_fast_solver_calls:                 1966
% 19.69/3.04  smt_solver_calls:                       0
% 19.69/3.04  smt_fast_solver_calls:                  0
% 19.69/3.04  prop_num_of_clauses:                    40503
% 19.69/3.04  prop_preprocess_simplified:             36579
% 19.69/3.04  prop_fo_subsumed:                       217
% 19.69/3.04  prop_solver_time:                       0.
% 19.69/3.04  smt_solver_time:                        0.
% 19.69/3.04  smt_fast_solver_time:                   0.
% 19.69/3.04  prop_fast_solver_time:                  0.
% 19.69/3.04  prop_unsat_core_time:                   0.004
% 19.69/3.04  
% 19.69/3.04  ------ QBF
% 19.69/3.04  
% 19.69/3.04  qbf_q_res:                              0
% 19.69/3.04  qbf_num_tautologies:                    0
% 19.69/3.04  qbf_prep_cycles:                        0
% 19.69/3.04  
% 19.69/3.04  ------ BMC1
% 19.69/3.04  
% 19.69/3.04  bmc1_current_bound:                     -1
% 19.69/3.04  bmc1_last_solved_bound:                 -1
% 19.69/3.04  bmc1_unsat_core_size:                   -1
% 19.69/3.04  bmc1_unsat_core_parents_size:           -1
% 19.69/3.04  bmc1_merge_next_fun:                    0
% 19.69/3.04  bmc1_unsat_core_clauses_time:           0.
% 19.69/3.04  
% 19.69/3.04  ------ Instantiation
% 19.69/3.04  
% 19.69/3.04  inst_num_of_clauses:                    4404
% 19.69/3.04  inst_num_in_passive:                    1917
% 19.69/3.04  inst_num_in_active:                     2207
% 19.69/3.04  inst_num_in_unprocessed:                286
% 19.69/3.04  inst_num_of_loops:                      2350
% 19.69/3.04  inst_num_of_learning_restarts:          0
% 19.69/3.04  inst_num_moves_active_passive:          138
% 19.69/3.04  inst_lit_activity:                      0
% 19.69/3.04  inst_lit_activity_moves:                0
% 19.69/3.04  inst_num_tautologies:                   0
% 19.69/3.04  inst_num_prop_implied:                  0
% 19.69/3.04  inst_num_existing_simplified:           0
% 19.69/3.04  inst_num_eq_res_simplified:             0
% 19.69/3.04  inst_num_child_elim:                    0
% 19.69/3.04  inst_num_of_dismatching_blockings:      4550
% 19.69/3.04  inst_num_of_non_proper_insts:           5905
% 19.69/3.04  inst_num_of_duplicates:                 0
% 19.69/3.04  inst_inst_num_from_inst_to_res:         0
% 19.69/3.04  inst_dismatching_checking_time:         0.
% 19.69/3.04  
% 19.69/3.04  ------ Resolution
% 19.69/3.04  
% 19.69/3.04  res_num_of_clauses:                     0
% 19.69/3.04  res_num_in_passive:                     0
% 19.69/3.04  res_num_in_active:                      0
% 19.69/3.04  res_num_of_loops:                       78
% 19.69/3.04  res_forward_subset_subsumed:            585
% 19.69/3.04  res_backward_subset_subsumed:           60
% 19.69/3.04  res_forward_subsumed:                   0
% 19.69/3.04  res_backward_subsumed:                  0
% 19.69/3.04  res_forward_subsumption_resolution:     0
% 19.69/3.04  res_backward_subsumption_resolution:    0
% 19.69/3.04  res_clause_to_clause_subsumption:       63079
% 19.69/3.04  res_orphan_elimination:                 0
% 19.69/3.04  res_tautology_del:                      672
% 19.69/3.04  res_num_eq_res_simplified:              0
% 19.69/3.04  res_num_sel_changes:                    0
% 19.69/3.04  res_moves_from_active_to_pass:          0
% 19.69/3.04  
% 19.69/3.04  ------ Superposition
% 19.69/3.04  
% 19.69/3.04  sup_time_total:                         0.
% 19.69/3.04  sup_time_generating:                    0.
% 19.69/3.04  sup_time_sim_full:                      0.
% 19.69/3.04  sup_time_sim_immed:                     0.
% 19.69/3.04  
% 19.69/3.04  sup_num_of_clauses:                     7234
% 19.69/3.04  sup_num_in_active:                      400
% 19.69/3.04  sup_num_in_passive:                     6834
% 19.69/3.04  sup_num_of_loops:                       469
% 19.69/3.04  sup_fw_superposition:                   5572
% 19.69/3.04  sup_bw_superposition:                   4897
% 19.69/3.04  sup_immediate_simplified:               1266
% 19.69/3.04  sup_given_eliminated:                   0
% 19.69/3.04  comparisons_done:                       0
% 19.69/3.04  comparisons_avoided:                    0
% 19.69/3.04  
% 19.69/3.04  ------ Simplifications
% 19.69/3.04  
% 19.69/3.04  
% 19.69/3.04  sim_fw_subset_subsumed:                 267
% 19.69/3.04  sim_bw_subset_subsumed:                 76
% 19.69/3.04  sim_fw_subsumed:                        458
% 19.69/3.04  sim_bw_subsumed:                        159
% 19.69/3.04  sim_fw_subsumption_res:                 0
% 19.69/3.04  sim_bw_subsumption_res:                 0
% 19.69/3.04  sim_tautology_del:                      12
% 19.69/3.04  sim_eq_tautology_del:                   5
% 19.69/3.04  sim_eq_res_simp:                        0
% 19.69/3.04  sim_fw_demodulated:                     481
% 19.69/3.04  sim_bw_demodulated:                     39
% 19.69/3.04  sim_light_normalised:                   66
% 19.69/3.04  sim_joinable_taut:                      0
% 19.69/3.04  sim_joinable_simp:                      0
% 19.69/3.04  sim_ac_normalised:                      0
% 19.69/3.04  sim_smt_subsumption:                    0
% 19.69/3.04  
%------------------------------------------------------------------------------
