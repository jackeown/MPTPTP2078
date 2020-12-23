%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:30 EST 2020

% Result     : Theorem 0.83s
% Output     : CNFRefutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 204 expanded)
%              Number of clauses        :   55 (  84 expanded)
%              Number of leaves         :   12 (  45 expanded)
%              Depth                    :   17
%              Number of atoms          :  233 ( 779 expanded)
%              Number of equality atoms :   62 (  88 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v3_pre_topc(X1,X0) )
          & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v3_pre_topc(X1,X0) )
          & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v3_pre_topc(X1,X0) )
          & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),sK1),X0)
          | ~ v3_pre_topc(sK1,X0) )
        & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),sK1),X0)
          | v3_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | ~ v3_pre_topc(X1,sK0) )
          & ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18,f17])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f29,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f28,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_621,plain,
    ( X0_39 != X1_39
    | X2_39 != X1_39
    | X2_39 = X0_39 ),
    theory(equality)).

cnf(c_1196,plain,
    ( X0_39 != X1_39
    | X0_39 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) != X1_39 ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_1197,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) != sK1
    | sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_624,plain,
    ( ~ v3_pre_topc(X0_39,X0_40)
    | v3_pre_topc(X1_39,X0_40)
    | X1_39 != X0_39 ),
    theory(equality)).

cnf(c_1082,plain,
    ( v3_pre_topc(X0_39,sK0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | X0_39 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_1084,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | v3_pre_topc(sK1,sK0)
    | sK1 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_1082])).

cnf(c_8,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_616,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_752,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_616])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_618,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(X0_41))
    | k3_subset_1(X0_41,X0_39) = k4_xboole_0(X0_41,X0_39) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_750,plain,
    ( k3_subset_1(X0_41,X0_39) = k4_xboole_0(X0_41,X0_39)
    | m1_subset_1(X0_39,k1_zfmisc_1(X0_41)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_618])).

cnf(c_928,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_752,c_750])).

cnf(c_6,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_77,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_9,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_168,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_9])).

cnf(c_169,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_168])).

cnf(c_310,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),sK1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_77,c_169])).

cnf(c_311,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_613,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_311])).

cnf(c_755,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) != iProver_top
    | v3_pre_topc(sK1,sK0) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_937,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)),sK0) != iProver_top
    | v3_pre_topc(sK1,sK0) != iProver_top
    | m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_928,c_755])).

cnf(c_312,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) != iProver_top
    | v3_pre_topc(sK1,sK0) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_617,plain,
    ( ~ m1_subset_1(X0_39,k1_zfmisc_1(X0_41))
    | k3_subset_1(X0_41,k3_subset_1(X0_41,X0_39)) = X0_39 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_794,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_617])).

cnf(c_802,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_618])).

cnf(c_623,plain,
    ( ~ m1_subset_1(X0_39,X0_42)
    | m1_subset_1(X1_39,X0_42)
    | X1_39 != X0_39 ),
    theory(equality)).

cnf(c_813,plain,
    ( m1_subset_1(X0_39,k1_zfmisc_1(X0_41))
    | ~ m1_subset_1(k4_xboole_0(X0_41,X1_39),k1_zfmisc_1(X0_41))
    | X0_39 != k4_xboole_0(X0_41,X1_39) ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_839,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),sK1) != k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_813])).

cnf(c_840,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k4_xboole_0(u1_struct_0(sK0),sK1)
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_839])).

cnf(c_0,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_142,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | k4_xboole_0(X2,X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_143,plain,
    ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_142])).

cnf(c_615,plain,
    ( m1_subset_1(k4_xboole_0(X0_41,X0_39),k1_zfmisc_1(X0_41)) ),
    inference(subtyping,[status(esa)],[c_143])).

cnf(c_854,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_615])).

cnf(c_855,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_854])).

cnf(c_917,plain,
    ( ~ v3_pre_topc(X0_39,sK0)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) != X0_39 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_918,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) != X0_39
    | v3_pre_topc(X0_39,sK0) != iProver_top
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_917])).

cnf(c_920,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) != sK1
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) = iProver_top
    | v3_pre_topc(sK1,sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_918])).

cnf(c_1012,plain,
    ( v3_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_937,c_8,c_312,c_794,c_802,c_840,c_855,c_920])).

cnf(c_1014,plain,
    ( ~ v3_pre_topc(sK1,sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1012])).

cnf(c_620,plain,
    ( X0_39 = X0_39 ),
    theory(equality)).

cnf(c_629,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_7,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_79,plain,
    ( v3_pre_topc(sK1,sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_153,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_9])).

cnf(c_154,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_153])).

cnf(c_297,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),sK1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_79,c_154])).

cnf(c_298,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1197,c_1084,c_1014,c_854,c_839,c_802,c_794,c_629,c_298,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:40:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.83/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.83/1.02  
% 0.83/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.83/1.02  
% 0.83/1.02  ------  iProver source info
% 0.83/1.02  
% 0.83/1.02  git: date: 2020-06-30 10:37:57 +0100
% 0.83/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.83/1.02  git: non_committed_changes: false
% 0.83/1.02  git: last_make_outside_of_git: false
% 0.83/1.02  
% 0.83/1.02  ------ 
% 0.83/1.02  
% 0.83/1.02  ------ Input Options
% 0.83/1.02  
% 0.83/1.02  --out_options                           all
% 0.83/1.02  --tptp_safe_out                         true
% 0.83/1.02  --problem_path                          ""
% 0.83/1.02  --include_path                          ""
% 0.83/1.02  --clausifier                            res/vclausify_rel
% 0.83/1.02  --clausifier_options                    --mode clausify
% 0.83/1.02  --stdin                                 false
% 0.83/1.02  --stats_out                             all
% 0.83/1.02  
% 0.83/1.02  ------ General Options
% 0.83/1.02  
% 0.83/1.02  --fof                                   false
% 0.83/1.02  --time_out_real                         305.
% 0.83/1.02  --time_out_virtual                      -1.
% 0.83/1.02  --symbol_type_check                     false
% 0.83/1.02  --clausify_out                          false
% 0.83/1.02  --sig_cnt_out                           false
% 0.83/1.02  --trig_cnt_out                          false
% 0.83/1.02  --trig_cnt_out_tolerance                1.
% 0.83/1.02  --trig_cnt_out_sk_spl                   false
% 0.83/1.02  --abstr_cl_out                          false
% 0.83/1.02  
% 0.83/1.02  ------ Global Options
% 0.83/1.02  
% 0.83/1.02  --schedule                              default
% 0.83/1.02  --add_important_lit                     false
% 0.83/1.02  --prop_solver_per_cl                    1000
% 0.83/1.02  --min_unsat_core                        false
% 0.83/1.02  --soft_assumptions                      false
% 0.83/1.02  --soft_lemma_size                       3
% 0.83/1.02  --prop_impl_unit_size                   0
% 0.83/1.02  --prop_impl_unit                        []
% 0.83/1.02  --share_sel_clauses                     true
% 0.83/1.02  --reset_solvers                         false
% 0.83/1.02  --bc_imp_inh                            [conj_cone]
% 0.83/1.02  --conj_cone_tolerance                   3.
% 0.83/1.02  --extra_neg_conj                        none
% 0.83/1.02  --large_theory_mode                     true
% 0.83/1.02  --prolific_symb_bound                   200
% 0.83/1.02  --lt_threshold                          2000
% 0.83/1.02  --clause_weak_htbl                      true
% 0.83/1.02  --gc_record_bc_elim                     false
% 0.83/1.02  
% 0.83/1.02  ------ Preprocessing Options
% 0.83/1.02  
% 0.83/1.02  --preprocessing_flag                    true
% 0.83/1.02  --time_out_prep_mult                    0.1
% 0.83/1.02  --splitting_mode                        input
% 0.83/1.02  --splitting_grd                         true
% 0.83/1.02  --splitting_cvd                         false
% 0.83/1.02  --splitting_cvd_svl                     false
% 0.83/1.02  --splitting_nvd                         32
% 0.83/1.02  --sub_typing                            true
% 0.83/1.02  --prep_gs_sim                           true
% 0.83/1.02  --prep_unflatten                        true
% 0.83/1.02  --prep_res_sim                          true
% 0.83/1.02  --prep_upred                            true
% 0.83/1.02  --prep_sem_filter                       exhaustive
% 0.83/1.02  --prep_sem_filter_out                   false
% 0.83/1.02  --pred_elim                             true
% 0.83/1.02  --res_sim_input                         true
% 0.83/1.02  --eq_ax_congr_red                       true
% 0.83/1.02  --pure_diseq_elim                       true
% 0.83/1.02  --brand_transform                       false
% 0.83/1.02  --non_eq_to_eq                          false
% 0.83/1.02  --prep_def_merge                        true
% 0.83/1.02  --prep_def_merge_prop_impl              false
% 0.83/1.02  --prep_def_merge_mbd                    true
% 0.83/1.02  --prep_def_merge_tr_red                 false
% 0.83/1.02  --prep_def_merge_tr_cl                  false
% 0.83/1.02  --smt_preprocessing                     true
% 0.83/1.02  --smt_ac_axioms                         fast
% 0.83/1.02  --preprocessed_out                      false
% 0.83/1.02  --preprocessed_stats                    false
% 0.83/1.02  
% 0.83/1.02  ------ Abstraction refinement Options
% 0.83/1.02  
% 0.83/1.02  --abstr_ref                             []
% 0.83/1.02  --abstr_ref_prep                        false
% 0.83/1.02  --abstr_ref_until_sat                   false
% 0.83/1.02  --abstr_ref_sig_restrict                funpre
% 0.83/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.83/1.02  --abstr_ref_under                       []
% 0.83/1.02  
% 0.83/1.02  ------ SAT Options
% 0.83/1.02  
% 0.83/1.02  --sat_mode                              false
% 0.83/1.02  --sat_fm_restart_options                ""
% 0.83/1.02  --sat_gr_def                            false
% 0.83/1.02  --sat_epr_types                         true
% 0.83/1.02  --sat_non_cyclic_types                  false
% 0.83/1.02  --sat_finite_models                     false
% 0.83/1.02  --sat_fm_lemmas                         false
% 0.83/1.02  --sat_fm_prep                           false
% 0.83/1.02  --sat_fm_uc_incr                        true
% 0.83/1.02  --sat_out_model                         small
% 0.83/1.02  --sat_out_clauses                       false
% 0.83/1.02  
% 0.83/1.02  ------ QBF Options
% 0.83/1.02  
% 0.83/1.02  --qbf_mode                              false
% 0.83/1.02  --qbf_elim_univ                         false
% 0.83/1.02  --qbf_dom_inst                          none
% 0.83/1.02  --qbf_dom_pre_inst                      false
% 0.83/1.02  --qbf_sk_in                             false
% 0.83/1.02  --qbf_pred_elim                         true
% 0.83/1.02  --qbf_split                             512
% 0.83/1.02  
% 0.83/1.02  ------ BMC1 Options
% 0.83/1.02  
% 0.83/1.02  --bmc1_incremental                      false
% 0.83/1.02  --bmc1_axioms                           reachable_all
% 0.83/1.02  --bmc1_min_bound                        0
% 0.83/1.02  --bmc1_max_bound                        -1
% 0.83/1.02  --bmc1_max_bound_default                -1
% 0.83/1.02  --bmc1_symbol_reachability              true
% 0.83/1.02  --bmc1_property_lemmas                  false
% 0.83/1.02  --bmc1_k_induction                      false
% 0.83/1.02  --bmc1_non_equiv_states                 false
% 0.83/1.02  --bmc1_deadlock                         false
% 0.83/1.02  --bmc1_ucm                              false
% 0.83/1.02  --bmc1_add_unsat_core                   none
% 0.83/1.02  --bmc1_unsat_core_children              false
% 0.83/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.83/1.02  --bmc1_out_stat                         full
% 0.83/1.02  --bmc1_ground_init                      false
% 0.83/1.02  --bmc1_pre_inst_next_state              false
% 0.83/1.02  --bmc1_pre_inst_state                   false
% 0.83/1.02  --bmc1_pre_inst_reach_state             false
% 0.83/1.02  --bmc1_out_unsat_core                   false
% 0.83/1.02  --bmc1_aig_witness_out                  false
% 0.83/1.02  --bmc1_verbose                          false
% 0.83/1.02  --bmc1_dump_clauses_tptp                false
% 0.83/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.83/1.02  --bmc1_dump_file                        -
% 0.83/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.83/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.83/1.02  --bmc1_ucm_extend_mode                  1
% 0.83/1.02  --bmc1_ucm_init_mode                    2
% 0.83/1.02  --bmc1_ucm_cone_mode                    none
% 0.83/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.83/1.02  --bmc1_ucm_relax_model                  4
% 0.83/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.83/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.83/1.02  --bmc1_ucm_layered_model                none
% 0.83/1.02  --bmc1_ucm_max_lemma_size               10
% 0.83/1.02  
% 0.83/1.02  ------ AIG Options
% 0.83/1.02  
% 0.83/1.02  --aig_mode                              false
% 0.83/1.02  
% 0.83/1.02  ------ Instantiation Options
% 0.83/1.02  
% 0.83/1.02  --instantiation_flag                    true
% 0.83/1.02  --inst_sos_flag                         false
% 0.83/1.02  --inst_sos_phase                        true
% 0.83/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.83/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.83/1.02  --inst_lit_sel_side                     num_symb
% 0.83/1.02  --inst_solver_per_active                1400
% 0.83/1.02  --inst_solver_calls_frac                1.
% 0.83/1.02  --inst_passive_queue_type               priority_queues
% 0.83/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.83/1.02  --inst_passive_queues_freq              [25;2]
% 0.83/1.02  --inst_dismatching                      true
% 0.83/1.02  --inst_eager_unprocessed_to_passive     true
% 0.83/1.02  --inst_prop_sim_given                   true
% 0.83/1.02  --inst_prop_sim_new                     false
% 0.83/1.02  --inst_subs_new                         false
% 0.83/1.02  --inst_eq_res_simp                      false
% 0.83/1.02  --inst_subs_given                       false
% 0.83/1.02  --inst_orphan_elimination               true
% 0.83/1.02  --inst_learning_loop_flag               true
% 0.83/1.02  --inst_learning_start                   3000
% 0.83/1.02  --inst_learning_factor                  2
% 0.83/1.02  --inst_start_prop_sim_after_learn       3
% 0.83/1.02  --inst_sel_renew                        solver
% 0.83/1.02  --inst_lit_activity_flag                true
% 0.83/1.02  --inst_restr_to_given                   false
% 0.83/1.02  --inst_activity_threshold               500
% 0.83/1.02  --inst_out_proof                        true
% 0.83/1.02  
% 0.83/1.02  ------ Resolution Options
% 0.83/1.02  
% 0.83/1.02  --resolution_flag                       true
% 0.83/1.02  --res_lit_sel                           adaptive
% 0.83/1.02  --res_lit_sel_side                      none
% 0.83/1.02  --res_ordering                          kbo
% 0.83/1.02  --res_to_prop_solver                    active
% 0.83/1.02  --res_prop_simpl_new                    false
% 0.83/1.02  --res_prop_simpl_given                  true
% 0.83/1.02  --res_passive_queue_type                priority_queues
% 0.83/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.83/1.02  --res_passive_queues_freq               [15;5]
% 0.83/1.02  --res_forward_subs                      full
% 0.83/1.02  --res_backward_subs                     full
% 0.83/1.02  --res_forward_subs_resolution           true
% 0.83/1.02  --res_backward_subs_resolution          true
% 0.83/1.02  --res_orphan_elimination                true
% 0.83/1.02  --res_time_limit                        2.
% 0.83/1.02  --res_out_proof                         true
% 0.83/1.02  
% 0.83/1.02  ------ Superposition Options
% 0.83/1.02  
% 0.83/1.02  --superposition_flag                    true
% 0.83/1.02  --sup_passive_queue_type                priority_queues
% 0.83/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.83/1.02  --sup_passive_queues_freq               [8;1;4]
% 0.83/1.02  --demod_completeness_check              fast
% 0.83/1.02  --demod_use_ground                      true
% 0.83/1.02  --sup_to_prop_solver                    passive
% 0.83/1.02  --sup_prop_simpl_new                    true
% 0.83/1.02  --sup_prop_simpl_given                  true
% 0.83/1.02  --sup_fun_splitting                     false
% 0.83/1.02  --sup_smt_interval                      50000
% 0.83/1.02  
% 0.83/1.02  ------ Superposition Simplification Setup
% 0.83/1.02  
% 0.83/1.02  --sup_indices_passive                   []
% 0.83/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 0.83/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.02  --sup_full_bw                           [BwDemod]
% 0.83/1.02  --sup_immed_triv                        [TrivRules]
% 0.83/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.83/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.02  --sup_immed_bw_main                     []
% 0.83/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 0.83/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/1.02  
% 0.83/1.02  ------ Combination Options
% 0.83/1.02  
% 0.83/1.02  --comb_res_mult                         3
% 0.83/1.02  --comb_sup_mult                         2
% 0.83/1.02  --comb_inst_mult                        10
% 0.83/1.02  
% 0.83/1.02  ------ Debug Options
% 0.83/1.02  
% 0.83/1.02  --dbg_backtrace                         false
% 0.83/1.02  --dbg_dump_prop_clauses                 false
% 0.83/1.02  --dbg_dump_prop_clauses_file            -
% 0.83/1.02  --dbg_out_stat                          false
% 0.83/1.02  ------ Parsing...
% 0.83/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.83/1.02  
% 0.83/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 0.83/1.02  
% 0.83/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.83/1.02  
% 0.83/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.83/1.02  ------ Proving...
% 0.83/1.02  ------ Problem Properties 
% 0.83/1.02  
% 0.83/1.02  
% 0.83/1.02  clauses                                 6
% 0.83/1.02  conjectures                             1
% 0.83/1.02  EPR                                     0
% 0.83/1.02  Horn                                    5
% 0.83/1.02  unary                                   2
% 0.83/1.02  binary                                  2
% 0.83/1.02  lits                                    12
% 0.83/1.02  lits eq                                 2
% 0.83/1.02  fd_pure                                 0
% 0.83/1.02  fd_pseudo                               0
% 0.83/1.02  fd_cond                                 0
% 0.83/1.02  fd_pseudo_cond                          0
% 0.83/1.02  AC symbols                              0
% 0.83/1.02  
% 0.83/1.02  ------ Schedule dynamic 5 is on 
% 0.83/1.02  
% 0.83/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.83/1.02  
% 0.83/1.02  
% 0.83/1.02  ------ 
% 0.83/1.02  Current options:
% 0.83/1.02  ------ 
% 0.83/1.02  
% 0.83/1.02  ------ Input Options
% 0.83/1.02  
% 0.83/1.02  --out_options                           all
% 0.83/1.02  --tptp_safe_out                         true
% 0.83/1.02  --problem_path                          ""
% 0.83/1.02  --include_path                          ""
% 0.83/1.02  --clausifier                            res/vclausify_rel
% 0.83/1.02  --clausifier_options                    --mode clausify
% 0.83/1.02  --stdin                                 false
% 0.83/1.02  --stats_out                             all
% 0.83/1.02  
% 0.83/1.02  ------ General Options
% 0.83/1.02  
% 0.83/1.02  --fof                                   false
% 0.83/1.02  --time_out_real                         305.
% 0.83/1.02  --time_out_virtual                      -1.
% 0.83/1.02  --symbol_type_check                     false
% 0.83/1.02  --clausify_out                          false
% 0.83/1.02  --sig_cnt_out                           false
% 0.83/1.02  --trig_cnt_out                          false
% 0.83/1.02  --trig_cnt_out_tolerance                1.
% 0.83/1.02  --trig_cnt_out_sk_spl                   false
% 0.83/1.02  --abstr_cl_out                          false
% 0.83/1.02  
% 0.83/1.02  ------ Global Options
% 0.83/1.02  
% 0.83/1.02  --schedule                              default
% 0.83/1.02  --add_important_lit                     false
% 0.83/1.02  --prop_solver_per_cl                    1000
% 0.83/1.02  --min_unsat_core                        false
% 0.83/1.02  --soft_assumptions                      false
% 0.83/1.02  --soft_lemma_size                       3
% 0.83/1.02  --prop_impl_unit_size                   0
% 0.83/1.02  --prop_impl_unit                        []
% 0.83/1.02  --share_sel_clauses                     true
% 0.83/1.02  --reset_solvers                         false
% 0.83/1.02  --bc_imp_inh                            [conj_cone]
% 0.83/1.02  --conj_cone_tolerance                   3.
% 0.83/1.02  --extra_neg_conj                        none
% 0.83/1.02  --large_theory_mode                     true
% 0.83/1.02  --prolific_symb_bound                   200
% 0.83/1.02  --lt_threshold                          2000
% 0.83/1.02  --clause_weak_htbl                      true
% 0.83/1.02  --gc_record_bc_elim                     false
% 0.83/1.02  
% 0.83/1.02  ------ Preprocessing Options
% 0.83/1.02  
% 0.83/1.02  --preprocessing_flag                    true
% 0.83/1.02  --time_out_prep_mult                    0.1
% 0.83/1.02  --splitting_mode                        input
% 0.83/1.02  --splitting_grd                         true
% 0.83/1.02  --splitting_cvd                         false
% 0.83/1.02  --splitting_cvd_svl                     false
% 0.83/1.02  --splitting_nvd                         32
% 0.83/1.02  --sub_typing                            true
% 0.83/1.02  --prep_gs_sim                           true
% 0.83/1.02  --prep_unflatten                        true
% 0.83/1.02  --prep_res_sim                          true
% 0.83/1.02  --prep_upred                            true
% 0.83/1.02  --prep_sem_filter                       exhaustive
% 0.83/1.02  --prep_sem_filter_out                   false
% 0.83/1.02  --pred_elim                             true
% 0.83/1.02  --res_sim_input                         true
% 0.83/1.02  --eq_ax_congr_red                       true
% 0.83/1.02  --pure_diseq_elim                       true
% 0.83/1.02  --brand_transform                       false
% 0.83/1.02  --non_eq_to_eq                          false
% 0.83/1.02  --prep_def_merge                        true
% 0.83/1.02  --prep_def_merge_prop_impl              false
% 0.83/1.02  --prep_def_merge_mbd                    true
% 0.83/1.02  --prep_def_merge_tr_red                 false
% 0.83/1.02  --prep_def_merge_tr_cl                  false
% 0.83/1.02  --smt_preprocessing                     true
% 0.83/1.02  --smt_ac_axioms                         fast
% 0.83/1.02  --preprocessed_out                      false
% 0.83/1.02  --preprocessed_stats                    false
% 0.83/1.02  
% 0.83/1.02  ------ Abstraction refinement Options
% 0.83/1.02  
% 0.83/1.02  --abstr_ref                             []
% 0.83/1.02  --abstr_ref_prep                        false
% 0.83/1.02  --abstr_ref_until_sat                   false
% 0.83/1.02  --abstr_ref_sig_restrict                funpre
% 0.83/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.83/1.02  --abstr_ref_under                       []
% 0.83/1.02  
% 0.83/1.02  ------ SAT Options
% 0.83/1.02  
% 0.83/1.02  --sat_mode                              false
% 0.83/1.02  --sat_fm_restart_options                ""
% 0.83/1.02  --sat_gr_def                            false
% 0.83/1.02  --sat_epr_types                         true
% 0.83/1.02  --sat_non_cyclic_types                  false
% 0.83/1.02  --sat_finite_models                     false
% 0.83/1.02  --sat_fm_lemmas                         false
% 0.83/1.02  --sat_fm_prep                           false
% 0.83/1.02  --sat_fm_uc_incr                        true
% 0.83/1.02  --sat_out_model                         small
% 0.83/1.02  --sat_out_clauses                       false
% 0.83/1.02  
% 0.83/1.02  ------ QBF Options
% 0.83/1.02  
% 0.83/1.02  --qbf_mode                              false
% 0.83/1.02  --qbf_elim_univ                         false
% 0.83/1.02  --qbf_dom_inst                          none
% 0.83/1.02  --qbf_dom_pre_inst                      false
% 0.83/1.02  --qbf_sk_in                             false
% 0.83/1.02  --qbf_pred_elim                         true
% 0.83/1.02  --qbf_split                             512
% 0.83/1.02  
% 0.83/1.02  ------ BMC1 Options
% 0.83/1.02  
% 0.83/1.02  --bmc1_incremental                      false
% 0.83/1.02  --bmc1_axioms                           reachable_all
% 0.83/1.02  --bmc1_min_bound                        0
% 0.83/1.02  --bmc1_max_bound                        -1
% 0.83/1.02  --bmc1_max_bound_default                -1
% 0.83/1.02  --bmc1_symbol_reachability              true
% 0.83/1.02  --bmc1_property_lemmas                  false
% 0.83/1.02  --bmc1_k_induction                      false
% 0.83/1.02  --bmc1_non_equiv_states                 false
% 0.83/1.02  --bmc1_deadlock                         false
% 0.83/1.02  --bmc1_ucm                              false
% 0.83/1.02  --bmc1_add_unsat_core                   none
% 0.83/1.02  --bmc1_unsat_core_children              false
% 0.83/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.83/1.02  --bmc1_out_stat                         full
% 0.83/1.02  --bmc1_ground_init                      false
% 0.83/1.02  --bmc1_pre_inst_next_state              false
% 0.83/1.02  --bmc1_pre_inst_state                   false
% 0.83/1.02  --bmc1_pre_inst_reach_state             false
% 0.83/1.02  --bmc1_out_unsat_core                   false
% 0.83/1.02  --bmc1_aig_witness_out                  false
% 0.83/1.02  --bmc1_verbose                          false
% 0.83/1.02  --bmc1_dump_clauses_tptp                false
% 0.83/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.83/1.02  --bmc1_dump_file                        -
% 0.83/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.83/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.83/1.02  --bmc1_ucm_extend_mode                  1
% 0.83/1.02  --bmc1_ucm_init_mode                    2
% 0.83/1.02  --bmc1_ucm_cone_mode                    none
% 0.83/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.83/1.02  --bmc1_ucm_relax_model                  4
% 0.83/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.83/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.83/1.02  --bmc1_ucm_layered_model                none
% 0.83/1.02  --bmc1_ucm_max_lemma_size               10
% 0.83/1.02  
% 0.83/1.02  ------ AIG Options
% 0.83/1.02  
% 0.83/1.02  --aig_mode                              false
% 0.83/1.02  
% 0.83/1.02  ------ Instantiation Options
% 0.83/1.02  
% 0.83/1.02  --instantiation_flag                    true
% 0.83/1.02  --inst_sos_flag                         false
% 0.83/1.02  --inst_sos_phase                        true
% 0.83/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.83/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.83/1.02  --inst_lit_sel_side                     none
% 0.83/1.02  --inst_solver_per_active                1400
% 0.83/1.02  --inst_solver_calls_frac                1.
% 0.83/1.02  --inst_passive_queue_type               priority_queues
% 0.83/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.83/1.02  --inst_passive_queues_freq              [25;2]
% 0.83/1.02  --inst_dismatching                      true
% 0.83/1.02  --inst_eager_unprocessed_to_passive     true
% 0.83/1.02  --inst_prop_sim_given                   true
% 0.83/1.02  --inst_prop_sim_new                     false
% 0.83/1.02  --inst_subs_new                         false
% 0.83/1.02  --inst_eq_res_simp                      false
% 0.83/1.02  --inst_subs_given                       false
% 0.83/1.02  --inst_orphan_elimination               true
% 0.83/1.02  --inst_learning_loop_flag               true
% 0.83/1.02  --inst_learning_start                   3000
% 0.83/1.02  --inst_learning_factor                  2
% 0.83/1.02  --inst_start_prop_sim_after_learn       3
% 0.83/1.02  --inst_sel_renew                        solver
% 0.83/1.02  --inst_lit_activity_flag                true
% 0.83/1.02  --inst_restr_to_given                   false
% 0.83/1.02  --inst_activity_threshold               500
% 0.83/1.02  --inst_out_proof                        true
% 0.83/1.02  
% 0.83/1.02  ------ Resolution Options
% 0.83/1.02  
% 0.83/1.02  --resolution_flag                       false
% 0.83/1.02  --res_lit_sel                           adaptive
% 0.83/1.02  --res_lit_sel_side                      none
% 0.83/1.02  --res_ordering                          kbo
% 0.83/1.02  --res_to_prop_solver                    active
% 0.83/1.02  --res_prop_simpl_new                    false
% 0.83/1.02  --res_prop_simpl_given                  true
% 0.83/1.02  --res_passive_queue_type                priority_queues
% 0.83/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.83/1.02  --res_passive_queues_freq               [15;5]
% 0.83/1.02  --res_forward_subs                      full
% 0.83/1.02  --res_backward_subs                     full
% 0.83/1.02  --res_forward_subs_resolution           true
% 0.83/1.02  --res_backward_subs_resolution          true
% 0.83/1.02  --res_orphan_elimination                true
% 0.83/1.02  --res_time_limit                        2.
% 0.83/1.02  --res_out_proof                         true
% 0.83/1.02  
% 0.83/1.02  ------ Superposition Options
% 0.83/1.02  
% 0.83/1.02  --superposition_flag                    true
% 0.83/1.02  --sup_passive_queue_type                priority_queues
% 0.83/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.83/1.02  --sup_passive_queues_freq               [8;1;4]
% 0.83/1.02  --demod_completeness_check              fast
% 0.83/1.02  --demod_use_ground                      true
% 0.83/1.02  --sup_to_prop_solver                    passive
% 0.83/1.02  --sup_prop_simpl_new                    true
% 0.83/1.02  --sup_prop_simpl_given                  true
% 0.83/1.02  --sup_fun_splitting                     false
% 0.83/1.02  --sup_smt_interval                      50000
% 0.83/1.02  
% 0.83/1.02  ------ Superposition Simplification Setup
% 0.83/1.02  
% 0.83/1.02  --sup_indices_passive                   []
% 0.83/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 0.83/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.02  --sup_full_bw                           [BwDemod]
% 0.83/1.02  --sup_immed_triv                        [TrivRules]
% 0.83/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.83/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.02  --sup_immed_bw_main                     []
% 0.83/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 0.83/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/1.02  
% 0.83/1.02  ------ Combination Options
% 0.83/1.02  
% 0.83/1.02  --comb_res_mult                         3
% 0.83/1.02  --comb_sup_mult                         2
% 0.83/1.02  --comb_inst_mult                        10
% 0.83/1.02  
% 0.83/1.02  ------ Debug Options
% 0.83/1.02  
% 0.83/1.02  --dbg_backtrace                         false
% 0.83/1.02  --dbg_dump_prop_clauses                 false
% 0.83/1.02  --dbg_dump_prop_clauses_file            -
% 0.83/1.02  --dbg_out_stat                          false
% 0.83/1.02  
% 0.83/1.02  
% 0.83/1.02  
% 0.83/1.02  
% 0.83/1.02  ------ Proving...
% 0.83/1.02  
% 0.83/1.02  
% 0.83/1.02  % SZS status Theorem for theBenchmark.p
% 0.83/1.02  
% 0.83/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 0.83/1.02  
% 0.83/1.02  fof(f6,conjecture,(
% 0.83/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.83/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.02  
% 0.83/1.02  fof(f7,negated_conjecture,(
% 0.83/1.02    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.83/1.02    inference(negated_conjecture,[],[f6])).
% 0.83/1.02  
% 0.83/1.02  fof(f13,plain,(
% 0.83/1.02    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.83/1.02    inference(ennf_transformation,[],[f7])).
% 0.83/1.02  
% 0.83/1.02  fof(f15,plain,(
% 0.83/1.02    ? [X0] : (? [X1] : (((~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.83/1.02    inference(nnf_transformation,[],[f13])).
% 0.83/1.02  
% 0.83/1.02  fof(f16,plain,(
% 0.83/1.02    ? [X0] : (? [X1] : ((~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.83/1.02    inference(flattening,[],[f15])).
% 0.83/1.02  
% 0.83/1.02  fof(f18,plain,(
% 0.83/1.02    ( ! [X0] : (? [X1] : ((~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~v4_pre_topc(k3_subset_1(u1_struct_0(X0),sK1),X0) | ~v3_pre_topc(sK1,X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),sK1),X0) | v3_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.83/1.02    introduced(choice_axiom,[])).
% 0.83/1.02  
% 0.83/1.02  fof(f17,plain,(
% 0.83/1.02    ? [X0] : (? [X1] : ((~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~v3_pre_topc(X1,sK0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.83/1.02    introduced(choice_axiom,[])).
% 0.83/1.02  
% 0.83/1.02  fof(f19,plain,(
% 0.83/1.02    ((~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v3_pre_topc(sK1,sK0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.83/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18,f17])).
% 0.83/1.02  
% 0.83/1.02  fof(f27,plain,(
% 0.83/1.02    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.83/1.02    inference(cnf_transformation,[],[f19])).
% 0.83/1.02  
% 0.83/1.02  fof(f2,axiom,(
% 0.83/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.83/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.02  
% 0.83/1.02  fof(f9,plain,(
% 0.83/1.02    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.83/1.02    inference(ennf_transformation,[],[f2])).
% 0.83/1.02  
% 0.83/1.02  fof(f21,plain,(
% 0.83/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.83/1.02    inference(cnf_transformation,[],[f9])).
% 0.83/1.02  
% 0.83/1.02  fof(f29,plain,(
% 0.83/1.02    ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v3_pre_topc(sK1,sK0)),
% 0.83/1.02    inference(cnf_transformation,[],[f19])).
% 0.83/1.02  
% 0.83/1.02  fof(f5,axiom,(
% 0.83/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.83/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.02  
% 0.83/1.02  fof(f12,plain,(
% 0.83/1.02    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.83/1.02    inference(ennf_transformation,[],[f5])).
% 0.83/1.02  
% 0.83/1.02  fof(f14,plain,(
% 0.83/1.02    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.83/1.02    inference(nnf_transformation,[],[f12])).
% 0.83/1.02  
% 0.83/1.02  fof(f25,plain,(
% 0.83/1.02    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.83/1.02    inference(cnf_transformation,[],[f14])).
% 0.83/1.02  
% 0.83/1.02  fof(f26,plain,(
% 0.83/1.02    l1_pre_topc(sK0)),
% 0.83/1.02    inference(cnf_transformation,[],[f19])).
% 0.83/1.02  
% 0.83/1.02  fof(f3,axiom,(
% 0.83/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.83/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.02  
% 0.83/1.02  fof(f10,plain,(
% 0.83/1.02    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.83/1.02    inference(ennf_transformation,[],[f3])).
% 0.83/1.02  
% 0.83/1.02  fof(f22,plain,(
% 0.83/1.02    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.83/1.02    inference(cnf_transformation,[],[f10])).
% 0.83/1.02  
% 0.83/1.02  fof(f1,axiom,(
% 0.83/1.02    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.83/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.02  
% 0.83/1.02  fof(f20,plain,(
% 0.83/1.02    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.83/1.02    inference(cnf_transformation,[],[f1])).
% 0.83/1.02  
% 0.83/1.02  fof(f4,axiom,(
% 0.83/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.83/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.02  
% 0.83/1.02  fof(f8,plain,(
% 0.83/1.02    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.83/1.02    inference(unused_predicate_definition_removal,[],[f4])).
% 0.83/1.02  
% 0.83/1.02  fof(f11,plain,(
% 0.83/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.83/1.02    inference(ennf_transformation,[],[f8])).
% 0.83/1.02  
% 0.83/1.02  fof(f23,plain,(
% 0.83/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.83/1.02    inference(cnf_transformation,[],[f11])).
% 0.83/1.02  
% 0.83/1.02  fof(f28,plain,(
% 0.83/1.02    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v3_pre_topc(sK1,sK0)),
% 0.83/1.02    inference(cnf_transformation,[],[f19])).
% 0.83/1.02  
% 0.83/1.02  fof(f24,plain,(
% 0.83/1.02    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.83/1.02    inference(cnf_transformation,[],[f14])).
% 0.83/1.02  
% 0.83/1.02  cnf(c_621,plain,
% 0.83/1.02      ( X0_39 != X1_39 | X2_39 != X1_39 | X2_39 = X0_39 ),
% 0.83/1.02      theory(equality) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_1196,plain,
% 0.83/1.02      ( X0_39 != X1_39
% 0.83/1.02      | X0_39 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
% 0.83/1.02      | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) != X1_39 ),
% 0.83/1.02      inference(instantiation,[status(thm)],[c_621]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_1197,plain,
% 0.83/1.02      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) != sK1
% 0.83/1.02      | sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
% 0.83/1.02      | sK1 != sK1 ),
% 0.83/1.02      inference(instantiation,[status(thm)],[c_1196]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_624,plain,
% 0.83/1.02      ( ~ v3_pre_topc(X0_39,X0_40)
% 0.83/1.02      | v3_pre_topc(X1_39,X0_40)
% 0.83/1.02      | X1_39 != X0_39 ),
% 0.83/1.02      theory(equality) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_1082,plain,
% 0.83/1.02      ( v3_pre_topc(X0_39,sK0)
% 0.83/1.02      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
% 0.83/1.02      | X0_39 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 0.83/1.02      inference(instantiation,[status(thm)],[c_624]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_1084,plain,
% 0.83/1.02      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
% 0.83/1.02      | v3_pre_topc(sK1,sK0)
% 0.83/1.02      | sK1 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 0.83/1.02      inference(instantiation,[status(thm)],[c_1082]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_8,negated_conjecture,
% 0.83/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.83/1.02      inference(cnf_transformation,[],[f27]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_616,negated_conjecture,
% 0.83/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.83/1.02      inference(subtyping,[status(esa)],[c_8]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_752,plain,
% 0.83/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 0.83/1.02      inference(predicate_to_equality,[status(thm)],[c_616]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_1,plain,
% 0.83/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.83/1.02      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 0.83/1.02      inference(cnf_transformation,[],[f21]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_618,plain,
% 0.83/1.02      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(X0_41))
% 0.83/1.02      | k3_subset_1(X0_41,X0_39) = k4_xboole_0(X0_41,X0_39) ),
% 0.83/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_750,plain,
% 0.83/1.02      ( k3_subset_1(X0_41,X0_39) = k4_xboole_0(X0_41,X0_39)
% 0.83/1.02      | m1_subset_1(X0_39,k1_zfmisc_1(X0_41)) != iProver_top ),
% 0.83/1.02      inference(predicate_to_equality,[status(thm)],[c_618]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_928,plain,
% 0.83/1.02      ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 0.83/1.02      inference(superposition,[status(thm)],[c_752,c_750]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_6,negated_conjecture,
% 0.83/1.02      ( ~ v3_pre_topc(sK1,sK0)
% 0.83/1.02      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
% 0.83/1.02      inference(cnf_transformation,[],[f29]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_77,plain,
% 0.83/1.02      ( ~ v3_pre_topc(sK1,sK0)
% 0.83/1.02      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
% 0.83/1.02      inference(prop_impl,[status(thm)],[c_6]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_4,plain,
% 0.83/1.02      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 0.83/1.02      | v4_pre_topc(X1,X0)
% 0.83/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 0.83/1.02      | ~ l1_pre_topc(X0) ),
% 0.83/1.02      inference(cnf_transformation,[],[f25]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_9,negated_conjecture,
% 0.83/1.02      ( l1_pre_topc(sK0) ),
% 0.83/1.02      inference(cnf_transformation,[],[f26]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_168,plain,
% 0.83/1.02      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 0.83/1.02      | v4_pre_topc(X1,X0)
% 0.83/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 0.83/1.02      | sK0 != X0 ),
% 0.83/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_9]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_169,plain,
% 0.83/1.02      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 0.83/1.02      | v4_pre_topc(X0,sK0)
% 0.83/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.83/1.02      inference(unflattening,[status(thm)],[c_168]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_310,plain,
% 0.83/1.02      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 0.83/1.02      | ~ v3_pre_topc(sK1,sK0)
% 0.83/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.83/1.02      | k3_subset_1(u1_struct_0(sK0),sK1) != X0
% 0.83/1.02      | sK0 != sK0 ),
% 0.83/1.02      inference(resolution_lifted,[status(thm)],[c_77,c_169]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_311,plain,
% 0.83/1.02      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
% 0.83/1.02      | ~ v3_pre_topc(sK1,sK0)
% 0.83/1.02      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.83/1.02      inference(unflattening,[status(thm)],[c_310]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_613,plain,
% 0.83/1.02      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
% 0.83/1.02      | ~ v3_pre_topc(sK1,sK0)
% 0.83/1.02      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.83/1.02      inference(subtyping,[status(esa)],[c_311]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_755,plain,
% 0.83/1.02      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) != iProver_top
% 0.83/1.02      | v3_pre_topc(sK1,sK0) != iProver_top
% 0.83/1.02      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.83/1.02      inference(predicate_to_equality,[status(thm)],[c_613]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_937,plain,
% 0.83/1.02      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)),sK0) != iProver_top
% 0.83/1.02      | v3_pre_topc(sK1,sK0) != iProver_top
% 0.83/1.02      | m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.83/1.02      inference(demodulation,[status(thm)],[c_928,c_755]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_312,plain,
% 0.83/1.02      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) != iProver_top
% 0.83/1.02      | v3_pre_topc(sK1,sK0) != iProver_top
% 0.83/1.02      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.83/1.02      inference(predicate_to_equality,[status(thm)],[c_311]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_2,plain,
% 0.83/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.83/1.02      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 0.83/1.02      inference(cnf_transformation,[],[f22]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_617,plain,
% 0.83/1.02      ( ~ m1_subset_1(X0_39,k1_zfmisc_1(X0_41))
% 0.83/1.02      | k3_subset_1(X0_41,k3_subset_1(X0_41,X0_39)) = X0_39 ),
% 0.83/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_794,plain,
% 0.83/1.02      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.83/1.02      | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
% 0.83/1.02      inference(instantiation,[status(thm)],[c_617]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_802,plain,
% 0.83/1.02      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.83/1.02      | k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 0.83/1.02      inference(instantiation,[status(thm)],[c_618]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_623,plain,
% 0.83/1.02      ( ~ m1_subset_1(X0_39,X0_42)
% 0.83/1.02      | m1_subset_1(X1_39,X0_42)
% 0.83/1.02      | X1_39 != X0_39 ),
% 0.83/1.02      theory(equality) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_813,plain,
% 0.83/1.02      ( m1_subset_1(X0_39,k1_zfmisc_1(X0_41))
% 0.83/1.02      | ~ m1_subset_1(k4_xboole_0(X0_41,X1_39),k1_zfmisc_1(X0_41))
% 0.83/1.02      | X0_39 != k4_xboole_0(X0_41,X1_39) ),
% 0.83/1.02      inference(instantiation,[status(thm)],[c_623]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_839,plain,
% 0.83/1.02      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 0.83/1.02      | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 0.83/1.02      | k3_subset_1(u1_struct_0(sK0),sK1) != k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 0.83/1.02      inference(instantiation,[status(thm)],[c_813]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_840,plain,
% 0.83/1.02      ( k3_subset_1(u1_struct_0(sK0),sK1) != k4_xboole_0(u1_struct_0(sK0),sK1)
% 0.83/1.02      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 0.83/1.02      | m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 0.83/1.02      inference(predicate_to_equality,[status(thm)],[c_839]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_0,plain,
% 0.83/1.02      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 0.83/1.02      inference(cnf_transformation,[],[f20]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_3,plain,
% 0.83/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 0.83/1.02      inference(cnf_transformation,[],[f23]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_142,plain,
% 0.83/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.83/1.02      | X1 != X2
% 0.83/1.02      | k4_xboole_0(X2,X3) != X0 ),
% 0.83/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_3]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_143,plain,
% 0.83/1.02      ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
% 0.83/1.02      inference(unflattening,[status(thm)],[c_142]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_615,plain,
% 0.83/1.02      ( m1_subset_1(k4_xboole_0(X0_41,X0_39),k1_zfmisc_1(X0_41)) ),
% 0.83/1.02      inference(subtyping,[status(esa)],[c_143]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_854,plain,
% 0.83/1.02      ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.83/1.02      inference(instantiation,[status(thm)],[c_615]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_855,plain,
% 0.83/1.02      ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 0.83/1.02      inference(predicate_to_equality,[status(thm)],[c_854]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_917,plain,
% 0.83/1.02      ( ~ v3_pre_topc(X0_39,sK0)
% 0.83/1.02      | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
% 0.83/1.02      | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) != X0_39 ),
% 0.83/1.02      inference(instantiation,[status(thm)],[c_624]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_918,plain,
% 0.83/1.02      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) != X0_39
% 0.83/1.02      | v3_pre_topc(X0_39,sK0) != iProver_top
% 0.83/1.02      | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) = iProver_top ),
% 0.83/1.02      inference(predicate_to_equality,[status(thm)],[c_917]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_920,plain,
% 0.83/1.02      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) != sK1
% 0.83/1.02      | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) = iProver_top
% 0.83/1.02      | v3_pre_topc(sK1,sK0) != iProver_top ),
% 0.83/1.02      inference(instantiation,[status(thm)],[c_918]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_1012,plain,
% 0.83/1.02      ( v3_pre_topc(sK1,sK0) != iProver_top ),
% 0.83/1.02      inference(global_propositional_subsumption,
% 0.83/1.02                [status(thm)],
% 0.83/1.02                [c_937,c_8,c_312,c_794,c_802,c_840,c_855,c_920]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_1014,plain,
% 0.83/1.02      ( ~ v3_pre_topc(sK1,sK0) ),
% 0.83/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_1012]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_620,plain,( X0_39 = X0_39 ),theory(equality) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_629,plain,
% 0.83/1.02      ( sK1 = sK1 ),
% 0.83/1.02      inference(instantiation,[status(thm)],[c_620]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_7,negated_conjecture,
% 0.83/1.02      ( v3_pre_topc(sK1,sK0)
% 0.83/1.02      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
% 0.83/1.02      inference(cnf_transformation,[],[f28]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_79,plain,
% 0.83/1.02      ( v3_pre_topc(sK1,sK0)
% 0.83/1.02      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
% 0.83/1.02      inference(prop_impl,[status(thm)],[c_7]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_5,plain,
% 0.83/1.02      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 0.83/1.02      | ~ v4_pre_topc(X1,X0)
% 0.83/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 0.83/1.02      | ~ l1_pre_topc(X0) ),
% 0.83/1.02      inference(cnf_transformation,[],[f24]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_153,plain,
% 0.83/1.02      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 0.83/1.02      | ~ v4_pre_topc(X1,X0)
% 0.83/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 0.83/1.02      | sK0 != X0 ),
% 0.83/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_9]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_154,plain,
% 0.83/1.02      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 0.83/1.02      | ~ v4_pre_topc(X0,sK0)
% 0.83/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.83/1.02      inference(unflattening,[status(thm)],[c_153]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_297,plain,
% 0.83/1.02      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 0.83/1.02      | v3_pre_topc(sK1,sK0)
% 0.83/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 0.83/1.02      | k3_subset_1(u1_struct_0(sK0),sK1) != X0
% 0.83/1.02      | sK0 != sK0 ),
% 0.83/1.02      inference(resolution_lifted,[status(thm)],[c_79,c_154]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(c_298,plain,
% 0.83/1.02      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
% 0.83/1.02      | v3_pre_topc(sK1,sK0)
% 0.83/1.02      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 0.83/1.02      inference(unflattening,[status(thm)],[c_297]) ).
% 0.83/1.02  
% 0.83/1.02  cnf(contradiction,plain,
% 0.83/1.02      ( $false ),
% 0.83/1.02      inference(minisat,
% 0.83/1.02                [status(thm)],
% 0.83/1.02                [c_1197,c_1084,c_1014,c_854,c_839,c_802,c_794,c_629,
% 0.83/1.02                 c_298,c_8]) ).
% 0.83/1.02  
% 0.83/1.02  
% 0.83/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 0.83/1.02  
% 0.83/1.02  ------                               Statistics
% 0.83/1.02  
% 0.83/1.02  ------ General
% 0.83/1.02  
% 0.83/1.02  abstr_ref_over_cycles:                  0
% 0.83/1.02  abstr_ref_under_cycles:                 0
% 0.83/1.02  gc_basic_clause_elim:                   0
% 0.83/1.02  forced_gc_time:                         0
% 0.83/1.02  parsing_time:                           0.006
% 0.83/1.02  unif_index_cands_time:                  0.
% 0.83/1.02  unif_index_add_time:                    0.
% 0.83/1.02  orderings_time:                         0.
% 0.83/1.02  out_proof_time:                         0.005
% 0.83/1.02  total_time:                             0.042
% 0.83/1.02  num_of_symbols:                         43
% 0.83/1.02  num_of_terms:                           1012
% 0.83/1.02  
% 0.83/1.02  ------ Preprocessing
% 0.83/1.02  
% 0.83/1.02  num_of_splits:                          0
% 0.83/1.02  num_of_split_atoms:                     0
% 0.83/1.02  num_of_reused_defs:                     0
% 0.83/1.02  num_eq_ax_congr_red:                    12
% 0.83/1.02  num_of_sem_filtered_clauses:            1
% 0.83/1.02  num_of_subtypes:                        4
% 0.83/1.02  monotx_restored_types:                  0
% 0.83/1.02  sat_num_of_epr_types:                   0
% 0.83/1.02  sat_num_of_non_cyclic_types:            0
% 0.83/1.02  sat_guarded_non_collapsed_types:        1
% 0.83/1.02  num_pure_diseq_elim:                    0
% 0.83/1.02  simp_replaced_by:                       0
% 0.83/1.02  res_preprocessed:                       39
% 0.83/1.02  prep_upred:                             0
% 0.83/1.02  prep_unflattend:                        22
% 0.83/1.02  smt_new_axioms:                         0
% 0.83/1.02  pred_elim_cands:                        2
% 0.83/1.02  pred_elim:                              3
% 0.83/1.02  pred_elim_cl:                           4
% 0.83/1.02  pred_elim_cycles:                       6
% 0.83/1.02  merged_defs:                            2
% 0.83/1.02  merged_defs_ncl:                        0
% 0.83/1.02  bin_hyper_res:                          2
% 0.83/1.02  prep_cycles:                            4
% 0.83/1.02  pred_elim_time:                         0.004
% 0.83/1.02  splitting_time:                         0.
% 0.83/1.02  sem_filter_time:                        0.
% 0.83/1.02  monotx_time:                            0.
% 0.83/1.02  subtype_inf_time:                       0.
% 0.83/1.02  
% 0.83/1.02  ------ Problem properties
% 0.83/1.02  
% 0.83/1.02  clauses:                                6
% 0.83/1.02  conjectures:                            1
% 0.83/1.02  epr:                                    0
% 0.83/1.02  horn:                                   5
% 0.83/1.02  ground:                                 3
% 0.83/1.02  unary:                                  2
% 0.83/1.02  binary:                                 2
% 0.83/1.02  lits:                                   12
% 0.83/1.02  lits_eq:                                2
% 0.83/1.02  fd_pure:                                0
% 0.83/1.02  fd_pseudo:                              0
% 0.83/1.02  fd_cond:                                0
% 0.83/1.02  fd_pseudo_cond:                         0
% 0.83/1.02  ac_symbols:                             0
% 0.83/1.02  
% 0.83/1.02  ------ Propositional Solver
% 0.83/1.02  
% 0.83/1.02  prop_solver_calls:                      27
% 0.83/1.02  prop_fast_solver_calls:                 267
% 0.83/1.02  smt_solver_calls:                       0
% 0.83/1.02  smt_fast_solver_calls:                  0
% 0.83/1.02  prop_num_of_clauses:                    311
% 0.83/1.02  prop_preprocess_simplified:             1331
% 0.83/1.02  prop_fo_subsumed:                       3
% 0.83/1.02  prop_solver_time:                       0.
% 0.83/1.02  smt_solver_time:                        0.
% 0.83/1.02  smt_fast_solver_time:                   0.
% 0.83/1.02  prop_fast_solver_time:                  0.
% 0.83/1.02  prop_unsat_core_time:                   0.
% 0.83/1.02  
% 0.83/1.02  ------ QBF
% 0.83/1.02  
% 0.83/1.02  qbf_q_res:                              0
% 0.83/1.02  qbf_num_tautologies:                    0
% 0.83/1.02  qbf_prep_cycles:                        0
% 0.83/1.02  
% 0.83/1.02  ------ BMC1
% 0.83/1.02  
% 0.83/1.02  bmc1_current_bound:                     -1
% 0.83/1.02  bmc1_last_solved_bound:                 -1
% 0.83/1.02  bmc1_unsat_core_size:                   -1
% 0.83/1.02  bmc1_unsat_core_parents_size:           -1
% 0.83/1.02  bmc1_merge_next_fun:                    0
% 0.83/1.02  bmc1_unsat_core_clauses_time:           0.
% 0.83/1.02  
% 0.83/1.02  ------ Instantiation
% 0.83/1.02  
% 0.83/1.02  inst_num_of_clauses:                    85
% 0.83/1.02  inst_num_in_passive:                    29
% 0.83/1.02  inst_num_in_active:                     53
% 0.83/1.02  inst_num_in_unprocessed:                2
% 0.83/1.02  inst_num_of_loops:                      62
% 0.83/1.02  inst_num_of_learning_restarts:          0
% 0.83/1.02  inst_num_moves_active_passive:          5
% 0.83/1.02  inst_lit_activity:                      0
% 0.83/1.02  inst_lit_activity_moves:                0
% 0.83/1.02  inst_num_tautologies:                   0
% 0.83/1.02  inst_num_prop_implied:                  0
% 0.83/1.02  inst_num_existing_simplified:           0
% 0.83/1.02  inst_num_eq_res_simplified:             0
% 0.83/1.02  inst_num_child_elim:                    0
% 0.83/1.02  inst_num_of_dismatching_blockings:      32
% 0.83/1.02  inst_num_of_non_proper_insts:           73
% 0.83/1.02  inst_num_of_duplicates:                 0
% 0.83/1.02  inst_inst_num_from_inst_to_res:         0
% 0.83/1.02  inst_dismatching_checking_time:         0.
% 0.83/1.02  
% 0.83/1.02  ------ Resolution
% 0.83/1.02  
% 0.83/1.02  res_num_of_clauses:                     0
% 0.83/1.02  res_num_in_passive:                     0
% 0.83/1.02  res_num_in_active:                      0
% 0.83/1.02  res_num_of_loops:                       43
% 0.83/1.02  res_forward_subset_subsumed:            5
% 0.83/1.02  res_backward_subset_subsumed:           0
% 0.83/1.02  res_forward_subsumed:                   0
% 0.83/1.02  res_backward_subsumed:                  0
% 0.83/1.02  res_forward_subsumption_resolution:     0
% 0.83/1.02  res_backward_subsumption_resolution:    0
% 0.83/1.02  res_clause_to_clause_subsumption:       28
% 0.83/1.02  res_orphan_elimination:                 0
% 0.83/1.02  res_tautology_del:                      13
% 0.83/1.02  res_num_eq_res_simplified:              0
% 0.83/1.02  res_num_sel_changes:                    0
% 0.83/1.02  res_moves_from_active_to_pass:          0
% 0.83/1.02  
% 0.83/1.02  ------ Superposition
% 0.83/1.02  
% 0.83/1.02  sup_time_total:                         0.
% 0.83/1.02  sup_time_generating:                    0.
% 0.83/1.02  sup_time_sim_full:                      0.
% 0.83/1.02  sup_time_sim_immed:                     0.
% 0.83/1.02  
% 0.83/1.02  sup_num_of_clauses:                     12
% 0.83/1.02  sup_num_in_active:                      10
% 0.83/1.02  sup_num_in_passive:                     2
% 0.83/1.02  sup_num_of_loops:                       12
% 0.83/1.02  sup_fw_superposition:                   6
% 0.83/1.02  sup_bw_superposition:                   7
% 0.83/1.02  sup_immediate_simplified:               5
% 0.83/1.02  sup_given_eliminated:                   0
% 0.83/1.02  comparisons_done:                       0
% 0.83/1.02  comparisons_avoided:                    0
% 0.83/1.02  
% 0.83/1.02  ------ Simplifications
% 0.83/1.02  
% 0.83/1.02  
% 0.83/1.02  sim_fw_subset_subsumed:                 0
% 0.83/1.02  sim_bw_subset_subsumed:                 1
% 0.83/1.02  sim_fw_subsumed:                        2
% 0.83/1.02  sim_bw_subsumed:                        0
% 0.83/1.02  sim_fw_subsumption_res:                 0
% 0.83/1.02  sim_bw_subsumption_res:                 0
% 0.83/1.02  sim_tautology_del:                      1
% 0.83/1.02  sim_eq_tautology_del:                   0
% 0.83/1.02  sim_eq_res_simp:                        0
% 0.83/1.02  sim_fw_demodulated:                     0
% 0.83/1.02  sim_bw_demodulated:                     2
% 0.83/1.02  sim_light_normalised:                   4
% 0.83/1.02  sim_joinable_taut:                      0
% 0.83/1.02  sim_joinable_simp:                      0
% 0.83/1.02  sim_ac_normalised:                      0
% 0.83/1.02  sim_smt_subsumption:                    0
% 0.83/1.02  
%------------------------------------------------------------------------------
