%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:04 EST 2020

% Result     : Theorem 19.38s
% Output     : CNFRefutation 19.38s
% Verified   : 
% Statistics : Number of formulae       :  742 (17850010422 expanded)
%              Number of clauses        :  689 (7511563530 expanded)
%              Number of leaves         :   20 (4126471115 expanded)
%              Depth                    :   90
%              Number of atoms          :  917 (30030024258 expanded)
%              Number of equality atoms :  783 (20286948729 expanded)
%              Maximal formula depth    :    9 (   1 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f52,f36])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k2_subset_1(sK1) != sK2
        | ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) )
      & ( k2_subset_1(sK1) = sK2
        | r1_tarski(k3_subset_1(sK1,sK2),sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( k2_subset_1(sK1) != sK2
      | ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) )
    & ( k2_subset_1(sK1) = sK2
      | r1_tarski(k3_subset_1(sK1,sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f31])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f55,plain,
    ( k2_subset_1(sK1) = sK2
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f40,f36])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f56,plain,
    ( k2_subset_1(sK1) != sK2
    | ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1154,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_7,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1168,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_3466,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_5,c_1168])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_302,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_303,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_1214,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_303])).

cnf(c_1167,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_2387,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = k5_xboole_0(X0,k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1214,c_1167])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2386,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8,c_1167])).

cnf(c_2423,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_2386,c_5])).

cnf(c_3228,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_2423,c_7])).

cnf(c_3468,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,X0)) = k5_xboole_0(X0,k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1214,c_1168])).

cnf(c_5465,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,sK1),X1),k3_subset_1(sK1,sK2)) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3228,c_3468])).

cnf(c_1683,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k5_xboole_0(k3_subset_1(sK1,sK2),X0) ),
    inference(superposition,[status(thm)],[c_1214,c_7])).

cnf(c_1687,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_2164,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1683,c_1687])).

cnf(c_2550,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_subset_1(sK1,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_2164])).

cnf(c_3483,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_subset_1(sK1,sK2)),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2550,c_1168])).

cnf(c_2442,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k5_xboole_0(X0,k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1,c_2387])).

cnf(c_3241,plain,
    ( k5_xboole_0(sK1,k3_subset_1(sK1,sK2)) = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_2423,c_2442])).

cnf(c_3523,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3483,c_5,c_3241])).

cnf(c_1898,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X1)) = k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),X0),X1) ),
    inference(superposition,[status(thm)],[c_1683,c_7])).

cnf(c_1960,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),X0),X1) ),
    inference(superposition,[status(thm)],[c_7,c_1898])).

cnf(c_1972,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),X0),X1) ),
    inference(demodulation,[status(thm)],[c_1960,c_1683])).

cnf(c_1974,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X1)) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_1972,c_1898])).

cnf(c_5605,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X1)) = k5_xboole_0(sK1,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3523,c_1974])).

cnf(c_1897,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8,c_1683])).

cnf(c_1899,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(sK1,sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1897,c_5])).

cnf(c_1978,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k5_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_1899,c_7])).

cnf(c_1169,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_5254,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X1)) = k5_xboole_0(X1,k5_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_1978,c_1169])).

cnf(c_3471,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),k5_xboole_0(sK1,X1)) = k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sK1,sK2),X0)) ),
    inference(superposition,[status(thm)],[c_1683,c_1168])).

cnf(c_5417,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1)),X2)) = k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X1),X2) ),
    inference(superposition,[status(thm)],[c_3471,c_3228])).

cnf(c_2390,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1))) = k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1)) ),
    inference(superposition,[status(thm)],[c_1683,c_1167])).

cnf(c_2895,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1)),X2) ),
    inference(superposition,[status(thm)],[c_2390,c_7])).

cnf(c_2412,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)),X2)) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k5_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_1167,c_1974])).

cnf(c_2420,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)),X2)) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_2412,c_7])).

cnf(c_2910,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1)),X2) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_2895,c_2420])).

cnf(c_5499,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_5417,c_2910])).

cnf(c_3700,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_3468,c_2423])).

cnf(c_3955,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),X1)) = k5_xboole_0(k3_xboole_0(sK1,sK2),X1) ),
    inference(superposition,[status(thm)],[c_3700,c_7])).

cnf(c_2449,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),X1)) = k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),X1) ),
    inference(superposition,[status(thm)],[c_2387,c_7])).

cnf(c_2074,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),X1)) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_1974])).

cnf(c_2459,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),X1) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_2449,c_2074])).

cnf(c_3972,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(k3_xboole_0(sK1,sK2),X1) ),
    inference(light_normalisation,[status(thm)],[c_3955,c_2459])).

cnf(c_5500,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X1) ),
    inference(demodulation,[status(thm)],[c_5499,c_3972])).

cnf(c_3694,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK1),k3_subset_1(sK1,sK2)) = k5_xboole_0(k3_xboole_0(sK1,sK2),X0) ),
    inference(superposition,[status(thm)],[c_2423,c_3468])).

cnf(c_5423,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X1)) = k5_xboole_0(k5_xboole_0(X0,sK1),X1) ),
    inference(superposition,[status(thm)],[c_3694,c_3228])).

cnf(c_5501,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,sK1),X1) ),
    inference(demodulation,[status(thm)],[c_5500,c_5423])).

cnf(c_5619,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK1),X1) = k5_xboole_0(sK1,k5_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_5605,c_5254,c_5500,c_5501])).

cnf(c_5947,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X0,X1)),k3_subset_1(sK1,sK2)) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_5465,c_5465,c_5619])).

cnf(c_5960,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_2387,c_5947])).

cnf(c_6118,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k3_subset_1(sK1,sK2)) = X0 ),
    inference(demodulation,[status(thm)],[c_5960,c_2423,c_2459])).

cnf(c_5433,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X0,X2)) = X1 ),
    inference(superposition,[status(thm)],[c_3228,c_2423])).

cnf(c_5492,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X2)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_5433,c_7])).

cnf(c_9541,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2 ),
    inference(superposition,[status(thm)],[c_1,c_5492])).

cnf(c_10390,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),k5_xboole_0(X0,sK1)) = k5_xboole_0(X1,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_2387,c_9541])).

cnf(c_14392,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k3_xboole_0(sK1,sK2)) = k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X1,sK1)) ),
    inference(superposition,[status(thm)],[c_6118,c_10390])).

cnf(c_10385,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(X0,sK1)) = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1214,c_9541])).

cnf(c_5388,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_1,c_3228])).

cnf(c_5511,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
    inference(light_normalisation,[status(thm)],[c_5388,c_7])).

cnf(c_10739,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k3_xboole_0(sK1,sK2)) = k5_xboole_0(X0,sK1) ),
    inference(superposition,[status(thm)],[c_10385,c_5511])).

cnf(c_14525,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,sK1)) = k5_xboole_0(X1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_14392,c_10739])).

cnf(c_9572,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),k5_xboole_0(X0,k5_xboole_0(sK1,X1))) = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_3468,c_5492])).

cnf(c_11697,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k3_xboole_0(sK1,sK2)) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_9572,c_3228])).

cnf(c_11704,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(sK1,X1))) = k5_xboole_0(X1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_11697,c_10739])).

cnf(c_10389,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_3466,c_9541])).

cnf(c_10635,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X0) = k5_xboole_0(X2,X1) ),
    inference(light_normalisation,[status(thm)],[c_10389,c_5])).

cnf(c_12858,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X0) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_1,c_10635])).

cnf(c_19458,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK1)),X0) = k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(sK1,X1))) ),
    inference(superposition,[status(thm)],[c_11704,c_12858])).

cnf(c_19459,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK1,X1)),X0) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,sK1)),X2) ),
    inference(superposition,[status(thm)],[c_11704,c_10635])).

cnf(c_19648,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK1)),X0) = sP0_iProver_split(X1) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_19459])).

cnf(c_19649,plain,
    ( k5_xboole_0(X0,sK1) = sP0_iProver_split(X0) ),
    inference(demodulation,[status(thm)],[c_19458,c_11704,c_19648])).

cnf(c_19754,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split(X0)) = k5_xboole_0(X1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_14525,c_14525,c_19649])).

cnf(c_19755,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split(X0)) = sP0_iProver_split(X1) ),
    inference(demodulation,[status(thm)],[c_19754,c_19649])).

cnf(c_19767,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),sP0_iProver_split(k5_xboole_0(X0,X1))) = sP0_iProver_split(X2) ),
    inference(superposition,[status(thm)],[c_7,c_19755])).

cnf(c_36520,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),sP0_iProver_split(k5_xboole_0(X0,k1_xboole_0))) = sP0_iProver_split(k5_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_3466,c_19767])).

cnf(c_36749,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),sP0_iProver_split(X0)) = sP0_iProver_split(k5_xboole_0(X2,X1)) ),
    inference(light_normalisation,[status(thm)],[c_36520,c_5])).

cnf(c_43653,plain,
    ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = sP0_iProver_split(k5_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_36749,c_1])).

cnf(c_48661,plain,
    ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(k5_xboole_0(X1,X2),X0)) = sP0_iProver_split(k5_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_43653])).

cnf(c_5368,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_1,c_3228])).

cnf(c_3472,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_2387,c_1168])).

cnf(c_7042,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2))),k5_xboole_0(X1,k3_subset_1(sK1,sK2))) = k5_xboole_0(X0,sK1) ),
    inference(superposition,[status(thm)],[c_5368,c_3472])).

cnf(c_1385,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_1])).

cnf(c_1894,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = k5_xboole_0(k3_subset_1(sK1,sK2),X0) ),
    inference(superposition,[status(thm)],[c_1,c_1683])).

cnf(c_1905,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7,c_1894])).

cnf(c_2045,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_8,c_1905])).

cnf(c_2052,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,X0) ),
    inference(light_normalisation,[status(thm)],[c_2045,c_5])).

cnf(c_2392,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = k5_xboole_0(X0,sK1) ),
    inference(superposition,[status(thm)],[c_1899,c_1167])).

cnf(c_19533,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,sK1))) = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,X1)),sK1) ),
    inference(superposition,[status(thm)],[c_11704,c_11704])).

cnf(c_10734,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,k5_xboole_0(X1,sK1))) = k5_xboole_0(X1,k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_10385,c_5492])).

cnf(c_14953,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,sK1))) ),
    inference(superposition,[status(thm)],[c_10734,c_3228])).

cnf(c_2452,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_2387,c_1167])).

cnf(c_3245,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = k5_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_2423,c_2452])).

cnf(c_14968,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,sK1))) = k5_xboole_0(sK1,X1) ),
    inference(light_normalisation,[status(thm)],[c_14953,c_3245])).

cnf(c_20127,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,X0)),sK1) = k5_xboole_0(sK1,X0) ),
    inference(light_normalisation,[status(thm)],[c_19533,c_14968])).

cnf(c_3084,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,k3_subset_1(sK1,sK2)),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2550,c_7])).

cnf(c_3104,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,k3_subset_1(sK1,sK2)),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3084,c_1385])).

cnf(c_1979,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k3_subset_1(sK1,sK2)) = sK1 ),
    inference(superposition,[status(thm)],[c_1899,c_1])).

cnf(c_2281,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),X0)) = k5_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_1979,c_7])).

cnf(c_3105,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_3104,c_2281,c_2459])).

cnf(c_10732,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) = k5_xboole_0(X1,sK1) ),
    inference(superposition,[status(thm)],[c_10385,c_9541])).

cnf(c_14640,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1)),k3_xboole_0(sK1,sK2)),X1) = k5_xboole_0(X0,sK1) ),
    inference(superposition,[status(thm)],[c_9541,c_10732])).

cnf(c_1967,plain,
    ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),X0),k3_xboole_0(sK1,sK2)) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) ),
    inference(superposition,[status(thm)],[c_1898,c_1894])).

cnf(c_1983,plain,
    ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),X0),k3_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_1967,c_1978])).

cnf(c_6818,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1)),k3_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1169,c_1983])).

cnf(c_14773,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X0,X1)),X0) = k5_xboole_0(X1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_14640,c_6818])).

cnf(c_20128,plain,
    ( k5_xboole_0(sK1,X0) = sP0_iProver_split(X0) ),
    inference(demodulation,[status(thm)],[c_20127,c_3105,c_14773,c_19649])).

cnf(c_21805,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = sP0_iProver_split(X0) ),
    inference(light_normalisation,[status(thm)],[c_2052,c_2392,c_20128])).

cnf(c_21822,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(sK1,sK2)) = sP0_iProver_split(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1385,c_21805])).

cnf(c_19763,plain,
    ( k5_xboole_0(X0,sP0_iProver_split(X0)) = sP0_iProver_split(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5,c_19755])).

cnf(c_19886,plain,
    ( k5_xboole_0(X0,sP0_iProver_split(X0)) = k5_xboole_0(X1,sP0_iProver_split(X1)) ),
    inference(superposition,[status(thm)],[c_19755,c_3228])).

cnf(c_19890,plain,
    ( k5_xboole_0(X0,sP0_iProver_split(X0)) = sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_19886])).

cnf(c_19994,plain,
    ( sP0_iProver_split(k1_xboole_0) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_19763,c_19890])).

cnf(c_21980,plain,
    ( sP1_iProver_split = sK1 ),
    inference(light_normalisation,[status(thm)],[c_21822,c_1899,c_19994])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | k2_subset_1(sK1) = sK2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1152,plain,
    ( k2_subset_1(sK1) = sK2
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1156,plain,
    ( sK2 = sK1
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1152,c_17])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1155,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3112,plain,
    ( k3_xboole_0(k3_subset_1(sK1,sK2),sK2) = k3_subset_1(sK1,sK2)
    | sK2 = sK1 ),
    inference(superposition,[status(thm)],[c_1156,c_1155])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_6,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_258,plain,
    ( X0 != X1
    | k5_xboole_0(X2,k3_xboole_0(X2,X0)) != X3
    | k3_xboole_0(X3,X1) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_6])).

cnf(c_259,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_258])).

cnf(c_1455,plain,
    ( k3_xboole_0(k3_subset_1(sK1,sK2),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1214,c_259])).

cnf(c_3116,plain,
    ( k3_subset_1(sK1,sK2) = k1_xboole_0
    | sK2 = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3112,c_1455])).

cnf(c_5071,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK1),k1_xboole_0) = k5_xboole_0(k3_xboole_0(sK1,sK2),X0)
    | sK2 = sK1 ),
    inference(superposition,[status(thm)],[c_3116,c_3694])).

cnf(c_5084,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),X0) = k5_xboole_0(X0,sK1)
    | sK2 = sK1 ),
    inference(demodulation,[status(thm)],[c_5071,c_5])).

cnf(c_897,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_912,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_897])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_650,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_651,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_650])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_289,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_290,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_19,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_296,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_290,c_19])).

cnf(c_770,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_651,c_296])).

cnf(c_771,plain,
    ( r1_tarski(sK2,X0)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_770])).

cnf(c_1191,plain,
    ( r1_tarski(sK2,sK1)
    | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_1206,plain,
    ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_897])).

cnf(c_1246,plain,
    ( k2_subset_1(sK1) = sK1 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_898,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1203,plain,
    ( X0 != X1
    | k2_subset_1(sK1) != X1
    | k2_subset_1(sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_898])).

cnf(c_1233,plain,
    ( X0 != sK1
    | k2_subset_1(sK1) = X0
    | k2_subset_1(sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_1203])).

cnf(c_1274,plain,
    ( k3_xboole_0(sK1,X0) != sK1
    | k2_subset_1(sK1) = k3_xboole_0(sK1,X0)
    | k2_subset_1(sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_1233])).

cnf(c_1275,plain,
    ( k3_xboole_0(sK1,sK2) != sK1
    | k2_subset_1(sK1) = k3_xboole_0(sK1,sK2)
    | k2_subset_1(sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_1274])).

cnf(c_1298,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_897])).

cnf(c_1229,plain,
    ( k2_subset_1(sK1) != X0
    | sK2 != X0
    | sK2 = k2_subset_1(sK1) ),
    inference(instantiation,[status(thm)],[c_898])).

cnf(c_1313,plain,
    ( k2_subset_1(sK1) != k3_xboole_0(sK1,X0)
    | sK2 != k3_xboole_0(sK1,X0)
    | sK2 = k2_subset_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1229])).

cnf(c_1316,plain,
    ( k2_subset_1(sK1) != k3_xboole_0(sK1,sK2)
    | sK2 != k3_xboole_0(sK1,sK2)
    | sK2 = k2_subset_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_1240,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_898])).

cnf(c_1267,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1240])).

cnf(c_1391,plain,
    ( k2_subset_1(sK1) != sK1
    | sK1 = k2_subset_1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1267])).

cnf(c_1327,plain,
    ( k3_xboole_0(sK1,X0) != X1
    | sK2 != X1
    | sK2 = k3_xboole_0(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_898])).

cnf(c_1411,plain,
    ( k3_xboole_0(sK1,X0) != k3_xboole_0(X0,sK1)
    | sK2 != k3_xboole_0(X0,sK1)
    | sK2 = k3_xboole_0(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_1327])).

cnf(c_1412,plain,
    ( k3_xboole_0(sK1,sK2) != k3_xboole_0(sK2,sK1)
    | sK2 != k3_xboole_0(sK2,sK1)
    | sK2 = k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1411])).

cnf(c_1227,plain,
    ( sK2 != X0
    | sK2 = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_898])).

cnf(c_1510,plain,
    ( sK2 != k2_subset_1(sK1)
    | sK2 = sK1
    | sK1 != k2_subset_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1227])).

cnf(c_1610,plain,
    ( k3_xboole_0(X0,sK1) != X1
    | sK2 != X1
    | sK2 = k3_xboole_0(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_898])).

cnf(c_1611,plain,
    ( k3_xboole_0(sK2,sK1) != sK2
    | sK2 = k3_xboole_0(sK2,sK1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1610])).

cnf(c_2539,plain,
    ( ~ r1_tarski(X0,sK1)
    | k3_xboole_0(X0,sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2541,plain,
    ( ~ r1_tarski(sK2,sK1)
    | k3_xboole_0(sK2,sK1) = sK2 ),
    inference(instantiation,[status(thm)],[c_2539])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_3418,plain,
    ( k3_xboole_0(sK1,X0) = k3_xboole_0(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3419,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_3418])).

cnf(c_5075,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK2)) = sK1
    | sK2 = sK1 ),
    inference(superposition,[status(thm)],[c_3116,c_1899])).

cnf(c_5080,plain,
    ( k3_xboole_0(sK1,sK2) = sK1
    | sK2 = sK1 ),
    inference(demodulation,[status(thm)],[c_5075,c_1385])).

cnf(c_32626,plain,
    ( sK2 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5084,c_912,c_1191,c_1206,c_1246,c_1275,c_1298,c_1316,c_1391,c_1412,c_1510,c_1611,c_2541,c_3419,c_5080])).

cnf(c_32628,plain,
    ( sP1_iProver_split = sK2 ),
    inference(light_normalisation,[status(thm)],[c_32626,c_21980])).

cnf(c_47342,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sP1_iProver_split))),k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = sP0_iProver_split(X0) ),
    inference(light_normalisation,[status(thm)],[c_7042,c_7042,c_19649,c_21980,c_32628])).

cnf(c_52268,plain,
    ( k5_xboole_0(sP0_iProver_split(k5_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X1,X0),k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = sP0_iProver_split(sP0_iProver_split(k3_xboole_0(sP1_iProver_split,sP1_iProver_split))) ),
    inference(superposition,[status(thm)],[c_48661,c_47342])).

cnf(c_6966,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2)))) = k5_xboole_0(k3_xboole_0(sK1,sK2),X1) ),
    inference(superposition,[status(thm)],[c_3468,c_5368])).

cnf(c_8141,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X0,X1)),k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = k5_xboole_0(k3_xboole_0(sK1,sK2),X1) ),
    inference(superposition,[status(thm)],[c_3228,c_6966])).

cnf(c_3238,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k3_subset_1(sK1,sK2)) = k5_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_2423,c_2442])).

cnf(c_3559,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7,c_3466])).

cnf(c_30673,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(sK1,X1))) ),
    inference(superposition,[status(thm)],[c_3238,c_3559])).

cnf(c_30785,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_3559,c_5511])).

cnf(c_31024,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(sK1,k5_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_30673,c_30785])).

cnf(c_6601,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(X0,k5_xboole_0(sK1,X1)) ),
    inference(superposition,[status(thm)],[c_3238,c_1169])).

cnf(c_6952,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2)))) = k5_xboole_0(sK1,X1) ),
    inference(superposition,[status(thm)],[c_2387,c_5368])).

cnf(c_7523,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_3245,c_6952])).

cnf(c_7628,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,X0)) = k3_subset_1(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_7523,c_1214])).

cnf(c_9599,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(X0,k5_xboole_0(sK1,X1))) = k5_xboole_0(X1,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_7628,c_5492])).

cnf(c_12087,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X1,sK1),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_2423,c_9599])).

cnf(c_10730,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK1),k3_xboole_0(sK1,sK2)) = k5_xboole_0(X0,k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_10385,c_2423])).

cnf(c_11132,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,sK1))) = k5_xboole_0(k5_xboole_0(X1,k3_subset_1(sK1,sK2)),X0) ),
    inference(superposition,[status(thm)],[c_10739,c_5368])).

cnf(c_3705,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(sK1,X1))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_3468,c_1167])).

cnf(c_4712,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,sK1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_1169,c_3705])).

cnf(c_11164,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_11132,c_4712])).

cnf(c_12186,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,k3_subset_1(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_12087,c_10730,c_11164])).

cnf(c_7735,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,sK1),k3_xboole_0(sK1,sK2)),X0) = k3_subset_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_2423,c_7628])).

cnf(c_3678,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,sK1)) = k5_xboole_0(X0,k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1,c_3468])).

cnf(c_3814,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK1),k3_xboole_0(sK1,sK2)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_3678,c_3466])).

cnf(c_3838,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK1),k3_xboole_0(sK1,sK2)) = k5_xboole_0(k3_subset_1(sK1,sK2),X0) ),
    inference(demodulation,[status(thm)],[c_3814,c_3466])).

cnf(c_7805,plain,
    ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),X0),X0) = k3_subset_1(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_7735,c_3838])).

cnf(c_18860,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(X0,X1)) = k5_xboole_0(k3_subset_1(sK1,sK2),X1) ),
    inference(superposition,[status(thm)],[c_7805,c_5492])).

cnf(c_28187,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_12186,c_18860,c_21980])).

cnf(c_28329,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)),sP0_iProver_split(k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sK2)))) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_28187,c_19755])).

cnf(c_3566,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_subset_1(sK1,sK2),X0)) = k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),sK1) ),
    inference(superposition,[status(thm)],[c_1683,c_3466])).

cnf(c_3627,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),sK1) = k5_xboole_0(X0,k3_subset_1(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_3566,c_3466])).

cnf(c_1961,plain,
    ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),X0),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8,c_1898])).

cnf(c_1988,plain,
    ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),X0),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1961,c_5])).

cnf(c_9316,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),sK1) = k5_xboole_0(k3_subset_1(sK1,sK2),X0) ),
    inference(superposition,[status(thm)],[c_1988,c_2423])).

cnf(c_24050,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),X0),sP1_iProver_split) = k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_3627,c_9316,c_21980])).

cnf(c_24082,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),X0),k5_xboole_0(sP1_iProver_split,X1)) = k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)),X1) ),
    inference(superposition,[status(thm)],[c_24050,c_7])).

cnf(c_5374,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_7,c_3228])).

cnf(c_19824,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X0,X2),sP0_iProver_split(X1)) ),
    inference(superposition,[status(thm)],[c_5374,c_19755])).

cnf(c_5402,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),X0),X1)) = k5_xboole_0(sK1,X1) ),
    inference(superposition,[status(thm)],[c_1683,c_3228])).

cnf(c_21884,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k3_xboole_0(sK1,sK2))),k5_xboole_0(sP0_iProver_split(X0),X1)) = k5_xboole_0(sK1,X1) ),
    inference(superposition,[status(thm)],[c_21805,c_5402])).

cnf(c_19859,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sP0_iProver_split(X0),X2)) = k5_xboole_0(sP0_iProver_split(X1),X2) ),
    inference(superposition,[status(thm)],[c_19755,c_7])).

cnf(c_19868,plain,
    ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X2,sP0_iProver_split(X1)),X2) ),
    inference(superposition,[status(thm)],[c_19755,c_10635])).

cnf(c_3229,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_2423,c_2423])).

cnf(c_19896,plain,
    ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X0,X1)) = sP0_iProver_split(X1) ),
    inference(demodulation,[status(thm)],[c_19868,c_3229])).

cnf(c_19874,plain,
    ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X2,sP0_iProver_split(X1)) ),
    inference(superposition,[status(thm)],[c_19755,c_1168])).

cnf(c_19894,plain,
    ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,sP0_iProver_split(X1)) ),
    inference(light_normalisation,[status(thm)],[c_19874,c_7])).

cnf(c_19897,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,X1)) = k5_xboole_0(X1,sP0_iProver_split(X0)) ),
    inference(demodulation,[status(thm)],[c_19896,c_19894])).

cnf(c_19873,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sP0_iProver_split(X0),X2)) = k5_xboole_0(X2,sP0_iProver_split(X1)) ),
    inference(superposition,[status(thm)],[c_19755,c_1169])).

cnf(c_19903,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sP0_iProver_split(X0),X2)) = sP0_iProver_split(k5_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_19897,c_19873])).

cnf(c_19924,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,X1)) = k5_xboole_0(sP0_iProver_split(X0),X1) ),
    inference(demodulation,[status(thm)],[c_19859,c_19903])).

cnf(c_22109,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sK2))),sP0_iProver_split(k5_xboole_0(X0,X1))) = k5_xboole_0(sP1_iProver_split,X1) ),
    inference(light_normalisation,[status(thm)],[c_21884,c_19924,c_21980])).

cnf(c_19876,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,sP0_iProver_split(X0))) = sP0_iProver_split(X1) ),
    inference(superposition,[status(thm)],[c_19755,c_7])).

cnf(c_19908,plain,
    ( k5_xboole_0(X0,sP0_iProver_split(k5_xboole_0(X0,X1))) = sP0_iProver_split(X1) ),
    inference(demodulation,[status(thm)],[c_19897,c_19876])).

cnf(c_22110,plain,
    ( k5_xboole_0(sP1_iProver_split,X0) = sP0_iProver_split(X0) ),
    inference(demodulation,[status(thm)],[c_22109,c_2423,c_19824,c_19908])).

cnf(c_24126,plain,
    ( sP0_iProver_split(k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sK2)),X0) ),
    inference(demodulation,[status(thm)],[c_24082,c_19824,c_22110])).

cnf(c_21830,plain,
    ( sP0_iProver_split(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10635,c_21805])).

cnf(c_12980,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)),k3_subset_1(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10635,c_2387])).

cnf(c_19761,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split(X1)) = sP0_iProver_split(X0) ),
    inference(superposition,[status(thm)],[c_1,c_19755])).

cnf(c_20929,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X0,X1)),sP0_iProver_split(k3_subset_1(sK1,sK2))) = sP0_iProver_split(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_12980,c_19761])).

cnf(c_4260,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,X0),X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_3468,c_1169])).

cnf(c_12904,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_subset_1(sK1,sK2)))),X0) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,X2),X1),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_4260,c_10635])).

cnf(c_13133,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,X0),X1),k3_xboole_0(sK1,sK2)) = k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),X1) ),
    inference(demodulation,[status(thm)],[c_12904,c_10635])).

cnf(c_4849,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,X0),X1),k3_xboole_0(sK1,sK2)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_4260,c_3466])).

cnf(c_3589,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_3466,c_1167])).

cnf(c_4875,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,X0),X1),k3_xboole_0(sK1,sK2)) = k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sK1,sK2),X0)) ),
    inference(demodulation,[status(thm)],[c_4849,c_3589])).

cnf(c_9603,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_5492])).

cnf(c_12545,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(sK1,X1),X0) ),
    inference(superposition,[status(thm)],[c_9603,c_6966])).

cnf(c_10042,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(sK1,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5511,c_2390])).

cnf(c_12558,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,X0),X1) = k5_xboole_0(sK1,k5_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_12545,c_10042])).

cnf(c_13134,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X0,X1)),k3_xboole_0(sK1,sK2)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_13133,c_4875,c_11164,c_12558])).

cnf(c_7286,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1))) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)) ),
    inference(superposition,[status(thm)],[c_1683,c_5374])).

cnf(c_19540,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,X0))) = k5_xboole_0(sK1,k5_xboole_0(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_11704,c_7286])).

cnf(c_5406,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,X0)) = k5_xboole_0(k3_subset_1(sK1,sK2),X0) ),
    inference(superposition,[status(thm)],[c_1899,c_3228])).

cnf(c_7566,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_subset_1(sK1,sK2))))) = k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_6952,c_1974])).

cnf(c_6954,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,sK1)) = k5_xboole_0(k3_subset_1(sK1,sK2),X0) ),
    inference(superposition,[status(thm)],[c_1899,c_5368])).

cnf(c_7586,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7566,c_1979,c_3105,c_6954])).

cnf(c_20011,plain,
    ( k5_xboole_0(sK1,sP0_iProver_split(X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_19540,c_5406,c_7586,c_19649])).

cnf(c_3213,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = sK1 ),
    inference(superposition,[status(thm)],[c_2442,c_2423])).

cnf(c_19799,plain,
    ( k5_xboole_0(sK1,sP0_iProver_split(k5_xboole_0(k3_xboole_0(sK1,sK2),X0))) = sP0_iProver_split(k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_3213,c_19755])).

cnf(c_20016,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = k5_xboole_0(k3_xboole_0(sK1,sK2),X0) ),
    inference(demodulation,[status(thm)],[c_20011,c_19799])).

cnf(c_10748,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),sK1) = k5_xboole_0(X0,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_10385,c_5374])).

cnf(c_19830,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),sP0_iProver_split(k5_xboole_0(X0,k3_subset_1(sK1,sK2)))) = sP0_iProver_split(sK1) ),
    inference(superposition,[status(thm)],[c_10748,c_19755])).

cnf(c_20021,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = sP0_iProver_split(sK1) ),
    inference(demodulation,[status(thm)],[c_20016,c_19830])).

cnf(c_3216,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),X0)) = sK1 ),
    inference(superposition,[status(thm)],[c_1894,c_2423])).

cnf(c_2408,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1167,c_8])).

cnf(c_6438,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(k3_subset_1(sK1,sK2),X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3216,c_2408])).

cnf(c_5196,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_subset_1(sK1,sK2),X0)) = k5_xboole_0(k3_xboole_0(sK1,sK2),X0) ),
    inference(superposition,[status(thm)],[c_3241,c_7])).

cnf(c_6473,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6438,c_5196])).

cnf(c_20024,plain,
    ( sP0_iProver_split(sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_20021,c_6473])).

cnf(c_19889,plain,
    ( k5_xboole_0(sP0_iProver_split(sK1),k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = k5_xboole_0(k3_xboole_0(sK1,sK2),sP0_iProver_split(X0)) ),
    inference(superposition,[status(thm)],[c_19755,c_4260])).

cnf(c_19911,plain,
    ( k5_xboole_0(sP0_iProver_split(sK1),k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = sP0_iProver_split(k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) ),
    inference(demodulation,[status(thm)],[c_19897,c_19889])).

cnf(c_20039,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = sP0_iProver_split(k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) ),
    inference(demodulation,[status(thm)],[c_20024,c_19911])).

cnf(c_20040,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = k5_xboole_0(k3_subset_1(sK1,sK2),X0) ),
    inference(demodulation,[status(thm)],[c_20039,c_3466])).

cnf(c_19806,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),sP0_iProver_split(k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = sP0_iProver_split(k5_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_3472,c_19755])).

cnf(c_19834,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),sP0_iProver_split(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)))) = sP0_iProver_split(k5_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_7628,c_19755])).

cnf(c_7715,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,sK1)) = k3_subset_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1,c_7628])).

cnf(c_19837,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),sP0_iProver_split(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)))) = sP0_iProver_split(k5_xboole_0(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_7715,c_19755])).

cnf(c_19947,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),sP0_iProver_split(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)))) = sP0_iProver_split(sP0_iProver_split(X0)) ),
    inference(light_normalisation,[status(thm)],[c_19837,c_19649])).

cnf(c_19948,plain,
    ( sP0_iProver_split(k5_xboole_0(sK1,X0)) = sP0_iProver_split(sP0_iProver_split(X0)) ),
    inference(demodulation,[status(thm)],[c_19834,c_19947])).

cnf(c_19980,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),sP0_iProver_split(k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = sP0_iProver_split(sP0_iProver_split(X0)) ),
    inference(demodulation,[status(thm)],[c_19806,c_19824,c_19948])).

cnf(c_20047,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),k5_xboole_0(k3_subset_1(sK1,sK2),X1)) = sP0_iProver_split(sP0_iProver_split(X0)) ),
    inference(demodulation,[status(thm)],[c_20040,c_19980])).

cnf(c_10452,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X1)),k5_xboole_0(k3_subset_1(sK1,sK2),X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1683,c_9541])).

cnf(c_4247,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_2442,c_1169])).

cnf(c_10624,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),k5_xboole_0(k3_subset_1(sK1,sK2),X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_10452,c_4247])).

cnf(c_20061,plain,
    ( sP0_iProver_split(sP0_iProver_split(X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_20047,c_10624])).

cnf(c_19828,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)),sP0_iProver_split(k5_xboole_0(sK1,k5_xboole_0(X0,X1)))) = sP0_iProver_split(k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_5947,c_19755])).

cnf(c_12960,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X0)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_10635,c_7])).

cnf(c_19844,plain,
    ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),sP0_iProver_split(X2)) ),
    inference(superposition,[status(thm)],[c_12960,c_19755])).

cnf(c_19945,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X1,X0),sP0_iProver_split(X2)) ),
    inference(light_normalisation,[status(thm)],[c_19844,c_7])).

cnf(c_19954,plain,
    ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(sK1,sK2),sP0_iProver_split(k5_xboole_0(X0,X1))))) = sP0_iProver_split(k3_subset_1(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_19828,c_19945,c_19948])).

cnf(c_19955,plain,
    ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(sK1,sK2)))))) = sP0_iProver_split(k3_subset_1(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_19954,c_19897,c_19945])).

cnf(c_7345,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_5374,c_1983])).

cnf(c_5772,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1))) = k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X1),X0) ),
    inference(superposition,[status(thm)],[c_2423,c_5402])).

cnf(c_5850,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1))) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_5772,c_5500])).

cnf(c_7428,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_7345,c_5850])).

cnf(c_19956,plain,
    ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)))))) = sP0_iProver_split(k3_subset_1(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_19955,c_7428])).

cnf(c_7282,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3)))) = k5_xboole_0(X1,k5_xboole_0(X3,X2)) ),
    inference(superposition,[status(thm)],[c_1169,c_5374])).

cnf(c_19957,plain,
    ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(sK1,sK2))))) = sP0_iProver_split(k3_subset_1(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_19956,c_7282])).

cnf(c_7888,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_7715,c_5368])).

cnf(c_7903,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_7888,c_3241])).

cnf(c_19958,plain,
    ( sP0_iProver_split(sP0_iProver_split(k3_xboole_0(sK1,sK2))) = sP0_iProver_split(k3_subset_1(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_19957,c_7903])).

cnf(c_20075,plain,
    ( sP0_iProver_split(k3_subset_1(sK1,sK2)) = k3_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_20061,c_19958])).

cnf(c_21051,plain,
    ( sP0_iProver_split(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_20929,c_13134,c_20075])).

cnf(c_22166,plain,
    ( sP0_iProver_split(k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k5_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_21830,c_21051,c_21980])).

cnf(c_24127,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)),X1) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k5_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_24126,c_22166])).

cnf(c_5450,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK1),k3_subset_1(sK1,sK2)) = k5_xboole_0(X0,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_3228,c_2387])).

cnf(c_6319,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,sK1)),k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = sK1 ),
    inference(superposition,[status(thm)],[c_5450,c_3213])).

cnf(c_6368,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_6319,c_3678])).

cnf(c_25983,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)),k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sK2))) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_6368,c_6368,c_21980])).

cnf(c_26015,plain,
    ( k5_xboole_0(sP1_iProver_split,sP0_iProver_split(k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sK2)))) = sP0_iProver_split(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2))) ),
    inference(superposition,[status(thm)],[c_25983,c_19761])).

cnf(c_26047,plain,
    ( k5_xboole_0(sP1_iProver_split,k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)),k3_xboole_0(sP1_iProver_split,sK2))) = X0 ),
    inference(superposition,[status(thm)],[c_25983,c_5492])).

cnf(c_21901,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_xboole_0(sK1,sK2),k3_subset_1(sK1,sK2))) = k5_xboole_0(k3_xboole_0(sK1,sK2),sP0_iProver_split(sK1)) ),
    inference(superposition,[status(thm)],[c_21805,c_3705])).

cnf(c_22083,plain,
    ( k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),k1_xboole_0) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),sK1) ),
    inference(light_normalisation,[status(thm)],[c_21901,c_1979,c_20024,c_21980])).

cnf(c_22084,plain,
    ( sP0_iProver_split(k3_subset_1(sP1_iProver_split,sK2)) = k3_xboole_0(sP1_iProver_split,sK2) ),
    inference(demodulation,[status(thm)],[c_22083,c_5,c_19649])).

cnf(c_23350,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)),k3_xboole_0(sP1_iProver_split,sK2)) = sP0_iProver_split(X0) ),
    inference(superposition,[status(thm)],[c_22084,c_19761])).

cnf(c_26111,plain,
    ( k5_xboole_0(sP1_iProver_split,sP0_iProver_split(X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_26047,c_23350])).

cnf(c_26146,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2))) = k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sK2)) ),
    inference(demodulation,[status(thm)],[c_26015,c_26111])).

cnf(c_28518,plain,
    ( k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sK2)))) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_28329,c_24127,c_26146])).

cnf(c_31025,plain,
    ( k5_xboole_0(sP1_iProver_split,k5_xboole_0(X0,X1)) = sP0_iProver_split(k5_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_31024,c_6601,c_21980,c_28518])).

cnf(c_52361,plain,
    ( k5_xboole_0(sP0_iProver_split(k5_xboole_0(X0,X1)),k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1) ),
    inference(light_normalisation,[status(thm)],[c_8141,c_8141,c_21980,c_31025,c_32628])).

cnf(c_7748,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = k3_subset_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_7628,c_1])).

cnf(c_7997,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = k3_subset_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_7,c_7748])).

cnf(c_50948,plain,
    ( k5_xboole_0(sP0_iProver_split(k5_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sP1_iProver_split)))) = k3_subset_1(sP1_iProver_split,sP1_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_7997,c_7997,c_21980,c_31025,c_32628])).

cnf(c_51126,plain,
    ( k5_xboole_0(sP0_iProver_split(k5_xboole_0(X0,X1)),k5_xboole_0(X2,k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sP1_iProver_split)))) ),
    inference(superposition,[status(thm)],[c_50948,c_5374])).

cnf(c_52225,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),sP0_iProver_split(X2)) = k5_xboole_0(k5_xboole_0(X3,sP0_iProver_split(k5_xboole_0(X1,X0))),X3) ),
    inference(superposition,[status(thm)],[c_48661,c_10635])).

cnf(c_52249,plain,
    ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X1,sP0_iProver_split(k5_xboole_0(X2,X3)))) = k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X3,X2),X0)) ),
    inference(superposition,[status(thm)],[c_48661,c_5374])).

cnf(c_19792,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,X1)) = k5_xboole_0(X0,sP0_iProver_split(X1)) ),
    inference(superposition,[status(thm)],[c_2423,c_19755])).

cnf(c_43687,plain,
    ( k5_xboole_0(sP0_iProver_split(X0),sP0_iProver_split(k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X2,X1),X0) ),
    inference(superposition,[status(thm)],[c_36749,c_12960])).

cnf(c_48686,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_12960,c_43653])).

cnf(c_52324,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X1),X0),X3) ),
    inference(demodulation,[status(thm)],[c_52249,c_19792,c_43687,c_48686])).

cnf(c_52233,plain,
    ( k5_xboole_0(sP0_iProver_split(sP0_iProver_split(X0)),sP0_iProver_split(k5_xboole_0(X1,X2))) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_48661,c_43653])).

cnf(c_52333,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X0,sP0_iProver_split(k5_xboole_0(X2,X1))) ),
    inference(light_normalisation,[status(thm)],[c_52233,c_20061])).

cnf(c_52345,plain,
    ( k5_xboole_0(sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2))),X0) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),X3),sP0_iProver_split(X3)) ),
    inference(demodulation,[status(thm)],[c_52225,c_52324,c_52333])).

cnf(c_52347,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),sP0_iProver_split(X2)) = sP2_iProver_split(X0,X1) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_52345])).

cnf(c_19770,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),sP0_iProver_split(X2)) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1168,c_19755])).

cnf(c_52348,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,X1)) = sP2_iProver_split(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_52347,c_7,c_19770])).

cnf(c_52362,plain,
    ( k5_xboole_0(sP2_iProver_split(X0,X1),k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X0) ),
    inference(demodulation,[status(thm)],[c_52361,c_51126,c_52348])).

cnf(c_52427,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)),k5_xboole_0(X1,sP2_iProver_split(X2,X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X2))) ),
    inference(superposition,[status(thm)],[c_52362,c_3559])).

cnf(c_6331,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = sK1 ),
    inference(superposition,[status(thm)],[c_3213,c_1])).

cnf(c_33108,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)),k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X0)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_6331,c_6331,c_21980,c_32628])).

cnf(c_8168,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k5_xboole_0(sK1,X1) ),
    inference(superposition,[status(thm)],[c_6966,c_2423])).

cnf(c_12400,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k5_xboole_0(X1,sK1) ),
    inference(superposition,[status(thm)],[c_10730,c_9603])).

cnf(c_52431,plain,
    ( k5_xboole_0(sP2_iProver_split(X0,X1),k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X0)),X2) ),
    inference(superposition,[status(thm)],[c_52362,c_12858])).

cnf(c_52432,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)),sP2_iProver_split(X1,X0)) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1)),X2) ),
    inference(superposition,[status(thm)],[c_52362,c_10635])).

cnf(c_52515,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1)),X0) = sP3_iProver_split(X1) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_52432])).

cnf(c_52516,plain,
    ( k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X0) = sP3_iProver_split(X0) ),
    inference(demodulation,[status(thm)],[c_52431,c_52362,c_52515])).

cnf(c_52558,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))),sP3_iProver_split(X0)) = k5_xboole_0(sP1_iProver_split,X1) ),
    inference(light_normalisation,[status(thm)],[c_8168,c_12400,c_21980,c_32628,c_52516])).

cnf(c_36825,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split(X2)) ),
    inference(superposition,[status(thm)],[c_1,c_19945])).

cnf(c_44597,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(sP0_iProver_split(X2),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_36825,c_1])).

cnf(c_36886,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(sP0_iProver_split(X2),k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_19945,c_1])).

cnf(c_49668,plain,
    ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sP0_iProver_split(X2),X3))) = k5_xboole_0(sP0_iProver_split(X3),sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2)))) ),
    inference(superposition,[status(thm)],[c_44597,c_36886])).

cnf(c_19477,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK1,X2))) = k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,sK1))) ),
    inference(superposition,[status(thm)],[c_11704,c_5374])).

cnf(c_20244,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,sK1))) = sP0_iProver_split(k5_xboole_0(X1,k5_xboole_0(X0,X2))) ),
    inference(demodulation,[status(thm)],[c_19477,c_19792,c_20128])).

cnf(c_20245,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X0,sP0_iProver_split(X2))) ),
    inference(demodulation,[status(thm)],[c_20244,c_19649])).

cnf(c_19482,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK1,X1)),k5_xboole_0(X2,k5_xboole_0(X1,sK1))) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_11704,c_5368])).

cnf(c_20236,plain,
    ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X1,sK1)))) = k5_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_19482,c_19792,c_19924,c_20128])).

cnf(c_20237,plain,
    ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,sP0_iProver_split(X1)))) = k5_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_20236,c_19649])).

cnf(c_20246,plain,
    ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X2)))) = k5_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_20245,c_20237])).

cnf(c_3576,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2423,c_3466])).

cnf(c_3615,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3576,c_1385])).

cnf(c_20247,plain,
    ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(X0,X1))) = k5_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_20246,c_3615])).

cnf(c_36878,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sP0_iProver_split(X2),X3)) = k5_xboole_0(sP0_iProver_split(k5_xboole_0(X1,k5_xboole_0(X0,X2))),X3) ),
    inference(superposition,[status(thm)],[c_19945,c_7])).

cnf(c_36880,plain,
    ( sP0_iProver_split(k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(k5_xboole_0(X1,X2),X3))) = k5_xboole_0(sP0_iProver_split(k5_xboole_0(X2,k5_xboole_0(X1,X0))),sP0_iProver_split(X3)) ),
    inference(superposition,[status(thm)],[c_19945,c_19945])).

cnf(c_36904,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,sP0_iProver_split(X3))) = k5_xboole_0(X2,sP0_iProver_split(k5_xboole_0(X1,k5_xboole_0(X0,X3)))) ),
    inference(superposition,[status(thm)],[c_19945,c_1167])).

cnf(c_36934,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X2,X1),X3))) ),
    inference(demodulation,[status(thm)],[c_36904,c_19792,c_20245])).

cnf(c_36963,plain,
    ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)))) = k5_xboole_0(sP0_iProver_split(k5_xboole_0(X2,k5_xboole_0(X0,X3))),sP0_iProver_split(X1)) ),
    inference(demodulation,[status(thm)],[c_36880,c_36886,c_36934])).

cnf(c_36604,plain,
    ( k5_xboole_0(sP0_iProver_split(k5_xboole_0(X0,X1)),sP0_iProver_split(X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_19767,c_2423])).

cnf(c_36964,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(k5_xboole_0(X0,X2),k5_xboole_0(X1,X3)) ),
    inference(demodulation,[status(thm)],[c_36963,c_20247,c_36604])).

cnf(c_36970,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sP0_iProver_split(X1),X2),X3)) = k5_xboole_0(sP0_iProver_split(k5_xboole_0(X2,k5_xboole_0(X0,X1))),X3) ),
    inference(demodulation,[status(thm)],[c_36878,c_36964])).

cnf(c_30757,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,X2))),k3_subset_1(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3559,c_12980])).

cnf(c_30781,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k1_xboole_0) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_3559,c_12858])).

cnf(c_30868,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,X2))),k3_subset_1(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(X2,k5_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_30757,c_30781])).

cnf(c_15764,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,X2))),k3_subset_1(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_1169,c_12980])).

cnf(c_16073,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,X2))),k3_subset_1(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_15764,c_7])).

cnf(c_30869,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),k5_xboole_0(X0,k5_xboole_0(X1,X2))),k3_subset_1(sP1_iProver_split,sK2)) = k5_xboole_0(sP1_iProver_split,k5_xboole_0(X2,k5_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_30868,c_16073,c_21980])).

cnf(c_24070,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),k5_xboole_0(X0,X1)),k3_subset_1(sP1_iProver_split,sK2)) = k5_xboole_0(k5_xboole_0(X0,X1),sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_5511,c_24050])).

cnf(c_19776,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split(k1_xboole_0)) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3466,c_19755])).

cnf(c_19996,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sP1_iProver_split) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_19994,c_19776])).

cnf(c_24154,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),k5_xboole_0(X0,X1)),k3_subset_1(sP1_iProver_split,sK2)) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_24070,c_19996])).

cnf(c_19549,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,X0),k3_subset_1(sK1,sK2))),k5_xboole_0(X0,sK1)) = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_11704,c_9572])).

cnf(c_5695,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,X0),k3_subset_1(sK1,sK2)) = k5_xboole_0(X0,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1,c_5450])).

cnf(c_20003,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),sP0_iProver_split(X0)) = k3_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_19549,c_2387,c_5695,c_19649])).

cnf(c_20535,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) = sP0_iProver_split(X1) ),
    inference(superposition,[status(thm)],[c_20003,c_9541])).

cnf(c_29789,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sK2)),k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sK2)))) = sP0_iProver_split(X1) ),
    inference(light_normalisation,[status(thm)],[c_20535,c_20535,c_21980])).

cnf(c_29846,plain,
    ( k5_xboole_0(k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k3_xboole_0(sP1_iProver_split,sK2)),k5_xboole_0(X0,X1)) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_12960,c_29789])).

cnf(c_3336,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),X0)),k5_xboole_0(k3_subset_1(sK1,sK2),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2408,c_2390])).

cnf(c_3338,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3336,c_2442])).

cnf(c_22840,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)),k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3338,c_3338,c_21980])).

cnf(c_22934,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sP1_iProver_split,sK2)),sK1)) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_22840,c_10390])).

cnf(c_22965,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k3_subset_1(sP1_iProver_split,sK2)),sP1_iProver_split)) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k3_xboole_0(sP1_iProver_split,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_22934,c_21980])).

cnf(c_22966,plain,
    ( sP0_iProver_split(k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k3_subset_1(sP1_iProver_split,sK2))) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k3_xboole_0(sP1_iProver_split,sK2)) ),
    inference(demodulation,[status(thm)],[c_22965,c_1385,c_3466,c_19996])).

cnf(c_22967,plain,
    ( k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k3_xboole_0(sP1_iProver_split,sK2)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_22966,c_8,c_19994])).

cnf(c_30029,plain,
    ( k5_xboole_0(sP1_iProver_split,k5_xboole_0(X0,X1)) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_29846,c_22967])).

cnf(c_30870,plain,
    ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),X2)) = sP0_iProver_split(k5_xboole_0(k5_xboole_0(X2,X0),X1)) ),
    inference(demodulation,[status(thm)],[c_30869,c_24154,c_30029])).

cnf(c_30871,plain,
    ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),X2)) = sP0_iProver_split(k5_xboole_0(X1,k5_xboole_0(X2,X0))) ),
    inference(light_normalisation,[status(thm)],[c_30870,c_7])).

cnf(c_36971,plain,
    ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3))) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X3),X2))) ),
    inference(demodulation,[status(thm)],[c_36970,c_19792,c_19924,c_30871])).

cnf(c_44897,plain,
    ( sP0_iProver_split(k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(k5_xboole_0(X1,X2),X3))) = k5_xboole_0(sP0_iProver_split(X3),sP0_iProver_split(k5_xboole_0(X2,k5_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_19945,c_36886])).

cnf(c_45183,plain,
    ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)))) = k5_xboole_0(sP0_iProver_split(X0),sP0_iProver_split(k5_xboole_0(X2,k5_xboole_0(X1,X3)))) ),
    inference(demodulation,[status(thm)],[c_44897,c_36886])).

cnf(c_44526,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,X0)),sP0_iProver_split(X3)) ),
    inference(superposition,[status(thm)],[c_1168,c_36825])).

cnf(c_36831,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),sP0_iProver_split(X3)) ),
    inference(superposition,[status(thm)],[c_7,c_19945])).

cnf(c_36833,plain,
    ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X2,X1)),sP0_iProver_split(X3)) ),
    inference(superposition,[status(thm)],[c_1167,c_19945])).

cnf(c_37090,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X3,X2)),sP0_iProver_split(X1)) ),
    inference(demodulation,[status(thm)],[c_36833,c_19945,c_36934,c_36971])).

cnf(c_37092,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,X0)),sP0_iProver_split(X3)) ),
    inference(demodulation,[status(thm)],[c_36831,c_36934,c_37090])).

cnf(c_44822,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3))) ),
    inference(light_normalisation,[status(thm)],[c_44526,c_37092])).

cnf(c_45184,plain,
    ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))))) = k5_xboole_0(sP0_iProver_split(X0),sP0_iProver_split(k5_xboole_0(X2,k5_xboole_0(X1,X3)))) ),
    inference(light_normalisation,[status(thm)],[c_45183,c_44822])).

cnf(c_45185,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X2),X1),X3) ),
    inference(demodulation,[status(thm)],[c_45184,c_20247,c_43687])).

cnf(c_49833,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,X1)),X3) ),
    inference(demodulation,[status(thm)],[c_49668,c_20245,c_20247,c_36971,c_43687,c_45185])).

cnf(c_49834,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),X3) ),
    inference(demodulation,[status(thm)],[c_49833,c_36964])).

cnf(c_52559,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))),sP3_iProver_split(X0)) = sP0_iProver_split(X1) ),
    inference(demodulation,[status(thm)],[c_52558,c_22110,c_49834])).

cnf(c_52588,plain,
    ( k5_xboole_0(sP1_iProver_split,sP3_iProver_split(k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),k3_subset_1(sP1_iProver_split,sP1_iProver_split)))) = sP0_iProver_split(k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) ),
    inference(superposition,[status(thm)],[c_33108,c_52559])).

cnf(c_8106,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k3_subset_1(sK1,sK2)))) = k5_xboole_0(k3_xboole_0(sK1,sK2),X1) ),
    inference(superposition,[status(thm)],[c_2387,c_6966])).

cnf(c_5471,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k3_subset_1(sK1,sK2)) = k5_xboole_0(X0,sK1) ),
    inference(superposition,[status(thm)],[c_3228,c_3678])).

cnf(c_8251,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(X1,k5_xboole_0(X0,sK1))) = k5_xboole_0(k3_xboole_0(sK1,sK2),X1) ),
    inference(light_normalisation,[status(thm)],[c_8106,c_5471])).

cnf(c_10747,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(X1,k5_xboole_0(X0,sK1))) = k5_xboole_0(X1,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_10385,c_1167])).

cnf(c_32681,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sP1_iProver_split)),k5_xboole_0(X1,k5_xboole_0(X0,sK1))) = k5_xboole_0(X1,k3_xboole_0(sK1,sP1_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_32628,c_10747])).

cnf(c_32822,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)),sP0_iProver_split(k5_xboole_0(X0,X1))) = k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) ),
    inference(light_normalisation,[status(thm)],[c_32681,c_19649,c_19897,c_21980])).

cnf(c_52742,plain,
    ( k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) = k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X0) ),
    inference(light_normalisation,[status(thm)],[c_8251,c_19649,c_19897,c_21980,c_32628,c_32822])).

cnf(c_52743,plain,
    ( k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) = sP3_iProver_split(X0) ),
    inference(demodulation,[status(thm)],[c_52742,c_52516])).

cnf(c_32746,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sP1_iProver_split)) = k3_subset_1(sK1,sP1_iProver_split) ),
    inference(demodulation,[status(thm)],[c_32628,c_1214])).

cnf(c_32749,plain,
    ( k5_xboole_0(sP1_iProver_split,k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) = k3_subset_1(sP1_iProver_split,sP1_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_32746,c_21980])).

cnf(c_52755,plain,
    ( k3_subset_1(sP1_iProver_split,sP1_iProver_split) = sP3_iProver_split(sP1_iProver_split) ),
    inference(demodulation,[status(thm)],[c_52743,c_32749])).

cnf(c_33392,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = k5_xboole_0(sP1_iProver_split,k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) ),
    inference(superposition,[status(thm)],[c_32749,c_5511])).

cnf(c_33409,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = k3_subset_1(sP1_iProver_split,sP1_iProver_split) ),
    inference(demodulation,[status(thm)],[c_33392,c_32749])).

cnf(c_52589,plain,
    ( k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),sP3_iProver_split(X0)) = sP0_iProver_split(X0) ),
    inference(superposition,[status(thm)],[c_33409,c_52559])).

cnf(c_53007,plain,
    ( k5_xboole_0(sP3_iProver_split(sP1_iProver_split),sP3_iProver_split(X0)) = sP0_iProver_split(X0) ),
    inference(demodulation,[status(thm)],[c_52589,c_52755])).

cnf(c_53008,plain,
    ( k5_xboole_0(sP1_iProver_split,sP3_iProver_split(sP0_iProver_split(sP1_iProver_split))) = sP0_iProver_split(k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_52588,c_52755,c_53007])).

cnf(c_23718,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),k3_subset_1(sP1_iProver_split,sK2))) = k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),sP1_iProver_split),k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_22967,c_12980])).

cnf(c_7709,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(X0,X1))) = k3_subset_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_7,c_7628])).

cnf(c_19855,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sP0_iProver_split(X0),k3_xboole_0(sK1,sK2))),k5_xboole_0(sK1,sP0_iProver_split(X1))) = k3_subset_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_19755,c_7709])).

cnf(c_19863,plain,
    ( k5_xboole_0(sP0_iProver_split(X0),sP0_iProver_split(X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_19755,c_2423])).

cnf(c_19925,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split(k5_xboole_0(X0,X2))) = sP0_iProver_split(k5_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_19924,c_19903])).

cnf(c_19933,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,sK1)) = k3_subset_1(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_19855,c_19863,c_19897,c_19924,c_19925])).

cnf(c_19934,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),sP0_iProver_split(X0)) = k3_subset_1(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_19933,c_7715,c_19649])).

cnf(c_22501,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sK2)),sP0_iProver_split(X0)) = k3_subset_1(sP1_iProver_split,sK2) ),
    inference(light_normalisation,[status(thm)],[c_19934,c_19934,c_21980])).

cnf(c_22553,plain,
    ( k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),k3_subset_1(sP1_iProver_split,sK2)) = k5_xboole_0(X0,sP0_iProver_split(X0)) ),
    inference(superposition,[status(thm)],[c_22501,c_3228])).

cnf(c_19493,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(sK1,X0)),k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_11704,c_3216])).

cnf(c_19501,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,X0))) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_11704,c_1978])).

cnf(c_19548,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_subset_1(sK1,sK2)),k5_xboole_0(X0,sK1)) = k5_xboole_0(k5_xboole_0(sK1,X0),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_11704,c_9599])).

cnf(c_8019,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,X0),k3_xboole_0(sK1,sK2)) = k5_xboole_0(X0,k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_7748,c_5374])).

cnf(c_20004,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),sP0_iProver_split(X0)) = k5_xboole_0(X0,k3_subset_1(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_19548,c_3241,c_8019,c_19649])).

cnf(c_20200,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,sK1)) = sP0_iProver_split(k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
    inference(demodulation,[status(thm)],[c_19501,c_20004,c_20128])).

cnf(c_20201,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,sK1)) = k5_xboole_0(k3_xboole_0(sK1,sK2),X0) ),
    inference(demodulation,[status(thm)],[c_20200,c_20016])).

cnf(c_3242,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),sK1) = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_2423,c_1683])).

cnf(c_3744,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,sK1)) = k5_xboole_0(X0,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_3242,c_1167])).

cnf(c_20202,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),sP0_iProver_split(X0)) = k5_xboole_0(k3_xboole_0(sK1,sK2),X0) ),
    inference(light_normalisation,[status(thm)],[c_20201,c_3744,c_19649])).

cnf(c_20215,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_19493,c_20128,c_20202])).

cnf(c_5587,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),k3_xboole_0(sK1,sK2)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_3523,c_3466])).

cnf(c_5625,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),k3_xboole_0(sK1,sK2)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5587,c_1385])).

cnf(c_20216,plain,
    ( k5_xboole_0(X0,sP0_iProver_split(X0)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_20215,c_5625,c_19649])).

cnf(c_22559,plain,
    ( k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),k3_subset_1(sP1_iProver_split,sK2)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_22553,c_20216,c_21980])).

cnf(c_22512,plain,
    ( k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),sP0_iProver_split(k1_xboole_0)) = k3_subset_1(sP1_iProver_split,sK2) ),
    inference(superposition,[status(thm)],[c_1385,c_22501])).

cnf(c_22602,plain,
    ( k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),sP1_iProver_split) = k3_subset_1(sP1_iProver_split,sK2) ),
    inference(light_normalisation,[status(thm)],[c_22512,c_19994])).

cnf(c_23782,plain,
    ( k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k3_subset_1(sP1_iProver_split,sK2)) = k5_xboole_0(sP1_iProver_split,sP1_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_23718,c_21980,c_22559,c_22602])).

cnf(c_23783,plain,
    ( sP0_iProver_split(sP1_iProver_split) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_23782,c_8,c_22110])).

cnf(c_33373,plain,
    ( k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),sP0_iProver_split(sP1_iProver_split)) = sP0_iProver_split(k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) ),
    inference(superposition,[status(thm)],[c_32749,c_19755])).

cnf(c_33422,plain,
    ( k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),k1_xboole_0) = sP0_iProver_split(k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) ),
    inference(light_normalisation,[status(thm)],[c_33373,c_23783])).

cnf(c_33423,plain,
    ( sP0_iProver_split(k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) = k3_subset_1(sP1_iProver_split,sP1_iProver_split) ),
    inference(demodulation,[status(thm)],[c_33422,c_5])).

cnf(c_53009,plain,
    ( k5_xboole_0(sP1_iProver_split,sP3_iProver_split(k1_xboole_0)) = k3_subset_1(sP1_iProver_split,sP1_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_53008,c_23783,c_33423])).

cnf(c_53010,plain,
    ( sP0_iProver_split(sP3_iProver_split(k1_xboole_0)) = k3_subset_1(sP1_iProver_split,sP1_iProver_split) ),
    inference(demodulation,[status(thm)],[c_53009,c_22110])).

cnf(c_53195,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sP0_iProver_split(sP3_iProver_split(k1_xboole_0))),k5_xboole_0(X1,sP2_iProver_split(X2,X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X2))) ),
    inference(demodulation,[status(thm)],[c_52427,c_53010])).

cnf(c_30637,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_1,c_3559])).

cnf(c_3513,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_1168,c_2452])).

cnf(c_4352,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_1169,c_2452])).

cnf(c_35768,plain,
    ( k5_xboole_0(sP1_iProver_split,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),k5_xboole_0(X0,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split))) ),
    inference(light_normalisation,[status(thm)],[c_3513,c_4352,c_21980,c_32628])).

cnf(c_36507,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))),sP0_iProver_split(k5_xboole_0(sP1_iProver_split,k3_xboole_0(sP1_iProver_split,sP1_iProver_split)))) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_35768,c_19767])).

cnf(c_32688,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sP1_iProver_split))),k5_xboole_0(X0,k5_xboole_0(sK1,X1))) = k3_xboole_0(sK1,sP1_iProver_split) ),
    inference(demodulation,[status(thm)],[c_32628,c_9572])).

cnf(c_32811,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))),k5_xboole_0(X0,k5_xboole_0(sP1_iProver_split,X1))) = k3_xboole_0(sP1_iProver_split,sP1_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_32688,c_21980])).

cnf(c_13368,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X3)) = k5_xboole_0(k5_xboole_0(X1,X2),X3) ),
    inference(superposition,[status(thm)],[c_12858,c_7])).

cnf(c_32812,plain,
    ( sP0_iProver_split(k3_subset_1(sP1_iProver_split,sP1_iProver_split)) = k3_xboole_0(sP1_iProver_split,sP1_iProver_split) ),
    inference(demodulation,[status(thm)],[c_32811,c_13368,c_19767,c_19792,c_22110])).

cnf(c_36753,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))),k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_36507,c_32749,c_32812])).

cnf(c_37956,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))),k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X2)) = k5_xboole_0(sP0_iProver_split(k5_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_36753,c_7])).

cnf(c_37976,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))),k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X2)) = k5_xboole_0(X2,sP0_iProver_split(k5_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_36753,c_1169])).

cnf(c_38012,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))),k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X2)) = sP0_iProver_split(k5_xboole_0(X2,k5_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_37976,c_19792,c_36964])).

cnf(c_38042,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(sP0_iProver_split(k5_xboole_0(X1,X2)),X0) ),
    inference(demodulation,[status(thm)],[c_37956,c_38012])).

cnf(c_53196,plain,
    ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,sP2_iProver_split(X1,X2)),k5_xboole_0(X2,sP3_iProver_split(k1_xboole_0)))) = sP3_iProver_split(k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_53195,c_19792,c_30637,c_36964,c_38042,c_52516])).

cnf(c_53197,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sP2_iProver_split(X2,X1),sP3_iProver_split(k1_xboole_0))))) = sP3_iProver_split(k5_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_53196,c_36964,c_36971,c_44822])).

cnf(c_52463,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)),k5_xboole_0(X1,sP2_iProver_split(X2,X0))) = k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X2)) ),
    inference(superposition,[status(thm)],[c_52362,c_1169])).

cnf(c_53101,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sP0_iProver_split(sP3_iProver_split(k1_xboole_0))),k5_xboole_0(X1,sP2_iProver_split(X2,X0))) = k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X2)) ),
    inference(demodulation,[status(thm)],[c_52463,c_53010])).

cnf(c_53102,plain,
    ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,sP2_iProver_split(X1,X2)),k5_xboole_0(X2,sP3_iProver_split(k1_xboole_0)))) = k5_xboole_0(X0,sP3_iProver_split(X1)) ),
    inference(demodulation,[status(thm)],[c_53101,c_19792,c_36964,c_38042,c_52516])).

cnf(c_53103,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sP2_iProver_split(X2,X1),sP3_iProver_split(k1_xboole_0))))) = k5_xboole_0(X0,sP3_iProver_split(X2)) ),
    inference(demodulation,[status(thm)],[c_53102,c_36964,c_36971,c_44822])).

cnf(c_53198,plain,
    ( sP3_iProver_split(k5_xboole_0(X0,X1)) = k5_xboole_0(X0,sP3_iProver_split(X1)) ),
    inference(demodulation,[status(thm)],[c_53197,c_53103])).

cnf(c_52647,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))),k5_xboole_0(X2,sP3_iProver_split(X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,sP0_iProver_split(X1))) ),
    inference(superposition,[status(thm)],[c_52559,c_30637])).

cnf(c_32732,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(sK1,sP1_iProver_split))) = k5_xboole_0(X0,k3_subset_1(sK1,sP1_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_32628,c_2387])).

cnf(c_32763,plain,
    ( k5_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sP1_iProver_split))) = k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)) ),
    inference(light_normalisation,[status(thm)],[c_32732,c_21980])).

cnf(c_52753,plain,
    ( k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)) = k5_xboole_0(sP1_iProver_split,sP3_iProver_split(X0)) ),
    inference(demodulation,[status(thm)],[c_52743,c_32763])).

cnf(c_52758,plain,
    ( k5_xboole_0(X0,sP3_iProver_split(sP1_iProver_split)) = k5_xboole_0(sP1_iProver_split,sP3_iProver_split(X0)) ),
    inference(demodulation,[status(thm)],[c_52753,c_52755])).

cnf(c_52759,plain,
    ( k5_xboole_0(X0,sP3_iProver_split(sP1_iProver_split)) = sP0_iProver_split(sP3_iProver_split(X0)) ),
    inference(demodulation,[status(thm)],[c_52758,c_22110])).

cnf(c_52853,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sP0_iProver_split(sP3_iProver_split(X1))),k5_xboole_0(X2,sP3_iProver_split(X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,sP0_iProver_split(X1))) ),
    inference(demodulation,[status(thm)],[c_52647,c_52755,c_52759])).

cnf(c_52854,plain,
    ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,sP3_iProver_split(X1)),k5_xboole_0(X1,sP3_iProver_split(X2)))) = sP0_iProver_split(k5_xboole_0(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_52853,c_3466,c_19792,c_19924,c_36964,c_38042])).

cnf(c_52855,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sP3_iProver_split(X1),sP3_iProver_split(X2))))) = sP2_iProver_split(X0,X2) ),
    inference(demodulation,[status(thm)],[c_52854,c_36964,c_36971,c_44822,c_52348])).

cnf(c_53237,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,sP3_iProver_split(k5_xboole_0(sP3_iProver_split(X1),X2))))) = sP2_iProver_split(X0,X2) ),
    inference(demodulation,[status(thm)],[c_53198,c_52855])).

cnf(c_52666,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))),k5_xboole_0(X2,sP3_iProver_split(X0))) = k5_xboole_0(X2,sP0_iProver_split(X1)) ),
    inference(superposition,[status(thm)],[c_52559,c_1167])).

cnf(c_52800,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sP0_iProver_split(sP3_iProver_split(X1))),k5_xboole_0(X2,sP3_iProver_split(X0))) = k5_xboole_0(X2,sP0_iProver_split(X1)) ),
    inference(demodulation,[status(thm)],[c_52666,c_52755,c_52759])).

cnf(c_52801,plain,
    ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,sP3_iProver_split(X1)),k5_xboole_0(X1,sP3_iProver_split(X2)))) = sP2_iProver_split(X2,X0) ),
    inference(demodulation,[status(thm)],[c_52800,c_19792,c_36964,c_38042,c_52348])).

cnf(c_52802,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sP3_iProver_split(X1),sP3_iProver_split(X2))))) = sP2_iProver_split(X2,X0) ),
    inference(demodulation,[status(thm)],[c_52801,c_36964,c_36971,c_44822])).

cnf(c_53238,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,sP3_iProver_split(k5_xboole_0(sP3_iProver_split(X1),X2))))) = sP2_iProver_split(X2,X0) ),
    inference(demodulation,[status(thm)],[c_53198,c_52802])).

cnf(c_53338,plain,
    ( sP0_iProver_split(sP3_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sP3_iProver_split(X1),X2))))) = sP2_iProver_split(X2,X0) ),
    inference(demodulation,[status(thm)],[c_53238,c_53198])).

cnf(c_53339,plain,
    ( sP2_iProver_split(X0,X1) = sP2_iProver_split(X1,X0) ),
    inference(demodulation,[status(thm)],[c_53237,c_53198,c_53338])).

cnf(c_52582,plain,
    ( k5_xboole_0(X0,sP3_iProver_split(k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),k5_xboole_0(X0,X1)))) = sP0_iProver_split(X1) ),
    inference(superposition,[status(thm)],[c_9603,c_52559])).

cnf(c_53023,plain,
    ( k5_xboole_0(X0,sP3_iProver_split(k5_xboole_0(sP0_iProver_split(sP3_iProver_split(k1_xboole_0)),k5_xboole_0(X0,X1)))) = sP0_iProver_split(X1) ),
    inference(demodulation,[status(thm)],[c_52582,c_53010])).

cnf(c_53024,plain,
    ( k5_xboole_0(X0,sP3_iProver_split(sP0_iProver_split(k5_xboole_0(sP3_iProver_split(k1_xboole_0),k5_xboole_0(X1,X0))))) = sP0_iProver_split(X1) ),
    inference(demodulation,[status(thm)],[c_53023,c_48686])).

cnf(c_53025,plain,
    ( k5_xboole_0(X0,sP3_iProver_split(sP2_iProver_split(k5_xboole_0(X1,X0),sP3_iProver_split(k1_xboole_0)))) = sP0_iProver_split(X1) ),
    inference(demodulation,[status(thm)],[c_53024,c_52348])).

cnf(c_53347,plain,
    ( k5_xboole_0(X0,sP3_iProver_split(sP2_iProver_split(sP3_iProver_split(k1_xboole_0),k5_xboole_0(X1,X0)))) = sP0_iProver_split(X1) ),
    inference(demodulation,[status(thm)],[c_53339,c_53025])).

cnf(c_52570,plain,
    ( k5_xboole_0(k1_xboole_0,sP3_iProver_split(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)))) = sP0_iProver_split(X0) ),
    inference(superposition,[status(thm)],[c_8,c_52559])).

cnf(c_53057,plain,
    ( k5_xboole_0(k1_xboole_0,sP3_iProver_split(k5_xboole_0(X0,sP0_iProver_split(sP3_iProver_split(k1_xboole_0))))) = sP0_iProver_split(X0) ),
    inference(demodulation,[status(thm)],[c_52570,c_53010])).

cnf(c_53058,plain,
    ( sP3_iProver_split(sP0_iProver_split(k5_xboole_0(X0,sP3_iProver_split(k1_xboole_0)))) = sP0_iProver_split(X0) ),
    inference(demodulation,[status(thm)],[c_53057,c_1385,c_19792])).

cnf(c_53059,plain,
    ( sP3_iProver_split(sP2_iProver_split(sP3_iProver_split(k1_xboole_0),X0)) = sP0_iProver_split(X0) ),
    inference(demodulation,[status(thm)],[c_53058,c_52348])).

cnf(c_53374,plain,
    ( k5_xboole_0(X0,sP0_iProver_split(k5_xboole_0(X1,X0))) = sP0_iProver_split(X1) ),
    inference(demodulation,[status(thm)],[c_53347,c_53059,c_53198])).

cnf(c_53375,plain,
    ( k5_xboole_0(X0,sP2_iProver_split(X0,X1)) = sP0_iProver_split(X1) ),
    inference(demodulation,[status(thm)],[c_53374,c_52348])).

cnf(c_52581,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sP3_iProver_split(k5_xboole_0(k5_xboole_0(X2,k3_subset_1(sP1_iProver_split,sP1_iProver_split)),k5_xboole_0(X1,X0)))) = sP0_iProver_split(X2) ),
    inference(superposition,[status(thm)],[c_10635,c_52559])).

cnf(c_53026,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sP3_iProver_split(k5_xboole_0(k5_xboole_0(X2,sP0_iProver_split(sP3_iProver_split(k1_xboole_0))),k5_xboole_0(X1,X0)))) = sP0_iProver_split(X2) ),
    inference(demodulation,[status(thm)],[c_52581,c_53010])).

cnf(c_53027,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sP3_iProver_split(k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X1,sP0_iProver_split(sP3_iProver_split(k1_xboole_0))),X0)))) = sP0_iProver_split(X2) ),
    inference(demodulation,[status(thm)],[c_53026,c_36964])).

cnf(c_53028,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sP3_iProver_split(sP0_iProver_split(k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,sP3_iProver_split(k1_xboole_0))))))) = sP0_iProver_split(X2) ),
    inference(demodulation,[status(thm)],[c_53027,c_19792,c_38042])).

cnf(c_53029,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sP3_iProver_split(sP2_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,sP3_iProver_split(k1_xboole_0))),X2))) = sP0_iProver_split(X2) ),
    inference(demodulation,[status(thm)],[c_53028,c_52348])).

cnf(c_53263,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sP3_iProver_split(sP2_iProver_split(k5_xboole_0(X0,sP3_iProver_split(k5_xboole_0(X1,k1_xboole_0))),X2))) = sP0_iProver_split(X2) ),
    inference(demodulation,[status(thm)],[c_53198,c_53029])).

cnf(c_52636,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = k5_xboole_0(sP3_iProver_split(X0),sP0_iProver_split(X1)) ),
    inference(superposition,[status(thm)],[c_52559,c_2423])).

cnf(c_52881,plain,
    ( k5_xboole_0(X0,sP0_iProver_split(sP3_iProver_split(X1))) = k5_xboole_0(sP3_iProver_split(X0),sP0_iProver_split(X1)) ),
    inference(demodulation,[status(thm)],[c_52636,c_52755,c_52759])).

cnf(c_52882,plain,
    ( sP2_iProver_split(sP3_iProver_split(X0),X1) = sP2_iProver_split(X0,sP3_iProver_split(X1)) ),
    inference(demodulation,[status(thm)],[c_52881,c_19792,c_52348])).

cnf(c_53301,plain,
    ( sP3_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),sP2_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)),sP3_iProver_split(X2)))) = sP0_iProver_split(X2) ),
    inference(demodulation,[status(thm)],[c_53263,c_52882,c_53198])).

cnf(c_53302,plain,
    ( sP3_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),sP2_iProver_split(k5_xboole_0(X0,X1),sP3_iProver_split(X2)))) = sP0_iProver_split(X2) ),
    inference(demodulation,[status(thm)],[c_53301,c_5])).

cnf(c_53376,plain,
    ( sP3_iProver_split(sP0_iProver_split(sP3_iProver_split(X0))) = sP0_iProver_split(X0) ),
    inference(demodulation,[status(thm)],[c_53375,c_53302])).

cnf(c_52584,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sP3_iProver_split(k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_12960,c_52559])).

cnf(c_53018,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sP3_iProver_split(sP0_iProver_split(sP3_iProver_split(k1_xboole_0)))) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_52584,c_53010])).

cnf(c_53019,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sP3_iProver_split(sP0_iProver_split(sP3_iProver_split(k1_xboole_0)))) = sP2_iProver_split(X0,X1) ),
    inference(demodulation,[status(thm)],[c_53018,c_52348])).

cnf(c_53379,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split(k1_xboole_0)) = sP2_iProver_split(X0,X1) ),
    inference(demodulation,[status(thm)],[c_53376,c_53019])).

cnf(c_3219,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2))),k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) = sK1 ),
    inference(superposition,[status(thm)],[c_2452,c_2423])).

cnf(c_31560,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sK2))),k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sK2)))) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_3219,c_3219,c_21980])).

cnf(c_14650,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X1,k3_subset_1(sK1,sK2)),sK1) ),
    inference(superposition,[status(thm)],[c_6118,c_10732])).

cnf(c_5704,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK1),k5_xboole_0(k3_subset_1(sK1,sK2),X1)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),X1) ),
    inference(superposition,[status(thm)],[c_5450,c_7])).

cnf(c_5460,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK1),k5_xboole_0(k3_subset_1(sK1,sK2),X1)) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)) ),
    inference(superposition,[status(thm)],[c_3228,c_2390])).

cnf(c_5726,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),X1) ),
    inference(light_normalisation,[status(thm)],[c_5704,c_5460])).

cnf(c_14764,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,k3_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_14650,c_5726,c_10748])).

cnf(c_28687,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sK2)),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_14764,c_14764,c_21980])).

cnf(c_31678,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sK2))),k3_xboole_0(sP1_iProver_split,sK2)),sP1_iProver_split) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sK2))),k3_xboole_0(sP1_iProver_split,sK2)) ),
    inference(superposition,[status(thm)],[c_31560,c_28687])).

cnf(c_7762,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(X1,k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_7628,c_1169])).

cnf(c_28795,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,X0),k3_xboole_0(sP1_iProver_split,sK2)),k5_xboole_0(X1,k3_subset_1(sK1,sK2))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sP1_iProver_split,sK2)) ),
    inference(superposition,[status(thm)],[c_7762,c_28687])).

cnf(c_22532,plain,
    ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sK2))) = k3_subset_1(sP1_iProver_split,sK2) ),
    inference(superposition,[status(thm)],[c_22501,c_1])).

cnf(c_26362,plain,
    ( k5_xboole_0(sP0_iProver_split(X0),k3_xboole_0(sP1_iProver_split,sK2)) = k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)) ),
    inference(superposition,[status(thm)],[c_22532,c_5374])).

cnf(c_28360,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)),k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sK2))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_28187,c_5511])).

cnf(c_29037,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sK2))),k3_xboole_0(sP1_iProver_split,sK2)) = k5_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_28795,c_20128,c_21980,c_26362,c_28360])).

cnf(c_28789,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sP1_iProver_split,sK2)),k5_xboole_0(sK1,X1)) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2))),k3_xboole_0(sP1_iProver_split,sK2)) ),
    inference(superposition,[status(thm)],[c_6952,c_28687])).

cnf(c_3946,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(k3_subset_1(sK1,sK2),X0)) = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1,c_3700])).

cnf(c_24190,plain,
    ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),X0)) = k3_xboole_0(sP1_iProver_split,sK2) ),
    inference(light_normalisation,[status(thm)],[c_3946,c_3946,c_20128,c_21980])).

cnf(c_24252,plain,
    ( k5_xboole_0(k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),X0))),k3_xboole_0(sP1_iProver_split,sK2)) = X1 ),
    inference(superposition,[status(thm)],[c_24190,c_5492])).

cnf(c_10388,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1)),k5_xboole_0(X0,sK1)) = k5_xboole_0(k3_xboole_0(sK1,sK2),X1) ),
    inference(superposition,[status(thm)],[c_1683,c_9541])).

cnf(c_19539,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK1),k5_xboole_0(k3_subset_1(sK1,sK2),sK1)) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_11704,c_10388])).

cnf(c_20117,plain,
    ( k5_xboole_0(sP0_iProver_split(X0),k3_xboole_0(sK1,sK2)) = k5_xboole_0(k3_subset_1(sK1,sK2),X0) ),
    inference(light_normalisation,[status(thm)],[c_19539,c_3242,c_5406,c_19649])).

cnf(c_19449,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(sK1,X1)))) = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X1,sK1)),k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_11704,c_5947])).

cnf(c_3701,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(sK1,sK2),X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_3468,c_1168])).

cnf(c_19527,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,X1)),k3_subset_1(sK1,sK2))) = k5_xboole_0(k5_xboole_0(X1,sK1),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) ),
    inference(superposition,[status(thm)],[c_11704,c_3701])).

cnf(c_20145,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK1,X1),k3_subset_1(sK1,sK2)))) = k5_xboole_0(k5_xboole_0(X1,sK1),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) ),
    inference(demodulation,[status(thm)],[c_19527,c_19792,c_19924,c_20128])).

cnf(c_19782,plain,
    ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)),sP0_iProver_split(sK1)) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_1905,c_19755])).

cnf(c_20031,plain,
    ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)),k1_xboole_0) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) ),
    inference(demodulation,[status(thm)],[c_20024,c_19782])).

cnf(c_2042,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1))) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_1905])).

cnf(c_19787,plain,
    ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)),sP0_iProver_split(sK1)) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1))) ),
    inference(superposition,[status(thm)],[c_2042,c_19755])).

cnf(c_20034,plain,
    ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)),k1_xboole_0) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1))) ),
    inference(demodulation,[status(thm)],[c_20024,c_19787])).

cnf(c_19838,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),sP0_iProver_split(k5_xboole_0(sK1,X1))) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_7762,c_19755])).

cnf(c_19950,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),sP0_iProver_split(sP0_iProver_split(X1))) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) ),
    inference(demodulation,[status(thm)],[c_19948,c_19838])).

cnf(c_20063,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),X1) ),
    inference(demodulation,[status(thm)],[c_20061,c_19950])).

cnf(c_20090,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_20063,c_11164])).

cnf(c_20099,plain,
    ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)),k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))) ),
    inference(demodulation,[status(thm)],[c_20031,c_20034,c_20090])).

cnf(c_20100,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))) ),
    inference(demodulation,[status(thm)],[c_20099,c_20034])).

cnf(c_19832,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,X0),sP0_iProver_split(k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_6952,c_19755])).

cnf(c_20049,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(k3_subset_1(sK1,sK2),X1)) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) ),
    inference(demodulation,[status(thm)],[c_20040,c_19832])).

cnf(c_5798,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),X0),X1),k5_xboole_0(k5_xboole_0(sK1,X1),X2)) = k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X2) ),
    inference(superposition,[status(thm)],[c_5402,c_3228])).

cnf(c_3480,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_2423,c_1168])).

cnf(c_5609,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),k5_xboole_0(X1,k3_subset_1(sK1,sK2))) = k5_xboole_0(k5_xboole_0(sK1,X1),X0) ),
    inference(superposition,[status(thm)],[c_3523,c_3701])).

cnf(c_5263,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),k5_xboole_0(X1,k3_subset_1(sK1,sK2))) = k5_xboole_0(X1,k5_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_1978,c_1169])).

cnf(c_5615,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sK1,X1)) = k5_xboole_0(k5_xboole_0(sK1,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_5609,c_5263])).

cnf(c_5823,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(k3_subset_1(sK1,sK2),X1)) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_5798,c_3480,c_5500,c_5615])).

cnf(c_20050,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_20049,c_5823])).

cnf(c_19818,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),sP0_iProver_split(k5_xboole_0(sK1,X1))) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_6966,c_19755])).

cnf(c_19965,plain,
    ( sP0_iProver_split(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sP0_iProver_split(X0),X1))) = sP0_iProver_split(k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2)))) ),
    inference(demodulation,[status(thm)],[c_19818,c_19824,c_19948])).

cnf(c_19966,plain,
    ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(sK1,sK2)))) = sP0_iProver_split(k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2)))) ),
    inference(demodulation,[status(thm)],[c_19965,c_19897,c_19924])).

cnf(c_11198,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),sK1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_7,c_10748])).

cnf(c_7288,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_2387,c_5374])).

cnf(c_8692,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),sK1) ),
    inference(superposition,[status(thm)],[c_7288,c_3466])).

cnf(c_5988,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X1))) = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1))),k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1974,c_5947])).

cnf(c_6087,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X1))) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_5988,c_5947])).

cnf(c_6088,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_6087,c_4247])).

cnf(c_3474,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),X0)) = k5_xboole_0(X0,sK1) ),
    inference(superposition,[status(thm)],[c_1899,c_1168])).

cnf(c_5585,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) = k5_xboole_0(X0,k5_xboole_0(sK1,X1)) ),
    inference(superposition,[status(thm)],[c_3705,c_3523])).

cnf(c_6089,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sK1) = k5_xboole_0(X1,k5_xboole_0(sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_6088,c_3474,c_5585])).

cnf(c_8750,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),sK1) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)) ),
    inference(demodulation,[status(thm)],[c_8692,c_3589,c_6089])).

cnf(c_11261,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(sK1,sK2)) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)) ),
    inference(light_normalisation,[status(thm)],[c_11198,c_8750])).

cnf(c_19967,plain,
    ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)))) = sP0_iProver_split(k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2)))) ),
    inference(light_normalisation,[status(thm)],[c_19966,c_11261])).

cnf(c_20052,plain,
    ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)))) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_20050,c_19967])).

cnf(c_20104,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_20100,c_20052])).

cnf(c_20146,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK1),k5_xboole_0(k3_xboole_0(sK1,sK2),X1)) = k5_xboole_0(k5_xboole_0(X1,X0),k3_subset_1(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_20145,c_19792,c_20004,c_20104,c_20128])).

cnf(c_8539,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK1),k5_xboole_0(k3_xboole_0(sK1,sK2),X1)) = k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1)) ),
    inference(superposition,[status(thm)],[c_7286,c_3228])).

cnf(c_20147,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k3_subset_1(sK1,sK2)) = k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sK1,sK2),X0)) ),
    inference(light_normalisation,[status(thm)],[c_20146,c_8539])).

cnf(c_20302,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK1),k5_xboole_0(k3_subset_1(sK1,sK2),sK1)) = k5_xboole_0(X0,k3_subset_1(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_19449,c_19792,c_19908,c_20004,c_20128,c_20147])).

cnf(c_20303,plain,
    ( k5_xboole_0(sP0_iProver_split(X0),k3_xboole_0(sK1,sK2)) = k5_xboole_0(X0,k3_subset_1(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_20302,c_3242,c_19649])).

cnf(c_22756,plain,
    ( k5_xboole_0(sP0_iProver_split(X0),k3_xboole_0(sP1_iProver_split,sK2)) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),X0) ),
    inference(light_normalisation,[status(thm)],[c_20117,c_20303,c_21980])).

cnf(c_22788,plain,
    ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),X0))) = k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sK2)) ),
    inference(superposition,[status(thm)],[c_22756,c_5374])).

cnf(c_24322,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sK2)),k3_xboole_0(sP1_iProver_split,sK2)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_24252,c_22788])).

cnf(c_29047,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sK2))),k3_xboole_0(sP1_iProver_split,sK2)) = k5_xboole_0(X1,k5_xboole_0(sP1_iProver_split,X0)) ),
    inference(light_normalisation,[status(thm)],[c_28789,c_21980,c_24322])).

cnf(c_29048,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sK2))),k3_xboole_0(sP1_iProver_split,sK2)) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_29047,c_19792,c_22110])).

cnf(c_31818,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),sP1_iProver_split) = sP0_iProver_split(k5_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_31678,c_29037,c_29048])).

cnf(c_53380,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,X1)) = sP2_iProver_split(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_53379,c_19994,c_31818])).

cnf(c_52577,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = k5_xboole_0(k1_xboole_0,sP3_iProver_split(X0)) ),
    inference(superposition,[status(thm)],[c_2408,c_52559])).

cnf(c_53040,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,sP0_iProver_split(sP3_iProver_split(k1_xboole_0)))) = k5_xboole_0(k1_xboole_0,sP3_iProver_split(X0)) ),
    inference(demodulation,[status(thm)],[c_52577,c_53010])).

cnf(c_19502,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,X1)))) = k5_xboole_0(k5_xboole_0(X1,sK1),k5_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_11704,c_3471])).

cnf(c_19508,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),k5_xboole_0(sK1,X1)))) = k5_xboole_0(sK1,k5_xboole_0(X1,sK1)) ),
    inference(superposition,[status(thm)],[c_11704,c_1974])).

cnf(c_19538,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,X0)),k5_xboole_0(k3_subset_1(sK1,sK2),X1)) = k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X1),k5_xboole_0(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_11704,c_3471])).

cnf(c_20118,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),sP0_iProver_split(X1)) = k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sK1,sK2),X0)) ),
    inference(light_normalisation,[status(thm)],[c_19538,c_3105,c_19649])).

cnf(c_20188,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sK1,sK2),X0)))) = sP0_iProver_split(k5_xboole_0(X1,sK1)) ),
    inference(demodulation,[status(thm)],[c_19508,c_20118,c_20128])).

cnf(c_18882,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sK1,sK2),X0))) = k5_xboole_0(X1,k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_7805,c_1169])).

cnf(c_20189,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = sP0_iProver_split(k5_xboole_0(X0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_20188,c_18882])).

cnf(c_2048,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = k5_xboole_0(sK1,k5_xboole_0(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_1899,c_1905])).

cnf(c_20190,plain,
    ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = sP0_iProver_split(sP0_iProver_split(X0)) ),
    inference(demodulation,[status(thm)],[c_20189,c_2048,c_19649])).

cnf(c_20197,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,sK1))) = sP0_iProver_split(k5_xboole_0(X1,sP0_iProver_split(X0))) ),
    inference(demodulation,[status(thm)],[c_19502,c_19792,c_19824,c_20004,c_20128,c_20190])).

cnf(c_20198,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,sK1))) = k5_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_20197,c_19792,c_20061])).

cnf(c_20199,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,sP0_iProver_split(X1))) = k5_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_20198,c_19649])).

cnf(c_53041,plain,
    ( k5_xboole_0(sP3_iProver_split(k1_xboole_0),X0) = sP3_iProver_split(X0) ),
    inference(demodulation,[status(thm)],[c_53040,c_1385,c_19792,c_20199,c_20247])).

cnf(c_32937,plain,
    ( k5_xboole_0(sP1_iProver_split,k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),X0)) = k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X0) ),
    inference(light_normalisation,[status(thm)],[c_5196,c_5196,c_21980,c_32628])).

cnf(c_52586,plain,
    ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),k3_subset_1(sP1_iProver_split,sP1_iProver_split)),sP3_iProver_split(sP1_iProver_split)) = sP0_iProver_split(k3_subset_1(sP1_iProver_split,sP1_iProver_split)) ),
    inference(superposition,[status(thm)],[c_32937,c_52559])).

cnf(c_53012,plain,
    ( sP0_iProver_split(sP3_iProver_split(k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),sP0_iProver_split(sP3_iProver_split(k1_xboole_0))))) = sP0_iProver_split(sP0_iProver_split(sP3_iProver_split(k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_52586,c_52759,c_53010])).

cnf(c_32728,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sP1_iProver_split),k5_xboole_0(sK1,X0)) = k5_xboole_0(X0,k3_subset_1(sK1,sP1_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_32628,c_3468])).

cnf(c_32767,plain,
    ( k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),sP0_iProver_split(X0)) = k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)) ),
    inference(light_normalisation,[status(thm)],[c_32728,c_20128,c_21980])).

cnf(c_53013,plain,
    ( sP0_iProver_split(sP3_iProver_split(k5_xboole_0(sP3_iProver_split(k1_xboole_0),k3_subset_1(sP1_iProver_split,sP1_iProver_split)))) = sP3_iProver_split(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_53012,c_20061,c_32767])).

cnf(c_53042,plain,
    ( sP0_iProver_split(sP3_iProver_split(sP3_iProver_split(k3_subset_1(sP1_iProver_split,sP1_iProver_split)))) = sP3_iProver_split(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_53041,c_53013])).

cnf(c_53045,plain,
    ( sP0_iProver_split(sP3_iProver_split(sP3_iProver_split(sP0_iProver_split(sP3_iProver_split(k1_xboole_0))))) = sP3_iProver_split(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_53042,c_53010])).

cnf(c_53378,plain,
    ( sP0_iProver_split(sP3_iProver_split(sP0_iProver_split(k1_xboole_0))) = sP3_iProver_split(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_53376,c_53045])).

cnf(c_53381,plain,
    ( sP0_iProver_split(sP3_iProver_split(sP1_iProver_split)) = sP3_iProver_split(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_53378,c_19994])).

cnf(c_52597,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),sP3_iProver_split(X0)) = sP0_iProver_split(k3_subset_1(sP1_iProver_split,sP1_iProver_split)) ),
    inference(superposition,[status(thm)],[c_8,c_52559])).

cnf(c_52996,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),sP3_iProver_split(X0)) = sP0_iProver_split(sP3_iProver_split(sP1_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_52597,c_52755])).

cnf(c_52997,plain,
    ( k5_xboole_0(X0,sP3_iProver_split(X0)) = sP0_iProver_split(sP3_iProver_split(sP1_iProver_split)) ),
    inference(light_normalisation,[status(thm)],[c_52996,c_5])).

cnf(c_53383,plain,
    ( k5_xboole_0(X0,sP3_iProver_split(X0)) = sP3_iProver_split(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_53381,c_52997])).

cnf(c_52675,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)),sP0_iProver_split(X0)) = k5_xboole_0(X1,sP3_iProver_split(X1)) ),
    inference(superposition,[status(thm)],[c_52559,c_3228])).

cnf(c_52770,plain,
    ( k5_xboole_0(sP0_iProver_split(sP3_iProver_split(X0)),sP0_iProver_split(X0)) = k5_xboole_0(X1,sP3_iProver_split(X1)) ),
    inference(demodulation,[status(thm)],[c_52675,c_52755,c_52759])).

cnf(c_52771,plain,
    ( k5_xboole_0(X0,sP3_iProver_split(X0)) = sP4_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP4_iProver_split])],[c_52770])).

cnf(c_53384,plain,
    ( sP3_iProver_split(k1_xboole_0) = sP4_iProver_split ),
    inference(demodulation,[status(thm)],[c_53383,c_52771])).

cnf(c_53403,plain,
    ( k3_subset_1(sP1_iProver_split,sP1_iProver_split) = sP0_iProver_split(sP4_iProver_split) ),
    inference(demodulation,[status(thm)],[c_53384,c_53010])).

cnf(c_53404,plain,
    ( sP3_iProver_split(sP1_iProver_split) = sP0_iProver_split(sP4_iProver_split) ),
    inference(demodulation,[status(thm)],[c_53403,c_52755])).

cnf(c_53412,plain,
    ( k5_xboole_0(X0,sP0_iProver_split(sP4_iProver_split)) = sP0_iProver_split(sP3_iProver_split(X0)) ),
    inference(demodulation,[status(thm)],[c_53404,c_52759])).

cnf(c_53797,plain,
    ( k5_xboole_0(sP2_iProver_split(X0,X1),sP0_iProver_split(sP3_iProver_split(k5_xboole_0(X1,X0)))) = sP0_iProver_split(sP0_iProver_split(k3_xboole_0(sP1_iProver_split,sP1_iProver_split))) ),
    inference(demodulation,[status(thm)],[c_52268,c_53380,c_53403,c_53412])).

cnf(c_52273,plain,
    ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split(k3_subset_1(sP1_iProver_split,sP1_iProver_split)))) = k5_xboole_0(sP0_iProver_split(k5_xboole_0(X1,X0)),k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) ),
    inference(superposition,[status(thm)],[c_48661,c_36753])).

cnf(c_53385,plain,
    ( sP0_iProver_split(sP3_iProver_split(sP1_iProver_split)) = sP4_iProver_split ),
    inference(demodulation,[status(thm)],[c_53384,c_53381])).

cnf(c_53439,plain,
    ( sP0_iProver_split(sP0_iProver_split(sP4_iProver_split)) = sP4_iProver_split ),
    inference(demodulation,[status(thm)],[c_53385,c_53404])).

cnf(c_52418,plain,
    ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)),sP2_iProver_split(X1,X0))) = k5_xboole_0(sP0_iProver_split(X2),k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1))) ),
    inference(superposition,[status(thm)],[c_52362,c_43653])).

cnf(c_53522,plain,
    ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1))) = sP2_iProver_split(sP0_iProver_split(sP3_iProver_split(X2)),sP2_iProver_split(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_52418,c_53380,c_53403,c_53412])).

cnf(c_52420,plain,
    ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)),sP2_iProver_split(X1,X0))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1)),sP0_iProver_split(X2)) ),
    inference(superposition,[status(thm)],[c_52362,c_36749])).

cnf(c_53517,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1)),sP0_iProver_split(X0)) = sP2_iProver_split(sP0_iProver_split(sP3_iProver_split(X2)),sP2_iProver_split(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_52420,c_53380,c_53403,c_53412])).

cnf(c_32980,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1)),k5_xboole_0(X0,sP1_iProver_split)) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),X1) ),
    inference(superposition,[status(thm)],[c_32937,c_9541])).

cnf(c_19773,plain,
    ( k5_xboole_0(X0,sP0_iProver_split(k1_xboole_0)) = sP0_iProver_split(X0) ),
    inference(superposition,[status(thm)],[c_1385,c_19755])).

cnf(c_19995,plain,
    ( k5_xboole_0(X0,sP1_iProver_split) = sP0_iProver_split(X0) ),
    inference(demodulation,[status(thm)],[c_19994,c_19773])).

cnf(c_33032,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1)),sP0_iProver_split(X0)) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),X1) ),
    inference(light_normalisation,[status(thm)],[c_32980,c_19995])).

cnf(c_53518,plain,
    ( sP2_iProver_split(sP0_iProver_split(sP3_iProver_split(X0)),sP2_iProver_split(X1,X0)) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),X1) ),
    inference(light_normalisation,[status(thm)],[c_53517,c_33032])).

cnf(c_53523,plain,
    ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1))) = k5_xboole_0(sP0_iProver_split(sP4_iProver_split),X1) ),
    inference(demodulation,[status(thm)],[c_53522,c_53403,c_53518])).

cnf(c_7037,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)),k5_xboole_0(k3_subset_1(sK1,sK2),X1)) = k5_xboole_0(X0,sK1) ),
    inference(superposition,[status(thm)],[c_5368,c_3471])).

cnf(c_46827,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1)),k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),X1)) = sP0_iProver_split(X0) ),
    inference(light_normalisation,[status(thm)],[c_7037,c_7037,c_19649,c_21980,c_32628])).

cnf(c_46967,plain,
    ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1))) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),X1) ),
    inference(superposition,[status(thm)],[c_46827,c_12858])).

cnf(c_53524,plain,
    ( sP2_iProver_split(X0,sP4_iProver_split) = sP0_iProver_split(sP3_iProver_split(X0)) ),
    inference(demodulation,[status(thm)],[c_53523,c_19896,c_19924,c_46967,c_52348,c_52516])).

cnf(c_53741,plain,
    ( k5_xboole_0(sP2_iProver_split(X0,X1),k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) = sP0_iProver_split(sP3_iProver_split(k5_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_52273,c_53380,c_53403,c_53439,c_53524])).

cnf(c_53402,plain,
    ( k5_xboole_0(sP4_iProver_split,X0) = sP3_iProver_split(X0) ),
    inference(demodulation,[status(thm)],[c_53384,c_53041])).

cnf(c_3473,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,X1)) = k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sK1,sK2),X0)) ),
    inference(superposition,[status(thm)],[c_1894,c_1168])).

cnf(c_4298,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(X1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_3468,c_1169])).

cnf(c_5029,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_4298,c_1])).

cnf(c_35341,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sP1_iProver_split)),k5_xboole_0(sP1_iProver_split,X1)) = k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),X0)) ),
    inference(light_normalisation,[status(thm)],[c_3473,c_5029,c_21980,c_32628])).

cnf(c_35342,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sP1_iProver_split)))) = k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),X0)) ),
    inference(demodulation,[status(thm)],[c_35341,c_19824,c_22110])).

cnf(c_52749,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),X1)) = sP0_iProver_split(k5_xboole_0(X1,sP3_iProver_split(X0))) ),
    inference(demodulation,[status(thm)],[c_52743,c_35342])).

cnf(c_52763,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sP3_iProver_split(sP1_iProver_split),X1)) = sP0_iProver_split(k5_xboole_0(X1,sP3_iProver_split(X0))) ),
    inference(demodulation,[status(thm)],[c_52749,c_52755])).

cnf(c_52764,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sP3_iProver_split(sP1_iProver_split),X1)) = sP2_iProver_split(sP3_iProver_split(X0),X1) ),
    inference(demodulation,[status(thm)],[c_52763,c_52348])).

cnf(c_52883,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sP3_iProver_split(sP1_iProver_split),X1)) = sP2_iProver_split(X0,sP3_iProver_split(X1)) ),
    inference(demodulation,[status(thm)],[c_52882,c_52764])).

cnf(c_53409,plain,
    ( k5_xboole_0(X0,k5_xboole_0(sP0_iProver_split(sP4_iProver_split),X1)) = sP2_iProver_split(X0,sP3_iProver_split(X1)) ),
    inference(demodulation,[status(thm)],[c_53404,c_52883])).

cnf(c_53416,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(sP4_iProver_split,X1))) = sP2_iProver_split(X0,sP3_iProver_split(X1)) ),
    inference(demodulation,[status(thm)],[c_53409,c_19792,c_19924])).

cnf(c_53420,plain,
    ( sP0_iProver_split(k5_xboole_0(X0,sP3_iProver_split(X1))) = sP2_iProver_split(X0,sP3_iProver_split(X1)) ),
    inference(demodulation,[status(thm)],[c_53402,c_53416])).

cnf(c_53421,plain,
    ( sP0_iProver_split(sP3_iProver_split(k5_xboole_0(X0,X1))) = sP2_iProver_split(X0,sP3_iProver_split(X1)) ),
    inference(demodulation,[status(thm)],[c_53420,c_53198,c_53380])).

cnf(c_53742,plain,
    ( k5_xboole_0(sP2_iProver_split(X0,X1),k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) = sP2_iProver_split(X1,sP3_iProver_split(X0)) ),
    inference(demodulation,[status(thm)],[c_53741,c_53421])).

cnf(c_53743,plain,
    ( sP3_iProver_split(sP2_iProver_split(X0,X1)) = sP2_iProver_split(X1,sP3_iProver_split(X0)) ),
    inference(demodulation,[status(thm)],[c_53742,c_52743])).

cnf(c_53745,plain,
    ( sP0_iProver_split(sP3_iProver_split(k5_xboole_0(X0,X1))) = sP3_iProver_split(sP2_iProver_split(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_53743,c_53421])).

cnf(c_53798,plain,
    ( sP0_iProver_split(sP0_iProver_split(k3_xboole_0(sP1_iProver_split,sP1_iProver_split))) = sP4_iProver_split ),
    inference(demodulation,[status(thm)],[c_53797,c_52771,c_53745])).

cnf(c_53799,plain,
    ( k3_xboole_0(sP1_iProver_split,sP1_iProver_split) = sP4_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_53798,c_32812,c_33423])).

cnf(c_1147,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_771])).

cnf(c_1258,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1147])).

cnf(c_3115,plain,
    ( k3_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_1258,c_1155])).

cnf(c_66861,plain,
    ( sP4_iProver_split = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_3115,c_3115,c_21980,c_32628,c_53799])).

cnf(c_81493,plain,
    ( k3_xboole_0(sP1_iProver_split,sP1_iProver_split) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_53799,c_53799,c_66861])).

cnf(c_81494,plain,
    ( k3_subset_1(sP1_iProver_split,sP1_iProver_split) = sP0_iProver_split(sP1_iProver_split) ),
    inference(demodulation,[status(thm)],[c_81493,c_33423])).

cnf(c_81495,plain,
    ( k3_subset_1(sP1_iProver_split,sP1_iProver_split) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_81494,c_23783,c_53403])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK2),sK2)
    | k2_subset_1(sK1) != sK2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1153,plain,
    ( k2_subset_1(sK1) != sK2
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1157,plain,
    ( sK2 != sK1
    | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1153,c_17])).

cnf(c_32745,plain,
    ( sP1_iProver_split != sK1
    | r1_tarski(k3_subset_1(sK1,sP1_iProver_split),sP1_iProver_split) != iProver_top ),
    inference(demodulation,[status(thm)],[c_32628,c_1157])).

cnf(c_32750,plain,
    ( sP1_iProver_split != sP1_iProver_split
    | r1_tarski(k3_subset_1(sP1_iProver_split,sP1_iProver_split),sP1_iProver_split) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_32745,c_21980])).

cnf(c_32751,plain,
    ( r1_tarski(k3_subset_1(sP1_iProver_split,sP1_iProver_split),sP1_iProver_split) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_32750])).

cnf(c_82043,plain,
    ( r1_tarski(k1_xboole_0,sP1_iProver_split) != iProver_top ),
    inference(demodulation,[status(thm)],[c_81495,c_32751])).

cnf(c_82059,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1154,c_82043])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:46:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.38/3.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.38/3.00  
% 19.38/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.38/3.00  
% 19.38/3.00  ------  iProver source info
% 19.38/3.00  
% 19.38/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.38/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.38/3.00  git: non_committed_changes: false
% 19.38/3.00  git: last_make_outside_of_git: false
% 19.38/3.00  
% 19.38/3.00  ------ 
% 19.38/3.00  
% 19.38/3.00  ------ Input Options
% 19.38/3.00  
% 19.38/3.00  --out_options                           all
% 19.38/3.00  --tptp_safe_out                         true
% 19.38/3.00  --problem_path                          ""
% 19.38/3.00  --include_path                          ""
% 19.38/3.00  --clausifier                            res/vclausify_rel
% 19.38/3.00  --clausifier_options                    ""
% 19.38/3.00  --stdin                                 false
% 19.38/3.00  --stats_out                             all
% 19.38/3.00  
% 19.38/3.00  ------ General Options
% 19.38/3.00  
% 19.38/3.00  --fof                                   false
% 19.38/3.00  --time_out_real                         305.
% 19.38/3.00  --time_out_virtual                      -1.
% 19.38/3.00  --symbol_type_check                     false
% 19.38/3.00  --clausify_out                          false
% 19.38/3.00  --sig_cnt_out                           false
% 19.38/3.00  --trig_cnt_out                          false
% 19.38/3.00  --trig_cnt_out_tolerance                1.
% 19.38/3.00  --trig_cnt_out_sk_spl                   false
% 19.38/3.00  --abstr_cl_out                          false
% 19.38/3.00  
% 19.38/3.00  ------ Global Options
% 19.38/3.00  
% 19.38/3.00  --schedule                              default
% 19.38/3.00  --add_important_lit                     false
% 19.38/3.00  --prop_solver_per_cl                    1000
% 19.38/3.00  --min_unsat_core                        false
% 19.38/3.00  --soft_assumptions                      false
% 19.38/3.00  --soft_lemma_size                       3
% 19.38/3.00  --prop_impl_unit_size                   0
% 19.38/3.00  --prop_impl_unit                        []
% 19.38/3.00  --share_sel_clauses                     true
% 19.38/3.00  --reset_solvers                         false
% 19.38/3.00  --bc_imp_inh                            [conj_cone]
% 19.38/3.00  --conj_cone_tolerance                   3.
% 19.38/3.00  --extra_neg_conj                        none
% 19.38/3.00  --large_theory_mode                     true
% 19.38/3.00  --prolific_symb_bound                   200
% 19.38/3.00  --lt_threshold                          2000
% 19.38/3.00  --clause_weak_htbl                      true
% 19.38/3.00  --gc_record_bc_elim                     false
% 19.38/3.00  
% 19.38/3.00  ------ Preprocessing Options
% 19.38/3.00  
% 19.38/3.00  --preprocessing_flag                    true
% 19.38/3.00  --time_out_prep_mult                    0.1
% 19.38/3.00  --splitting_mode                        input
% 19.38/3.00  --splitting_grd                         true
% 19.38/3.00  --splitting_cvd                         false
% 19.38/3.00  --splitting_cvd_svl                     false
% 19.38/3.00  --splitting_nvd                         32
% 19.38/3.00  --sub_typing                            true
% 19.38/3.00  --prep_gs_sim                           true
% 19.38/3.00  --prep_unflatten                        true
% 19.38/3.00  --prep_res_sim                          true
% 19.38/3.00  --prep_upred                            true
% 19.38/3.00  --prep_sem_filter                       exhaustive
% 19.38/3.00  --prep_sem_filter_out                   false
% 19.38/3.00  --pred_elim                             true
% 19.38/3.00  --res_sim_input                         true
% 19.38/3.00  --eq_ax_congr_red                       true
% 19.38/3.00  --pure_diseq_elim                       true
% 19.38/3.00  --brand_transform                       false
% 19.38/3.00  --non_eq_to_eq                          false
% 19.38/3.00  --prep_def_merge                        true
% 19.38/3.00  --prep_def_merge_prop_impl              false
% 19.38/3.00  --prep_def_merge_mbd                    true
% 19.38/3.00  --prep_def_merge_tr_red                 false
% 19.38/3.00  --prep_def_merge_tr_cl                  false
% 19.38/3.00  --smt_preprocessing                     true
% 19.38/3.00  --smt_ac_axioms                         fast
% 19.38/3.00  --preprocessed_out                      false
% 19.38/3.00  --preprocessed_stats                    false
% 19.38/3.00  
% 19.38/3.00  ------ Abstraction refinement Options
% 19.38/3.00  
% 19.38/3.00  --abstr_ref                             []
% 19.38/3.00  --abstr_ref_prep                        false
% 19.38/3.00  --abstr_ref_until_sat                   false
% 19.38/3.00  --abstr_ref_sig_restrict                funpre
% 19.38/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.38/3.00  --abstr_ref_under                       []
% 19.38/3.00  
% 19.38/3.00  ------ SAT Options
% 19.38/3.00  
% 19.38/3.00  --sat_mode                              false
% 19.38/3.00  --sat_fm_restart_options                ""
% 19.38/3.00  --sat_gr_def                            false
% 19.38/3.00  --sat_epr_types                         true
% 19.38/3.00  --sat_non_cyclic_types                  false
% 19.38/3.00  --sat_finite_models                     false
% 19.38/3.00  --sat_fm_lemmas                         false
% 19.38/3.00  --sat_fm_prep                           false
% 19.38/3.00  --sat_fm_uc_incr                        true
% 19.38/3.00  --sat_out_model                         small
% 19.38/3.00  --sat_out_clauses                       false
% 19.38/3.00  
% 19.38/3.00  ------ QBF Options
% 19.38/3.00  
% 19.38/3.00  --qbf_mode                              false
% 19.38/3.00  --qbf_elim_univ                         false
% 19.38/3.00  --qbf_dom_inst                          none
% 19.38/3.00  --qbf_dom_pre_inst                      false
% 19.38/3.00  --qbf_sk_in                             false
% 19.38/3.00  --qbf_pred_elim                         true
% 19.38/3.00  --qbf_split                             512
% 19.38/3.00  
% 19.38/3.00  ------ BMC1 Options
% 19.38/3.00  
% 19.38/3.00  --bmc1_incremental                      false
% 19.38/3.00  --bmc1_axioms                           reachable_all
% 19.38/3.00  --bmc1_min_bound                        0
% 19.38/3.00  --bmc1_max_bound                        -1
% 19.38/3.00  --bmc1_max_bound_default                -1
% 19.38/3.00  --bmc1_symbol_reachability              true
% 19.38/3.00  --bmc1_property_lemmas                  false
% 19.38/3.00  --bmc1_k_induction                      false
% 19.38/3.00  --bmc1_non_equiv_states                 false
% 19.38/3.00  --bmc1_deadlock                         false
% 19.38/3.00  --bmc1_ucm                              false
% 19.38/3.00  --bmc1_add_unsat_core                   none
% 19.38/3.00  --bmc1_unsat_core_children              false
% 19.38/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.38/3.00  --bmc1_out_stat                         full
% 19.38/3.00  --bmc1_ground_init                      false
% 19.38/3.00  --bmc1_pre_inst_next_state              false
% 19.38/3.00  --bmc1_pre_inst_state                   false
% 19.38/3.00  --bmc1_pre_inst_reach_state             false
% 19.38/3.00  --bmc1_out_unsat_core                   false
% 19.38/3.00  --bmc1_aig_witness_out                  false
% 19.38/3.00  --bmc1_verbose                          false
% 19.38/3.00  --bmc1_dump_clauses_tptp                false
% 19.38/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.38/3.00  --bmc1_dump_file                        -
% 19.38/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.38/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.38/3.00  --bmc1_ucm_extend_mode                  1
% 19.38/3.00  --bmc1_ucm_init_mode                    2
% 19.38/3.00  --bmc1_ucm_cone_mode                    none
% 19.38/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.38/3.00  --bmc1_ucm_relax_model                  4
% 19.38/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.38/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.38/3.00  --bmc1_ucm_layered_model                none
% 19.38/3.00  --bmc1_ucm_max_lemma_size               10
% 19.38/3.00  
% 19.38/3.00  ------ AIG Options
% 19.38/3.00  
% 19.38/3.00  --aig_mode                              false
% 19.38/3.00  
% 19.38/3.00  ------ Instantiation Options
% 19.38/3.00  
% 19.38/3.00  --instantiation_flag                    true
% 19.38/3.00  --inst_sos_flag                         true
% 19.38/3.00  --inst_sos_phase                        true
% 19.38/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.38/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.38/3.00  --inst_lit_sel_side                     num_symb
% 19.38/3.00  --inst_solver_per_active                1400
% 19.38/3.00  --inst_solver_calls_frac                1.
% 19.38/3.00  --inst_passive_queue_type               priority_queues
% 19.38/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.38/3.00  --inst_passive_queues_freq              [25;2]
% 19.38/3.00  --inst_dismatching                      true
% 19.38/3.00  --inst_eager_unprocessed_to_passive     true
% 19.38/3.00  --inst_prop_sim_given                   true
% 19.38/3.00  --inst_prop_sim_new                     false
% 19.38/3.00  --inst_subs_new                         false
% 19.38/3.00  --inst_eq_res_simp                      false
% 19.38/3.00  --inst_subs_given                       false
% 19.38/3.00  --inst_orphan_elimination               true
% 19.38/3.00  --inst_learning_loop_flag               true
% 19.38/3.00  --inst_learning_start                   3000
% 19.38/3.00  --inst_learning_factor                  2
% 19.38/3.00  --inst_start_prop_sim_after_learn       3
% 19.38/3.00  --inst_sel_renew                        solver
% 19.38/3.00  --inst_lit_activity_flag                true
% 19.38/3.00  --inst_restr_to_given                   false
% 19.38/3.00  --inst_activity_threshold               500
% 19.38/3.00  --inst_out_proof                        true
% 19.38/3.00  
% 19.38/3.00  ------ Resolution Options
% 19.38/3.00  
% 19.38/3.00  --resolution_flag                       true
% 19.38/3.00  --res_lit_sel                           adaptive
% 19.38/3.00  --res_lit_sel_side                      none
% 19.38/3.00  --res_ordering                          kbo
% 19.38/3.00  --res_to_prop_solver                    active
% 19.38/3.00  --res_prop_simpl_new                    false
% 19.38/3.00  --res_prop_simpl_given                  true
% 19.38/3.00  --res_passive_queue_type                priority_queues
% 19.38/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.38/3.00  --res_passive_queues_freq               [15;5]
% 19.38/3.00  --res_forward_subs                      full
% 19.38/3.00  --res_backward_subs                     full
% 19.38/3.00  --res_forward_subs_resolution           true
% 19.38/3.00  --res_backward_subs_resolution          true
% 19.38/3.00  --res_orphan_elimination                true
% 19.38/3.00  --res_time_limit                        2.
% 19.38/3.00  --res_out_proof                         true
% 19.38/3.00  
% 19.38/3.00  ------ Superposition Options
% 19.38/3.00  
% 19.38/3.00  --superposition_flag                    true
% 19.38/3.00  --sup_passive_queue_type                priority_queues
% 19.38/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.38/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.38/3.00  --demod_completeness_check              fast
% 19.38/3.00  --demod_use_ground                      true
% 19.38/3.00  --sup_to_prop_solver                    passive
% 19.38/3.00  --sup_prop_simpl_new                    true
% 19.38/3.00  --sup_prop_simpl_given                  true
% 19.38/3.00  --sup_fun_splitting                     true
% 19.38/3.00  --sup_smt_interval                      50000
% 19.38/3.00  
% 19.38/3.00  ------ Superposition Simplification Setup
% 19.38/3.00  
% 19.38/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.38/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.38/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.38/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.38/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.38/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.38/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.38/3.00  --sup_immed_triv                        [TrivRules]
% 19.38/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.38/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.38/3.00  --sup_immed_bw_main                     []
% 19.38/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.38/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.38/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.38/3.00  --sup_input_bw                          []
% 19.38/3.00  
% 19.38/3.00  ------ Combination Options
% 19.38/3.00  
% 19.38/3.00  --comb_res_mult                         3
% 19.38/3.00  --comb_sup_mult                         2
% 19.38/3.00  --comb_inst_mult                        10
% 19.38/3.00  
% 19.38/3.00  ------ Debug Options
% 19.38/3.00  
% 19.38/3.00  --dbg_backtrace                         false
% 19.38/3.00  --dbg_dump_prop_clauses                 false
% 19.38/3.00  --dbg_dump_prop_clauses_file            -
% 19.38/3.00  --dbg_out_stat                          false
% 19.38/3.00  ------ Parsing...
% 19.38/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.38/3.00  
% 19.38/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 19.38/3.00  
% 19.38/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.38/3.00  
% 19.38/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.38/3.00  ------ Proving...
% 19.38/3.00  ------ Problem Properties 
% 19.38/3.00  
% 19.38/3.00  
% 19.38/3.00  clauses                                 17
% 19.38/3.00  conjectures                             2
% 19.38/3.00  EPR                                     1
% 19.38/3.00  Horn                                    15
% 19.38/3.00  unary                                   8
% 19.38/3.00  binary                                  6
% 19.38/3.00  lits                                    29
% 19.38/3.00  lits eq                                 18
% 19.38/3.00  fd_pure                                 0
% 19.38/3.00  fd_pseudo                               0
% 19.38/3.00  fd_cond                                 0
% 19.38/3.00  fd_pseudo_cond                          0
% 19.38/3.00  AC symbols                              1
% 19.38/3.00  
% 19.38/3.00  ------ Schedule dynamic 5 is on 
% 19.38/3.00  
% 19.38/3.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.38/3.00  
% 19.38/3.00  
% 19.38/3.00  ------ 
% 19.38/3.00  Current options:
% 19.38/3.00  ------ 
% 19.38/3.00  
% 19.38/3.00  ------ Input Options
% 19.38/3.00  
% 19.38/3.00  --out_options                           all
% 19.38/3.00  --tptp_safe_out                         true
% 19.38/3.00  --problem_path                          ""
% 19.38/3.00  --include_path                          ""
% 19.38/3.00  --clausifier                            res/vclausify_rel
% 19.38/3.00  --clausifier_options                    ""
% 19.38/3.00  --stdin                                 false
% 19.38/3.00  --stats_out                             all
% 19.38/3.00  
% 19.38/3.00  ------ General Options
% 19.38/3.00  
% 19.38/3.00  --fof                                   false
% 19.38/3.00  --time_out_real                         305.
% 19.38/3.00  --time_out_virtual                      -1.
% 19.38/3.00  --symbol_type_check                     false
% 19.38/3.00  --clausify_out                          false
% 19.38/3.00  --sig_cnt_out                           false
% 19.38/3.00  --trig_cnt_out                          false
% 19.38/3.00  --trig_cnt_out_tolerance                1.
% 19.38/3.00  --trig_cnt_out_sk_spl                   false
% 19.38/3.00  --abstr_cl_out                          false
% 19.38/3.00  
% 19.38/3.00  ------ Global Options
% 19.38/3.00  
% 19.38/3.00  --schedule                              default
% 19.38/3.00  --add_important_lit                     false
% 19.38/3.00  --prop_solver_per_cl                    1000
% 19.38/3.00  --min_unsat_core                        false
% 19.38/3.00  --soft_assumptions                      false
% 19.38/3.00  --soft_lemma_size                       3
% 19.38/3.00  --prop_impl_unit_size                   0
% 19.38/3.00  --prop_impl_unit                        []
% 19.38/3.00  --share_sel_clauses                     true
% 19.38/3.00  --reset_solvers                         false
% 19.38/3.00  --bc_imp_inh                            [conj_cone]
% 19.38/3.00  --conj_cone_tolerance                   3.
% 19.38/3.00  --extra_neg_conj                        none
% 19.38/3.00  --large_theory_mode                     true
% 19.38/3.00  --prolific_symb_bound                   200
% 19.38/3.00  --lt_threshold                          2000
% 19.38/3.00  --clause_weak_htbl                      true
% 19.38/3.00  --gc_record_bc_elim                     false
% 19.38/3.00  
% 19.38/3.00  ------ Preprocessing Options
% 19.38/3.00  
% 19.38/3.00  --preprocessing_flag                    true
% 19.38/3.00  --time_out_prep_mult                    0.1
% 19.38/3.00  --splitting_mode                        input
% 19.38/3.00  --splitting_grd                         true
% 19.38/3.00  --splitting_cvd                         false
% 19.38/3.00  --splitting_cvd_svl                     false
% 19.38/3.00  --splitting_nvd                         32
% 19.38/3.00  --sub_typing                            true
% 19.38/3.00  --prep_gs_sim                           true
% 19.38/3.00  --prep_unflatten                        true
% 19.38/3.00  --prep_res_sim                          true
% 19.38/3.00  --prep_upred                            true
% 19.38/3.00  --prep_sem_filter                       exhaustive
% 19.38/3.00  --prep_sem_filter_out                   false
% 19.38/3.00  --pred_elim                             true
% 19.38/3.00  --res_sim_input                         true
% 19.38/3.00  --eq_ax_congr_red                       true
% 19.38/3.00  --pure_diseq_elim                       true
% 19.38/3.00  --brand_transform                       false
% 19.38/3.00  --non_eq_to_eq                          false
% 19.38/3.00  --prep_def_merge                        true
% 19.38/3.00  --prep_def_merge_prop_impl              false
% 19.38/3.00  --prep_def_merge_mbd                    true
% 19.38/3.00  --prep_def_merge_tr_red                 false
% 19.38/3.00  --prep_def_merge_tr_cl                  false
% 19.38/3.00  --smt_preprocessing                     true
% 19.38/3.00  --smt_ac_axioms                         fast
% 19.38/3.00  --preprocessed_out                      false
% 19.38/3.00  --preprocessed_stats                    false
% 19.38/3.00  
% 19.38/3.00  ------ Abstraction refinement Options
% 19.38/3.00  
% 19.38/3.00  --abstr_ref                             []
% 19.38/3.00  --abstr_ref_prep                        false
% 19.38/3.00  --abstr_ref_until_sat                   false
% 19.38/3.00  --abstr_ref_sig_restrict                funpre
% 19.38/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.38/3.00  --abstr_ref_under                       []
% 19.38/3.00  
% 19.38/3.00  ------ SAT Options
% 19.38/3.00  
% 19.38/3.00  --sat_mode                              false
% 19.38/3.00  --sat_fm_restart_options                ""
% 19.38/3.00  --sat_gr_def                            false
% 19.38/3.00  --sat_epr_types                         true
% 19.38/3.00  --sat_non_cyclic_types                  false
% 19.38/3.00  --sat_finite_models                     false
% 19.38/3.00  --sat_fm_lemmas                         false
% 19.38/3.00  --sat_fm_prep                           false
% 19.38/3.00  --sat_fm_uc_incr                        true
% 19.38/3.00  --sat_out_model                         small
% 19.38/3.00  --sat_out_clauses                       false
% 19.38/3.00  
% 19.38/3.00  ------ QBF Options
% 19.38/3.00  
% 19.38/3.00  --qbf_mode                              false
% 19.38/3.00  --qbf_elim_univ                         false
% 19.38/3.00  --qbf_dom_inst                          none
% 19.38/3.00  --qbf_dom_pre_inst                      false
% 19.38/3.00  --qbf_sk_in                             false
% 19.38/3.00  --qbf_pred_elim                         true
% 19.38/3.00  --qbf_split                             512
% 19.38/3.00  
% 19.38/3.00  ------ BMC1 Options
% 19.38/3.00  
% 19.38/3.00  --bmc1_incremental                      false
% 19.38/3.00  --bmc1_axioms                           reachable_all
% 19.38/3.00  --bmc1_min_bound                        0
% 19.38/3.00  --bmc1_max_bound                        -1
% 19.38/3.00  --bmc1_max_bound_default                -1
% 19.38/3.00  --bmc1_symbol_reachability              true
% 19.38/3.00  --bmc1_property_lemmas                  false
% 19.38/3.00  --bmc1_k_induction                      false
% 19.38/3.00  --bmc1_non_equiv_states                 false
% 19.38/3.00  --bmc1_deadlock                         false
% 19.38/3.00  --bmc1_ucm                              false
% 19.38/3.00  --bmc1_add_unsat_core                   none
% 19.38/3.00  --bmc1_unsat_core_children              false
% 19.38/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.38/3.00  --bmc1_out_stat                         full
% 19.38/3.00  --bmc1_ground_init                      false
% 19.38/3.00  --bmc1_pre_inst_next_state              false
% 19.38/3.00  --bmc1_pre_inst_state                   false
% 19.38/3.00  --bmc1_pre_inst_reach_state             false
% 19.38/3.00  --bmc1_out_unsat_core                   false
% 19.38/3.00  --bmc1_aig_witness_out                  false
% 19.38/3.00  --bmc1_verbose                          false
% 19.38/3.00  --bmc1_dump_clauses_tptp                false
% 19.38/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.38/3.00  --bmc1_dump_file                        -
% 19.38/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.38/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.38/3.00  --bmc1_ucm_extend_mode                  1
% 19.38/3.00  --bmc1_ucm_init_mode                    2
% 19.38/3.00  --bmc1_ucm_cone_mode                    none
% 19.38/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.38/3.00  --bmc1_ucm_relax_model                  4
% 19.38/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.38/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.38/3.00  --bmc1_ucm_layered_model                none
% 19.38/3.00  --bmc1_ucm_max_lemma_size               10
% 19.38/3.00  
% 19.38/3.00  ------ AIG Options
% 19.38/3.00  
% 19.38/3.00  --aig_mode                              false
% 19.38/3.00  
% 19.38/3.00  ------ Instantiation Options
% 19.38/3.00  
% 19.38/3.00  --instantiation_flag                    true
% 19.38/3.00  --inst_sos_flag                         true
% 19.38/3.00  --inst_sos_phase                        true
% 19.38/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.38/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.38/3.00  --inst_lit_sel_side                     none
% 19.38/3.00  --inst_solver_per_active                1400
% 19.38/3.00  --inst_solver_calls_frac                1.
% 19.38/3.00  --inst_passive_queue_type               priority_queues
% 19.38/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.38/3.00  --inst_passive_queues_freq              [25;2]
% 19.38/3.00  --inst_dismatching                      true
% 19.38/3.00  --inst_eager_unprocessed_to_passive     true
% 19.38/3.00  --inst_prop_sim_given                   true
% 19.38/3.00  --inst_prop_sim_new                     false
% 19.38/3.00  --inst_subs_new                         false
% 19.38/3.00  --inst_eq_res_simp                      false
% 19.38/3.00  --inst_subs_given                       false
% 19.38/3.00  --inst_orphan_elimination               true
% 19.38/3.00  --inst_learning_loop_flag               true
% 19.38/3.00  --inst_learning_start                   3000
% 19.38/3.00  --inst_learning_factor                  2
% 19.38/3.00  --inst_start_prop_sim_after_learn       3
% 19.38/3.00  --inst_sel_renew                        solver
% 19.38/3.00  --inst_lit_activity_flag                true
% 19.38/3.00  --inst_restr_to_given                   false
% 19.38/3.00  --inst_activity_threshold               500
% 19.38/3.00  --inst_out_proof                        true
% 19.38/3.00  
% 19.38/3.00  ------ Resolution Options
% 19.38/3.00  
% 19.38/3.00  --resolution_flag                       false
% 19.38/3.00  --res_lit_sel                           adaptive
% 19.38/3.00  --res_lit_sel_side                      none
% 19.38/3.00  --res_ordering                          kbo
% 19.38/3.00  --res_to_prop_solver                    active
% 19.38/3.00  --res_prop_simpl_new                    false
% 19.38/3.00  --res_prop_simpl_given                  true
% 19.38/3.00  --res_passive_queue_type                priority_queues
% 19.38/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.38/3.00  --res_passive_queues_freq               [15;5]
% 19.38/3.00  --res_forward_subs                      full
% 19.38/3.00  --res_backward_subs                     full
% 19.38/3.00  --res_forward_subs_resolution           true
% 19.38/3.00  --res_backward_subs_resolution          true
% 19.38/3.00  --res_orphan_elimination                true
% 19.38/3.00  --res_time_limit                        2.
% 19.38/3.00  --res_out_proof                         true
% 19.38/3.00  
% 19.38/3.00  ------ Superposition Options
% 19.38/3.00  
% 19.38/3.00  --superposition_flag                    true
% 19.38/3.00  --sup_passive_queue_type                priority_queues
% 19.38/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.38/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.38/3.00  --demod_completeness_check              fast
% 19.38/3.00  --demod_use_ground                      true
% 19.38/3.00  --sup_to_prop_solver                    passive
% 19.38/3.00  --sup_prop_simpl_new                    true
% 19.38/3.00  --sup_prop_simpl_given                  true
% 19.38/3.00  --sup_fun_splitting                     true
% 19.38/3.00  --sup_smt_interval                      50000
% 19.38/3.00  
% 19.38/3.00  ------ Superposition Simplification Setup
% 19.38/3.00  
% 19.38/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.38/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.38/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.38/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.38/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.38/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.38/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.38/3.00  --sup_immed_triv                        [TrivRules]
% 19.38/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.38/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.38/3.00  --sup_immed_bw_main                     []
% 19.38/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.38/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.38/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.38/3.00  --sup_input_bw                          []
% 19.38/3.00  
% 19.38/3.00  ------ Combination Options
% 19.38/3.00  
% 19.38/3.00  --comb_res_mult                         3
% 19.38/3.00  --comb_sup_mult                         2
% 19.38/3.00  --comb_inst_mult                        10
% 19.38/3.00  
% 19.38/3.00  ------ Debug Options
% 19.38/3.00  
% 19.38/3.00  --dbg_backtrace                         false
% 19.38/3.00  --dbg_dump_prop_clauses                 false
% 19.38/3.00  --dbg_dump_prop_clauses_file            -
% 19.38/3.00  --dbg_out_stat                          false
% 19.38/3.00  
% 19.38/3.00  
% 19.38/3.00  
% 19.38/3.00  
% 19.38/3.00  ------ Proving...
% 19.38/3.00  
% 19.38/3.00  
% 19.38/3.00  % SZS status Theorem for theBenchmark.p
% 19.38/3.00  
% 19.38/3.00   Resolution empty clause
% 19.38/3.00  
% 19.38/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.38/3.00  
% 19.38/3.00  fof(f6,axiom,(
% 19.38/3.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 19.38/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.38/3.00  
% 19.38/3.00  fof(f38,plain,(
% 19.38/3.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 19.38/3.00    inference(cnf_transformation,[],[f6])).
% 19.38/3.00  
% 19.38/3.00  fof(f2,axiom,(
% 19.38/3.00    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 19.38/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.38/3.00  
% 19.38/3.00  fof(f34,plain,(
% 19.38/3.00    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 19.38/3.00    inference(cnf_transformation,[],[f2])).
% 19.38/3.00  
% 19.38/3.00  fof(f7,axiom,(
% 19.38/3.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 19.38/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.38/3.00  
% 19.38/3.00  fof(f39,plain,(
% 19.38/3.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.38/3.00    inference(cnf_transformation,[],[f7])).
% 19.38/3.00  
% 19.38/3.00  fof(f9,axiom,(
% 19.38/3.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 19.38/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.38/3.00  
% 19.38/3.00  fof(f41,plain,(
% 19.38/3.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 19.38/3.00    inference(cnf_transformation,[],[f9])).
% 19.38/3.00  
% 19.38/3.00  fof(f14,axiom,(
% 19.38/3.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 19.38/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.38/3.00  
% 19.38/3.00  fof(f22,plain,(
% 19.38/3.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.38/3.00    inference(ennf_transformation,[],[f14])).
% 19.38/3.00  
% 19.38/3.00  fof(f52,plain,(
% 19.38/3.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.38/3.00    inference(cnf_transformation,[],[f22])).
% 19.38/3.00  
% 19.38/3.00  fof(f4,axiom,(
% 19.38/3.00    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 19.38/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.38/3.00  
% 19.38/3.00  fof(f36,plain,(
% 19.38/3.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 19.38/3.00    inference(cnf_transformation,[],[f4])).
% 19.38/3.00  
% 19.38/3.00  fof(f58,plain,(
% 19.38/3.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.38/3.00    inference(definition_unfolding,[],[f52,f36])).
% 19.38/3.00  
% 19.38/3.00  fof(f16,conjecture,(
% 19.38/3.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 19.38/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.38/3.00  
% 19.38/3.00  fof(f17,negated_conjecture,(
% 19.38/3.00    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 19.38/3.00    inference(negated_conjecture,[],[f16])).
% 19.38/3.00  
% 19.38/3.00  fof(f23,plain,(
% 19.38/3.00    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.38/3.00    inference(ennf_transformation,[],[f17])).
% 19.38/3.00  
% 19.38/3.00  fof(f29,plain,(
% 19.38/3.00    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.38/3.00    inference(nnf_transformation,[],[f23])).
% 19.38/3.00  
% 19.38/3.00  fof(f30,plain,(
% 19.38/3.00    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.38/3.00    inference(flattening,[],[f29])).
% 19.38/3.00  
% 19.38/3.00  fof(f31,plain,(
% 19.38/3.00    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k2_subset_1(sK1) != sK2 | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)) & (k2_subset_1(sK1) = sK2 | r1_tarski(k3_subset_1(sK1,sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 19.38/3.00    introduced(choice_axiom,[])).
% 19.38/3.00  
% 19.38/3.00  fof(f32,plain,(
% 19.38/3.00    (k2_subset_1(sK1) != sK2 | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)) & (k2_subset_1(sK1) = sK2 | r1_tarski(k3_subset_1(sK1,sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 19.38/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f31])).
% 19.38/3.00  
% 19.38/3.00  fof(f54,plain,(
% 19.38/3.00    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 19.38/3.00    inference(cnf_transformation,[],[f32])).
% 19.38/3.00  
% 19.38/3.00  fof(f10,axiom,(
% 19.38/3.00    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 19.38/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.38/3.00  
% 19.38/3.00  fof(f42,plain,(
% 19.38/3.00    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 19.38/3.00    inference(cnf_transformation,[],[f10])).
% 19.38/3.00  
% 19.38/3.00  fof(f55,plain,(
% 19.38/3.00    k2_subset_1(sK1) = sK2 | r1_tarski(k3_subset_1(sK1,sK2),sK2)),
% 19.38/3.00    inference(cnf_transformation,[],[f32])).
% 19.38/3.00  
% 19.38/3.00  fof(f13,axiom,(
% 19.38/3.00    ! [X0] : k2_subset_1(X0) = X0),
% 19.38/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.38/3.00  
% 19.38/3.00  fof(f51,plain,(
% 19.38/3.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 19.38/3.00    inference(cnf_transformation,[],[f13])).
% 19.38/3.00  
% 19.38/3.00  fof(f5,axiom,(
% 19.38/3.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 19.38/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.38/3.00  
% 19.38/3.00  fof(f20,plain,(
% 19.38/3.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 19.38/3.00    inference(ennf_transformation,[],[f5])).
% 19.38/3.00  
% 19.38/3.00  fof(f37,plain,(
% 19.38/3.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 19.38/3.00    inference(cnf_transformation,[],[f20])).
% 19.38/3.00  
% 19.38/3.00  fof(f3,axiom,(
% 19.38/3.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 19.38/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.38/3.00  
% 19.38/3.00  fof(f18,plain,(
% 19.38/3.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 19.38/3.00    inference(unused_predicate_definition_removal,[],[f3])).
% 19.38/3.00  
% 19.38/3.00  fof(f19,plain,(
% 19.38/3.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 19.38/3.00    inference(ennf_transformation,[],[f18])).
% 19.38/3.00  
% 19.38/3.00  fof(f35,plain,(
% 19.38/3.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 19.38/3.00    inference(cnf_transformation,[],[f19])).
% 19.38/3.00  
% 19.38/3.00  fof(f8,axiom,(
% 19.38/3.00    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 19.38/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.38/3.00  
% 19.38/3.00  fof(f40,plain,(
% 19.38/3.00    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 19.38/3.00    inference(cnf_transformation,[],[f8])).
% 19.38/3.00  
% 19.38/3.00  fof(f57,plain,(
% 19.38/3.00    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 19.38/3.00    inference(definition_unfolding,[],[f40,f36])).
% 19.38/3.00  
% 19.38/3.00  fof(f11,axiom,(
% 19.38/3.00    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 19.38/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.38/3.00  
% 19.38/3.00  fof(f24,plain,(
% 19.38/3.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 19.38/3.00    inference(nnf_transformation,[],[f11])).
% 19.38/3.00  
% 19.38/3.00  fof(f25,plain,(
% 19.38/3.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 19.38/3.00    inference(rectify,[],[f24])).
% 19.38/3.00  
% 19.38/3.00  fof(f26,plain,(
% 19.38/3.00    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 19.38/3.00    introduced(choice_axiom,[])).
% 19.38/3.00  
% 19.38/3.00  fof(f27,plain,(
% 19.38/3.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 19.38/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 19.38/3.00  
% 19.38/3.00  fof(f43,plain,(
% 19.38/3.00    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 19.38/3.00    inference(cnf_transformation,[],[f27])).
% 19.38/3.00  
% 19.38/3.00  fof(f60,plain,(
% 19.38/3.00    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 19.38/3.00    inference(equality_resolution,[],[f43])).
% 19.38/3.00  
% 19.38/3.00  fof(f12,axiom,(
% 19.38/3.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 19.38/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.38/3.00  
% 19.38/3.00  fof(f21,plain,(
% 19.38/3.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 19.38/3.00    inference(ennf_transformation,[],[f12])).
% 19.38/3.00  
% 19.38/3.00  fof(f28,plain,(
% 19.38/3.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 19.38/3.00    inference(nnf_transformation,[],[f21])).
% 19.38/3.00  
% 19.38/3.00  fof(f47,plain,(
% 19.38/3.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 19.38/3.00    inference(cnf_transformation,[],[f28])).
% 19.38/3.00  
% 19.38/3.00  fof(f15,axiom,(
% 19.38/3.00    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 19.38/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.38/3.00  
% 19.38/3.00  fof(f53,plain,(
% 19.38/3.00    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 19.38/3.00    inference(cnf_transformation,[],[f15])).
% 19.38/3.00  
% 19.38/3.00  fof(f1,axiom,(
% 19.38/3.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 19.38/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.38/3.00  
% 19.38/3.00  fof(f33,plain,(
% 19.38/3.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 19.38/3.00    inference(cnf_transformation,[],[f1])).
% 19.38/3.00  
% 19.38/3.00  fof(f56,plain,(
% 19.38/3.00    k2_subset_1(sK1) != sK2 | ~r1_tarski(k3_subset_1(sK1,sK2),sK2)),
% 19.38/3.00    inference(cnf_transformation,[],[f32])).
% 19.38/3.00  
% 19.38/3.00  cnf(c_4,plain,
% 19.38/3.00      ( r1_tarski(k1_xboole_0,X0) ),
% 19.38/3.00      inference(cnf_transformation,[],[f38]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1154,plain,
% 19.38/3.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 19.38/3.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1,plain,
% 19.38/3.00      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 19.38/3.00      inference(cnf_transformation,[],[f34]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.38/3.00      inference(cnf_transformation,[],[f39]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_7,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 19.38/3.00      inference(cnf_transformation,[],[f41]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1168,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3466,plain,
% 19.38/3.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_5,c_1168]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_18,plain,
% 19.38/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.38/3.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 19.38/3.00      inference(cnf_transformation,[],[f58]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_22,negated_conjecture,
% 19.38/3.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 19.38/3.00      inference(cnf_transformation,[],[f54]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_302,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 19.38/3.00      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 19.38/3.00      | sK2 != X1 ),
% 19.38/3.00      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_303,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) = k3_subset_1(X0,sK2)
% 19.38/3.00      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 19.38/3.00      inference(unflattening,[status(thm)],[c_302]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1214,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
% 19.38/3.00      inference(equality_resolution,[status(thm)],[c_303]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1167,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2387,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = k5_xboole_0(X0,k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1214,c_1167]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_8,plain,
% 19.38/3.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.38/3.00      inference(cnf_transformation,[],[f42]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2386,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_8,c_1167]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2423,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_2386,c_5]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3228,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X1,X2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2423,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3468,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,X0)) = k5_xboole_0(X0,k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1214,c_1168]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5465,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,sK1),X1),k3_subset_1(sK1,sK2)) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3228,c_3468]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1683,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k5_xboole_0(k3_subset_1(sK1,sK2),X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1214,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1687,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2164,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),sK1)) = k1_xboole_0 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1683,c_1687]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2550,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,k3_subset_1(sK1,sK2))) = k1_xboole_0 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1,c_2164]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3483,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,k3_subset_1(sK1,sK2)),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k5_xboole_0(X0,k1_xboole_0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2550,c_1168]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2442,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k5_xboole_0(X0,k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1,c_2387]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3241,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k3_subset_1(sK1,sK2)) = k3_xboole_0(sK1,sK2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2423,c_2442]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3523,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = X0 ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_3483,c_5,c_3241]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1898,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X1)) = k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),X0),X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1683,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1960,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),X0),X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7,c_1898]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1972,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),X0),X1) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_1960,c_1683]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1974,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X1)) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_1972,c_1898]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5605,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X1)) = k5_xboole_0(sK1,k5_xboole_0(X0,X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3523,c_1974]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1897,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k1_xboole_0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_8,c_1683]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1899,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(sK1,sK2)) = sK1 ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_1897,c_5]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1978,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k5_xboole_0(sK1,X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1899,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1169,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5254,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X1)) = k5_xboole_0(X1,k5_xboole_0(sK1,X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1978,c_1169]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3471,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),k5_xboole_0(sK1,X1)) = k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sK1,sK2),X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1683,c_1168]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5417,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1)),X2)) = k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X1),X2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3471,c_3228]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2390,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1))) = k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1683,c_1167]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2895,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1)),X2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2390,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2412,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)),X2)) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k5_xboole_0(X0,X1),X2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1167,c_1974]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2420,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)),X2)) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_2412,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2910,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1)),X2) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_2895,c_2420]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5499,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X1),X2) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_5417,c_2910]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3700,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = k3_xboole_0(sK1,sK2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3468,c_2423]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3955,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),X1)) = k5_xboole_0(k3_xboole_0(sK1,sK2),X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3700,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2449,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),X1)) = k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2387,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2074,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),X1)) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1,c_1974]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2459,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),X1) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_2449,c_2074]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3972,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(k3_xboole_0(sK1,sK2),X1) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_3955,c_2459]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5500,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X1) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_5499,c_3972]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3694,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,sK1),k3_subset_1(sK1,sK2)) = k5_xboole_0(k3_xboole_0(sK1,sK2),X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2423,c_3468]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5423,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X1)) = k5_xboole_0(k5_xboole_0(X0,sK1),X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3694,c_3228]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5501,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,sK1),X1) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_5500,c_5423]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5619,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,sK1),X1) = k5_xboole_0(sK1,k5_xboole_0(X0,X1)) ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_5605,c_5254,c_5500,c_5501]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5947,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X0,X1)),k3_subset_1(sK1,sK2)) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_5465,c_5465,c_5619]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5960,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2387,c_5947]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_6118,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k3_subset_1(sK1,sK2)) = X0 ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_5960,c_2423,c_2459]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5433,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X0,X2)) = X1 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3228,c_2423]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5492,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X2)) = X1 ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_5433,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_9541,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1,c_5492]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_10390,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),k5_xboole_0(X0,sK1)) = k5_xboole_0(X1,k3_xboole_0(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2387,c_9541]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_14392,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k3_xboole_0(sK1,sK2)) = k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X1,sK1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_6118,c_10390]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_10385,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(X0,sK1)) = k3_xboole_0(sK1,sK2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1214,c_9541]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5388,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X1,X2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1,c_3228]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5511,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_5388,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_10739,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k3_xboole_0(sK1,sK2)) = k5_xboole_0(X0,sK1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_10385,c_5511]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_14525,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,sK1)) = k5_xboole_0(X1,sK1) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_14392,c_10739]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_9572,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),k5_xboole_0(X0,k5_xboole_0(sK1,X1))) = k3_xboole_0(sK1,sK2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3468,c_5492]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_11697,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k3_xboole_0(sK1,sK2)) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(sK1,X0))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_9572,c_3228]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_11704,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(sK1,X1))) = k5_xboole_0(X1,sK1) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_11697,c_10739]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_10389,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X2,X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3466,c_9541]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_10635,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X0) = k5_xboole_0(X2,X1) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_10389,c_5]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_12858,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X0) = k5_xboole_0(X1,X2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1,c_10635]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19458,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK1)),X0) = k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(sK1,X1))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_11704,c_12858]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19459,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK1,X1)),X0) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,sK1)),X2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_11704,c_10635]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19648,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,sK1)),X0) = sP0_iProver_split(X1) ),
% 19.38/3.00      inference(splitting,
% 19.38/3.00                [splitting(split),new_symbols(definition,[])],
% 19.38/3.00                [c_19459]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19649,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sK1) = sP0_iProver_split(X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19458,c_11704,c_19648]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19754,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split(X0)) = k5_xboole_0(X1,sK1) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_14525,c_14525,c_19649]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19755,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split(X0)) = sP0_iProver_split(X1) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19754,c_19649]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19767,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),sP0_iProver_split(k5_xboole_0(X0,X1))) = sP0_iProver_split(X2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_36520,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),sP0_iProver_split(k5_xboole_0(X0,k1_xboole_0))) = sP0_iProver_split(k5_xboole_0(X2,X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3466,c_19767]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_36749,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),sP0_iProver_split(X0)) = sP0_iProver_split(k5_xboole_0(X2,X1)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_36520,c_5]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_43653,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = sP0_iProver_split(k5_xboole_0(X2,X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_36749,c_1]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_48661,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(k5_xboole_0(X1,X2),X0)) = sP0_iProver_split(k5_xboole_0(X2,X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1,c_43653]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5368,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X2,X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1,c_3228]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3472,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2387,c_1168]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_7042,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2))),k5_xboole_0(X1,k3_subset_1(sK1,sK2))) = k5_xboole_0(X0,sK1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_5368,c_3472]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1385,plain,
% 19.38/3.00      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_5,c_1]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1894,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = k5_xboole_0(k3_subset_1(sK1,sK2),X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1,c_1683]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1905,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7,c_1894]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2045,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k5_xboole_0(X0,k1_xboole_0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_8,c_1905]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2052,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,X0) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_2045,c_5]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2392,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = k5_xboole_0(X0,sK1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1899,c_1167]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19533,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,sK1))) = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,X1)),sK1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_11704,c_11704]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_10734,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,k5_xboole_0(X1,sK1))) = k5_xboole_0(X1,k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_10385,c_5492]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_14953,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,sK1))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_10734,c_3228]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2452,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2387,c_1167]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3245,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = k5_xboole_0(sK1,X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2423,c_2452]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_14968,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,sK1))) = k5_xboole_0(sK1,X1) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_14953,c_3245]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20127,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,X0)),sK1) = k5_xboole_0(sK1,X0) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_19533,c_14968]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3084,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,k3_subset_1(sK1,sK2)),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2550,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3104,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,k3_subset_1(sK1,sK2)),X0)) = X0 ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_3084,c_1385]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1979,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k3_subset_1(sK1,sK2)) = sK1 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1899,c_1]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2281,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),X0)) = k5_xboole_0(sK1,X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1979,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3105,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = X0 ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_3104,c_2281,c_2459]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_10732,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) = k5_xboole_0(X1,sK1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_10385,c_9541]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_14640,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1)),k3_xboole_0(sK1,sK2)),X1) = k5_xboole_0(X0,sK1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_9541,c_10732]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1967,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),X0),k3_xboole_0(sK1,sK2)) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1898,c_1894]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1983,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),X0),k3_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_1967,c_1978]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_6818,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1)),k3_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1169,c_1983]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_14773,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X0,X1)),X0) = k5_xboole_0(X1,sK1) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_14640,c_6818]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20128,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,X0) = sP0_iProver_split(X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20127,c_3105,c_14773,c_19649]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_21805,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = sP0_iProver_split(X0) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_2052,c_2392,c_20128]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_21822,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k3_xboole_0(sK1,sK2)) = sP0_iProver_split(k1_xboole_0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1385,c_21805]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19763,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sP0_iProver_split(X0)) = sP0_iProver_split(k1_xboole_0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_5,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19886,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sP0_iProver_split(X0)) = k5_xboole_0(X1,sP0_iProver_split(X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_19755,c_3228]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19890,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sP0_iProver_split(X0)) = sP1_iProver_split ),
% 19.38/3.00      inference(splitting,
% 19.38/3.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 19.38/3.00                [c_19886]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19994,plain,
% 19.38/3.00      ( sP0_iProver_split(k1_xboole_0) = sP1_iProver_split ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19763,c_19890]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_21980,plain,
% 19.38/3.00      ( sP1_iProver_split = sK1 ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_21822,c_1899,c_19994]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_21,negated_conjecture,
% 19.38/3.00      ( r1_tarski(k3_subset_1(sK1,sK2),sK2) | k2_subset_1(sK1) = sK2 ),
% 19.38/3.00      inference(cnf_transformation,[],[f55]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1152,plain,
% 19.38/3.00      ( k2_subset_1(sK1) = sK2
% 19.38/3.00      | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
% 19.38/3.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_17,plain,
% 19.38/3.00      ( k2_subset_1(X0) = X0 ),
% 19.38/3.00      inference(cnf_transformation,[],[f51]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1156,plain,
% 19.38/3.00      ( sK2 = sK1 | r1_tarski(k3_subset_1(sK1,sK2),sK2) = iProver_top ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_1152,c_17]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3,plain,
% 19.38/3.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 19.38/3.00      inference(cnf_transformation,[],[f37]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1155,plain,
% 19.38/3.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 19.38/3.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3112,plain,
% 19.38/3.00      ( k3_xboole_0(k3_subset_1(sK1,sK2),sK2) = k3_subset_1(sK1,sK2)
% 19.38/3.00      | sK2 = sK1 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1156,c_1155]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2,plain,
% 19.38/3.00      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 19.38/3.00      inference(cnf_transformation,[],[f35]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_6,plain,
% 19.38/3.00      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 19.38/3.00      inference(cnf_transformation,[],[f57]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_258,plain,
% 19.38/3.00      ( X0 != X1
% 19.38/3.00      | k5_xboole_0(X2,k3_xboole_0(X2,X0)) != X3
% 19.38/3.00      | k3_xboole_0(X3,X1) = k1_xboole_0 ),
% 19.38/3.00      inference(resolution_lifted,[status(thm)],[c_2,c_6]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_259,plain,
% 19.38/3.00      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 19.38/3.00      inference(unflattening,[status(thm)],[c_258]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1455,plain,
% 19.38/3.00      ( k3_xboole_0(k3_subset_1(sK1,sK2),sK2) = k1_xboole_0 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1214,c_259]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3116,plain,
% 19.38/3.00      ( k3_subset_1(sK1,sK2) = k1_xboole_0 | sK2 = sK1 ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_3112,c_1455]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5071,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,sK1),k1_xboole_0) = k5_xboole_0(k3_xboole_0(sK1,sK2),X0)
% 19.38/3.00      | sK2 = sK1 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3116,c_3694]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5084,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),X0) = k5_xboole_0(X0,sK1)
% 19.38/3.00      | sK2 = sK1 ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_5071,c_5]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_897,plain,( X0 = X0 ),theory(equality) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_912,plain,
% 19.38/3.00      ( sK2 = sK2 ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_897]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_12,plain,
% 19.38/3.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 19.38/3.00      inference(cnf_transformation,[],[f60]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_650,plain,
% 19.38/3.00      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 19.38/3.00      inference(prop_impl,[status(thm)],[c_12]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_651,plain,
% 19.38/3.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 19.38/3.00      inference(renaming,[status(thm)],[c_650]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_16,plain,
% 19.38/3.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 19.38/3.00      inference(cnf_transformation,[],[f47]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_289,plain,
% 19.38/3.00      ( r2_hidden(X0,X1)
% 19.38/3.00      | v1_xboole_0(X1)
% 19.38/3.00      | k1_zfmisc_1(sK1) != X1
% 19.38/3.00      | sK2 != X0 ),
% 19.38/3.00      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_290,plain,
% 19.38/3.00      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 19.38/3.00      inference(unflattening,[status(thm)],[c_289]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19,plain,
% 19.38/3.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 19.38/3.00      inference(cnf_transformation,[],[f53]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_296,plain,
% 19.38/3.00      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
% 19.38/3.00      inference(forward_subsumption_resolution,[status(thm)],[c_290,c_19]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_770,plain,
% 19.38/3.00      ( r1_tarski(X0,X1) | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1) | sK2 != X0 ),
% 19.38/3.00      inference(resolution_lifted,[status(thm)],[c_651,c_296]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_771,plain,
% 19.38/3.00      ( r1_tarski(sK2,X0) | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 19.38/3.00      inference(unflattening,[status(thm)],[c_770]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1191,plain,
% 19.38/3.00      ( r1_tarski(sK2,sK1) | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_771]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1206,plain,
% 19.38/3.00      ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1) ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_897]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1246,plain,
% 19.38/3.00      ( k2_subset_1(sK1) = sK1 ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_17]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_898,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1203,plain,
% 19.38/3.00      ( X0 != X1 | k2_subset_1(sK1) != X1 | k2_subset_1(sK1) = X0 ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_898]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1233,plain,
% 19.38/3.00      ( X0 != sK1 | k2_subset_1(sK1) = X0 | k2_subset_1(sK1) != sK1 ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_1203]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1274,plain,
% 19.38/3.00      ( k3_xboole_0(sK1,X0) != sK1
% 19.38/3.00      | k2_subset_1(sK1) = k3_xboole_0(sK1,X0)
% 19.38/3.00      | k2_subset_1(sK1) != sK1 ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_1233]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1275,plain,
% 19.38/3.00      ( k3_xboole_0(sK1,sK2) != sK1
% 19.38/3.00      | k2_subset_1(sK1) = k3_xboole_0(sK1,sK2)
% 19.38/3.00      | k2_subset_1(sK1) != sK1 ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_1274]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1298,plain,
% 19.38/3.00      ( sK1 = sK1 ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_897]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1229,plain,
% 19.38/3.00      ( k2_subset_1(sK1) != X0 | sK2 != X0 | sK2 = k2_subset_1(sK1) ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_898]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1313,plain,
% 19.38/3.00      ( k2_subset_1(sK1) != k3_xboole_0(sK1,X0)
% 19.38/3.00      | sK2 != k3_xboole_0(sK1,X0)
% 19.38/3.00      | sK2 = k2_subset_1(sK1) ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_1229]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1316,plain,
% 19.38/3.00      ( k2_subset_1(sK1) != k3_xboole_0(sK1,sK2)
% 19.38/3.00      | sK2 != k3_xboole_0(sK1,sK2)
% 19.38/3.00      | sK2 = k2_subset_1(sK1) ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_1313]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1240,plain,
% 19.38/3.00      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_898]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1267,plain,
% 19.38/3.00      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_1240]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1391,plain,
% 19.38/3.00      ( k2_subset_1(sK1) != sK1 | sK1 = k2_subset_1(sK1) | sK1 != sK1 ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_1267]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1327,plain,
% 19.38/3.00      ( k3_xboole_0(sK1,X0) != X1 | sK2 != X1 | sK2 = k3_xboole_0(sK1,X0) ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_898]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1411,plain,
% 19.38/3.00      ( k3_xboole_0(sK1,X0) != k3_xboole_0(X0,sK1)
% 19.38/3.00      | sK2 != k3_xboole_0(X0,sK1)
% 19.38/3.00      | sK2 = k3_xboole_0(sK1,X0) ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_1327]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1412,plain,
% 19.38/3.00      ( k3_xboole_0(sK1,sK2) != k3_xboole_0(sK2,sK1)
% 19.38/3.00      | sK2 != k3_xboole_0(sK2,sK1)
% 19.38/3.00      | sK2 = k3_xboole_0(sK1,sK2) ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_1411]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1227,plain,
% 19.38/3.00      ( sK2 != X0 | sK2 = sK1 | sK1 != X0 ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_898]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1510,plain,
% 19.38/3.00      ( sK2 != k2_subset_1(sK1) | sK2 = sK1 | sK1 != k2_subset_1(sK1) ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_1227]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1610,plain,
% 19.38/3.00      ( k3_xboole_0(X0,sK1) != X1 | sK2 != X1 | sK2 = k3_xboole_0(X0,sK1) ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_898]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1611,plain,
% 19.38/3.00      ( k3_xboole_0(sK2,sK1) != sK2 | sK2 = k3_xboole_0(sK2,sK1) | sK2 != sK2 ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_1610]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2539,plain,
% 19.38/3.00      ( ~ r1_tarski(X0,sK1) | k3_xboole_0(X0,sK1) = X0 ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_3]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2541,plain,
% 19.38/3.00      ( ~ r1_tarski(sK2,sK1) | k3_xboole_0(sK2,sK1) = sK2 ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_2539]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_0,plain,
% 19.38/3.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 19.38/3.00      inference(cnf_transformation,[],[f33]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3418,plain,
% 19.38/3.00      ( k3_xboole_0(sK1,X0) = k3_xboole_0(X0,sK1) ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_0]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3419,plain,
% 19.38/3.00      ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,sK1) ),
% 19.38/3.00      inference(instantiation,[status(thm)],[c_3418]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5075,plain,
% 19.38/3.00      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK2)) = sK1 | sK2 = sK1 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3116,c_1899]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5080,plain,
% 19.38/3.00      ( k3_xboole_0(sK1,sK2) = sK1 | sK2 = sK1 ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_5075,c_1385]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_32626,plain,
% 19.38/3.00      ( sK2 = sK1 ),
% 19.38/3.00      inference(global_propositional_subsumption,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_5084,c_912,c_1191,c_1206,c_1246,c_1275,c_1298,c_1316,
% 19.38/3.00                 c_1391,c_1412,c_1510,c_1611,c_2541,c_3419,c_5080]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_32628,plain,
% 19.38/3.00      ( sP1_iProver_split = sK2 ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_32626,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_47342,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sP1_iProver_split))),k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = sP0_iProver_split(X0) ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_7042,c_7042,c_19649,c_21980,c_32628]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52268,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(k5_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X1,X0),k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = sP0_iProver_split(sP0_iProver_split(k3_xboole_0(sP1_iProver_split,sP1_iProver_split))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_48661,c_47342]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_6966,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2)))) = k5_xboole_0(k3_xboole_0(sK1,sK2),X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3468,c_5368]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_8141,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X0,X1)),k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = k5_xboole_0(k3_xboole_0(sK1,sK2),X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3228,c_6966]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3238,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k3_subset_1(sK1,sK2)) = k5_xboole_0(sK1,X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2423,c_2442]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3559,plain,
% 19.38/3.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7,c_3466]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_30673,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(sK1,X1))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3238,c_3559]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_30785,plain,
% 19.38/3.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3559,c_5511]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_31024,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(sK1,k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_30673,c_30785]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_6601,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(X0,k5_xboole_0(sK1,X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3238,c_1169]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_6952,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2)))) = k5_xboole_0(sK1,X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2387,c_5368]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_7523,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3245,c_6952]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_7628,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,X0)) = k3_subset_1(sK1,sK2) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_7523,c_1214]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_9599,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(X0,k5_xboole_0(sK1,X1))) = k5_xboole_0(X1,k3_xboole_0(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7628,c_5492]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_12087,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X1,sK1),k3_xboole_0(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2423,c_9599]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_10730,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,sK1),k3_xboole_0(sK1,sK2)) = k5_xboole_0(X0,k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_10385,c_2423]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_11132,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,sK1))) = k5_xboole_0(k5_xboole_0(X1,k3_subset_1(sK1,sK2)),X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_10739,c_5368]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3705,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(sK1,X1))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3468,c_1167]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_4712,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,sK1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1169,c_3705]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_11164,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_11132,c_4712]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_12186,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_12087,c_10730,c_11164]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_7735,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,sK1),k3_xboole_0(sK1,sK2)),X0) = k3_subset_1(sK1,sK2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2423,c_7628]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3678,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,sK1)) = k5_xboole_0(X0,k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1,c_3468]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3814,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,sK1),k3_xboole_0(sK1,sK2)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3678,c_3466]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3838,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,sK1),k3_xboole_0(sK1,sK2)) = k5_xboole_0(k3_subset_1(sK1,sK2),X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_3814,c_3466]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_7805,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),X0),X0) = k3_subset_1(sK1,sK2) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_7735,c_3838]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_18860,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(X0,X1)) = k5_xboole_0(k3_subset_1(sK1,sK2),X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7805,c_5492]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_28187,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sK2)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_12186,c_18860,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_28329,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)),sP0_iProver_split(k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sK2)))) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_28187,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3566,plain,
% 19.38/3.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_subset_1(sK1,sK2),X0)) = k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),sK1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1683,c_3466]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3627,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),sK1) = k5_xboole_0(X0,k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_3566,c_3466]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1961,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),X0),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k5_xboole_0(sK1,k1_xboole_0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_8,c_1898]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1988,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),X0),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = sK1 ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_1961,c_5]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_9316,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),sK1) = k5_xboole_0(k3_subset_1(sK1,sK2),X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1988,c_2423]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_24050,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),X0),sP1_iProver_split) = k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_3627,c_9316,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_24082,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),X0),k5_xboole_0(sP1_iProver_split,X1)) = k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)),X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_24050,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5374,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X1,X2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7,c_3228]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19824,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X0,X2),sP0_iProver_split(X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_5374,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5402,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),X0),X1)) = k5_xboole_0(sK1,X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1683,c_3228]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_21884,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k3_xboole_0(sK1,sK2))),k5_xboole_0(sP0_iProver_split(X0),X1)) = k5_xboole_0(sK1,X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_21805,c_5402]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19859,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sP0_iProver_split(X0),X2)) = k5_xboole_0(sP0_iProver_split(X1),X2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_19755,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19868,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X2,sP0_iProver_split(X1)),X2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_19755,c_10635]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3229,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2423,c_2423]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19896,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X0,X1)) = sP0_iProver_split(X1) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19868,c_3229]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19874,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X2,sP0_iProver_split(X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_19755,c_1168]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19894,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,sP0_iProver_split(X1)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_19874,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19897,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,X1)) = k5_xboole_0(X1,sP0_iProver_split(X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19896,c_19894]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19873,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sP0_iProver_split(X0),X2)) = k5_xboole_0(X2,sP0_iProver_split(X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_19755,c_1169]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19903,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sP0_iProver_split(X0),X2)) = sP0_iProver_split(k5_xboole_0(X1,X2)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19897,c_19873]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19924,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,X1)) = k5_xboole_0(sP0_iProver_split(X0),X1) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19859,c_19903]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_22109,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sK2))),sP0_iProver_split(k5_xboole_0(X0,X1))) = k5_xboole_0(sP1_iProver_split,X1) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_21884,c_19924,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19876,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,sP0_iProver_split(X0))) = sP0_iProver_split(X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_19755,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19908,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sP0_iProver_split(k5_xboole_0(X0,X1))) = sP0_iProver_split(X1) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19897,c_19876]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_22110,plain,
% 19.38/3.00      ( k5_xboole_0(sP1_iProver_split,X0) = sP0_iProver_split(X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_22109,c_2423,c_19824,c_19908]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_24126,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sK2)),X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_24082,c_19824,c_22110]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_21830,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_10635,c_21805]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_12980,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)),k3_subset_1(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_10635,c_2387]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19761,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split(X1)) = sP0_iProver_split(X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20929,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X0,X1)),sP0_iProver_split(k3_subset_1(sK1,sK2))) = sP0_iProver_split(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X1,X0))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_12980,c_19761]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_4260,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,X0),X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3468,c_1169]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_12904,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_subset_1(sK1,sK2)))),X0) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,X2),X1),k3_xboole_0(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_4260,c_10635]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_13133,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,X0),X1),k3_xboole_0(sK1,sK2)) = k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),X1) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_12904,c_10635]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_4849,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,X0),X1),k3_xboole_0(sK1,sK2)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2)))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_4260,c_3466]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3589,plain,
% 19.38/3.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3466,c_1167]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_4875,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,X0),X1),k3_xboole_0(sK1,sK2)) = k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sK1,sK2),X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_4849,c_3589]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_9603,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,X0)) = X1 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1,c_5492]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_12545,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(sK1,X1),X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_9603,c_6966]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_10042,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(sK1,k5_xboole_0(X0,X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_5511,c_2390]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_12558,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,X0),X1) = k5_xboole_0(sK1,k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_12545,c_10042]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_13134,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X0,X1)),k3_xboole_0(sK1,sK2)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_13133,c_4875,c_11164,c_12558]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_7286,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1))) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1683,c_5374]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19540,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,X0))) = k5_xboole_0(sK1,k5_xboole_0(X0,sK1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_11704,c_7286]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5406,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,X0)) = k5_xboole_0(k3_subset_1(sK1,sK2),X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1899,c_3228]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_7566,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_subset_1(sK1,sK2))))) = k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_6952,c_1974]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_6954,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,sK1)) = k5_xboole_0(k3_subset_1(sK1,sK2),X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1899,c_5368]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_7586,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),X0)) = X0 ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_7566,c_1979,c_3105,c_6954]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20011,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,sP0_iProver_split(X0)) = X0 ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_19540,c_5406,c_7586,c_19649]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3213,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = sK1 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2442,c_2423]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19799,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,sP0_iProver_split(k5_xboole_0(k3_xboole_0(sK1,sK2),X0))) = sP0_iProver_split(k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3213,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20016,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = k5_xboole_0(k3_xboole_0(sK1,sK2),X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20011,c_19799]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_10748,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),sK1) = k5_xboole_0(X0,k3_xboole_0(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_10385,c_5374]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19830,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),sP0_iProver_split(k5_xboole_0(X0,k3_subset_1(sK1,sK2)))) = sP0_iProver_split(sK1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_10748,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20021,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = sP0_iProver_split(sK1) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20016,c_19830]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3216,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),X0)) = sK1 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1894,c_2423]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2408,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1167,c_8]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_6438,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,k5_xboole_0(k3_subset_1(sK1,sK2),X0))) = k1_xboole_0 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3216,c_2408]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5196,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(k3_subset_1(sK1,sK2),X0)) = k5_xboole_0(k3_xboole_0(sK1,sK2),X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3241,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_6473,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k1_xboole_0 ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_6438,c_5196]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20024,plain,
% 19.38/3.00      ( sP0_iProver_split(sK1) = k1_xboole_0 ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_20021,c_6473]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19889,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(sK1),k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = k5_xboole_0(k3_xboole_0(sK1,sK2),sP0_iProver_split(X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_19755,c_4260]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19911,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(sK1),k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = sP0_iProver_split(k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19897,c_19889]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20039,plain,
% 19.38/3.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = sP0_iProver_split(k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20024,c_19911]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20040,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = k5_xboole_0(k3_subset_1(sK1,sK2),X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20039,c_3466]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19806,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),sP0_iProver_split(k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = sP0_iProver_split(k5_xboole_0(sK1,X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3472,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19834,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),sP0_iProver_split(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)))) = sP0_iProver_split(k5_xboole_0(sK1,X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7628,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_7715,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,sK1)) = k3_subset_1(sK1,sK2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1,c_7628]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19837,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),sP0_iProver_split(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)))) = sP0_iProver_split(k5_xboole_0(X0,sK1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7715,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19947,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),sP0_iProver_split(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)))) = sP0_iProver_split(sP0_iProver_split(X0)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_19837,c_19649]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19948,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(sK1,X0)) = sP0_iProver_split(sP0_iProver_split(X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19834,c_19947]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19980,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),sP0_iProver_split(k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = sP0_iProver_split(sP0_iProver_split(X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19806,c_19824,c_19948]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20047,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),k5_xboole_0(k3_subset_1(sK1,sK2),X1)) = sP0_iProver_split(sP0_iProver_split(X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20040,c_19980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_10452,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X1)),k5_xboole_0(k3_subset_1(sK1,sK2),X0)) = X1 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1683,c_9541]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_4247,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2442,c_1169]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_10624,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),k5_xboole_0(k3_subset_1(sK1,sK2),X1)) = X0 ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_10452,c_4247]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20061,plain,
% 19.38/3.00      ( sP0_iProver_split(sP0_iProver_split(X0)) = X0 ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_20047,c_10624]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19828,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)),sP0_iProver_split(k5_xboole_0(sK1,k5_xboole_0(X0,X1)))) = sP0_iProver_split(k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_5947,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_12960,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X0)) = k5_xboole_0(X2,X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_10635,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19844,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),sP0_iProver_split(X2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_12960,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19945,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X1,X0),sP0_iProver_split(X2)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_19844,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19954,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(sK1,sK2),sP0_iProver_split(k5_xboole_0(X0,X1))))) = sP0_iProver_split(k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19828,c_19945,c_19948]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19955,plain,
% 19.38/3.00      ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(sK1,sK2)))))) = sP0_iProver_split(k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19954,c_19897,c_19945]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_7345,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_5374,c_1983]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5772,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1))) = k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X1),X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2423,c_5402]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5850,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1))) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_5772,c_5500]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_7428,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(sK1,sK2)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_7345,c_5850]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19956,plain,
% 19.38/3.00      ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)))))) = sP0_iProver_split(k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_19955,c_7428]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_7282,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3)))) = k5_xboole_0(X1,k5_xboole_0(X3,X2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1169,c_5374]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19957,plain,
% 19.38/3.00      ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(sK1,sK2))))) = sP0_iProver_split(k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19956,c_7282]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_7888,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7715,c_5368]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_7903,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = k3_xboole_0(sK1,sK2) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_7888,c_3241]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19958,plain,
% 19.38/3.00      ( sP0_iProver_split(sP0_iProver_split(k3_xboole_0(sK1,sK2))) = sP0_iProver_split(k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_19957,c_7903]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20075,plain,
% 19.38/3.00      ( sP0_iProver_split(k3_subset_1(sK1,sK2)) = k3_xboole_0(sK1,sK2) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20061,c_19958]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_21051,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_20929,c_13134,c_20075]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_22166,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_21830,c_21051,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_24127,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)),X1) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k5_xboole_0(X0,X1)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_24126,c_22166]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5450,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,sK1),k3_subset_1(sK1,sK2)) = k5_xboole_0(X0,k3_xboole_0(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3228,c_2387]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_6319,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,sK1)),k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = sK1 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_5450,c_3213]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_6368,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = sK1 ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_6319,c_3678]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_25983,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)),k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sK2))) = sP1_iProver_split ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_6368,c_6368,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_26015,plain,
% 19.38/3.00      ( k5_xboole_0(sP1_iProver_split,sP0_iProver_split(k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sK2)))) = sP0_iProver_split(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_25983,c_19761]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_26047,plain,
% 19.38/3.00      ( k5_xboole_0(sP1_iProver_split,k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)),k3_xboole_0(sP1_iProver_split,sK2))) = X0 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_25983,c_5492]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_21901,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_xboole_0(sK1,sK2),k3_subset_1(sK1,sK2))) = k5_xboole_0(k3_xboole_0(sK1,sK2),sP0_iProver_split(sK1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_21805,c_3705]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_22083,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),k1_xboole_0) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),sK1) ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_21901,c_1979,c_20024,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_22084,plain,
% 19.38/3.00      ( sP0_iProver_split(k3_subset_1(sP1_iProver_split,sK2)) = k3_xboole_0(sP1_iProver_split,sK2) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_22083,c_5,c_19649]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_23350,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)),k3_xboole_0(sP1_iProver_split,sK2)) = sP0_iProver_split(X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_22084,c_19761]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_26111,plain,
% 19.38/3.00      ( k5_xboole_0(sP1_iProver_split,sP0_iProver_split(X0)) = X0 ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_26047,c_23350]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_26146,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2))) = k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sK2)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_26015,c_26111]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_28518,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sK2)))) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_28329,c_24127,c_26146]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_31025,plain,
% 19.38/3.00      ( k5_xboole_0(sP1_iProver_split,k5_xboole_0(X0,X1)) = sP0_iProver_split(k5_xboole_0(X0,X1)) ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_31024,c_6601,c_21980,c_28518]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52361,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(k5_xboole_0(X0,X1)),k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1) ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_8141,c_8141,c_21980,c_31025,c_32628]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_7748,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(X0,k3_xboole_0(sK1,sK2))) = k3_subset_1(sK1,sK2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7628,c_1]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_7997,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = k3_subset_1(sK1,sK2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7,c_7748]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_50948,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(k5_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sP1_iProver_split)))) = k3_subset_1(sP1_iProver_split,sP1_iProver_split) ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_7997,c_7997,c_21980,c_31025,c_32628]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_51126,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(k5_xboole_0(X0,X1)),k5_xboole_0(X2,k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sP1_iProver_split)))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_50948,c_5374]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52225,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),sP0_iProver_split(X2)) = k5_xboole_0(k5_xboole_0(X3,sP0_iProver_split(k5_xboole_0(X1,X0))),X3) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_48661,c_10635]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52249,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X1,sP0_iProver_split(k5_xboole_0(X2,X3)))) = k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X3,X2),X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_48661,c_5374]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19792,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,X1)) = k5_xboole_0(X0,sP0_iProver_split(X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2423,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_43687,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(X0),sP0_iProver_split(k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X2,X1),X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_36749,c_12960]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_48686,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X2,X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_12960,c_43653]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52324,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X1),X0),X3) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52249,c_19792,c_43687,c_48686]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52233,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(sP0_iProver_split(X0)),sP0_iProver_split(k5_xboole_0(X1,X2))) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X2,X1))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_48661,c_43653]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52333,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X0,sP0_iProver_split(k5_xboole_0(X2,X1))) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_52233,c_20061]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52345,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2))),X0) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),X3),sP0_iProver_split(X3)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52225,c_52324,c_52333]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52347,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),sP0_iProver_split(X2)) = sP2_iProver_split(X0,X1) ),
% 19.38/3.00      inference(splitting,
% 19.38/3.00                [splitting(split),new_symbols(definition,[])],
% 19.38/3.00                [c_52345]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19770,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),sP0_iProver_split(X2)) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1168,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52348,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,X1)) = sP2_iProver_split(X1,X0) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_52347,c_7,c_19770]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52362,plain,
% 19.38/3.00      ( k5_xboole_0(sP2_iProver_split(X0,X1),k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52361,c_51126,c_52348]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52427,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)),k5_xboole_0(X1,sP2_iProver_split(X2,X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X2))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_52362,c_3559]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_6331,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = sK1 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3213,c_1]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_33108,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)),k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X0)) = sP1_iProver_split ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_6331,c_6331,c_21980,c_32628]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_8168,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k5_xboole_0(sK1,X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_6966,c_2423]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_12400,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k5_xboole_0(X1,sK1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_10730,c_9603]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52431,plain,
% 19.38/3.00      ( k5_xboole_0(sP2_iProver_split(X0,X1),k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X0)),X2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_52362,c_12858]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52432,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)),sP2_iProver_split(X1,X0)) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1)),X2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_52362,c_10635]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52515,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1)),X0) = sP3_iProver_split(X1) ),
% 19.38/3.00      inference(splitting,
% 19.38/3.00                [splitting(split),new_symbols(definition,[])],
% 19.38/3.00                [c_52432]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52516,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X0) = sP3_iProver_split(X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52431,c_52362,c_52515]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52558,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))),sP3_iProver_split(X0)) = k5_xboole_0(sP1_iProver_split,X1) ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_8168,c_12400,c_21980,c_32628,c_52516]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_36825,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split(X2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1,c_19945]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_44597,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(sP0_iProver_split(X2),k5_xboole_0(X0,X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_36825,c_1]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_36886,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(sP0_iProver_split(X2),k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_19945,c_1]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_49668,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sP0_iProver_split(X2),X3))) = k5_xboole_0(sP0_iProver_split(X3),sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2)))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_44597,c_36886]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19477,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sK1,X2))) = k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,sK1))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_11704,c_5374]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20244,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,sK1))) = sP0_iProver_split(k5_xboole_0(X1,k5_xboole_0(X0,X2))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19477,c_19792,c_20128]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20245,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X0,sP0_iProver_split(X2))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20244,c_19649]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19482,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK1,X1)),k5_xboole_0(X2,k5_xboole_0(X1,sK1))) = k5_xboole_0(X0,X2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_11704,c_5368]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20236,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X1,sK1)))) = k5_xboole_0(X0,X2) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19482,c_19792,c_19924,c_20128]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20237,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,sP0_iProver_split(X1)))) = k5_xboole_0(X0,X2) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20236,c_19649]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20246,plain,
% 19.38/3.00      ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X2)))) = k5_xboole_0(X1,X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20245,c_20237]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3576,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = k5_xboole_0(k1_xboole_0,X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2423,c_3466]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3615,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_3576,c_1385]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20247,plain,
% 19.38/3.00      ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(X0,X1))) = k5_xboole_0(X1,X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20246,c_3615]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_36878,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sP0_iProver_split(X2),X3)) = k5_xboole_0(sP0_iProver_split(k5_xboole_0(X1,k5_xboole_0(X0,X2))),X3) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_19945,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_36880,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(k5_xboole_0(X1,X2),X3))) = k5_xboole_0(sP0_iProver_split(k5_xboole_0(X2,k5_xboole_0(X1,X0))),sP0_iProver_split(X3)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_19945,c_19945]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_36904,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,sP0_iProver_split(X3))) = k5_xboole_0(X2,sP0_iProver_split(k5_xboole_0(X1,k5_xboole_0(X0,X3)))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_19945,c_1167]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_36934,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X2,X1),X3))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_36904,c_19792,c_20245]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_36963,plain,
% 19.38/3.00      ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)))) = k5_xboole_0(sP0_iProver_split(k5_xboole_0(X2,k5_xboole_0(X0,X3))),sP0_iProver_split(X1)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_36880,c_36886,c_36934]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_36604,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(k5_xboole_0(X0,X1)),sP0_iProver_split(X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_19767,c_2423]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_36964,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(k5_xboole_0(X0,X2),k5_xboole_0(X1,X3)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_36963,c_20247,c_36604]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_36970,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sP0_iProver_split(X1),X2),X3)) = k5_xboole_0(sP0_iProver_split(k5_xboole_0(X2,k5_xboole_0(X0,X1))),X3) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_36878,c_36964]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_30757,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,X2))),k3_subset_1(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),k1_xboole_0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3559,c_12980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_30781,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k1_xboole_0) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3559,c_12858]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_30868,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,X2))),k3_subset_1(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(X2,k5_xboole_0(X0,X1))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_30757,c_30781]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_15764,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,X2))),k3_subset_1(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(X0,X1),X2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1169,c_12980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_16073,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,X2))),k3_subset_1(sK1,sK2)) = k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(X1,X2))) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_15764,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_30869,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),k5_xboole_0(X0,k5_xboole_0(X1,X2))),k3_subset_1(sP1_iProver_split,sK2)) = k5_xboole_0(sP1_iProver_split,k5_xboole_0(X2,k5_xboole_0(X0,X1))) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_30868,c_16073,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_24070,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),k5_xboole_0(X0,X1)),k3_subset_1(sP1_iProver_split,sK2)) = k5_xboole_0(k5_xboole_0(X0,X1),sP1_iProver_split) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_5511,c_24050]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19776,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split(k1_xboole_0)) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3466,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19996,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),sP1_iProver_split) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19994,c_19776]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_24154,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),k5_xboole_0(X0,X1)),k3_subset_1(sP1_iProver_split,sK2)) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_24070,c_19996]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19549,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,X0),k3_subset_1(sK1,sK2))),k5_xboole_0(X0,sK1)) = k3_xboole_0(sK1,sK2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_11704,c_9572]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5695,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,X0),k3_subset_1(sK1,sK2)) = k5_xboole_0(X0,k3_xboole_0(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1,c_5450]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20003,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),sP0_iProver_split(X0)) = k3_xboole_0(sK1,sK2) ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_19549,c_2387,c_5695,c_19649]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20535,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) = sP0_iProver_split(X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_20003,c_9541]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_29789,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sK2)),k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sK2)))) = sP0_iProver_split(X1) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_20535,c_20535,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_29846,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k3_xboole_0(sP1_iProver_split,sK2)),k5_xboole_0(X0,X1)) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_12960,c_29789]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3336,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),X0)),k5_xboole_0(k3_subset_1(sK1,sK2),X0)) = k1_xboole_0 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2408,c_2390]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3338,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(k3_subset_1(sK1,sK2),X0)) = k1_xboole_0 ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_3336,c_2442]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_22840,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)),k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),X0)) = k1_xboole_0 ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_3338,c_3338,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_22934,plain,
% 19.38/3.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k3_subset_1(sP1_iProver_split,sK2)),sK1)) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k3_xboole_0(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_22840,c_10390]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_22965,plain,
% 19.38/3.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k3_subset_1(sP1_iProver_split,sK2)),sP1_iProver_split)) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k3_xboole_0(sP1_iProver_split,sK2)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_22934,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_22966,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k3_subset_1(sP1_iProver_split,sK2))) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k3_xboole_0(sP1_iProver_split,sK2)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_22965,c_1385,c_3466,c_19996]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_22967,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k3_xboole_0(sP1_iProver_split,sK2)) = sP1_iProver_split ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_22966,c_8,c_19994]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_30029,plain,
% 19.38/3.00      ( k5_xboole_0(sP1_iProver_split,k5_xboole_0(X0,X1)) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_29846,c_22967]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_30870,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),X2)) = sP0_iProver_split(k5_xboole_0(k5_xboole_0(X2,X0),X1)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_30869,c_24154,c_30029]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_30871,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),X2)) = sP0_iProver_split(k5_xboole_0(X1,k5_xboole_0(X2,X0))) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_30870,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_36971,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3))) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X3),X2))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_36970,c_19792,c_19924,c_30871]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_44897,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(k5_xboole_0(X1,X2),X3))) = k5_xboole_0(sP0_iProver_split(X3),sP0_iProver_split(k5_xboole_0(X2,k5_xboole_0(X1,X0)))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_19945,c_36886]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_45183,plain,
% 19.38/3.00      ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)))) = k5_xboole_0(sP0_iProver_split(X0),sP0_iProver_split(k5_xboole_0(X2,k5_xboole_0(X1,X3)))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_44897,c_36886]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_44526,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,X0)),sP0_iProver_split(X3)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1168,c_36825]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_36831,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),sP0_iProver_split(X3)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7,c_19945]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_36833,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X2,X1)),sP0_iProver_split(X3)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1167,c_19945]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_37090,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X3,X2)),sP0_iProver_split(X1)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_36833,c_19945,c_36934,c_36971]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_37092,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,X0)),sP0_iProver_split(X3)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_36831,c_36934,c_37090]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_44822,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3))) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_44526,c_37092]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_45184,plain,
% 19.38/3.00      ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))))) = k5_xboole_0(sP0_iProver_split(X0),sP0_iProver_split(k5_xboole_0(X2,k5_xboole_0(X1,X3)))) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_45183,c_44822]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_45185,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X2),X1),X3) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_45184,c_20247,c_43687]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_49833,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,X3)) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,X1)),X3) ),
% 19.38/3.00      inference(demodulation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_49668,c_20245,c_20247,c_36971,c_43687,c_45185]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_49834,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),X3) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_49833,c_36964]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52559,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))),sP3_iProver_split(X0)) = sP0_iProver_split(X1) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52558,c_22110,c_49834]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52588,plain,
% 19.38/3.00      ( k5_xboole_0(sP1_iProver_split,sP3_iProver_split(k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),k3_subset_1(sP1_iProver_split,sP1_iProver_split)))) = sP0_iProver_split(k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_33108,c_52559]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_8106,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k3_subset_1(sK1,sK2)))) = k5_xboole_0(k3_xboole_0(sK1,sK2),X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2387,c_6966]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5471,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k3_subset_1(sK1,sK2)) = k5_xboole_0(X0,sK1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3228,c_3678]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_8251,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(X1,k5_xboole_0(X0,sK1))) = k5_xboole_0(k3_xboole_0(sK1,sK2),X1) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_8106,c_5471]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_10747,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),k5_xboole_0(X1,k5_xboole_0(X0,sK1))) = k5_xboole_0(X1,k3_xboole_0(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_10385,c_1167]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_32681,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sP1_iProver_split)),k5_xboole_0(X1,k5_xboole_0(X0,sK1))) = k5_xboole_0(X1,k3_xboole_0(sK1,sP1_iProver_split)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_32628,c_10747]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_32822,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)),sP0_iProver_split(k5_xboole_0(X0,X1))) = k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_32681,c_19649,c_19897,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52742,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) = k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X0) ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_8251,c_19649,c_19897,c_21980,c_32628,c_32822]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52743,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) = sP3_iProver_split(X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52742,c_52516]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_32746,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sP1_iProver_split)) = k3_subset_1(sK1,sP1_iProver_split) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_32628,c_1214]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_32749,plain,
% 19.38/3.00      ( k5_xboole_0(sP1_iProver_split,k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) = k3_subset_1(sP1_iProver_split,sP1_iProver_split) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_32746,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52755,plain,
% 19.38/3.00      ( k3_subset_1(sP1_iProver_split,sP1_iProver_split) = sP3_iProver_split(sP1_iProver_split) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52743,c_32749]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_33392,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = k5_xboole_0(sP1_iProver_split,k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_32749,c_5511]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_33409,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = k3_subset_1(sP1_iProver_split,sP1_iProver_split) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_33392,c_32749]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52589,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),sP3_iProver_split(X0)) = sP0_iProver_split(X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_33409,c_52559]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53007,plain,
% 19.38/3.00      ( k5_xboole_0(sP3_iProver_split(sP1_iProver_split),sP3_iProver_split(X0)) = sP0_iProver_split(X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52589,c_52755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53008,plain,
% 19.38/3.00      ( k5_xboole_0(sP1_iProver_split,sP3_iProver_split(sP0_iProver_split(sP1_iProver_split))) = sP0_iProver_split(k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52588,c_52755,c_53007]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_23718,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),k3_subset_1(sP1_iProver_split,sK2))) = k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),sP1_iProver_split),k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_22967,c_12980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_7709,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2))),k5_xboole_0(sK1,k5_xboole_0(X0,X1))) = k3_subset_1(sK1,sK2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7,c_7628]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19855,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(sP0_iProver_split(X0),k3_xboole_0(sK1,sK2))),k5_xboole_0(sK1,sP0_iProver_split(X1))) = k3_subset_1(sK1,sK2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_19755,c_7709]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19863,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(X0),sP0_iProver_split(X1)) = k5_xboole_0(X0,X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_19755,c_2423]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19925,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split(k5_xboole_0(X0,X2))) = sP0_iProver_split(k5_xboole_0(X1,X2)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19924,c_19903]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19933,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,sK1)) = k3_subset_1(sK1,sK2) ),
% 19.38/3.00      inference(demodulation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_19855,c_19863,c_19897,c_19924,c_19925]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19934,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),sP0_iProver_split(X0)) = k3_subset_1(sK1,sK2) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_19933,c_7715,c_19649]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_22501,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sK2)),sP0_iProver_split(X0)) = k3_subset_1(sP1_iProver_split,sK2) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_19934,c_19934,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_22553,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),k3_subset_1(sP1_iProver_split,sK2)) = k5_xboole_0(X0,sP0_iProver_split(X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_22501,c_3228]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19493,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(sK1,X0)),k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,sK1)) = sK1 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_11704,c_3216]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19501,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,X0))) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,sK1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_11704,c_1978]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19548,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,k3_subset_1(sK1,sK2)),k5_xboole_0(X0,sK1)) = k5_xboole_0(k5_xboole_0(sK1,X0),k3_xboole_0(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_11704,c_9599]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_8019,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,X0),k3_xboole_0(sK1,sK2)) = k5_xboole_0(X0,k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7748,c_5374]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20004,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),sP0_iProver_split(X0)) = k5_xboole_0(X0,k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_19548,c_3241,c_8019,c_19649]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20200,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,sK1)) = sP0_iProver_split(k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19501,c_20004,c_20128]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20201,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,sK1)) = k5_xboole_0(k3_xboole_0(sK1,sK2),X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20200,c_20016]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3242,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),sK1) = k3_xboole_0(sK1,sK2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2423,c_1683]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3744,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,sK1)) = k5_xboole_0(X0,k3_xboole_0(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3242,c_1167]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20202,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),sP0_iProver_split(X0)) = k5_xboole_0(k3_xboole_0(sK1,sK2),X0) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_20201,c_3744,c_19649]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20215,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,sK1)) = sK1 ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19493,c_20128,c_20202]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5587,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),k3_xboole_0(sK1,sK2)) = k5_xboole_0(k1_xboole_0,X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3523,c_3466]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5625,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),k3_xboole_0(sK1,sK2)) = X0 ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_5587,c_1385]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20216,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sP0_iProver_split(X0)) = sK1 ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_20215,c_5625,c_19649]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_22559,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),k3_subset_1(sP1_iProver_split,sK2)) = sP1_iProver_split ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_22553,c_20216,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_22512,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),sP0_iProver_split(k1_xboole_0)) = k3_subset_1(sP1_iProver_split,sK2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1385,c_22501]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_22602,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sP1_iProver_split,sK2),sP1_iProver_split) = k3_subset_1(sP1_iProver_split,sK2) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_22512,c_19994]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_23782,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),k3_subset_1(sP1_iProver_split,sK2)) = k5_xboole_0(sP1_iProver_split,sP1_iProver_split) ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_23718,c_21980,c_22559,c_22602]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_23783,plain,
% 19.38/3.00      ( sP0_iProver_split(sP1_iProver_split) = k1_xboole_0 ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_23782,c_8,c_22110]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_33373,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),sP0_iProver_split(sP1_iProver_split)) = sP0_iProver_split(k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_32749,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_33422,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),k1_xboole_0) = sP0_iProver_split(k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_33373,c_23783]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_33423,plain,
% 19.38/3.00      ( sP0_iProver_split(k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) = k3_subset_1(sP1_iProver_split,sP1_iProver_split) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_33422,c_5]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53009,plain,
% 19.38/3.00      ( k5_xboole_0(sP1_iProver_split,sP3_iProver_split(k1_xboole_0)) = k3_subset_1(sP1_iProver_split,sP1_iProver_split) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_53008,c_23783,c_33423]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53010,plain,
% 19.38/3.00      ( sP0_iProver_split(sP3_iProver_split(k1_xboole_0)) = k3_subset_1(sP1_iProver_split,sP1_iProver_split) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53009,c_22110]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53195,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,sP0_iProver_split(sP3_iProver_split(k1_xboole_0))),k5_xboole_0(X1,sP2_iProver_split(X2,X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X2))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52427,c_53010]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_30637,plain,
% 19.38/3.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1,c_3559]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3513,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1168,c_2452]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_4352,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1169,c_2452]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_35768,plain,
% 19.38/3.00      ( k5_xboole_0(sP1_iProver_split,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),k5_xboole_0(X0,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split))) ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_3513,c_4352,c_21980,c_32628]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_36507,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))),sP0_iProver_split(k5_xboole_0(sP1_iProver_split,k3_xboole_0(sP1_iProver_split,sP1_iProver_split)))) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_35768,c_19767]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_32688,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sP1_iProver_split))),k5_xboole_0(X0,k5_xboole_0(sK1,X1))) = k3_xboole_0(sK1,sP1_iProver_split) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_32628,c_9572]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_32811,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))),k5_xboole_0(X0,k5_xboole_0(sP1_iProver_split,X1))) = k3_xboole_0(sP1_iProver_split,sP1_iProver_split) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_32688,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_13368,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X3)) = k5_xboole_0(k5_xboole_0(X1,X2),X3) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_12858,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_32812,plain,
% 19.38/3.00      ( sP0_iProver_split(k3_subset_1(sP1_iProver_split,sP1_iProver_split)) = k3_xboole_0(sP1_iProver_split,sP1_iProver_split) ),
% 19.38/3.00      inference(demodulation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_32811,c_13368,c_19767,c_19792,c_22110]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_36753,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))),k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_36507,c_32749,c_32812]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_37956,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))),k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X2)) = k5_xboole_0(sP0_iProver_split(k5_xboole_0(X1,X0)),X2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_36753,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_37976,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))),k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X2)) = k5_xboole_0(X2,sP0_iProver_split(k5_xboole_0(X1,X0))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_36753,c_1169]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_38012,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))),k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X2)) = sP0_iProver_split(k5_xboole_0(X2,k5_xboole_0(X1,X0))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_37976,c_19792,c_36964]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_38042,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(sP0_iProver_split(k5_xboole_0(X1,X2)),X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_37956,c_38012]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53196,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,sP2_iProver_split(X1,X2)),k5_xboole_0(X2,sP3_iProver_split(k1_xboole_0)))) = sP3_iProver_split(k5_xboole_0(X0,X1)) ),
% 19.38/3.00      inference(demodulation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_53195,c_19792,c_30637,c_36964,c_38042,c_52516]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53197,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sP2_iProver_split(X2,X1),sP3_iProver_split(k1_xboole_0))))) = sP3_iProver_split(k5_xboole_0(X0,X2)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53196,c_36964,c_36971,c_44822]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52463,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)),k5_xboole_0(X1,sP2_iProver_split(X2,X0))) = k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_52362,c_1169]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53101,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,sP0_iProver_split(sP3_iProver_split(k1_xboole_0))),k5_xboole_0(X1,sP2_iProver_split(X2,X0))) = k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X2)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52463,c_53010]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53102,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,sP2_iProver_split(X1,X2)),k5_xboole_0(X2,sP3_iProver_split(k1_xboole_0)))) = k5_xboole_0(X0,sP3_iProver_split(X1)) ),
% 19.38/3.00      inference(demodulation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_53101,c_19792,c_36964,c_38042,c_52516]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53103,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sP2_iProver_split(X2,X1),sP3_iProver_split(k1_xboole_0))))) = k5_xboole_0(X0,sP3_iProver_split(X2)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53102,c_36964,c_36971,c_44822]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53198,plain,
% 19.38/3.00      ( sP3_iProver_split(k5_xboole_0(X0,X1)) = k5_xboole_0(X0,sP3_iProver_split(X1)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53197,c_53103]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52647,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))),k5_xboole_0(X2,sP3_iProver_split(X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,sP0_iProver_split(X1))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_52559,c_30637]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_32732,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(sK1,sP1_iProver_split))) = k5_xboole_0(X0,k3_subset_1(sK1,sP1_iProver_split)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_32628,c_2387]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_32763,plain,
% 19.38/3.00      ( k5_xboole_0(sP1_iProver_split,k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sP1_iProver_split))) = k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_32732,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52753,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)) = k5_xboole_0(sP1_iProver_split,sP3_iProver_split(X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52743,c_32763]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52758,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sP3_iProver_split(sP1_iProver_split)) = k5_xboole_0(sP1_iProver_split,sP3_iProver_split(X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52753,c_52755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52759,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sP3_iProver_split(sP1_iProver_split)) = sP0_iProver_split(sP3_iProver_split(X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52758,c_22110]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52853,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,sP0_iProver_split(sP3_iProver_split(X1))),k5_xboole_0(X2,sP3_iProver_split(X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,sP0_iProver_split(X1))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52647,c_52755,c_52759]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52854,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,sP3_iProver_split(X1)),k5_xboole_0(X1,sP3_iProver_split(X2)))) = sP0_iProver_split(k5_xboole_0(X2,X0)) ),
% 19.38/3.00      inference(demodulation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_52853,c_3466,c_19792,c_19924,c_36964,c_38042]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52855,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sP3_iProver_split(X1),sP3_iProver_split(X2))))) = sP2_iProver_split(X0,X2) ),
% 19.38/3.00      inference(demodulation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_52854,c_36964,c_36971,c_44822,c_52348]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53237,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,sP3_iProver_split(k5_xboole_0(sP3_iProver_split(X1),X2))))) = sP2_iProver_split(X0,X2) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53198,c_52855]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52666,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))),k5_xboole_0(X2,sP3_iProver_split(X0))) = k5_xboole_0(X2,sP0_iProver_split(X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_52559,c_1167]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52800,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,sP0_iProver_split(sP3_iProver_split(X1))),k5_xboole_0(X2,sP3_iProver_split(X0))) = k5_xboole_0(X2,sP0_iProver_split(X1)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52666,c_52755,c_52759]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52801,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,sP3_iProver_split(X1)),k5_xboole_0(X1,sP3_iProver_split(X2)))) = sP2_iProver_split(X2,X0) ),
% 19.38/3.00      inference(demodulation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_52800,c_19792,c_36964,c_38042,c_52348]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52802,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sP3_iProver_split(X1),sP3_iProver_split(X2))))) = sP2_iProver_split(X2,X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52801,c_36964,c_36971,c_44822]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53238,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,sP3_iProver_split(k5_xboole_0(sP3_iProver_split(X1),X2))))) = sP2_iProver_split(X2,X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53198,c_52802]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53338,plain,
% 19.38/3.00      ( sP0_iProver_split(sP3_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(sP3_iProver_split(X1),X2))))) = sP2_iProver_split(X2,X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53238,c_53198]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53339,plain,
% 19.38/3.00      ( sP2_iProver_split(X0,X1) = sP2_iProver_split(X1,X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53237,c_53198,c_53338]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52582,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sP3_iProver_split(k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),k5_xboole_0(X0,X1)))) = sP0_iProver_split(X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_9603,c_52559]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53023,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sP3_iProver_split(k5_xboole_0(sP0_iProver_split(sP3_iProver_split(k1_xboole_0)),k5_xboole_0(X0,X1)))) = sP0_iProver_split(X1) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52582,c_53010]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53024,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sP3_iProver_split(sP0_iProver_split(k5_xboole_0(sP3_iProver_split(k1_xboole_0),k5_xboole_0(X1,X0))))) = sP0_iProver_split(X1) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53023,c_48686]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53025,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sP3_iProver_split(sP2_iProver_split(k5_xboole_0(X1,X0),sP3_iProver_split(k1_xboole_0)))) = sP0_iProver_split(X1) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53024,c_52348]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53347,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sP3_iProver_split(sP2_iProver_split(sP3_iProver_split(k1_xboole_0),k5_xboole_0(X1,X0)))) = sP0_iProver_split(X1) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53339,c_53025]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52570,plain,
% 19.38/3.00      ( k5_xboole_0(k1_xboole_0,sP3_iProver_split(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)))) = sP0_iProver_split(X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_8,c_52559]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53057,plain,
% 19.38/3.00      ( k5_xboole_0(k1_xboole_0,sP3_iProver_split(k5_xboole_0(X0,sP0_iProver_split(sP3_iProver_split(k1_xboole_0))))) = sP0_iProver_split(X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52570,c_53010]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53058,plain,
% 19.38/3.00      ( sP3_iProver_split(sP0_iProver_split(k5_xboole_0(X0,sP3_iProver_split(k1_xboole_0)))) = sP0_iProver_split(X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53057,c_1385,c_19792]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53059,plain,
% 19.38/3.00      ( sP3_iProver_split(sP2_iProver_split(sP3_iProver_split(k1_xboole_0),X0)) = sP0_iProver_split(X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53058,c_52348]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53374,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sP0_iProver_split(k5_xboole_0(X1,X0))) = sP0_iProver_split(X1) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53347,c_53059,c_53198]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53375,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sP2_iProver_split(X0,X1)) = sP0_iProver_split(X1) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53374,c_52348]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52581,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),sP3_iProver_split(k5_xboole_0(k5_xboole_0(X2,k3_subset_1(sP1_iProver_split,sP1_iProver_split)),k5_xboole_0(X1,X0)))) = sP0_iProver_split(X2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_10635,c_52559]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53026,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),sP3_iProver_split(k5_xboole_0(k5_xboole_0(X2,sP0_iProver_split(sP3_iProver_split(k1_xboole_0))),k5_xboole_0(X1,X0)))) = sP0_iProver_split(X2) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52581,c_53010]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53027,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),sP3_iProver_split(k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X1,sP0_iProver_split(sP3_iProver_split(k1_xboole_0))),X0)))) = sP0_iProver_split(X2) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53026,c_36964]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53028,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),sP3_iProver_split(sP0_iProver_split(k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,sP3_iProver_split(k1_xboole_0))))))) = sP0_iProver_split(X2) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53027,c_19792,c_38042]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53029,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),sP3_iProver_split(sP2_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,sP3_iProver_split(k1_xboole_0))),X2))) = sP0_iProver_split(X2) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53028,c_52348]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53263,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),sP3_iProver_split(sP2_iProver_split(k5_xboole_0(X0,sP3_iProver_split(k5_xboole_0(X1,k1_xboole_0))),X2))) = sP0_iProver_split(X2) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53198,c_53029]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52636,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = k5_xboole_0(sP3_iProver_split(X0),sP0_iProver_split(X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_52559,c_2423]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52881,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sP0_iProver_split(sP3_iProver_split(X1))) = k5_xboole_0(sP3_iProver_split(X0),sP0_iProver_split(X1)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52636,c_52755,c_52759]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52882,plain,
% 19.38/3.00      ( sP2_iProver_split(sP3_iProver_split(X0),X1) = sP2_iProver_split(X0,sP3_iProver_split(X1)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52881,c_19792,c_52348]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53301,plain,
% 19.38/3.00      ( sP3_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),sP2_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)),sP3_iProver_split(X2)))) = sP0_iProver_split(X2) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53263,c_52882,c_53198]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53302,plain,
% 19.38/3.00      ( sP3_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),sP2_iProver_split(k5_xboole_0(X0,X1),sP3_iProver_split(X2)))) = sP0_iProver_split(X2) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53301,c_5]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53376,plain,
% 19.38/3.00      ( sP3_iProver_split(sP0_iProver_split(sP3_iProver_split(X0))) = sP0_iProver_split(X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53375,c_53302]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52584,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),sP3_iProver_split(k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_12960,c_52559]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53018,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),sP3_iProver_split(sP0_iProver_split(sP3_iProver_split(k1_xboole_0)))) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52584,c_53010]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53019,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),sP3_iProver_split(sP0_iProver_split(sP3_iProver_split(k1_xboole_0)))) = sP2_iProver_split(X0,X1) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53018,c_52348]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53379,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split(k1_xboole_0)) = sP2_iProver_split(X0,X1) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53376,c_53019]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3219,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2))),k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) = sK1 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2452,c_2423]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_31560,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sK2))),k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sK2)))) = sP1_iProver_split ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_3219,c_3219,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_14650,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X1,k3_subset_1(sK1,sK2)),sK1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_6118,c_10732]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5704,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,sK1),k5_xboole_0(k3_subset_1(sK1,sK2),X1)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_5450,c_7]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5460,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,sK1),k5_xboole_0(k3_subset_1(sK1,sK2),X1)) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3228,c_2390]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5726,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),X1) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_5704,c_5460]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_14764,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,k3_xboole_0(sK1,sK2)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_14650,c_5726,c_10748]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_28687,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sK2)),k5_xboole_0(X0,X1)) = k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sK2)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_14764,c_14764,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_31678,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sK2))),k3_xboole_0(sP1_iProver_split,sK2)),sP1_iProver_split) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sK2))),k3_xboole_0(sP1_iProver_split,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_31560,c_28687]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_7762,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(X1,k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7628,c_1169]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_28795,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,X0),k3_xboole_0(sP1_iProver_split,sK2)),k5_xboole_0(X1,k3_subset_1(sK1,sK2))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(sK1,sK2))),k3_xboole_0(sP1_iProver_split,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7762,c_28687]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_22532,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sK2))) = k3_subset_1(sP1_iProver_split,sK2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_22501,c_1]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_26362,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(X0),k3_xboole_0(sP1_iProver_split,sK2)) = k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_22532,c_5374]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_28360,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sK2)),k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sK2))) = k5_xboole_0(X0,X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_28187,c_5511]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_29037,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sK2))),k3_xboole_0(sP1_iProver_split,sK2)) = k5_xboole_0(X1,X0) ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_28795,c_20128,c_21980,c_26362,c_28360]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_28789,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sP1_iProver_split,sK2)),k5_xboole_0(sK1,X1)) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2))),k3_xboole_0(sP1_iProver_split,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_6952,c_28687]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3946,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(k3_subset_1(sK1,sK2),X0)) = k3_xboole_0(sK1,sK2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1,c_3700]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_24190,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),X0)) = k3_xboole_0(sP1_iProver_split,sK2) ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_3946,c_3946,c_20128,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_24252,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),X0))),k3_xboole_0(sP1_iProver_split,sK2)) = X1 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_24190,c_5492]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_10388,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1)),k5_xboole_0(X0,sK1)) = k5_xboole_0(k3_xboole_0(sK1,sK2),X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1683,c_9541]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19539,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,sK1),k5_xboole_0(k3_subset_1(sK1,sK2),sK1)) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_11704,c_10388]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20117,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(X0),k3_xboole_0(sK1,sK2)) = k5_xboole_0(k3_subset_1(sK1,sK2),X0) ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_19539,c_3242,c_5406,c_19649]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19449,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(sK1,X1)))) = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(X1,sK1)),k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_11704,c_5947]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3701,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(sK1,sK2),X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3468,c_1168]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19527,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,X1)),k3_subset_1(sK1,sK2))) = k5_xboole_0(k5_xboole_0(X1,sK1),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_11704,c_3701]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20145,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(sK1,X1),k3_subset_1(sK1,sK2)))) = k5_xboole_0(k5_xboole_0(X1,sK1),k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19527,c_19792,c_19924,c_20128]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19782,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)),sP0_iProver_split(sK1)) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1905,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20031,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)),k1_xboole_0) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20024,c_19782]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2042,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1))) = k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1,c_1905]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19787,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)),sP0_iProver_split(sK1)) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2042,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20034,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)),k1_xboole_0) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20024,c_19787]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19838,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),sP0_iProver_split(k5_xboole_0(sK1,X1))) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7762,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19950,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),sP0_iProver_split(sP0_iProver_split(X1))) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19948,c_19838]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20063,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sK1,sK2)),X1) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20061,c_19950]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20090,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_20063,c_11164]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20099,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1)),k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20031,c_20034,c_20090]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20100,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20099,c_20034]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19832,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,X0),sP0_iProver_split(k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_6952,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20049,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(k3_subset_1(sK1,sK2),X1)) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20040,c_19832]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5798,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_subset_1(sK1,sK2),X0),X1),k5_xboole_0(k5_xboole_0(sK1,X1),X2)) = k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X2) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_5402,c_3228]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3480,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X2,X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2423,c_1168]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5609,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),k5_xboole_0(X1,k3_subset_1(sK1,sK2))) = k5_xboole_0(k5_xboole_0(sK1,X1),X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3523,c_3701]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5263,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),k5_xboole_0(X1,k3_subset_1(sK1,sK2))) = k5_xboole_0(X1,k5_xboole_0(sK1,X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1978,c_1169]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5615,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(sK1,X1)) = k5_xboole_0(k5_xboole_0(sK1,X0),X1) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_5609,c_5263]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5823,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(k3_subset_1(sK1,sK2),X1)) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_5798,c_3480,c_5500,c_5615]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20050,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_20049,c_5823]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19818,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),sP0_iProver_split(k5_xboole_0(sK1,X1))) = sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_6966,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19965,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sP0_iProver_split(X0),X1))) = sP0_iProver_split(k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2)))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19818,c_19824,c_19948]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19966,plain,
% 19.38/3.00      ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(sK1,sK2)))) = sP0_iProver_split(k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2)))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19965,c_19897,c_19924]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_11198,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),sK1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7,c_10748]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_7288,plain,
% 19.38/3.00      ( k5_xboole_0(sK1,k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2387,c_5374]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_8692,plain,
% 19.38/3.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),sK1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7288,c_3466]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5988,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X1))) = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1))),k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1974,c_5947]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_6087,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),X1))) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,X1))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_5988,c_5947]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_6088,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X1,X0))) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_6087,c_4247]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3474,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(k3_subset_1(sK1,sK2),X0)) = k5_xboole_0(X0,sK1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1899,c_1168]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5585,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) = k5_xboole_0(X0,k5_xboole_0(sK1,X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3705,c_3523]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_6089,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),sK1) = k5_xboole_0(X1,k5_xboole_0(sK1,X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_6088,c_3474,c_5585]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_8750,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))),sK1) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_8692,c_3589,c_6089]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_11261,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(sK1,sK2)) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_11198,c_8750]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19967,plain,
% 19.38/3.00      ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)))) = sP0_iProver_split(k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2)))) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_19966,c_11261]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20052,plain,
% 19.38/3.00      ( sP0_iProver_split(sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)))) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20050,c_19967]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20104,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2)))) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(X0,X1)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20100,c_20052]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20146,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,sK1),k5_xboole_0(k3_xboole_0(sK1,sK2),X1)) = k5_xboole_0(k5_xboole_0(X1,X0),k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(demodulation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_20145,c_19792,c_20004,c_20104,c_20128]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_8539,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,sK1),k5_xboole_0(k3_xboole_0(sK1,sK2),X1)) = k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7286,c_3228]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20147,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_subset_1(sK1,sK2)) = k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sK1,sK2),X0)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_20146,c_8539]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20302,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,sK1),k5_xboole_0(k3_subset_1(sK1,sK2),sK1)) = k5_xboole_0(X0,k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(demodulation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_19449,c_19792,c_19908,c_20004,c_20128,c_20147]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20303,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(X0),k3_xboole_0(sK1,sK2)) = k5_xboole_0(X0,k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_20302,c_3242,c_19649]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_22756,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(X0),k3_xboole_0(sP1_iProver_split,sK2)) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),X0) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_20117,c_20303,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_22788,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sP1_iProver_split,sK2),X0))) = k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_22756,c_5374]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_24322,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sK2)),k3_xboole_0(sP1_iProver_split,sK2)) = X0 ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_24252,c_22788]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_29047,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sK2))),k3_xboole_0(sP1_iProver_split,sK2)) = k5_xboole_0(X1,k5_xboole_0(sP1_iProver_split,X0)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_28789,c_21980,c_24322]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_29048,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sP1_iProver_split,sK2))),k3_xboole_0(sP1_iProver_split,sK2)) = sP0_iProver_split(k5_xboole_0(X1,X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_29047,c_19792,c_22110]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_31818,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,X1),sP1_iProver_split) = sP0_iProver_split(k5_xboole_0(X0,X1)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_31678,c_29037,c_29048]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53380,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,X1)) = sP2_iProver_split(X0,X1) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_53379,c_19994,c_31818]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52577,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split))) = k5_xboole_0(k1_xboole_0,sP3_iProver_split(X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_2408,c_52559]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53040,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,sP0_iProver_split(sP3_iProver_split(k1_xboole_0)))) = k5_xboole_0(k1_xboole_0,sP3_iProver_split(X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52577,c_53010]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19502,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,X1)))) = k5_xboole_0(k5_xboole_0(X1,sK1),k5_xboole_0(sK1,X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_11704,c_3471]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19508,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),k5_xboole_0(sK1,X1)))) = k5_xboole_0(sK1,k5_xboole_0(X1,sK1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_11704,c_1974]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19538,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,X0)),k5_xboole_0(k3_subset_1(sK1,sK2),X1)) = k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X1),k5_xboole_0(X0,sK1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_11704,c_3471]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20118,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),X0),sP0_iProver_split(X1)) = k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sK1,sK2),X0)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_19538,c_3105,c_19649]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20188,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sK1,sK2),X0)))) = sP0_iProver_split(k5_xboole_0(X1,sK1)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19508,c_20118,c_20128]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_18882,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sK1,sK2),X0))) = k5_xboole_0(X1,k3_subset_1(sK1,sK2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_7805,c_1169]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20189,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = sP0_iProver_split(k5_xboole_0(X0,sK1)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_20188,c_18882]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_2048,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = k5_xboole_0(sK1,k5_xboole_0(X0,sK1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1899,c_1905]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20190,plain,
% 19.38/3.00      ( k5_xboole_0(k3_subset_1(sK1,sK2),k5_xboole_0(X0,k3_subset_1(sK1,sK2))) = sP0_iProver_split(sP0_iProver_split(X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20189,c_2048,c_19649]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20197,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,sK1))) = sP0_iProver_split(k5_xboole_0(X1,sP0_iProver_split(X0))) ),
% 19.38/3.00      inference(demodulation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_19502,c_19792,c_19824,c_20004,c_20128,c_20190]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20198,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,sK1))) = k5_xboole_0(X1,X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20197,c_19792,c_20061]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20199,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,sP0_iProver_split(X1))) = k5_xboole_0(X1,X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_20198,c_19649]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53041,plain,
% 19.38/3.00      ( k5_xboole_0(sP3_iProver_split(k1_xboole_0),X0) = sP3_iProver_split(X0) ),
% 19.38/3.00      inference(demodulation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_53040,c_1385,c_19792,c_20199,c_20247]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_32937,plain,
% 19.38/3.00      ( k5_xboole_0(sP1_iProver_split,k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),X0)) = k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X0) ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_5196,c_5196,c_21980,c_32628]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52586,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),k3_subset_1(sP1_iProver_split,sP1_iProver_split)),sP3_iProver_split(sP1_iProver_split)) = sP0_iProver_split(k3_subset_1(sP1_iProver_split,sP1_iProver_split)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_32937,c_52559]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53012,plain,
% 19.38/3.00      ( sP0_iProver_split(sP3_iProver_split(k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),sP0_iProver_split(sP3_iProver_split(k1_xboole_0))))) = sP0_iProver_split(sP0_iProver_split(sP3_iProver_split(k1_xboole_0))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52586,c_52759,c_53010]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_32728,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sK1,sP1_iProver_split),k5_xboole_0(sK1,X0)) = k5_xboole_0(X0,k3_subset_1(sK1,sP1_iProver_split)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_32628,c_3468]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_32767,plain,
% 19.38/3.00      ( k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),sP0_iProver_split(X0)) = k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_32728,c_20128,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53013,plain,
% 19.38/3.00      ( sP0_iProver_split(sP3_iProver_split(k5_xboole_0(sP3_iProver_split(k1_xboole_0),k3_subset_1(sP1_iProver_split,sP1_iProver_split)))) = sP3_iProver_split(k1_xboole_0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53012,c_20061,c_32767]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53042,plain,
% 19.38/3.00      ( sP0_iProver_split(sP3_iProver_split(sP3_iProver_split(k3_subset_1(sP1_iProver_split,sP1_iProver_split)))) = sP3_iProver_split(k1_xboole_0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53041,c_53013]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53045,plain,
% 19.38/3.00      ( sP0_iProver_split(sP3_iProver_split(sP3_iProver_split(sP0_iProver_split(sP3_iProver_split(k1_xboole_0))))) = sP3_iProver_split(k1_xboole_0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53042,c_53010]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53378,plain,
% 19.38/3.00      ( sP0_iProver_split(sP3_iProver_split(sP0_iProver_split(k1_xboole_0))) = sP3_iProver_split(k1_xboole_0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53376,c_53045]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53381,plain,
% 19.38/3.00      ( sP0_iProver_split(sP3_iProver_split(sP1_iProver_split)) = sP3_iProver_split(k1_xboole_0) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_53378,c_19994]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52597,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),sP3_iProver_split(X0)) = sP0_iProver_split(k3_subset_1(sP1_iProver_split,sP1_iProver_split)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_8,c_52559]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52996,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),sP3_iProver_split(X0)) = sP0_iProver_split(sP3_iProver_split(sP1_iProver_split)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52597,c_52755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52997,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sP3_iProver_split(X0)) = sP0_iProver_split(sP3_iProver_split(sP1_iProver_split)) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_52996,c_5]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53383,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sP3_iProver_split(X0)) = sP3_iProver_split(k1_xboole_0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53381,c_52997]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52675,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)),sP0_iProver_split(X0)) = k5_xboole_0(X1,sP3_iProver_split(X1)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_52559,c_3228]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52770,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(sP3_iProver_split(X0)),sP0_iProver_split(X0)) = k5_xboole_0(X1,sP3_iProver_split(X1)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52675,c_52755,c_52759]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52771,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sP3_iProver_split(X0)) = sP4_iProver_split ),
% 19.38/3.00      inference(splitting,
% 19.38/3.00                [splitting(split),new_symbols(definition,[sP4_iProver_split])],
% 19.38/3.00                [c_52770]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53384,plain,
% 19.38/3.00      ( sP3_iProver_split(k1_xboole_0) = sP4_iProver_split ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53383,c_52771]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53403,plain,
% 19.38/3.00      ( k3_subset_1(sP1_iProver_split,sP1_iProver_split) = sP0_iProver_split(sP4_iProver_split) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53384,c_53010]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53404,plain,
% 19.38/3.00      ( sP3_iProver_split(sP1_iProver_split) = sP0_iProver_split(sP4_iProver_split) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53403,c_52755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53412,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sP0_iProver_split(sP4_iProver_split)) = sP0_iProver_split(sP3_iProver_split(X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53404,c_52759]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53797,plain,
% 19.38/3.00      ( k5_xboole_0(sP2_iProver_split(X0,X1),sP0_iProver_split(sP3_iProver_split(k5_xboole_0(X1,X0)))) = sP0_iProver_split(sP0_iProver_split(k3_xboole_0(sP1_iProver_split,sP1_iProver_split))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52268,c_53380,c_53403,c_53412]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52273,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,X1),sP0_iProver_split(k3_subset_1(sP1_iProver_split,sP1_iProver_split)))) = k5_xboole_0(sP0_iProver_split(k5_xboole_0(X1,X0)),k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_48661,c_36753]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53385,plain,
% 19.38/3.00      ( sP0_iProver_split(sP3_iProver_split(sP1_iProver_split)) = sP4_iProver_split ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53384,c_53381]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53439,plain,
% 19.38/3.00      ( sP0_iProver_split(sP0_iProver_split(sP4_iProver_split)) = sP4_iProver_split ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53385,c_53404]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52418,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)),sP2_iProver_split(X1,X0))) = k5_xboole_0(sP0_iProver_split(X2),k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_52362,c_43653]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53522,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1))) = sP2_iProver_split(sP0_iProver_split(sP3_iProver_split(X2)),sP2_iProver_split(X1,X2)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52418,c_53380,c_53403,c_53412]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52420,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(k5_xboole_0(X0,k3_subset_1(sP1_iProver_split,sP1_iProver_split)),sP2_iProver_split(X1,X0))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1)),sP0_iProver_split(X2)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_52362,c_36749]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53517,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1)),sP0_iProver_split(X0)) = sP2_iProver_split(sP0_iProver_split(sP3_iProver_split(X2)),sP2_iProver_split(X1,X2)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52420,c_53380,c_53403,c_53412]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_32980,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1)),k5_xboole_0(X0,sP1_iProver_split)) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_32937,c_9541]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19773,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sP0_iProver_split(k1_xboole_0)) = sP0_iProver_split(X0) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1385,c_19755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_19995,plain,
% 19.38/3.00      ( k5_xboole_0(X0,sP1_iProver_split) = sP0_iProver_split(X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_19994,c_19773]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_33032,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1)),sP0_iProver_split(X0)) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),X1) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_32980,c_19995]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53518,plain,
% 19.38/3.00      ( sP2_iProver_split(sP0_iProver_split(sP3_iProver_split(X0)),sP2_iProver_split(X1,X0)) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),X1) ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_53517,c_33032]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53523,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1))) = k5_xboole_0(sP0_iProver_split(sP4_iProver_split),X1) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53522,c_53403,c_53518]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_7037,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),X1)),k5_xboole_0(k3_subset_1(sK1,sK2),X1)) = k5_xboole_0(X0,sK1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_5368,c_3471]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_46827,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1)),k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),X1)) = sP0_iProver_split(X0) ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_7037,c_7037,c_19649,c_21980,c_32628]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_46967,plain,
% 19.38/3.00      ( k5_xboole_0(sP0_iProver_split(X0),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sP1_iProver_split,sP1_iProver_split),X1))) = k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),X1) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_46827,c_12858]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53524,plain,
% 19.38/3.00      ( sP2_iProver_split(X0,sP4_iProver_split) = sP0_iProver_split(sP3_iProver_split(X0)) ),
% 19.38/3.00      inference(demodulation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_53523,c_19896,c_19924,c_46967,c_52348,c_52516]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53741,plain,
% 19.38/3.00      ( k5_xboole_0(sP2_iProver_split(X0,X1),k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) = sP0_iProver_split(sP3_iProver_split(k5_xboole_0(X1,X0))) ),
% 19.38/3.00      inference(demodulation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_52273,c_53380,c_53403,c_53439,c_53524]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53402,plain,
% 19.38/3.00      ( k5_xboole_0(sP4_iProver_split,X0) = sP3_iProver_split(X0) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53384,c_53041]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3473,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,X1)) = k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sK1,sK2),X0)) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1894,c_1168]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_4298,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(sK1,X0),k5_xboole_0(X1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_subset_1(sK1,sK2))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_3468,c_1169]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_5029,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK1,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_subset_1(sK1,sK2))) ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_4298,c_1]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_35341,plain,
% 19.38/3.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(sP1_iProver_split,sP1_iProver_split)),k5_xboole_0(sP1_iProver_split,X1)) = k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),X0)) ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_3473,c_5029,c_21980,c_32628]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_35342,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sP1_iProver_split,sP1_iProver_split)))) = k5_xboole_0(X1,k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_35341,c_19824,c_22110]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52749,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(k3_subset_1(sP1_iProver_split,sP1_iProver_split),X1)) = sP0_iProver_split(k5_xboole_0(X1,sP3_iProver_split(X0))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52743,c_35342]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52763,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(sP3_iProver_split(sP1_iProver_split),X1)) = sP0_iProver_split(k5_xboole_0(X1,sP3_iProver_split(X0))) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52749,c_52755]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52764,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(sP3_iProver_split(sP1_iProver_split),X1)) = sP2_iProver_split(sP3_iProver_split(X0),X1) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52763,c_52348]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_52883,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(sP3_iProver_split(sP1_iProver_split),X1)) = sP2_iProver_split(X0,sP3_iProver_split(X1)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_52882,c_52764]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53409,plain,
% 19.38/3.00      ( k5_xboole_0(X0,k5_xboole_0(sP0_iProver_split(sP4_iProver_split),X1)) = sP2_iProver_split(X0,sP3_iProver_split(X1)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53404,c_52883]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53416,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,k5_xboole_0(sP4_iProver_split,X1))) = sP2_iProver_split(X0,sP3_iProver_split(X1)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53409,c_19792,c_19924]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53420,plain,
% 19.38/3.00      ( sP0_iProver_split(k5_xboole_0(X0,sP3_iProver_split(X1))) = sP2_iProver_split(X0,sP3_iProver_split(X1)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53402,c_53416]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53421,plain,
% 19.38/3.00      ( sP0_iProver_split(sP3_iProver_split(k5_xboole_0(X0,X1))) = sP2_iProver_split(X0,sP3_iProver_split(X1)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53420,c_53198,c_53380]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53742,plain,
% 19.38/3.00      ( k5_xboole_0(sP2_iProver_split(X0,X1),k3_xboole_0(sP1_iProver_split,sP1_iProver_split)) = sP2_iProver_split(X1,sP3_iProver_split(X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53741,c_53421]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53743,plain,
% 19.38/3.00      ( sP3_iProver_split(sP2_iProver_split(X0,X1)) = sP2_iProver_split(X1,sP3_iProver_split(X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53742,c_52743]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53745,plain,
% 19.38/3.00      ( sP0_iProver_split(sP3_iProver_split(k5_xboole_0(X0,X1))) = sP3_iProver_split(sP2_iProver_split(X1,X0)) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53743,c_53421]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53798,plain,
% 19.38/3.00      ( sP0_iProver_split(sP0_iProver_split(k3_xboole_0(sP1_iProver_split,sP1_iProver_split))) = sP4_iProver_split ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_53797,c_52771,c_53745]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_53799,plain,
% 19.38/3.00      ( k3_xboole_0(sP1_iProver_split,sP1_iProver_split) = sP4_iProver_split ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_53798,c_32812,c_33423]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1147,plain,
% 19.38/3.00      ( k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) | r1_tarski(sK2,X0) = iProver_top ),
% 19.38/3.00      inference(predicate_to_equality,[status(thm)],[c_771]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1258,plain,
% 19.38/3.00      ( r1_tarski(sK2,sK1) = iProver_top ),
% 19.38/3.00      inference(equality_resolution,[status(thm)],[c_1147]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_3115,plain,
% 19.38/3.00      ( k3_xboole_0(sK2,sK1) = sK2 ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1258,c_1155]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_66861,plain,
% 19.38/3.00      ( sP4_iProver_split = sP1_iProver_split ),
% 19.38/3.00      inference(light_normalisation,
% 19.38/3.00                [status(thm)],
% 19.38/3.00                [c_3115,c_3115,c_21980,c_32628,c_53799]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_81493,plain,
% 19.38/3.00      ( k3_xboole_0(sP1_iProver_split,sP1_iProver_split) = sP1_iProver_split ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_53799,c_53799,c_66861]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_81494,plain,
% 19.38/3.00      ( k3_subset_1(sP1_iProver_split,sP1_iProver_split) = sP0_iProver_split(sP1_iProver_split) ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_81493,c_33423]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_81495,plain,
% 19.38/3.00      ( k3_subset_1(sP1_iProver_split,sP1_iProver_split) = k1_xboole_0 ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_81494,c_23783,c_53403]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_20,negated_conjecture,
% 19.38/3.00      ( ~ r1_tarski(k3_subset_1(sK1,sK2),sK2) | k2_subset_1(sK1) != sK2 ),
% 19.38/3.00      inference(cnf_transformation,[],[f56]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1153,plain,
% 19.38/3.00      ( k2_subset_1(sK1) != sK2
% 19.38/3.00      | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
% 19.38/3.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_1157,plain,
% 19.38/3.00      ( sK2 != sK1 | r1_tarski(k3_subset_1(sK1,sK2),sK2) != iProver_top ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_1153,c_17]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_32745,plain,
% 19.38/3.00      ( sP1_iProver_split != sK1
% 19.38/3.00      | r1_tarski(k3_subset_1(sK1,sP1_iProver_split),sP1_iProver_split) != iProver_top ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_32628,c_1157]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_32750,plain,
% 19.38/3.00      ( sP1_iProver_split != sP1_iProver_split
% 19.38/3.00      | r1_tarski(k3_subset_1(sP1_iProver_split,sP1_iProver_split),sP1_iProver_split) != iProver_top ),
% 19.38/3.00      inference(light_normalisation,[status(thm)],[c_32745,c_21980]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_32751,plain,
% 19.38/3.00      ( r1_tarski(k3_subset_1(sP1_iProver_split,sP1_iProver_split),sP1_iProver_split) != iProver_top ),
% 19.38/3.00      inference(equality_resolution_simp,[status(thm)],[c_32750]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_82043,plain,
% 19.38/3.00      ( r1_tarski(k1_xboole_0,sP1_iProver_split) != iProver_top ),
% 19.38/3.00      inference(demodulation,[status(thm)],[c_81495,c_32751]) ).
% 19.38/3.00  
% 19.38/3.00  cnf(c_82059,plain,
% 19.38/3.00      ( $false ),
% 19.38/3.00      inference(superposition,[status(thm)],[c_1154,c_82043]) ).
% 19.38/3.00  
% 19.38/3.00  
% 19.38/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.38/3.00  
% 19.38/3.00  ------                               Statistics
% 19.38/3.00  
% 19.38/3.00  ------ General
% 19.38/3.00  
% 19.38/3.00  abstr_ref_over_cycles:                  0
% 19.38/3.00  abstr_ref_under_cycles:                 0
% 19.38/3.00  gc_basic_clause_elim:                   0
% 19.38/3.00  forced_gc_time:                         0
% 19.38/3.00  parsing_time:                           0.015
% 19.38/3.00  unif_index_cands_time:                  0.
% 19.38/3.00  unif_index_add_time:                    0.
% 19.38/3.00  orderings_time:                         0.
% 19.38/3.00  out_proof_time:                         0.029
% 19.38/3.00  total_time:                             2.348
% 19.38/3.00  num_of_symbols:                         51
% 19.38/3.00  num_of_terms:                           142223
% 19.38/3.00  
% 19.38/3.00  ------ Preprocessing
% 19.38/3.00  
% 19.38/3.00  num_of_splits:                          0
% 19.38/3.00  num_of_split_atoms:                     6
% 19.38/3.00  num_of_reused_defs:                     0
% 19.38/3.00  num_eq_ax_congr_red:                    9
% 19.38/3.00  num_of_sem_filtered_clauses:            1
% 19.38/3.00  num_of_subtypes:                        0
% 19.38/3.00  monotx_restored_types:                  0
% 19.38/3.00  sat_num_of_epr_types:                   0
% 19.38/3.00  sat_num_of_non_cyclic_types:            0
% 19.38/3.00  sat_guarded_non_collapsed_types:        0
% 19.38/3.00  num_pure_diseq_elim:                    0
% 19.38/3.00  simp_replaced_by:                       0
% 19.38/3.00  res_preprocessed:                       111
% 19.38/3.00  prep_upred:                             0
% 19.38/3.00  prep_unflattend:                        46
% 19.38/3.00  smt_new_axioms:                         0
% 19.38/3.00  pred_elim_cands:                        1
% 19.38/3.00  pred_elim:                              4
% 19.38/3.00  pred_elim_cl:                           6
% 19.38/3.00  pred_elim_cycles:                       8
% 19.38/3.00  merged_defs:                            14
% 19.38/3.00  merged_defs_ncl:                        0
% 19.38/3.00  bin_hyper_res:                          15
% 19.38/3.00  prep_cycles:                            5
% 19.38/3.00  pred_elim_time:                         0.007
% 19.38/3.00  splitting_time:                         0.
% 19.38/3.00  sem_filter_time:                        0.
% 19.38/3.00  monotx_time:                            0.
% 19.38/3.00  subtype_inf_time:                       0.
% 19.38/3.00  
% 19.38/3.00  ------ Problem properties
% 19.38/3.00  
% 19.38/3.00  clauses:                                17
% 19.38/3.00  conjectures:                            2
% 19.38/3.00  epr:                                    1
% 19.38/3.00  horn:                                   15
% 19.38/3.00  ground:                                 2
% 19.38/3.00  unary:                                  8
% 19.38/3.00  binary:                                 6
% 19.38/3.00  lits:                                   29
% 19.38/3.00  lits_eq:                                18
% 19.38/3.00  fd_pure:                                0
% 19.38/3.00  fd_pseudo:                              0
% 19.38/3.00  fd_cond:                                0
% 19.38/3.00  fd_pseudo_cond:                         0
% 19.38/3.00  ac_symbols:                             1
% 19.38/3.00  
% 19.38/3.00  ------ Propositional Solver
% 19.38/3.00  
% 19.38/3.00  prop_solver_calls:                      39
% 19.38/3.00  prop_fast_solver_calls:                 1975
% 19.38/3.00  smt_solver_calls:                       0
% 19.38/3.00  smt_fast_solver_calls:                  0
% 19.38/3.00  prop_num_of_clauses:                    16338
% 19.38/3.00  prop_preprocess_simplified:             19819
% 19.38/3.00  prop_fo_subsumed:                       6
% 19.38/3.00  prop_solver_time:                       0.
% 19.38/3.00  smt_solver_time:                        0.
% 19.38/3.00  smt_fast_solver_time:                   0.
% 19.38/3.00  prop_fast_solver_time:                  0.
% 19.38/3.00  prop_unsat_core_time:                   0.
% 19.38/3.00  
% 19.38/3.00  ------ QBF
% 19.38/3.00  
% 19.38/3.00  qbf_q_res:                              0
% 19.38/3.00  qbf_num_tautologies:                    0
% 19.38/3.00  qbf_prep_cycles:                        0
% 19.38/3.00  
% 19.38/3.00  ------ BMC1
% 19.38/3.00  
% 19.38/3.00  bmc1_current_bound:                     -1
% 19.38/3.00  bmc1_last_solved_bound:                 -1
% 19.38/3.00  bmc1_unsat_core_size:                   -1
% 19.38/3.00  bmc1_unsat_core_parents_size:           -1
% 19.38/3.00  bmc1_merge_next_fun:                    0
% 19.38/3.00  bmc1_unsat_core_clauses_time:           0.
% 19.38/3.00  
% 19.38/3.00  ------ Instantiation
% 19.38/3.00  
% 19.38/3.00  inst_num_of_clauses:                    4203
% 19.38/3.00  inst_num_in_passive:                    2171
% 19.38/3.00  inst_num_in_active:                     1577
% 19.38/3.00  inst_num_in_unprocessed:                457
% 19.38/3.00  inst_num_of_loops:                      1960
% 19.38/3.00  inst_num_of_learning_restarts:          0
% 19.38/3.00  inst_num_moves_active_passive:          377
% 19.38/3.00  inst_lit_activity:                      0
% 19.38/3.00  inst_lit_activity_moves:                0
% 19.38/3.00  inst_num_tautologies:                   0
% 19.38/3.00  inst_num_prop_implied:                  0
% 19.38/3.00  inst_num_existing_simplified:           0
% 19.38/3.00  inst_num_eq_res_simplified:             0
% 19.38/3.00  inst_num_child_elim:                    0
% 19.38/3.00  inst_num_of_dismatching_blockings:      2222
% 19.38/3.00  inst_num_of_non_proper_insts:           3391
% 19.38/3.00  inst_num_of_duplicates:                 0
% 19.38/3.00  inst_inst_num_from_inst_to_res:         0
% 19.38/3.00  inst_dismatching_checking_time:         0.
% 19.38/3.00  
% 19.38/3.00  ------ Resolution
% 19.38/3.00  
% 19.38/3.00  res_num_of_clauses:                     0
% 19.38/3.00  res_num_in_passive:                     0
% 19.38/3.00  res_num_in_active:                      0
% 19.38/3.00  res_num_of_loops:                       116
% 19.38/3.00  res_forward_subset_subsumed:            763
% 19.38/3.00  res_backward_subset_subsumed:           8
% 19.38/3.00  res_forward_subsumed:                   2
% 19.38/3.00  res_backward_subsumed:                  0
% 19.38/3.00  res_forward_subsumption_resolution:     2
% 19.38/3.00  res_backward_subsumption_resolution:    0
% 19.38/3.00  res_clause_to_clause_subsumption:       78280
% 19.38/3.00  res_orphan_elimination:                 0
% 19.38/3.00  res_tautology_del:                      482
% 19.38/3.00  res_num_eq_res_simplified:              0
% 19.38/3.00  res_num_sel_changes:                    0
% 19.38/3.00  res_moves_from_active_to_pass:          0
% 19.38/3.00  
% 19.38/3.00  ------ Superposition
% 19.38/3.00  
% 19.38/3.00  sup_time_total:                         0.
% 19.38/3.00  sup_time_generating:                    0.
% 19.38/3.00  sup_time_sim_full:                      0.
% 19.38/3.00  sup_time_sim_immed:                     0.
% 19.38/3.00  
% 19.38/3.00  sup_num_of_clauses:                     5589
% 19.38/3.00  sup_num_in_active:                      97
% 19.38/3.00  sup_num_in_passive:                     5492
% 19.38/3.00  sup_num_of_loops:                       390
% 19.38/3.00  sup_fw_superposition:                   15852
% 19.38/3.00  sup_bw_superposition:                   9882
% 19.38/3.00  sup_immediate_simplified:               17922
% 19.38/3.00  sup_given_eliminated:                   20
% 19.38/3.00  comparisons_done:                       0
% 19.38/3.00  comparisons_avoided:                    11
% 19.38/3.00  
% 19.38/3.00  ------ Simplifications
% 19.38/3.00  
% 19.38/3.00  
% 19.38/3.00  sim_fw_subset_subsumed:                 4
% 19.38/3.00  sim_bw_subset_subsumed:                 0
% 19.38/3.00  sim_fw_subsumed:                        1483
% 19.38/3.00  sim_bw_subsumed:                        88
% 19.38/3.00  sim_fw_subsumption_res:                 0
% 19.38/3.00  sim_bw_subsumption_res:                 0
% 19.38/3.00  sim_tautology_del:                      2
% 19.38/3.00  sim_eq_tautology_del:                   6400
% 19.38/3.00  sim_eq_res_simp:                        1
% 19.38/3.00  sim_fw_demodulated:                     16746
% 19.38/3.00  sim_bw_demodulated:                     1167
% 19.38/3.00  sim_light_normalised:                   8837
% 19.38/3.00  sim_joinable_taut:                      439
% 19.38/3.00  sim_joinable_simp:                      0
% 19.38/3.00  sim_ac_normalised:                      0
% 19.38/3.00  sim_smt_subsumption:                    0
% 19.38/3.00  
%------------------------------------------------------------------------------
