%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1010+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:38 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   57 (  84 expanded)
%              Number of clauses        :   28 (  29 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :   19
%              Number of atoms          :  193 ( 336 expanded)
%              Number of equality atoms :   81 ( 109 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f11])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK4,sK3) != sK2
      & r2_hidden(sK3,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
      & v1_funct_2(sK4,sK1,k1_tarski(sK2))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( k1_funct_1(sK4,sK3) != sK2
    & r2_hidden(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))))
    & v1_funct_2(sK4,sK1,k1_tarski(sK2))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f12,f17])).

fof(f30,plain,(
    r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    v1_funct_2(sK4,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f9])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f29,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f19,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f31,plain,(
    k1_funct_1(sK4,sK3) != sK2 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_9,negated_conjecture,
    ( r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_362,plain,
    ( r2_hidden(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11,negated_conjecture,
    ( v1_funct_2(sK4,sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_149,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_10])).

cnf(c_150,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK4,X2),X1)
    | ~ v1_funct_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_149])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_154,plain,
    ( r2_hidden(k1_funct_1(sK4,X2),X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_funct_2(sK4,X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_150,c_12])).

cnf(c_155,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(k1_funct_1(sK4,X2),X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_154])).

cnf(c_182,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k1_funct_1(sK4,X0),X2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | k1_tarski(sK2) != X2
    | sK1 != X1
    | sK4 != sK4
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_155])).

cnf(c_183,plain,
    ( ~ r2_hidden(X0,sK1)
    | r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2))) != k1_zfmisc_1(k2_zfmisc_1(sK1,k1_tarski(sK2)))
    | k1_xboole_0 = k1_tarski(sK2) ),
    inference(unflattening,[status(thm)],[c_182])).

cnf(c_211,plain,
    ( ~ r2_hidden(X0,sK1)
    | r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2))
    | k1_xboole_0 = k1_tarski(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_183])).

cnf(c_361,plain,
    ( k1_xboole_0 = k1_tarski(sK2)
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_211])).

cnf(c_4,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_142,plain,
    ( k1_xboole_0 = X0
    | o_0_0_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_6])).

cnf(c_143,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_142])).

cnf(c_387,plain,
    ( k1_tarski(sK2) = o_0_0_xboole_0
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_361,c_143])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_137,plain,
    ( k1_tarski(X0) != o_0_0_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_5])).

cnf(c_391,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k1_tarski(sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_387,c_137])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_363,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_622,plain,
    ( k1_funct_1(sK4,X0) = sK2
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_391,c_363])).

cnf(c_633,plain,
    ( k1_funct_1(sK4,sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_362,c_622])).

cnf(c_8,negated_conjecture,
    ( k1_funct_1(sK4,sK3) != sK2 ),
    inference(cnf_transformation,[],[f31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_633,c_8])).


%------------------------------------------------------------------------------
