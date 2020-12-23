%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0932+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:27 EST 2020

% Result     : Theorem 0.91s
% Output     : CNFRefutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   51 (  93 expanded)
%              Number of clauses        :   22 (  28 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :   14
%              Number of atoms          :  161 ( 289 expanded)
%              Number of equality atoms :   41 (  43 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( r2_hidden(X1,X0)
           => r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1)))
          & r2_hidden(X1,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1)))
          & r2_hidden(X1,X0) )
     => ( ~ r2_hidden(k2_mcart_1(sK2),k11_relat_1(X0,k1_mcart_1(sK2)))
        & r2_hidden(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1)))
            & r2_hidden(X1,X0) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r2_hidden(k2_mcart_1(X1),k11_relat_1(sK1,k1_mcart_1(X1)))
          & r2_hidden(X1,sK1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ~ r2_hidden(k2_mcart_1(sK2),k11_relat_1(sK1,k1_mcart_1(sK2)))
    & r2_hidden(sK2,sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f13,f19,f18])).

fof(f29,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X1) )
     => ( r2_hidden(X0,a_2_0_mcart_1(X1,X2))
      <=> ? [X3] :
            ( k1_mcart_1(X3) = X2
            & k2_mcart_1(X3) = X0
            & m1_subset_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_mcart_1(X1,X2))
      <=> ? [X3] :
            ( k1_mcart_1(X3) = X2
            & k2_mcart_1(X3) = X0
            & m1_subset_1(X3,X1) ) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_mcart_1(X1,X2))
      <=> ? [X3] :
            ( k1_mcart_1(X3) = X2
            & k2_mcart_1(X3) = X0
            & m1_subset_1(X3,X1) ) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f7])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_mcart_1(X1,X2))
          | ! [X3] :
              ( k1_mcart_1(X3) != X2
              | k2_mcart_1(X3) != X0
              | ~ m1_subset_1(X3,X1) ) )
        & ( ? [X3] :
              ( k1_mcart_1(X3) = X2
              & k2_mcart_1(X3) = X0
              & m1_subset_1(X3,X1) )
          | ~ r2_hidden(X0,a_2_0_mcart_1(X1,X2)) ) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_mcart_1(X1,X2))
          | ! [X3] :
              ( k1_mcart_1(X3) != X2
              | k2_mcart_1(X3) != X0
              | ~ m1_subset_1(X3,X1) ) )
        & ( ? [X4] :
              ( k1_mcart_1(X4) = X2
              & k2_mcart_1(X4) = X0
              & m1_subset_1(X4,X1) )
          | ~ r2_hidden(X0,a_2_0_mcart_1(X1,X2)) ) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X1) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_mcart_1(X4) = X2
          & k2_mcart_1(X4) = X0
          & m1_subset_1(X4,X1) )
     => ( k1_mcart_1(sK0(X0,X1,X2)) = X2
        & k2_mcart_1(sK0(X0,X1,X2)) = X0
        & m1_subset_1(sK0(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_mcart_1(X1,X2))
          | ! [X3] :
              ( k1_mcart_1(X3) != X2
              | k2_mcart_1(X3) != X0
              | ~ m1_subset_1(X3,X1) ) )
        & ( ( k1_mcart_1(sK0(X0,X1,X2)) = X2
            & k2_mcart_1(sK0(X0,X1,X2)) = X0
            & m1_subset_1(sK0(X0,X1,X2),X1) )
          | ~ r2_hidden(X0,a_2_0_mcart_1(X1,X2)) ) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_mcart_1(X1,X2))
      | k1_mcart_1(X3) != X2
      | k2_mcart_1(X3) != X0
      | ~ m1_subset_1(X3,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_mcart_1(X1,k1_mcart_1(X3)))
      | k2_mcart_1(X3) != X0
      | ~ m1_subset_1(X3,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X1) ) ),
    inference(equality_resolution,[],[f24])).

fof(f32,plain,(
    ! [X3,X1] :
      ( r2_hidden(k2_mcart_1(X3),a_2_0_mcart_1(X1,k1_mcart_1(X3)))
      | ~ m1_subset_1(X3,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X1) ) ),
    inference(equality_resolution,[],[f31])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    ~ r2_hidden(k2_mcart_1(sK2),k11_relat_1(sK1,k1_mcart_1(sK2))) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] : a_2_0_mcart_1(X0,X1) = k11_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] : a_2_0_mcart_1(X0,X1) = k11_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : a_2_0_mcart_1(X0,X1) = k11_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( a_2_0_mcart_1(X0,X1) = k11_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_8,negated_conjecture,
    ( r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_375,plain,
    ( ~ v1_xboole_0(X0)
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_8])).

cnf(c_376,plain,
    ( ~ v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(k2_mcart_1(X0),a_2_0_mcart_1(X1,k1_mcart_1(X0)))
    | v1_xboole_0(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_206,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(k2_mcart_1(X0),a_2_0_mcart_1(X1,k1_mcart_1(X0)))
    | v1_xboole_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_207,plain,
    ( ~ m1_subset_1(X0,sK1)
    | r2_hidden(k2_mcart_1(X0),a_2_0_mcart_1(sK1,k1_mcart_1(X0)))
    | v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_206])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X0,sK1)
    | r2_hidden(k2_mcart_1(X0),a_2_0_mcart_1(sK1,k1_mcart_1(X0))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_376,c_207])).

cnf(c_1179,plain,
    ( ~ m1_subset_1(sK2,sK1)
    | r2_hidden(k2_mcart_1(sK2),a_2_0_mcart_1(sK1,k1_mcart_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_7,negated_conjecture,
    ( ~ r2_hidden(k2_mcart_1(sK2),k11_relat_1(sK1,k1_mcart_1(sK2))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1118,plain,
    ( r2_hidden(k2_mcart_1(sK2),k11_relat_1(sK1,k1_mcart_1(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( v1_xboole_0(X0)
    | ~ v1_relat_1(X0)
    | k11_relat_1(X0,X1) = a_2_0_mcart_1(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_221,plain,
    ( v1_xboole_0(X0)
    | k11_relat_1(X0,X1) = a_2_0_mcart_1(X0,X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_9])).

cnf(c_222,plain,
    ( v1_xboole_0(sK1)
    | k11_relat_1(sK1,X0) = a_2_0_mcart_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_566,plain,
    ( k11_relat_1(sK1,X0) = a_2_0_mcart_1(sK1,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_376,c_222])).

cnf(c_1124,plain,
    ( r2_hidden(k2_mcart_1(sK2),a_2_0_mcart_1(sK1,k1_mcart_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1118,c_566])).

cnf(c_1150,plain,
    ( ~ r2_hidden(k2_mcart_1(sK2),a_2_0_mcart_1(sK1,k1_mcart_1(sK2))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1124])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_382,plain,
    ( m1_subset_1(X0,X1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_8])).

cnf(c_383,plain,
    ( m1_subset_1(sK2,sK1) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1179,c_1150,c_383])).


%------------------------------------------------------------------------------
