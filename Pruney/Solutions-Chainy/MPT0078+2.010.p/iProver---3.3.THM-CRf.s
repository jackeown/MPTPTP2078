%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:42 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 455 expanded)
%              Number of clauses        :   54 ( 164 expanded)
%              Number of leaves         :   16 ( 124 expanded)
%              Depth                    :   20
%              Number of atoms          :  150 ( 668 expanded)
%              Number of equality atoms :   96 ( 478 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f20])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f18])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f27,f33])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f16])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
   => ( sK2 != sK4
      & r1_xboole_0(sK4,sK3)
      & r1_xboole_0(sK2,sK3)
      & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( sK2 != sK4
    & r1_xboole_0(sK4,sK3)
    & r1_xboole_0(sK2,sK3)
    & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f22])).

fof(f37,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f34,f33,f33])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f29,f33])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f25,f33,f33])).

fof(f36,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    sK2 != sK4 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_229,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_11,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_89,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK3 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_90,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) ),
    inference(unflattening,[status(thm)],[c_89])).

cnf(c_227,plain,
    ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_90])).

cnf(c_4845,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_229,c_227])).

cnf(c_9,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_231,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_9,c_7])).

cnf(c_4995,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK4,sK4),sK3)) = k4_xboole_0(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4845,c_231])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_230,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5,c_6])).

cnf(c_626,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_7])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_457,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_540,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[status(thm)],[c_231,c_231])).

cnf(c_541,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_540,c_230])).

cnf(c_1772,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_541,c_626])).

cnf(c_1777,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_457,c_1772])).

cnf(c_1869,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1777,c_6])).

cnf(c_1931,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_1869,c_7])).

cnf(c_5017,plain,
    ( k4_xboole_0(sK4,sK3) = sK4 ),
    inference(demodulation,[status(thm)],[c_4995,c_6,c_230,c_626,c_1931])).

cnf(c_6078,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_5017,c_7])).

cnf(c_6150,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(X0,sK3)) = k4_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_0,c_6078])).

cnf(c_13,negated_conjecture,
    ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_459,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13,c_8])).

cnf(c_8187,plain,
    ( k4_xboole_0(sK4,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6150,c_459])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_8865,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k4_xboole_0(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8187,c_1])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_98,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_12])).

cnf(c_99,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(unflattening,[status(thm)],[c_98])).

cnf(c_226,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_99])).

cnf(c_4846,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_229,c_226])).

cnf(c_5121,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK2),sK3)) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4846,c_231])).

cnf(c_5126,plain,
    ( k4_xboole_0(sK2,sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_5121,c_6,c_230,c_626,c_1931])).

cnf(c_6132,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_5126,c_7])).

cnf(c_6258,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(X0,sK3)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_0,c_6132])).

cnf(c_8251,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_13,c_6258])).

cnf(c_8288,plain,
    ( k4_xboole_0(sK2,sK4) = k4_xboole_0(sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_8251,c_6258])).

cnf(c_8289,plain,
    ( k4_xboole_0(sK2,sK4) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8288,c_230])).

cnf(c_8884,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK4,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_8865,c_8289])).

cnf(c_8885,plain,
    ( sK4 = sK2 ),
    inference(demodulation,[status(thm)],[c_8884,c_6])).

cnf(c_147,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_794,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_148,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_239,plain,
    ( sK4 != X0
    | sK2 != X0
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_148])).

cnf(c_446,plain,
    ( sK4 != sK2
    | sK2 = sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_239])).

cnf(c_10,negated_conjecture,
    ( sK2 != sK4 ),
    inference(cnf_transformation,[],[f38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8885,c_794,c_446,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:42:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.04/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/0.99  
% 4.04/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.04/0.99  
% 4.04/0.99  ------  iProver source info
% 4.04/0.99  
% 4.04/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.04/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.04/0.99  git: non_committed_changes: false
% 4.04/0.99  git: last_make_outside_of_git: false
% 4.04/0.99  
% 4.04/0.99  ------ 
% 4.04/0.99  
% 4.04/0.99  ------ Input Options
% 4.04/0.99  
% 4.04/0.99  --out_options                           all
% 4.04/0.99  --tptp_safe_out                         true
% 4.04/0.99  --problem_path                          ""
% 4.04/0.99  --include_path                          ""
% 4.04/0.99  --clausifier                            res/vclausify_rel
% 4.04/0.99  --clausifier_options                    ""
% 4.04/0.99  --stdin                                 false
% 4.04/0.99  --stats_out                             all
% 4.04/0.99  
% 4.04/0.99  ------ General Options
% 4.04/0.99  
% 4.04/0.99  --fof                                   false
% 4.04/0.99  --time_out_real                         305.
% 4.04/0.99  --time_out_virtual                      -1.
% 4.04/0.99  --symbol_type_check                     false
% 4.04/0.99  --clausify_out                          false
% 4.04/0.99  --sig_cnt_out                           false
% 4.04/0.99  --trig_cnt_out                          false
% 4.04/0.99  --trig_cnt_out_tolerance                1.
% 4.04/0.99  --trig_cnt_out_sk_spl                   false
% 4.04/0.99  --abstr_cl_out                          false
% 4.04/0.99  
% 4.04/0.99  ------ Global Options
% 4.04/0.99  
% 4.04/0.99  --schedule                              default
% 4.04/0.99  --add_important_lit                     false
% 4.04/0.99  --prop_solver_per_cl                    1000
% 4.04/0.99  --min_unsat_core                        false
% 4.04/0.99  --soft_assumptions                      false
% 4.04/0.99  --soft_lemma_size                       3
% 4.04/0.99  --prop_impl_unit_size                   0
% 4.04/0.99  --prop_impl_unit                        []
% 4.04/0.99  --share_sel_clauses                     true
% 4.04/0.99  --reset_solvers                         false
% 4.04/0.99  --bc_imp_inh                            [conj_cone]
% 4.04/0.99  --conj_cone_tolerance                   3.
% 4.04/0.99  --extra_neg_conj                        none
% 4.04/0.99  --large_theory_mode                     true
% 4.04/0.99  --prolific_symb_bound                   200
% 4.04/0.99  --lt_threshold                          2000
% 4.04/0.99  --clause_weak_htbl                      true
% 4.04/0.99  --gc_record_bc_elim                     false
% 4.04/0.99  
% 4.04/0.99  ------ Preprocessing Options
% 4.04/0.99  
% 4.04/0.99  --preprocessing_flag                    true
% 4.04/0.99  --time_out_prep_mult                    0.1
% 4.04/0.99  --splitting_mode                        input
% 4.04/0.99  --splitting_grd                         true
% 4.04/0.99  --splitting_cvd                         false
% 4.04/0.99  --splitting_cvd_svl                     false
% 4.04/0.99  --splitting_nvd                         32
% 4.04/0.99  --sub_typing                            true
% 4.04/0.99  --prep_gs_sim                           true
% 4.04/0.99  --prep_unflatten                        true
% 4.04/0.99  --prep_res_sim                          true
% 4.04/0.99  --prep_upred                            true
% 4.04/0.99  --prep_sem_filter                       exhaustive
% 4.04/0.99  --prep_sem_filter_out                   false
% 4.04/0.99  --pred_elim                             true
% 4.04/0.99  --res_sim_input                         true
% 4.04/0.99  --eq_ax_congr_red                       true
% 4.04/0.99  --pure_diseq_elim                       true
% 4.04/0.99  --brand_transform                       false
% 4.04/0.99  --non_eq_to_eq                          false
% 4.04/0.99  --prep_def_merge                        true
% 4.04/0.99  --prep_def_merge_prop_impl              false
% 4.04/0.99  --prep_def_merge_mbd                    true
% 4.04/0.99  --prep_def_merge_tr_red                 false
% 4.04/0.99  --prep_def_merge_tr_cl                  false
% 4.04/0.99  --smt_preprocessing                     true
% 4.04/0.99  --smt_ac_axioms                         fast
% 4.04/0.99  --preprocessed_out                      false
% 4.04/0.99  --preprocessed_stats                    false
% 4.04/0.99  
% 4.04/0.99  ------ Abstraction refinement Options
% 4.04/0.99  
% 4.04/0.99  --abstr_ref                             []
% 4.04/0.99  --abstr_ref_prep                        false
% 4.04/0.99  --abstr_ref_until_sat                   false
% 4.04/0.99  --abstr_ref_sig_restrict                funpre
% 4.04/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.04/0.99  --abstr_ref_under                       []
% 4.04/0.99  
% 4.04/0.99  ------ SAT Options
% 4.04/0.99  
% 4.04/0.99  --sat_mode                              false
% 4.04/0.99  --sat_fm_restart_options                ""
% 4.04/0.99  --sat_gr_def                            false
% 4.04/0.99  --sat_epr_types                         true
% 4.04/0.99  --sat_non_cyclic_types                  false
% 4.04/0.99  --sat_finite_models                     false
% 4.04/0.99  --sat_fm_lemmas                         false
% 4.04/0.99  --sat_fm_prep                           false
% 4.04/0.99  --sat_fm_uc_incr                        true
% 4.04/0.99  --sat_out_model                         small
% 4.04/0.99  --sat_out_clauses                       false
% 4.04/0.99  
% 4.04/0.99  ------ QBF Options
% 4.04/0.99  
% 4.04/0.99  --qbf_mode                              false
% 4.04/0.99  --qbf_elim_univ                         false
% 4.04/0.99  --qbf_dom_inst                          none
% 4.04/0.99  --qbf_dom_pre_inst                      false
% 4.04/0.99  --qbf_sk_in                             false
% 4.04/0.99  --qbf_pred_elim                         true
% 4.04/0.99  --qbf_split                             512
% 4.04/0.99  
% 4.04/0.99  ------ BMC1 Options
% 4.04/0.99  
% 4.04/0.99  --bmc1_incremental                      false
% 4.04/0.99  --bmc1_axioms                           reachable_all
% 4.04/0.99  --bmc1_min_bound                        0
% 4.04/0.99  --bmc1_max_bound                        -1
% 4.04/0.99  --bmc1_max_bound_default                -1
% 4.04/0.99  --bmc1_symbol_reachability              true
% 4.04/0.99  --bmc1_property_lemmas                  false
% 4.04/0.99  --bmc1_k_induction                      false
% 4.04/0.99  --bmc1_non_equiv_states                 false
% 4.04/0.99  --bmc1_deadlock                         false
% 4.04/0.99  --bmc1_ucm                              false
% 4.04/0.99  --bmc1_add_unsat_core                   none
% 4.04/0.99  --bmc1_unsat_core_children              false
% 4.04/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.04/0.99  --bmc1_out_stat                         full
% 4.04/0.99  --bmc1_ground_init                      false
% 4.04/0.99  --bmc1_pre_inst_next_state              false
% 4.04/0.99  --bmc1_pre_inst_state                   false
% 4.04/0.99  --bmc1_pre_inst_reach_state             false
% 4.04/0.99  --bmc1_out_unsat_core                   false
% 4.04/0.99  --bmc1_aig_witness_out                  false
% 4.04/0.99  --bmc1_verbose                          false
% 4.04/0.99  --bmc1_dump_clauses_tptp                false
% 4.04/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.04/0.99  --bmc1_dump_file                        -
% 4.04/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.04/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.04/0.99  --bmc1_ucm_extend_mode                  1
% 4.04/0.99  --bmc1_ucm_init_mode                    2
% 4.04/0.99  --bmc1_ucm_cone_mode                    none
% 4.04/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.04/0.99  --bmc1_ucm_relax_model                  4
% 4.04/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.04/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.04/0.99  --bmc1_ucm_layered_model                none
% 4.04/0.99  --bmc1_ucm_max_lemma_size               10
% 4.04/0.99  
% 4.04/0.99  ------ AIG Options
% 4.04/0.99  
% 4.04/0.99  --aig_mode                              false
% 4.04/0.99  
% 4.04/0.99  ------ Instantiation Options
% 4.04/0.99  
% 4.04/0.99  --instantiation_flag                    true
% 4.04/0.99  --inst_sos_flag                         true
% 4.04/0.99  --inst_sos_phase                        true
% 4.04/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.04/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.04/0.99  --inst_lit_sel_side                     num_symb
% 4.04/0.99  --inst_solver_per_active                1400
% 4.04/0.99  --inst_solver_calls_frac                1.
% 4.04/0.99  --inst_passive_queue_type               priority_queues
% 4.04/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.04/0.99  --inst_passive_queues_freq              [25;2]
% 4.04/0.99  --inst_dismatching                      true
% 4.04/0.99  --inst_eager_unprocessed_to_passive     true
% 4.04/0.99  --inst_prop_sim_given                   true
% 4.04/0.99  --inst_prop_sim_new                     false
% 4.04/0.99  --inst_subs_new                         false
% 4.04/0.99  --inst_eq_res_simp                      false
% 4.04/0.99  --inst_subs_given                       false
% 4.04/0.99  --inst_orphan_elimination               true
% 4.04/0.99  --inst_learning_loop_flag               true
% 4.04/0.99  --inst_learning_start                   3000
% 4.04/0.99  --inst_learning_factor                  2
% 4.04/0.99  --inst_start_prop_sim_after_learn       3
% 4.04/0.99  --inst_sel_renew                        solver
% 4.04/0.99  --inst_lit_activity_flag                true
% 4.04/0.99  --inst_restr_to_given                   false
% 4.04/0.99  --inst_activity_threshold               500
% 4.04/0.99  --inst_out_proof                        true
% 4.04/0.99  
% 4.04/0.99  ------ Resolution Options
% 4.04/0.99  
% 4.04/0.99  --resolution_flag                       true
% 4.04/0.99  --res_lit_sel                           adaptive
% 4.04/0.99  --res_lit_sel_side                      none
% 4.04/0.99  --res_ordering                          kbo
% 4.04/0.99  --res_to_prop_solver                    active
% 4.04/0.99  --res_prop_simpl_new                    false
% 4.04/0.99  --res_prop_simpl_given                  true
% 4.04/0.99  --res_passive_queue_type                priority_queues
% 4.04/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.04/0.99  --res_passive_queues_freq               [15;5]
% 4.04/0.99  --res_forward_subs                      full
% 4.04/0.99  --res_backward_subs                     full
% 4.04/0.99  --res_forward_subs_resolution           true
% 4.04/0.99  --res_backward_subs_resolution          true
% 4.04/0.99  --res_orphan_elimination                true
% 4.04/0.99  --res_time_limit                        2.
% 4.04/0.99  --res_out_proof                         true
% 4.04/0.99  
% 4.04/0.99  ------ Superposition Options
% 4.04/0.99  
% 4.04/0.99  --superposition_flag                    true
% 4.04/0.99  --sup_passive_queue_type                priority_queues
% 4.04/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.04/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.04/0.99  --demod_completeness_check              fast
% 4.04/0.99  --demod_use_ground                      true
% 4.04/0.99  --sup_to_prop_solver                    passive
% 4.04/0.99  --sup_prop_simpl_new                    true
% 4.04/0.99  --sup_prop_simpl_given                  true
% 4.04/0.99  --sup_fun_splitting                     true
% 4.04/0.99  --sup_smt_interval                      50000
% 4.04/0.99  
% 4.04/0.99  ------ Superposition Simplification Setup
% 4.04/0.99  
% 4.04/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.04/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.04/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.04/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.04/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.04/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.04/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.04/0.99  --sup_immed_triv                        [TrivRules]
% 4.04/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/0.99  --sup_immed_bw_main                     []
% 4.04/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.04/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.04/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/0.99  --sup_input_bw                          []
% 4.04/0.99  
% 4.04/0.99  ------ Combination Options
% 4.04/0.99  
% 4.04/0.99  --comb_res_mult                         3
% 4.04/0.99  --comb_sup_mult                         2
% 4.04/0.99  --comb_inst_mult                        10
% 4.04/0.99  
% 4.04/0.99  ------ Debug Options
% 4.04/0.99  
% 4.04/0.99  --dbg_backtrace                         false
% 4.04/0.99  --dbg_dump_prop_clauses                 false
% 4.04/0.99  --dbg_dump_prop_clauses_file            -
% 4.04/0.99  --dbg_out_stat                          false
% 4.04/0.99  ------ Parsing...
% 4.04/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.04/0.99  
% 4.04/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.04/0.99  
% 4.04/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.04/0.99  
% 4.04/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.04/0.99  ------ Proving...
% 4.04/0.99  ------ Problem Properties 
% 4.04/0.99  
% 4.04/0.99  
% 4.04/0.99  clauses                                 13
% 4.04/0.99  conjectures                             2
% 4.04/0.99  EPR                                     1
% 4.04/0.99  Horn                                    12
% 4.04/0.99  unary                                   11
% 4.04/0.99  binary                                  2
% 4.04/0.99  lits                                    15
% 4.04/0.99  lits eq                                 10
% 4.04/0.99  fd_pure                                 0
% 4.04/0.99  fd_pseudo                               0
% 4.04/0.99  fd_cond                                 1
% 4.04/0.99  fd_pseudo_cond                          0
% 4.04/0.99  AC symbols                              0
% 4.04/0.99  
% 4.04/0.99  ------ Schedule dynamic 5 is on 
% 4.04/0.99  
% 4.04/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.04/0.99  
% 4.04/0.99  
% 4.04/0.99  ------ 
% 4.04/0.99  Current options:
% 4.04/0.99  ------ 
% 4.04/0.99  
% 4.04/0.99  ------ Input Options
% 4.04/0.99  
% 4.04/0.99  --out_options                           all
% 4.04/0.99  --tptp_safe_out                         true
% 4.04/0.99  --problem_path                          ""
% 4.04/0.99  --include_path                          ""
% 4.04/0.99  --clausifier                            res/vclausify_rel
% 4.04/0.99  --clausifier_options                    ""
% 4.04/0.99  --stdin                                 false
% 4.04/0.99  --stats_out                             all
% 4.04/0.99  
% 4.04/0.99  ------ General Options
% 4.04/0.99  
% 4.04/0.99  --fof                                   false
% 4.04/0.99  --time_out_real                         305.
% 4.04/0.99  --time_out_virtual                      -1.
% 4.04/0.99  --symbol_type_check                     false
% 4.04/0.99  --clausify_out                          false
% 4.04/0.99  --sig_cnt_out                           false
% 4.04/0.99  --trig_cnt_out                          false
% 4.04/0.99  --trig_cnt_out_tolerance                1.
% 4.04/0.99  --trig_cnt_out_sk_spl                   false
% 4.04/0.99  --abstr_cl_out                          false
% 4.04/0.99  
% 4.04/0.99  ------ Global Options
% 4.04/0.99  
% 4.04/0.99  --schedule                              default
% 4.04/0.99  --add_important_lit                     false
% 4.04/0.99  --prop_solver_per_cl                    1000
% 4.04/0.99  --min_unsat_core                        false
% 4.04/0.99  --soft_assumptions                      false
% 4.04/0.99  --soft_lemma_size                       3
% 4.04/0.99  --prop_impl_unit_size                   0
% 4.04/0.99  --prop_impl_unit                        []
% 4.04/0.99  --share_sel_clauses                     true
% 4.04/0.99  --reset_solvers                         false
% 4.04/0.99  --bc_imp_inh                            [conj_cone]
% 4.04/0.99  --conj_cone_tolerance                   3.
% 4.04/0.99  --extra_neg_conj                        none
% 4.04/0.99  --large_theory_mode                     true
% 4.04/0.99  --prolific_symb_bound                   200
% 4.04/0.99  --lt_threshold                          2000
% 4.04/0.99  --clause_weak_htbl                      true
% 4.04/0.99  --gc_record_bc_elim                     false
% 4.04/0.99  
% 4.04/0.99  ------ Preprocessing Options
% 4.04/0.99  
% 4.04/0.99  --preprocessing_flag                    true
% 4.04/0.99  --time_out_prep_mult                    0.1
% 4.04/0.99  --splitting_mode                        input
% 4.04/0.99  --splitting_grd                         true
% 4.04/0.99  --splitting_cvd                         false
% 4.04/0.99  --splitting_cvd_svl                     false
% 4.04/0.99  --splitting_nvd                         32
% 4.04/0.99  --sub_typing                            true
% 4.04/0.99  --prep_gs_sim                           true
% 4.04/0.99  --prep_unflatten                        true
% 4.04/0.99  --prep_res_sim                          true
% 4.04/0.99  --prep_upred                            true
% 4.04/0.99  --prep_sem_filter                       exhaustive
% 4.04/0.99  --prep_sem_filter_out                   false
% 4.04/0.99  --pred_elim                             true
% 4.04/0.99  --res_sim_input                         true
% 4.04/0.99  --eq_ax_congr_red                       true
% 4.04/0.99  --pure_diseq_elim                       true
% 4.04/0.99  --brand_transform                       false
% 4.04/0.99  --non_eq_to_eq                          false
% 4.04/0.99  --prep_def_merge                        true
% 4.04/0.99  --prep_def_merge_prop_impl              false
% 4.04/0.99  --prep_def_merge_mbd                    true
% 4.04/0.99  --prep_def_merge_tr_red                 false
% 4.04/0.99  --prep_def_merge_tr_cl                  false
% 4.04/0.99  --smt_preprocessing                     true
% 4.04/0.99  --smt_ac_axioms                         fast
% 4.04/0.99  --preprocessed_out                      false
% 4.04/0.99  --preprocessed_stats                    false
% 4.04/0.99  
% 4.04/0.99  ------ Abstraction refinement Options
% 4.04/0.99  
% 4.04/0.99  --abstr_ref                             []
% 4.04/0.99  --abstr_ref_prep                        false
% 4.04/0.99  --abstr_ref_until_sat                   false
% 4.04/0.99  --abstr_ref_sig_restrict                funpre
% 4.04/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.04/0.99  --abstr_ref_under                       []
% 4.04/0.99  
% 4.04/0.99  ------ SAT Options
% 4.04/0.99  
% 4.04/0.99  --sat_mode                              false
% 4.04/0.99  --sat_fm_restart_options                ""
% 4.04/0.99  --sat_gr_def                            false
% 4.04/0.99  --sat_epr_types                         true
% 4.04/0.99  --sat_non_cyclic_types                  false
% 4.04/0.99  --sat_finite_models                     false
% 4.04/0.99  --sat_fm_lemmas                         false
% 4.04/0.99  --sat_fm_prep                           false
% 4.04/0.99  --sat_fm_uc_incr                        true
% 4.04/0.99  --sat_out_model                         small
% 4.04/0.99  --sat_out_clauses                       false
% 4.04/0.99  
% 4.04/0.99  ------ QBF Options
% 4.04/0.99  
% 4.04/0.99  --qbf_mode                              false
% 4.04/0.99  --qbf_elim_univ                         false
% 4.04/0.99  --qbf_dom_inst                          none
% 4.04/0.99  --qbf_dom_pre_inst                      false
% 4.04/0.99  --qbf_sk_in                             false
% 4.04/0.99  --qbf_pred_elim                         true
% 4.04/0.99  --qbf_split                             512
% 4.04/0.99  
% 4.04/0.99  ------ BMC1 Options
% 4.04/0.99  
% 4.04/0.99  --bmc1_incremental                      false
% 4.04/0.99  --bmc1_axioms                           reachable_all
% 4.04/0.99  --bmc1_min_bound                        0
% 4.04/0.99  --bmc1_max_bound                        -1
% 4.04/0.99  --bmc1_max_bound_default                -1
% 4.04/0.99  --bmc1_symbol_reachability              true
% 4.04/0.99  --bmc1_property_lemmas                  false
% 4.04/0.99  --bmc1_k_induction                      false
% 4.04/0.99  --bmc1_non_equiv_states                 false
% 4.04/0.99  --bmc1_deadlock                         false
% 4.04/0.99  --bmc1_ucm                              false
% 4.04/0.99  --bmc1_add_unsat_core                   none
% 4.04/0.99  --bmc1_unsat_core_children              false
% 4.04/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.04/0.99  --bmc1_out_stat                         full
% 4.04/0.99  --bmc1_ground_init                      false
% 4.04/0.99  --bmc1_pre_inst_next_state              false
% 4.04/0.99  --bmc1_pre_inst_state                   false
% 4.04/0.99  --bmc1_pre_inst_reach_state             false
% 4.04/0.99  --bmc1_out_unsat_core                   false
% 4.04/0.99  --bmc1_aig_witness_out                  false
% 4.04/0.99  --bmc1_verbose                          false
% 4.04/0.99  --bmc1_dump_clauses_tptp                false
% 4.04/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.04/0.99  --bmc1_dump_file                        -
% 4.04/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.04/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.04/0.99  --bmc1_ucm_extend_mode                  1
% 4.04/0.99  --bmc1_ucm_init_mode                    2
% 4.04/0.99  --bmc1_ucm_cone_mode                    none
% 4.04/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.04/0.99  --bmc1_ucm_relax_model                  4
% 4.04/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.04/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.04/0.99  --bmc1_ucm_layered_model                none
% 4.04/0.99  --bmc1_ucm_max_lemma_size               10
% 4.04/0.99  
% 4.04/0.99  ------ AIG Options
% 4.04/0.99  
% 4.04/0.99  --aig_mode                              false
% 4.04/0.99  
% 4.04/0.99  ------ Instantiation Options
% 4.04/0.99  
% 4.04/0.99  --instantiation_flag                    true
% 4.04/0.99  --inst_sos_flag                         true
% 4.04/0.99  --inst_sos_phase                        true
% 4.04/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.04/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.04/0.99  --inst_lit_sel_side                     none
% 4.04/0.99  --inst_solver_per_active                1400
% 4.04/0.99  --inst_solver_calls_frac                1.
% 4.04/0.99  --inst_passive_queue_type               priority_queues
% 4.04/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.04/0.99  --inst_passive_queues_freq              [25;2]
% 4.04/0.99  --inst_dismatching                      true
% 4.04/0.99  --inst_eager_unprocessed_to_passive     true
% 4.04/0.99  --inst_prop_sim_given                   true
% 4.04/0.99  --inst_prop_sim_new                     false
% 4.04/0.99  --inst_subs_new                         false
% 4.04/0.99  --inst_eq_res_simp                      false
% 4.04/0.99  --inst_subs_given                       false
% 4.04/0.99  --inst_orphan_elimination               true
% 4.04/0.99  --inst_learning_loop_flag               true
% 4.04/0.99  --inst_learning_start                   3000
% 4.04/0.99  --inst_learning_factor                  2
% 4.04/0.99  --inst_start_prop_sim_after_learn       3
% 4.04/0.99  --inst_sel_renew                        solver
% 4.04/0.99  --inst_lit_activity_flag                true
% 4.04/0.99  --inst_restr_to_given                   false
% 4.04/0.99  --inst_activity_threshold               500
% 4.04/0.99  --inst_out_proof                        true
% 4.04/0.99  
% 4.04/0.99  ------ Resolution Options
% 4.04/0.99  
% 4.04/0.99  --resolution_flag                       false
% 4.04/0.99  --res_lit_sel                           adaptive
% 4.04/0.99  --res_lit_sel_side                      none
% 4.04/0.99  --res_ordering                          kbo
% 4.04/0.99  --res_to_prop_solver                    active
% 4.04/0.99  --res_prop_simpl_new                    false
% 4.04/0.99  --res_prop_simpl_given                  true
% 4.04/0.99  --res_passive_queue_type                priority_queues
% 4.04/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.04/0.99  --res_passive_queues_freq               [15;5]
% 4.04/0.99  --res_forward_subs                      full
% 4.04/0.99  --res_backward_subs                     full
% 4.04/0.99  --res_forward_subs_resolution           true
% 4.04/0.99  --res_backward_subs_resolution          true
% 4.04/0.99  --res_orphan_elimination                true
% 4.04/0.99  --res_time_limit                        2.
% 4.04/0.99  --res_out_proof                         true
% 4.04/0.99  
% 4.04/0.99  ------ Superposition Options
% 4.04/0.99  
% 4.04/0.99  --superposition_flag                    true
% 4.04/0.99  --sup_passive_queue_type                priority_queues
% 4.04/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.04/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.04/0.99  --demod_completeness_check              fast
% 4.04/0.99  --demod_use_ground                      true
% 4.04/0.99  --sup_to_prop_solver                    passive
% 4.04/0.99  --sup_prop_simpl_new                    true
% 4.04/0.99  --sup_prop_simpl_given                  true
% 4.04/0.99  --sup_fun_splitting                     true
% 4.04/0.99  --sup_smt_interval                      50000
% 4.04/0.99  
% 4.04/0.99  ------ Superposition Simplification Setup
% 4.04/0.99  
% 4.04/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.04/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.04/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.04/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.04/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.04/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.04/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.04/0.99  --sup_immed_triv                        [TrivRules]
% 4.04/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/0.99  --sup_immed_bw_main                     []
% 4.04/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.04/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.04/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/0.99  --sup_input_bw                          []
% 4.04/0.99  
% 4.04/0.99  ------ Combination Options
% 4.04/0.99  
% 4.04/0.99  --comb_res_mult                         3
% 4.04/0.99  --comb_sup_mult                         2
% 4.04/0.99  --comb_inst_mult                        10
% 4.04/0.99  
% 4.04/0.99  ------ Debug Options
% 4.04/0.99  
% 4.04/0.99  --dbg_backtrace                         false
% 4.04/0.99  --dbg_dump_prop_clauses                 false
% 4.04/0.99  --dbg_dump_prop_clauses_file            -
% 4.04/0.99  --dbg_out_stat                          false
% 4.04/0.99  
% 4.04/0.99  
% 4.04/0.99  
% 4.04/0.99  
% 4.04/0.99  ------ Proving...
% 4.04/0.99  
% 4.04/0.99  
% 4.04/0.99  % SZS status Theorem for theBenchmark.p
% 4.04/0.99  
% 4.04/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.04/0.99  
% 4.04/0.99  fof(f1,axiom,(
% 4.04/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/0.99  
% 4.04/0.99  fof(f24,plain,(
% 4.04/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.04/0.99    inference(cnf_transformation,[],[f1])).
% 4.04/0.99  
% 4.04/0.99  fof(f4,axiom,(
% 4.04/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 4.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/0.99  
% 4.04/0.99  fof(f15,plain,(
% 4.04/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 4.04/0.99    inference(ennf_transformation,[],[f4])).
% 4.04/0.99  
% 4.04/0.99  fof(f20,plain,(
% 4.04/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 4.04/0.99    introduced(choice_axiom,[])).
% 4.04/0.99  
% 4.04/0.99  fof(f21,plain,(
% 4.04/0.99    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 4.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f20])).
% 4.04/0.99  
% 4.04/0.99  fof(f28,plain,(
% 4.04/0.99    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 4.04/0.99    inference(cnf_transformation,[],[f21])).
% 4.04/0.99  
% 4.04/0.99  fof(f3,axiom,(
% 4.04/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 4.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/0.99  
% 4.04/0.99  fof(f13,plain,(
% 4.04/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 4.04/0.99    inference(rectify,[],[f3])).
% 4.04/0.99  
% 4.04/0.99  fof(f14,plain,(
% 4.04/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 4.04/0.99    inference(ennf_transformation,[],[f13])).
% 4.04/0.99  
% 4.04/0.99  fof(f18,plain,(
% 4.04/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 4.04/0.99    introduced(choice_axiom,[])).
% 4.04/0.99  
% 4.04/0.99  fof(f19,plain,(
% 4.04/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 4.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f18])).
% 4.04/0.99  
% 4.04/0.99  fof(f27,plain,(
% 4.04/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 4.04/0.99    inference(cnf_transformation,[],[f19])).
% 4.04/0.99  
% 4.04/0.99  fof(f9,axiom,(
% 4.04/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/0.99  
% 4.04/0.99  fof(f33,plain,(
% 4.04/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.04/0.99    inference(cnf_transformation,[],[f9])).
% 4.04/0.99  
% 4.04/0.99  fof(f40,plain,(
% 4.04/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 4.04/0.99    inference(definition_unfolding,[],[f27,f33])).
% 4.04/0.99  
% 4.04/0.99  fof(f11,conjecture,(
% 4.04/0.99    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 4.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/0.99  
% 4.04/0.99  fof(f12,negated_conjecture,(
% 4.04/0.99    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 4.04/0.99    inference(negated_conjecture,[],[f11])).
% 4.04/0.99  
% 4.04/0.99  fof(f16,plain,(
% 4.04/0.99    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 4.04/0.99    inference(ennf_transformation,[],[f12])).
% 4.04/0.99  
% 4.04/0.99  fof(f17,plain,(
% 4.04/0.99    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 4.04/0.99    inference(flattening,[],[f16])).
% 4.04/0.99  
% 4.04/0.99  fof(f22,plain,(
% 4.04/0.99    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => (sK2 != sK4 & r1_xboole_0(sK4,sK3) & r1_xboole_0(sK2,sK3) & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3))),
% 4.04/0.99    introduced(choice_axiom,[])).
% 4.04/0.99  
% 4.04/0.99  fof(f23,plain,(
% 4.04/0.99    sK2 != sK4 & r1_xboole_0(sK4,sK3) & r1_xboole_0(sK2,sK3) & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3)),
% 4.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f22])).
% 4.04/0.99  
% 4.04/0.99  fof(f37,plain,(
% 4.04/0.99    r1_xboole_0(sK4,sK3)),
% 4.04/0.99    inference(cnf_transformation,[],[f23])).
% 4.04/0.99  
% 4.04/0.99  fof(f10,axiom,(
% 4.04/0.99    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 4.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/0.99  
% 4.04/0.99  fof(f34,plain,(
% 4.04/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 4.04/0.99    inference(cnf_transformation,[],[f10])).
% 4.04/0.99  
% 4.04/0.99  fof(f43,plain,(
% 4.04/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 4.04/0.99    inference(definition_unfolding,[],[f34,f33,f33])).
% 4.04/0.99  
% 4.04/0.99  fof(f7,axiom,(
% 4.04/0.99    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 4.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/0.99  
% 4.04/0.99  fof(f31,plain,(
% 4.04/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 4.04/0.99    inference(cnf_transformation,[],[f7])).
% 4.04/0.99  
% 4.04/0.99  fof(f6,axiom,(
% 4.04/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 4.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/0.99  
% 4.04/0.99  fof(f30,plain,(
% 4.04/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.04/0.99    inference(cnf_transformation,[],[f6])).
% 4.04/0.99  
% 4.04/0.99  fof(f5,axiom,(
% 4.04/0.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 4.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/0.99  
% 4.04/0.99  fof(f29,plain,(
% 4.04/0.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 4.04/0.99    inference(cnf_transformation,[],[f5])).
% 4.04/0.99  
% 4.04/0.99  fof(f42,plain,(
% 4.04/0.99    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 4.04/0.99    inference(definition_unfolding,[],[f29,f33])).
% 4.04/0.99  
% 4.04/0.99  fof(f8,axiom,(
% 4.04/0.99    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 4.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/0.99  
% 4.04/0.99  fof(f32,plain,(
% 4.04/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 4.04/0.99    inference(cnf_transformation,[],[f8])).
% 4.04/0.99  
% 4.04/0.99  fof(f35,plain,(
% 4.04/0.99    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3)),
% 4.04/0.99    inference(cnf_transformation,[],[f23])).
% 4.04/0.99  
% 4.04/0.99  fof(f2,axiom,(
% 4.04/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/0.99  
% 4.04/0.99  fof(f25,plain,(
% 4.04/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.04/0.99    inference(cnf_transformation,[],[f2])).
% 4.04/0.99  
% 4.04/0.99  fof(f39,plain,(
% 4.04/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 4.04/0.99    inference(definition_unfolding,[],[f25,f33,f33])).
% 4.04/0.99  
% 4.04/0.99  fof(f36,plain,(
% 4.04/0.99    r1_xboole_0(sK2,sK3)),
% 4.04/0.99    inference(cnf_transformation,[],[f23])).
% 4.04/0.99  
% 4.04/0.99  fof(f38,plain,(
% 4.04/0.99    sK2 != sK4),
% 4.04/0.99    inference(cnf_transformation,[],[f23])).
% 4.04/0.99  
% 4.04/0.99  cnf(c_0,plain,
% 4.04/0.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 4.04/0.99      inference(cnf_transformation,[],[f24]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_4,plain,
% 4.04/0.99      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 4.04/0.99      inference(cnf_transformation,[],[f28]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_229,plain,
% 4.04/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 4.04/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_2,plain,
% 4.04/0.99      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 4.04/0.99      | ~ r1_xboole_0(X1,X2) ),
% 4.04/0.99      inference(cnf_transformation,[],[f40]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_11,negated_conjecture,
% 4.04/0.99      ( r1_xboole_0(sK4,sK3) ),
% 4.04/0.99      inference(cnf_transformation,[],[f37]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_89,plain,
% 4.04/0.99      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 4.04/0.99      | sK3 != X2
% 4.04/0.99      | sK4 != X1 ),
% 4.04/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_11]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_90,plain,
% 4.04/0.99      ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) ),
% 4.04/0.99      inference(unflattening,[status(thm)],[c_89]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_227,plain,
% 4.04/0.99      ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) != iProver_top ),
% 4.04/0.99      inference(predicate_to_equality,[status(thm)],[c_90]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_4845,plain,
% 4.04/0.99      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) = k1_xboole_0 ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_229,c_227]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_9,plain,
% 4.04/0.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 4.04/0.99      inference(cnf_transformation,[],[f43]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_7,plain,
% 4.04/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 4.04/0.99      inference(cnf_transformation,[],[f31]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_231,plain,
% 4.04/0.99      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 4.04/0.99      inference(demodulation,[status(thm)],[c_9,c_7]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_4995,plain,
% 4.04/0.99      ( k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK4,sK4),sK3)) = k4_xboole_0(sK4,k1_xboole_0) ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_4845,c_231]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_6,plain,
% 4.04/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.04/0.99      inference(cnf_transformation,[],[f30]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_5,plain,
% 4.04/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 4.04/0.99      inference(cnf_transformation,[],[f42]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_230,plain,
% 4.04/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 4.04/0.99      inference(light_normalisation,[status(thm)],[c_5,c_6]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_626,plain,
% 4.04/0.99      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_6,c_7]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_8,plain,
% 4.04/0.99      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 4.04/0.99      inference(cnf_transformation,[],[f32]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_457,plain,
% 4.04/0.99      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_540,plain,
% 4.04/0.99      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_231,c_231]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_541,plain,
% 4.04/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) ),
% 4.04/0.99      inference(light_normalisation,[status(thm)],[c_540,c_230]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_1772,plain,
% 4.04/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 4.04/0.99      inference(demodulation,[status(thm)],[c_541,c_626]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_1777,plain,
% 4.04/0.99      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_457,c_1772]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_1869,plain,
% 4.04/0.99      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 4.04/0.99      inference(light_normalisation,[status(thm)],[c_1777,c_6]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_1931,plain,
% 4.04/0.99      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_1869,c_7]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_5017,plain,
% 4.04/0.99      ( k4_xboole_0(sK4,sK3) = sK4 ),
% 4.04/0.99      inference(demodulation,
% 4.04/0.99                [status(thm)],
% 4.04/0.99                [c_4995,c_6,c_230,c_626,c_1931]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_6078,plain,
% 4.04/0.99      ( k4_xboole_0(sK4,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK4,X0) ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_5017,c_7]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_6150,plain,
% 4.04/0.99      ( k4_xboole_0(sK4,k2_xboole_0(X0,sK3)) = k4_xboole_0(sK4,X0) ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_0,c_6078]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_13,negated_conjecture,
% 4.04/0.99      ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
% 4.04/0.99      inference(cnf_transformation,[],[f35]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_459,plain,
% 4.04/0.99      ( k4_xboole_0(sK4,k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_13,c_8]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_8187,plain,
% 4.04/0.99      ( k4_xboole_0(sK4,sK2) = k1_xboole_0 ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_6150,c_459]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_1,plain,
% 4.04/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 4.04/0.99      inference(cnf_transformation,[],[f39]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_8865,plain,
% 4.04/0.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k4_xboole_0(sK4,k1_xboole_0) ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_8187,c_1]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_12,negated_conjecture,
% 4.04/0.99      ( r1_xboole_0(sK2,sK3) ),
% 4.04/0.99      inference(cnf_transformation,[],[f36]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_98,plain,
% 4.04/0.99      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 4.04/0.99      | sK3 != X2
% 4.04/0.99      | sK2 != X1 ),
% 4.04/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_12]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_99,plain,
% 4.04/0.99      ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 4.04/0.99      inference(unflattening,[status(thm)],[c_98]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_226,plain,
% 4.04/0.99      ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
% 4.04/0.99      inference(predicate_to_equality,[status(thm)],[c_99]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_4846,plain,
% 4.04/0.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_229,c_226]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_5121,plain,
% 4.04/0.99      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK2),sK3)) = k4_xboole_0(sK2,k1_xboole_0) ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_4846,c_231]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_5126,plain,
% 4.04/0.99      ( k4_xboole_0(sK2,sK3) = sK2 ),
% 4.04/0.99      inference(demodulation,
% 4.04/0.99                [status(thm)],
% 4.04/0.99                [c_5121,c_6,c_230,c_626,c_1931]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_6132,plain,
% 4.04/0.99      ( k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,X0) ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_5126,c_7]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_6258,plain,
% 4.04/0.99      ( k4_xboole_0(sK2,k2_xboole_0(X0,sK3)) = k4_xboole_0(sK2,X0) ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_0,c_6132]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_8251,plain,
% 4.04/0.99      ( k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK2,sK4) ),
% 4.04/0.99      inference(superposition,[status(thm)],[c_13,c_6258]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_8288,plain,
% 4.04/0.99      ( k4_xboole_0(sK2,sK4) = k4_xboole_0(sK2,sK2) ),
% 4.04/0.99      inference(demodulation,[status(thm)],[c_8251,c_6258]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_8289,plain,
% 4.04/0.99      ( k4_xboole_0(sK2,sK4) = k1_xboole_0 ),
% 4.04/0.99      inference(demodulation,[status(thm)],[c_8288,c_230]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_8884,plain,
% 4.04/0.99      ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK4,k1_xboole_0) ),
% 4.04/0.99      inference(light_normalisation,[status(thm)],[c_8865,c_8289]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_8885,plain,
% 4.04/0.99      ( sK4 = sK2 ),
% 4.04/0.99      inference(demodulation,[status(thm)],[c_8884,c_6]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_147,plain,( X0 = X0 ),theory(equality) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_794,plain,
% 4.04/0.99      ( sK2 = sK2 ),
% 4.04/0.99      inference(instantiation,[status(thm)],[c_147]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_148,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_239,plain,
% 4.04/0.99      ( sK4 != X0 | sK2 != X0 | sK2 = sK4 ),
% 4.04/0.99      inference(instantiation,[status(thm)],[c_148]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_446,plain,
% 4.04/0.99      ( sK4 != sK2 | sK2 = sK4 | sK2 != sK2 ),
% 4.04/0.99      inference(instantiation,[status(thm)],[c_239]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(c_10,negated_conjecture,
% 4.04/0.99      ( sK2 != sK4 ),
% 4.04/0.99      inference(cnf_transformation,[],[f38]) ).
% 4.04/0.99  
% 4.04/0.99  cnf(contradiction,plain,
% 4.04/0.99      ( $false ),
% 4.04/0.99      inference(minisat,[status(thm)],[c_8885,c_794,c_446,c_10]) ).
% 4.04/0.99  
% 4.04/0.99  
% 4.04/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.04/0.99  
% 4.04/0.99  ------                               Statistics
% 4.04/0.99  
% 4.04/0.99  ------ General
% 4.04/0.99  
% 4.04/0.99  abstr_ref_over_cycles:                  0
% 4.04/0.99  abstr_ref_under_cycles:                 0
% 4.04/0.99  gc_basic_clause_elim:                   0
% 4.04/0.99  forced_gc_time:                         0
% 4.04/0.99  parsing_time:                           0.008
% 4.04/0.99  unif_index_cands_time:                  0.
% 4.04/0.99  unif_index_add_time:                    0.
% 4.04/0.99  orderings_time:                         0.
% 4.04/0.99  out_proof_time:                         0.009
% 4.04/0.99  total_time:                             0.419
% 4.04/0.99  num_of_symbols:                         41
% 4.04/0.99  num_of_terms:                           22240
% 4.04/0.99  
% 4.04/0.99  ------ Preprocessing
% 4.04/0.99  
% 4.04/0.99  num_of_splits:                          0
% 4.04/0.99  num_of_split_atoms:                     0
% 4.04/0.99  num_of_reused_defs:                     0
% 4.04/0.99  num_eq_ax_congr_red:                    9
% 4.04/0.99  num_of_sem_filtered_clauses:            1
% 4.04/0.99  num_of_subtypes:                        0
% 4.04/0.99  monotx_restored_types:                  0
% 4.04/0.99  sat_num_of_epr_types:                   0
% 4.04/0.99  sat_num_of_non_cyclic_types:            0
% 4.04/0.99  sat_guarded_non_collapsed_types:        0
% 4.04/0.99  num_pure_diseq_elim:                    0
% 4.04/0.99  simp_replaced_by:                       0
% 4.04/0.99  res_preprocessed:                       64
% 4.04/0.99  prep_upred:                             0
% 4.04/0.99  prep_unflattend:                        6
% 4.04/0.99  smt_new_axioms:                         0
% 4.04/0.99  pred_elim_cands:                        1
% 4.04/0.99  pred_elim:                              1
% 4.04/0.99  pred_elim_cl:                           1
% 4.04/0.99  pred_elim_cycles:                       3
% 4.04/0.99  merged_defs:                            0
% 4.04/0.99  merged_defs_ncl:                        0
% 4.04/0.99  bin_hyper_res:                          0
% 4.04/0.99  prep_cycles:                            4
% 4.04/0.99  pred_elim_time:                         0.001
% 4.04/0.99  splitting_time:                         0.
% 4.04/0.99  sem_filter_time:                        0.
% 4.04/1.00  monotx_time:                            0.
% 4.04/1.00  subtype_inf_time:                       0.
% 4.04/1.00  
% 4.04/1.00  ------ Problem properties
% 4.04/1.00  
% 4.04/1.00  clauses:                                13
% 4.04/1.00  conjectures:                            2
% 4.04/1.00  epr:                                    1
% 4.04/1.00  horn:                                   12
% 4.04/1.00  ground:                                 2
% 4.04/1.00  unary:                                  11
% 4.04/1.00  binary:                                 2
% 4.04/1.00  lits:                                   15
% 4.04/1.00  lits_eq:                                10
% 4.04/1.00  fd_pure:                                0
% 4.04/1.00  fd_pseudo:                              0
% 4.04/1.00  fd_cond:                                1
% 4.04/1.00  fd_pseudo_cond:                         0
% 4.04/1.00  ac_symbols:                             0
% 4.04/1.00  
% 4.04/1.00  ------ Propositional Solver
% 4.04/1.00  
% 4.04/1.00  prop_solver_calls:                      33
% 4.04/1.00  prop_fast_solver_calls:                 269
% 4.04/1.00  smt_solver_calls:                       0
% 4.04/1.00  smt_fast_solver_calls:                  0
% 4.04/1.00  prop_num_of_clauses:                    2955
% 4.04/1.00  prop_preprocess_simplified:             2603
% 4.04/1.00  prop_fo_subsumed:                       0
% 4.04/1.00  prop_solver_time:                       0.
% 4.04/1.00  smt_solver_time:                        0.
% 4.04/1.00  smt_fast_solver_time:                   0.
% 4.04/1.00  prop_fast_solver_time:                  0.
% 4.04/1.00  prop_unsat_core_time:                   0.
% 4.04/1.00  
% 4.04/1.00  ------ QBF
% 4.04/1.00  
% 4.04/1.00  qbf_q_res:                              0
% 4.04/1.00  qbf_num_tautologies:                    0
% 4.04/1.00  qbf_prep_cycles:                        0
% 4.04/1.00  
% 4.04/1.00  ------ BMC1
% 4.04/1.00  
% 4.04/1.00  bmc1_current_bound:                     -1
% 4.04/1.00  bmc1_last_solved_bound:                 -1
% 4.04/1.00  bmc1_unsat_core_size:                   -1
% 4.04/1.00  bmc1_unsat_core_parents_size:           -1
% 4.04/1.00  bmc1_merge_next_fun:                    0
% 4.04/1.00  bmc1_unsat_core_clauses_time:           0.
% 4.04/1.00  
% 4.04/1.00  ------ Instantiation
% 4.04/1.00  
% 4.04/1.00  inst_num_of_clauses:                    478
% 4.04/1.00  inst_num_in_passive:                    133
% 4.04/1.00  inst_num_in_active:                     274
% 4.04/1.00  inst_num_in_unprocessed:                71
% 4.04/1.00  inst_num_of_loops:                      390
% 4.04/1.00  inst_num_of_learning_restarts:          0
% 4.04/1.00  inst_num_moves_active_passive:          111
% 4.04/1.00  inst_lit_activity:                      0
% 4.04/1.00  inst_lit_activity_moves:                0
% 4.04/1.00  inst_num_tautologies:                   0
% 4.04/1.00  inst_num_prop_implied:                  0
% 4.04/1.00  inst_num_existing_simplified:           0
% 4.04/1.00  inst_num_eq_res_simplified:             0
% 4.04/1.00  inst_num_child_elim:                    0
% 4.04/1.00  inst_num_of_dismatching_blockings:      264
% 4.04/1.00  inst_num_of_non_proper_insts:           551
% 4.04/1.00  inst_num_of_duplicates:                 0
% 4.04/1.00  inst_inst_num_from_inst_to_res:         0
% 4.04/1.00  inst_dismatching_checking_time:         0.
% 4.04/1.00  
% 4.04/1.00  ------ Resolution
% 4.04/1.00  
% 4.04/1.00  res_num_of_clauses:                     0
% 4.04/1.00  res_num_in_passive:                     0
% 4.04/1.00  res_num_in_active:                      0
% 4.04/1.00  res_num_of_loops:                       68
% 4.04/1.00  res_forward_subset_subsumed:            147
% 4.04/1.00  res_backward_subset_subsumed:           0
% 4.04/1.00  res_forward_subsumed:                   0
% 4.04/1.00  res_backward_subsumed:                  0
% 4.04/1.00  res_forward_subsumption_resolution:     0
% 4.04/1.00  res_backward_subsumption_resolution:    0
% 4.04/1.00  res_clause_to_clause_subsumption:       8595
% 4.04/1.00  res_orphan_elimination:                 0
% 4.04/1.00  res_tautology_del:                      74
% 4.04/1.00  res_num_eq_res_simplified:              0
% 4.04/1.00  res_num_sel_changes:                    0
% 4.04/1.00  res_moves_from_active_to_pass:          0
% 4.04/1.00  
% 4.04/1.00  ------ Superposition
% 4.04/1.00  
% 4.04/1.00  sup_time_total:                         0.
% 4.04/1.00  sup_time_generating:                    0.
% 4.04/1.00  sup_time_sim_full:                      0.
% 4.04/1.00  sup_time_sim_immed:                     0.
% 4.04/1.00  
% 4.04/1.00  sup_num_of_clauses:                     1107
% 4.04/1.00  sup_num_in_active:                      68
% 4.04/1.00  sup_num_in_passive:                     1039
% 4.04/1.00  sup_num_of_loops:                       76
% 4.04/1.00  sup_fw_superposition:                   1699
% 4.04/1.00  sup_bw_superposition:                   1120
% 4.04/1.00  sup_immediate_simplified:               1962
% 4.04/1.00  sup_given_eliminated:                   7
% 4.04/1.00  comparisons_done:                       0
% 4.04/1.00  comparisons_avoided:                    0
% 4.04/1.00  
% 4.04/1.00  ------ Simplifications
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  sim_fw_subset_subsumed:                 0
% 4.04/1.00  sim_bw_subset_subsumed:                 0
% 4.04/1.00  sim_fw_subsumed:                        328
% 4.04/1.00  sim_bw_subsumed:                        15
% 4.04/1.00  sim_fw_subsumption_res:                 0
% 4.04/1.00  sim_bw_subsumption_res:                 0
% 4.04/1.00  sim_tautology_del:                      0
% 4.04/1.00  sim_eq_tautology_del:                   613
% 4.04/1.00  sim_eq_res_simp:                        0
% 4.04/1.00  sim_fw_demodulated:                     1811
% 4.04/1.00  sim_bw_demodulated:                     33
% 4.04/1.00  sim_light_normalised:                   570
% 4.04/1.00  sim_joinable_taut:                      0
% 4.04/1.00  sim_joinable_simp:                      0
% 4.04/1.00  sim_ac_normalised:                      0
% 4.04/1.00  sim_smt_subsumption:                    0
% 4.04/1.00  
%------------------------------------------------------------------------------
