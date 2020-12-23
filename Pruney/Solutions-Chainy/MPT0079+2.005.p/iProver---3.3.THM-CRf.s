%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:46 EST 2020

% Result     : Theorem 55.01s
% Output     : CNFRefutation 55.01s
% Verified   : 
% Statistics : Number of formulae       : 1424 (17699848920 expanded)
%              Number of clauses        : 1376 (7286611431 expanded)
%              Number of leaves         :   19 (4598048212 expanded)
%              Depth                    :  103
%              Number of atoms          : 1479 (24054079344 expanded)
%              Number of equality atoms : 1425 (20010474197 expanded)
%              Maximal formula depth    :    9 (   1 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f42,f40])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f21])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK3 != sK4
      & r1_xboole_0(sK5,sK3)
      & r1_xboole_0(sK4,sK2)
      & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( sK3 != sK4
    & r1_xboole_0(sK5,sK3)
    & r1_xboole_0(sK4,sK2)
    & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f27])).

fof(f43,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f30,f40,f40])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f25])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f23])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f33,f40])).

fof(f44,plain,(
    r1_xboole_0(sK4,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    r1_xboole_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_12,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_11,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_153,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_12,c_11,c_0])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_505,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_153,c_6])).

cnf(c_16,negated_conjecture,
    ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_152,negated_conjecture,
    ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK4,sK5) ),
    inference(theory_normalisation,[status(thm)],[c_16,c_11,c_0])).

cnf(c_243,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_11,c_0])).

cnf(c_961,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK4,k2_xboole_0(X0,sK5)) ),
    inference(superposition,[status(thm)],[c_152,c_243])).

cnf(c_1249,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) = k2_xboole_0(sK4,k2_xboole_0(X0,sK5)) ),
    inference(superposition,[status(thm)],[c_961,c_243])).

cnf(c_1758,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_505,c_1249])).

cnf(c_1761,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_1758,c_152])).

cnf(c_8,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2099,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) ),
    inference(superposition,[status(thm)],[c_1761,c_8])).

cnf(c_511,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_8])).

cnf(c_509,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3021,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_509,c_1])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_517,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8,c_7])).

cnf(c_518,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_517,c_7])).

cnf(c_1070,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_518,c_0])).

cnf(c_1145,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1070,c_8])).

cnf(c_1757,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_505,c_518])).

cnf(c_1849,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1145,c_1757])).

cnf(c_9,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1857,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_1849,c_9])).

cnf(c_1865,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1857,c_1757])).

cnf(c_3026,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3021,c_7,c_511,c_1865])).

cnf(c_3755,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_511,c_511,c_3026])).

cnf(c_3765,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_152,c_3755])).

cnf(c_4236,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(k4_xboole_0(sK5,sK4),X0)) = k4_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_3765,c_9])).

cnf(c_42651,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,sK4),sK2)) = k4_xboole_0(sK4,sK2) ),
    inference(superposition,[status(thm)],[c_2099,c_4236])).

cnf(c_618,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_9,c_1])).

cnf(c_621,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_618,c_9])).

cnf(c_617,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_9,c_6])).

cnf(c_14690,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_617])).

cnf(c_16936,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_621,c_14690])).

cnf(c_17109,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,sK4)))) = k4_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) ),
    inference(superposition,[status(thm)],[c_16936,c_4236])).

cnf(c_17193,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_17109,c_3765])).

cnf(c_18162,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
    inference(superposition,[status(thm)],[c_8,c_17193])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_679,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_10])).

cnf(c_52071,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,sK2))) = k4_xboole_0(sK4,sK2) ),
    inference(superposition,[status(thm)],[c_18162,c_679])).

cnf(c_1861,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1849,c_9])).

cnf(c_1862,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1861,c_6])).

cnf(c_2909,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_1862])).

cnf(c_6029,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK5),sK4),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_961,c_2909])).

cnf(c_244,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_11,c_0])).

cnf(c_1674,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_152,c_244])).

cnf(c_615,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_9,c_153])).

cnf(c_622,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_615,c_9,c_617])).

cnf(c_20476,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))),k4_xboole_0(X0,sK5)) = k4_xboole_0(X0,sK5) ),
    inference(superposition,[status(thm)],[c_1674,c_622])).

cnf(c_33909,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK5),sK4),sK5)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK5),sK4),sK5) ),
    inference(superposition,[status(thm)],[c_6029,c_20476])).

cnf(c_33984,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(X0,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_20476,c_1862])).

cnf(c_1745,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_505,c_11])).

cnf(c_21186,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK3,X0),sK5)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1745,c_961])).

cnf(c_1990,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK4,X0)) = k4_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_1674,c_8])).

cnf(c_22107,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),sK5),k2_xboole_0(sK3,sK2)),k2_xboole_0(sK3,sK2)) = k4_xboole_0(sK5,k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK3,X0),sK5))) ),
    inference(superposition,[status(thm)],[c_21186,c_1990])).

cnf(c_22124,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),sK5),k2_xboole_0(sK3,sK2)),k2_xboole_0(sK3,sK2)) = k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)) ),
    inference(demodulation,[status(thm)],[c_22107,c_21186])).

cnf(c_2914,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_152,c_1862])).

cnf(c_22125,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),sK5),k2_xboole_0(sK3,sK2)),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_22124,c_2914])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1672,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2,c_244])).

cnf(c_512,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),sK5) = k4_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_152,c_8])).

cnf(c_709,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,X0)) = k4_xboole_0(k4_xboole_0(sK4,sK5),X0) ),
    inference(superposition,[status(thm)],[c_512,c_9])).

cnf(c_717,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,X0)) = k4_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
    inference(demodulation,[status(thm)],[c_709,c_9])).

cnf(c_3019,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_509,c_153])).

cnf(c_3027,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_3019,c_6,c_511])).

cnf(c_6250,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,k2_xboole_0(sK5,X0)),k2_xboole_0(sK5,X0)) = k2_xboole_0(k2_xboole_0(sK5,X0),k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_717,c_3027])).

cnf(c_6336,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,X0),k2_xboole_0(sK3,sK2)) = k2_xboole_0(k2_xboole_0(sK5,X0),sK4) ),
    inference(demodulation,[status(thm)],[c_6250,c_3027])).

cnf(c_714,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK5,k4_xboole_0(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_512,c_6])).

cnf(c_715,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK5,sK4) ),
    inference(demodulation,[status(thm)],[c_714,c_6])).

cnf(c_1251,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,sK5)) = k2_xboole_0(sK5,sK4) ),
    inference(superposition,[status(thm)],[c_961,c_715])).

cnf(c_1259,plain,
    ( k2_xboole_0(sK5,sK4) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_1251,c_2,c_152])).

cnf(c_959,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2,c_243])).

cnf(c_3929,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_959,c_11])).

cnf(c_516,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_8,c_6])).

cnf(c_519,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_516,c_6])).

cnf(c_3207,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_519,c_11])).

cnf(c_3240,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_3207,c_11])).

cnf(c_3970,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_3929,c_3240])).

cnf(c_6337,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,X0),k2_xboole_0(sK3,sK2)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(demodulation,[status(thm)],[c_6336,c_1259,c_3970])).

cnf(c_10442,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK3,sK2)) = k2_xboole_0(k2_xboole_0(sK5,X0),k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_1672,c_6337])).

cnf(c_10525,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK3,sK2)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(demodulation,[status(thm)],[c_10442,c_6337])).

cnf(c_22126,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_22125,c_8,c_10525])).

cnf(c_14697,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK5,k4_xboole_0(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_152,c_617])).

cnf(c_23958,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK3,X0),sK4)) = k2_xboole_0(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_22126,c_14697])).

cnf(c_23964,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(sK3,k2_xboole_0(X0,sK4))) = sK5 ),
    inference(demodulation,[status(thm)],[c_23958,c_9,c_518])).

cnf(c_616,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_9,c_1])).

cnf(c_24608,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,k2_xboole_0(X0,sK4)),k4_xboole_0(k4_xboole_0(sK3,k2_xboole_0(X0,sK4)),k4_xboole_0(X1,sK5))) = k4_xboole_0(k4_xboole_0(X1,sK5),k4_xboole_0(X1,sK5)) ),
    inference(superposition,[status(thm)],[c_23964,c_616])).

cnf(c_3133,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_3026])).

cnf(c_24615,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,k2_xboole_0(X0,sK4)),k4_xboole_0(X1,sK5)) = k4_xboole_0(sK3,k2_xboole_0(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_23964,c_3133])).

cnf(c_24626,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,k2_xboole_0(X0,sK4)),k4_xboole_0(sK3,k2_xboole_0(X0,sK4))) = k4_xboole_0(k4_xboole_0(X1,sK5),k4_xboole_0(X1,sK5)) ),
    inference(demodulation,[status(thm)],[c_24608,c_24615])).

cnf(c_24627,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(X0,sK5)) = sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_24626])).

cnf(c_34016,plain,
    ( sP1_iProver_split = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_33984,c_24627])).

cnf(c_34083,plain,
    ( k2_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK5),sK4),sK5)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK5),sK4),sK5) ),
    inference(demodulation,[status(thm)],[c_33909,c_34016])).

cnf(c_21184,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK3,X0))) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1745,c_1674])).

cnf(c_608,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_8,c_9])).

cnf(c_625,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_608,c_9])).

cnf(c_23356,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK3,X1)))) = k4_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_21184,c_625])).

cnf(c_23456,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK3,sK2)) = k4_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(demodulation,[status(thm)],[c_23356,c_21184])).

cnf(c_34084,plain,
    ( k2_xboole_0(sP1_iProver_split,k4_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK4,sK5))) = k4_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(demodulation,[status(thm)],[c_34083,c_9,c_152,c_23456])).

cnf(c_34085,plain,
    ( k2_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k4_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_34084,c_152,c_23456])).

cnf(c_1749,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_505,c_0])).

cnf(c_34187,plain,
    ( k4_xboole_0(sP1_iProver_split,k2_xboole_0(sK3,sK2)) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_34085,c_1749])).

cnf(c_6389,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = sK4 ),
    inference(superposition,[status(thm)],[c_1259,c_3133])).

cnf(c_34383,plain,
    ( k4_xboole_0(sK4,sP1_iProver_split) = sK4 ),
    inference(superposition,[status(thm)],[c_34187,c_6389])).

cnf(c_52075,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) ),
    inference(superposition,[status(thm)],[c_18162,c_1])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_238,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK4,sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_104,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK2 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_105,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) ),
    inference(unflattening,[status(thm)],[c_104])).

cnf(c_235,plain,
    ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_105])).

cnf(c_15262,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_238,c_235])).

cnf(c_52081,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK3,sK2)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_52075,c_15262,c_34016])).

cnf(c_52854,plain,
    ( k4_xboole_0(sK4,sK2) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_52071,c_34383,c_52081])).

cnf(c_2927,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_961,c_1862])).

cnf(c_33903,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X0,sK5),sK5)) = k4_xboole_0(k2_xboole_0(X0,sK5),sK5) ),
    inference(superposition,[status(thm)],[c_2927,c_20476])).

cnf(c_34091,plain,
    ( k2_xboole_0(sP1_iProver_split,k4_xboole_0(k2_xboole_0(X0,sK5),sK5)) = k4_xboole_0(k2_xboole_0(X0,sK5),sK5) ),
    inference(demodulation,[status(thm)],[c_33903,c_34016])).

cnf(c_34092,plain,
    ( k2_xboole_0(sP1_iProver_split,k4_xboole_0(X0,sK5)) = k4_xboole_0(X0,sK5) ),
    inference(demodulation,[status(thm)],[c_34091,c_8])).

cnf(c_34788,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK5),k2_xboole_0(k4_xboole_0(X0,sK5),X1)) = k4_xboole_0(sP1_iProver_split,k2_xboole_0(k4_xboole_0(X0,sK5),X1)) ),
    inference(superposition,[status(thm)],[c_34092,c_625])).

cnf(c_687,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_10,c_9])).

cnf(c_696,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_687,c_9])).

cnf(c_34343,plain,
    ( k4_xboole_0(sP1_iProver_split,k2_xboole_0(k2_xboole_0(sK3,sK2),X0)) = k4_xboole_0(sP1_iProver_split,k2_xboole_0(k4_xboole_0(sP1_iProver_split,sP1_iProver_split),X0)) ),
    inference(superposition,[status(thm)],[c_34187,c_696])).

cnf(c_597,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_6])).

cnf(c_598,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_597,c_505])).

cnf(c_23157,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_505,c_625])).

cnf(c_23749,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_23157,c_9,c_1865])).

cnf(c_24101,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_598,c_23749])).

cnf(c_24299,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_24101,c_9])).

cnf(c_34369,plain,
    ( k4_xboole_0(sP1_iProver_split,sP1_iProver_split) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_34187,c_24299])).

cnf(c_34396,plain,
    ( k4_xboole_0(sP1_iProver_split,sP1_iProver_split) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_34369,c_34016])).

cnf(c_34345,plain,
    ( k4_xboole_0(sP1_iProver_split,k2_xboole_0(sP1_iProver_split,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_34187,c_23749])).

cnf(c_34420,plain,
    ( k4_xboole_0(sP1_iProver_split,k2_xboole_0(sP1_iProver_split,X0)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_34345,c_34016])).

cnf(c_34421,plain,
    ( k4_xboole_0(sP1_iProver_split,k2_xboole_0(k2_xboole_0(sK3,sK2),X0)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_34343,c_34396,c_34420])).

cnf(c_34422,plain,
    ( k4_xboole_0(sP1_iProver_split,k2_xboole_0(sK2,k2_xboole_0(sK3,X0))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_34421,c_3970])).

cnf(c_1700,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK4,k2_xboole_0(X0,sK5)) ),
    inference(superposition,[status(thm)],[c_244,c_961])).

cnf(c_1703,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_1700,c_1249])).

cnf(c_34423,plain,
    ( k4_xboole_0(sP1_iProver_split,k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_34422,c_1703])).

cnf(c_34360,plain,
    ( k4_xboole_0(sP1_iProver_split,k2_xboole_0(k2_xboole_0(sK3,sK2),X0)) = k4_xboole_0(sP1_iProver_split,X0) ),
    inference(superposition,[status(thm)],[c_34187,c_9])).

cnf(c_34402,plain,
    ( k4_xboole_0(sP1_iProver_split,k2_xboole_0(sK2,k2_xboole_0(sK3,X0))) = k4_xboole_0(sP1_iProver_split,X0) ),
    inference(demodulation,[status(thm)],[c_34360,c_3970])).

cnf(c_34403,plain,
    ( k4_xboole_0(sP1_iProver_split,k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) = k4_xboole_0(sP1_iProver_split,X0) ),
    inference(light_normalisation,[status(thm)],[c_34402,c_1703])).

cnf(c_34425,plain,
    ( k4_xboole_0(sP1_iProver_split,X0) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_34423,c_34403])).

cnf(c_34835,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK5),k2_xboole_0(k4_xboole_0(X0,sK5),X1)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_34788,c_9,c_34425])).

cnf(c_21035,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_0,c_1745])).

cnf(c_53529,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X3)) ),
    inference(superposition,[status(thm)],[c_21035,c_21035])).

cnf(c_53683,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = sP4_iProver_split(X0,X1) ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP4_iProver_split])],[c_53529])).

cnf(c_245,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_11,c_0])).

cnf(c_34178,plain,
    ( k2_xboole_0(sP1_iProver_split,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1)) = k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_34085,c_245])).

cnf(c_53599,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sP1_iProver_split,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_21035,c_34178])).

cnf(c_34793,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(k4_xboole_0(X0,sK5),sP1_iProver_split)) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_34092,c_3755])).

cnf(c_17153,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_16936,c_616])).

cnf(c_34829,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK5,k4_xboole_0(X0,sP1_iProver_split))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_34793,c_9,c_17153])).

cnf(c_35092,plain,
    ( k2_xboole_0(sP1_iProver_split,X0) = X0 ),
    inference(superposition,[status(thm)],[c_34829,c_505])).

cnf(c_53636,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_53599,c_3970,c_35092])).

cnf(c_53685,plain,
    ( sP4_iProver_split(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_53683,c_53636])).

cnf(c_63039,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK5,sP4_iProver_split(X1,k4_xboole_0(X0,sK5)))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_34835,c_9,c_53685])).

cnf(c_63040,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(sP4_iProver_split(X1,k4_xboole_0(X0,sK5)),sK5)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_63039,c_53685])).

cnf(c_53518,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X2,X0),X3)) = k2_xboole_0(X3,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_21035,c_245])).

cnf(c_1958,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_1749,c_244])).

cnf(c_54099,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(demodulation,[status(thm)],[c_53518,c_1958,c_3970,c_53685])).

cnf(c_54100,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,X1),X2) = sP4_iProver_split(X1,sP4_iProver_split(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_54099,c_3970,c_53685])).

cnf(c_63041,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,sK5),sP4_iProver_split(sK5,X1))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_63040,c_54100])).

cnf(c_1955,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_1749,c_11])).

cnf(c_26518,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK4,X0),sK2)) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_1955,c_1249])).

cnf(c_26587,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK4,X0),sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_26518,c_152])).

cnf(c_6382,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_11,c_3133])).

cnf(c_32645,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,X0),sK2),k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(sK3,sK2)))) = k2_xboole_0(k4_xboole_0(sK4,X0),sK2) ),
    inference(superposition,[status(thm)],[c_26587,c_6382])).

cnf(c_15297,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(X1,k2_xboole_0(sK5,k4_xboole_0(X0,sK4)))) = k4_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_14697,c_3133])).

cnf(c_58973,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sP4_iProver_split(sK2,sK3),k4_xboole_0(X1,sP4_iProver_split(k4_xboole_0(X0,sK4),sK5)))) = k4_xboole_0(X0,sP4_iProver_split(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_15297,c_9,c_53685])).

cnf(c_58974,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X1,sP4_iProver_split(k4_xboole_0(X0,sK4),sK5)),sP4_iProver_split(sK2,sK3))) = k4_xboole_0(X0,sP4_iProver_split(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_58973,c_53685])).

cnf(c_1044,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
    inference(superposition,[status(thm)],[c_152,c_11])).

cnf(c_1329,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
    inference(superposition,[status(thm)],[c_1044,c_11])).

cnf(c_3229,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_519,c_1329])).

cnf(c_3233,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_3229,c_152])).

cnf(c_3353,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,sK4))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_3233,c_243])).

cnf(c_7786,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),X0),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
    inference(superposition,[status(thm)],[c_505,c_3353])).

cnf(c_7838,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),X0),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_7786,c_3233])).

cnf(c_11611,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK2,sK4),X0))) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_7838,c_1674])).

cnf(c_59085,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK2,sK4),sP4_iProver_split(sK2,sK3)))) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_58974,c_11611])).

cnf(c_12475,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
    inference(superposition,[status(thm)],[c_152,c_616])).

cnf(c_13677,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4)))) = k4_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_12475,c_3026])).

cnf(c_58703,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sP4_iProver_split(sK2,sK3),k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))))) = k4_xboole_0(X0,sP4_iProver_split(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_13677,c_9,c_53685])).

cnf(c_58704,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))),sP4_iProver_split(sK2,sK3))) = k4_xboole_0(X0,sP4_iProver_split(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_58703,c_53685])).

cnf(c_6412,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k4_xboole_0(sK5,X0),sK2) ),
    inference(superposition,[status(thm)],[c_1761,c_3133])).

cnf(c_58772,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))),sP4_iProver_split(sK2,sK3))),sK2) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),sK2),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_58704,c_6412])).

cnf(c_14669,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = k2_xboole_0(X0,k4_xboole_0(X2,k2_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_509,c_617])).

cnf(c_14981,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = k2_xboole_0(X0,k4_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_14669,c_617])).

cnf(c_2993,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_245,c_509])).

cnf(c_14982,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_14981,c_2993,c_3970])).

cnf(c_1733,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_505])).

cnf(c_2102,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK5,X1),sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_1761,c_243])).

cnf(c_23026,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),X1),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) ),
    inference(superposition,[status(thm)],[c_505,c_2102])).

cnf(c_23118,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),X1),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_23026,c_1761])).

cnf(c_35485,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),X1))) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_23118,c_1674])).

cnf(c_38300,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK2,X0))) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1733,c_35485])).

cnf(c_59112,plain,
    ( sP4_iProver_split(sK2,sK3) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_59085,c_11611,c_14982,c_38300,c_53685])).

cnf(c_59341,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))),sP4_iProver_split(sK2,sK3))),sK2) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),sK2),k4_xboole_0(X0,sP4_iProver_split(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_58772,c_59112])).

cnf(c_17105,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(sK3,sK2),sK5))) = k4_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK3,sK2),X0))) ),
    inference(superposition,[status(thm)],[c_16936,c_717])).

cnf(c_1253,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(X0,sK5)) = k4_xboole_0(sK4,k2_xboole_0(X0,sK5)) ),
    inference(superposition,[status(thm)],[c_961,c_8])).

cnf(c_14675,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),X0)) = k2_xboole_0(sK5,k4_xboole_0(sK4,k2_xboole_0(X0,sK5))) ),
    inference(superposition,[status(thm)],[c_1253,c_617])).

cnf(c_14973,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),X0)) = k2_xboole_0(sK5,k4_xboole_0(sK4,X0)) ),
    inference(demodulation,[status(thm)],[c_14675,c_617])).

cnf(c_14974,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) = k2_xboole_0(sK5,k4_xboole_0(sK4,X0)) ),
    inference(demodulation,[status(thm)],[c_14973,c_509])).

cnf(c_17194,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK4,sK5))) = k4_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(sK4,X0))) ),
    inference(light_normalisation,[status(thm)],[c_17105,c_512,c_14974])).

cnf(c_43985,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(sK4,sK5))),sK2),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK4,sK5))),sK2) ),
    inference(superposition,[status(thm)],[c_17194,c_6412])).

cnf(c_1250,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK4,k2_xboole_0(sK5,sK5))) = k4_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_961,c_717])).

cnf(c_1260,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK4,k2_xboole_0(sK5,sK5))) = k4_xboole_0(sK4,k2_xboole_0(sK5,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_1250,c_715])).

cnf(c_972,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK5,X1))) = k4_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_243,c_717])).

cnf(c_1261,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) = k4_xboole_0(sK4,k2_xboole_0(sK5,sK4)) ),
    inference(demodulation,[status(thm)],[c_1260,c_2,c_152,c_972])).

cnf(c_1347,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) = k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_1261,c_1259,c_1261])).

cnf(c_1853,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1849,c_1347])).

cnf(c_3226,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,sK2)) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_519,c_1674])).

cnf(c_3436,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,sK2),k2_xboole_0(sK2,sK3)) = k2_xboole_0(k2_xboole_0(sK4,sK2),sK5) ),
    inference(superposition,[status(thm)],[c_3226,c_519])).

cnf(c_3213,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_519,c_244])).

cnf(c_3452,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,sK2),sK5) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_3436,c_3213,c_3233])).

cnf(c_3627,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,sK2),sK5) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK5) ),
    inference(superposition,[status(thm)],[c_3452,c_8])).

cnf(c_3643,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,sK2),sK5) = k4_xboole_0(sK4,sK5) ),
    inference(light_normalisation,[status(thm)],[c_3627,c_512])).

cnf(c_4337,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,sK2)) = k2_xboole_0(sK5,k4_xboole_0(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_3643,c_6])).

cnf(c_3632,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_3452,c_0])).

cnf(c_4338,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(sK4,sK5)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_4337,c_3632])).

cnf(c_44127,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,sK2),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK4,sK5))),sK2) ),
    inference(light_normalisation,[status(thm)],[c_43985,c_1853,c_4338])).

cnf(c_3147,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_3026,c_9])).

cnf(c_28777,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_6,c_3147])).

cnf(c_29031,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_28777,c_3147])).

cnf(c_44128,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,sK5),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_44127,c_1070,c_3133,c_29031])).

cnf(c_35069,plain,
    ( k4_xboole_0(sK5,sK5) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_1749,c_34829])).

cnf(c_44129,plain,
    ( k2_xboole_0(sP1_iProver_split,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_44128,c_35069])).

cnf(c_605,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_9])).

cnf(c_10787,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) = X1 ),
    inference(superposition,[status(thm)],[c_605,c_153])).

cnf(c_10886,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)),X1) = X1 ),
    inference(demodulation,[status(thm)],[c_10787,c_6,c_9])).

cnf(c_39445,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1)))) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_10886,c_1674])).

cnf(c_55753,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1)),sK4),sK5) = sP4_iProver_split(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_39445,c_53685])).

cnf(c_55754,plain,
    ( sP4_iProver_split(sK4,sP4_iProver_split(sK5,k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))))) = sP4_iProver_split(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_55753,c_53685,c_54100])).

cnf(c_55755,plain,
    ( sP4_iProver_split(sK4,sP4_iProver_split(sK5,k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X0,sP4_iProver_split(sK2,sK3)))))) = sP4_iProver_split(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_55754,c_53685])).

cnf(c_24104,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_622,c_23749])).

cnf(c_24294,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_24104,c_9])).

cnf(c_24295,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X0,X2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_24294,c_3970])).

cnf(c_24296,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X0,X3))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_24295,c_3970])).

cnf(c_24297,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_24296,c_6])).

cnf(c_56980,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X0)))) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_24297,c_24297,c_34016])).

cnf(c_56981,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(k2_xboole_0(X1,k2_xboole_0(X2,X0)),X3)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_56980,c_24297,c_53685])).

cnf(c_56982,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,k2_xboole_0(X3,X0)))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_56981,c_53685,c_54100])).

cnf(c_56983,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,sP4_iProver_split(X0,X3)))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_56982,c_53685])).

cnf(c_56991,plain,
    ( k4_xboole_0(sK5,sP4_iProver_split(X0,sP4_iProver_split(sK2,sK3))) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_55755,c_56983])).

cnf(c_59342,plain,
    ( k4_xboole_0(sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3))),k4_xboole_0(X0,sP4_iProver_split(sK2,sK3))) = sK2 ),
    inference(demodulation,[status(thm)],[c_59341,c_44129,c_53685,c_56991])).

cnf(c_59044,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(sK5,sK4),sK5)),sP4_iProver_split(sK2,sK3))),sK2) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),sK2),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_58974,c_6412])).

cnf(c_59216,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),sK2),k4_xboole_0(X0,sP4_iProver_split(sK2,sK3))) = k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),sK2) ),
    inference(demodulation,[status(thm)],[c_59044,c_58974,c_59112])).

cnf(c_59217,plain,
    ( k4_xboole_0(sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3))),k4_xboole_0(X0,sP4_iProver_split(sK2,sK3))) = sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_59216,c_53685])).

cnf(c_59343,plain,
    ( sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3))) = sK2 ),
    inference(demodulation,[status(thm)],[c_59342,c_59217])).

cnf(c_23033,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK5,X1),sK2))),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,X1),sK2)) ),
    inference(superposition,[status(thm)],[c_1733,c_2102])).

cnf(c_2246,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_2,c_1329])).

cnf(c_2281,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_2246,c_152])).

cnf(c_2294,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK2,sK5),X0)) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
    inference(superposition,[status(thm)],[c_2281,c_11])).

cnf(c_2590,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK2,sK5),X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_2281,c_245])).

cnf(c_5438,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK5,k2_xboole_0(sK2,X0))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_2294,c_1703,c_2590,c_3970])).

cnf(c_14800,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK5,k2_xboole_0(sK2,k4_xboole_0(X0,X1)))) = k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,sK2)),sK2)) ),
    inference(superposition,[status(thm)],[c_617,c_5438])).

cnf(c_2298,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,sK5))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_2281,c_243])).

cnf(c_5747,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK5,k2_xboole_0(sK2,X0))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_244,c_2298])).

cnf(c_6242,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(X2,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_9,c_3027])).

cnf(c_14817,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(sK3,sK2)) ),
    inference(demodulation,[status(thm)],[c_14800,c_5747,c_6242])).

cnf(c_23114,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK5,X1),sK2))),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_23033,c_1761,c_14817])).

cnf(c_59065,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),sK2))),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_58974,c_23114])).

cnf(c_59168,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),sK2))),sP4_iProver_split(sK2,sK3)) = sP4_iProver_split(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_59065,c_59112])).

cnf(c_59169,plain,
    ( sP4_iProver_split(sP4_iProver_split(sK2,sK3),k4_xboole_0(X0,k4_xboole_0(X0,sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)))))) = sP4_iProver_split(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_59168,c_53685])).

cnf(c_59353,plain,
    ( sP4_iProver_split(sP4_iProver_split(sK2,sK3),k4_xboole_0(X0,k4_xboole_0(X0,sK2))) = sP4_iProver_split(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_59343,c_59169])).

cnf(c_53206,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_1,c_21035])).

cnf(c_4949,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_1733,c_243])).

cnf(c_54999,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0))) = sP4_iProver_split(X1,X0) ),
    inference(demodulation,[status(thm)],[c_53206,c_4949,c_53685])).

cnf(c_59354,plain,
    ( sP4_iProver_split(sK2,sK3) = sP4_iProver_split(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_59353,c_54999])).

cnf(c_59876,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK2,sK4),sP4_iProver_split(sK3,sK2)))) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_59085,c_59354])).

cnf(c_59877,plain,
    ( sP4_iProver_split(sK3,sK2) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_59876,c_11611,c_14982,c_38300,c_53685,c_59354])).

cnf(c_65206,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,X0),sK2),k4_xboole_0(X1,k2_xboole_0(X2,sP4_iProver_split(sK3,sK2)))) = k2_xboole_0(k4_xboole_0(sK4,X0),sK2) ),
    inference(light_normalisation,[status(thm)],[c_32645,c_32645,c_59877])).

cnf(c_65207,plain,
    ( k4_xboole_0(sP4_iProver_split(sK2,k4_xboole_0(sK4,X0)),k4_xboole_0(X1,sP4_iProver_split(sP4_iProver_split(sK3,sK2),X2))) = sP4_iProver_split(sK2,k4_xboole_0(sK4,X0)) ),
    inference(demodulation,[status(thm)],[c_65206,c_53685])).

cnf(c_59058,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_58974,c_1761])).

cnf(c_59966,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),sK2)) = sP4_iProver_split(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_59058,c_59877])).

cnf(c_59967,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK3,sK2)),sK2)) = sP4_iProver_split(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_59966,c_59354])).

cnf(c_59968,plain,
    ( sP4_iProver_split(sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(sK3,sK2))),sK3) = sP4_iProver_split(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_59967,c_1761,c_53685])).

cnf(c_58715,plain,
    ( k4_xboole_0(sK4,sP4_iProver_split(k4_xboole_0(sK5,k4_xboole_0(sK5,k1_xboole_0)),sP4_iProver_split(sK2,sK3))) = k4_xboole_0(sK4,sP4_iProver_split(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_1849,c_58704])).

cnf(c_5745,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK5),X0),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) ),
    inference(superposition,[status(thm)],[c_505,c_2298])).

cnf(c_5792,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK5),X0),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_5745,c_2281])).

cnf(c_9878,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK5),X0),k2_xboole_0(sK3,sK2)) = k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_5792,c_8])).

cnf(c_3017,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_509,c_9])).

cnf(c_3028,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_3017,c_9])).

cnf(c_9921,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK5),X0),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9878,c_9,c_1862,c_3028])).

cnf(c_37775,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK5),X0),k2_xboole_0(sK3,sK2)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_9921,c_9921,c_34016])).

cnf(c_37853,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK5),X0),sK4)) = k2_xboole_0(sK5,sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_37775,c_14697])).

cnf(c_34144,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sP1_iProver_split,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1849,c_34085])).

cnf(c_34234,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sP1_iProver_split,sP1_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_34144,c_34016])).

cnf(c_3348,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK2)) = k2_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(superposition,[status(thm)],[c_3233,c_519])).

cnf(c_3352,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_3233,c_244])).

cnf(c_3356,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK4),sK3) = k2_xboole_0(sK2,k2_xboole_0(sK3,sK2)) ),
    inference(demodulation,[status(thm)],[c_3348,c_3352])).

cnf(c_3357,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK4),sK3) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_3356,c_2,c_1703])).

cnf(c_23219,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,X0)) = k4_xboole_0(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_3357,c_625])).

cnf(c_7327,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK3,X0)) = k4_xboole_0(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_3352,c_8])).

cnf(c_1695,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X0)) = k4_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_244,c_8])).

cnf(c_7376,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_7327,c_1695])).

cnf(c_23651,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_23219,c_7376])).

cnf(c_34235,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_34234,c_2,c_23651])).

cnf(c_35002,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK3,sK2),sK4)) = k2_xboole_0(sK5,sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_34235,c_14697])).

cnf(c_1279,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),sK4) = k4_xboole_0(sK5,sK4) ),
    inference(superposition,[status(thm)],[c_1259,c_8])).

cnf(c_35014,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(sK5,sK4)) = k2_xboole_0(sK5,sP1_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_35002,c_1279])).

cnf(c_35015,plain,
    ( k2_xboole_0(sK5,sP1_iProver_split) = sK5 ),
    inference(demodulation,[status(thm)],[c_35014,c_1749])).

cnf(c_37860,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK5),X0),sK4)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_37853,c_35015])).

cnf(c_37861,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(sK2,k2_xboole_0(X0,sK4))) = sK5 ),
    inference(demodulation,[status(thm)],[c_37860,c_9,c_14982])).

cnf(c_39016,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK2,k2_xboole_0(X0,sK4)),sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_37861,c_3755])).

cnf(c_39021,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k2_xboole_0(X0,sK4)),sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_37861,c_1862])).

cnf(c_39049,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k2_xboole_0(X0,sK4)),sK5) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_39021,c_34016])).

cnf(c_39054,plain,
    ( k4_xboole_0(sK5,sP1_iProver_split) = sK5 ),
    inference(demodulation,[status(thm)],[c_39016,c_39049])).

cnf(c_39447,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1)),sK5)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_10886,c_961])).

cnf(c_55934,plain,
    ( sP4_iProver_split(sP4_iProver_split(sK5,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1))),sK4) = sP4_iProver_split(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_39447,c_53685])).

cnf(c_2939,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1761,c_1862])).

cnf(c_4689,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),k2_xboole_0(k2_xboole_0(sK3,sK2),X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_2939,c_9])).

cnf(c_4702,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,X0),k2_xboole_0(sK2,k2_xboole_0(sK3,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4689,c_625,c_1757,c_3970])).

cnf(c_4703,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4702,c_9,c_1703])).

cnf(c_53253,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK5)) = k2_xboole_0(sK5,X0) ),
    inference(superposition,[status(thm)],[c_4703,c_21035])).

cnf(c_15298,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(X1,sK5)) = k2_xboole_0(X1,k2_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
    inference(superposition,[status(thm)],[c_14697,c_245])).

cnf(c_46509,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK5,k4_xboole_0(sK2,sK4))) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK5)) ),
    inference(superposition,[status(thm)],[c_1862,c_15298])).

cnf(c_3349,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3233,c_1862])).

cnf(c_15277,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK2,sK4),sK4)) = k2_xboole_0(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3349,c_14697])).

cnf(c_15328,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(sK2,sK4)) = sK5 ),
    inference(demodulation,[status(thm)],[c_15277,c_8,c_518])).

cnf(c_46655,plain,
    ( k2_xboole_0(sP1_iProver_split,k2_xboole_0(X0,sK5)) = k2_xboole_0(X0,sK5) ),
    inference(light_normalisation,[status(thm)],[c_46509,c_15328,c_34016])).

cnf(c_54919,plain,
    ( k2_xboole_0(X0,sK5) = k2_xboole_0(sK5,X0) ),
    inference(light_normalisation,[status(thm)],[c_53253,c_34016,c_46655])).

cnf(c_54920,plain,
    ( sP4_iProver_split(sK5,X0) = sP4_iProver_split(X0,sK5) ),
    inference(demodulation,[status(thm)],[c_54919,c_53685])).

cnf(c_20583,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK5),sK4),k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK5),sK4),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_6029,c_622])).

cnf(c_1237,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_0,c_961])).

cnf(c_1512,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1)) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1) ),
    inference(superposition,[status(thm)],[c_1237,c_11])).

cnf(c_20656,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK5),sK4),k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1))),k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_20583,c_1512,c_6029])).

cnf(c_20657,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_20656,c_9,c_518])).

cnf(c_3935,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_959,c_245])).

cnf(c_3971,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_3970,c_3935])).

cnf(c_20658,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(sK5,X0),sK4))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_20657,c_3971])).

cnf(c_20659,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK5,sK4)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_20658,c_3970])).

cnf(c_20660,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_20659,c_1259])).

cnf(c_53294,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,sK5))) = k2_xboole_0(k2_xboole_0(X1,sK5),X0) ),
    inference(superposition,[status(thm)],[c_20660,c_21035])).

cnf(c_54858,plain,
    ( k2_xboole_0(sP1_iProver_split,k2_xboole_0(X0,k2_xboole_0(X1,sK5))) = k2_xboole_0(k2_xboole_0(X1,sK5),X0) ),
    inference(light_normalisation,[status(thm)],[c_53294,c_34016])).

cnf(c_54859,plain,
    ( sP4_iProver_split(k2_xboole_0(X0,sK5),X1) = sP4_iProver_split(sP4_iProver_split(X1,X0),sK5) ),
    inference(demodulation,[status(thm)],[c_54858,c_3970,c_35092,c_53685])).

cnf(c_54860,plain,
    ( sP4_iProver_split(sP4_iProver_split(sK5,X0),X1) = sP4_iProver_split(sP4_iProver_split(X1,X0),sK5) ),
    inference(demodulation,[status(thm)],[c_54859,c_53685])).

cnf(c_54923,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(X0,X1)) = sP4_iProver_split(sP4_iProver_split(sK5,X1),X0) ),
    inference(demodulation,[status(thm)],[c_54920,c_54860])).

cnf(c_55935,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(sK4,k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))))) = sP4_iProver_split(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_55934,c_53685,c_54923])).

cnf(c_55936,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(sK4,k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X0,sP4_iProver_split(sK2,sK3)))))) = sP4_iProver_split(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_55935,c_53685])).

cnf(c_878,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(k2_xboole_0(sK5,X0),X1)) = k4_xboole_0(k4_xboole_0(sK4,k2_xboole_0(sK5,X0)),X1) ),
    inference(superposition,[status(thm)],[c_717,c_9])).

cnf(c_883,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(k2_xboole_0(sK5,X0),X1)) = k4_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1)) ),
    inference(demodulation,[status(thm)],[c_878,c_9])).

cnf(c_57989,plain,
    ( k4_xboole_0(sP4_iProver_split(sK2,sK3),k2_xboole_0(X0,k2_xboole_0(sK5,X1))) = k4_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(sK5,X1))) ),
    inference(demodulation,[status(thm)],[c_883,c_3970,c_53685])).

cnf(c_57990,plain,
    ( k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(k2_xboole_0(sK5,X0),X1)) = k4_xboole_0(sK4,sP4_iProver_split(k2_xboole_0(sK5,X0),X1)) ),
    inference(demodulation,[status(thm)],[c_57989,c_53685])).

cnf(c_57991,plain,
    ( k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(sK5,sP4_iProver_split(X0,X1))) = k4_xboole_0(sK4,sP4_iProver_split(sK5,sP4_iProver_split(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_57990,c_53685,c_54100])).

cnf(c_57995,plain,
    ( k4_xboole_0(sK4,sP4_iProver_split(sK5,sP4_iProver_split(sK4,k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X0,sP4_iProver_split(sK2,sK3))))))) = k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_55936,c_57991])).

cnf(c_58120,plain,
    ( k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(sK2,sK3)) = k4_xboole_0(sK4,sP4_iProver_split(sK2,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_57995,c_55936])).

cnf(c_39381,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)),X1) = k4_xboole_0(X1,X1) ),
    inference(superposition,[status(thm)],[c_10886,c_8])).

cnf(c_24102,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1733,c_23749])).

cnf(c_10745,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_605])).

cnf(c_24298,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)),X1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_24102,c_10745])).

cnf(c_39584,plain,
    ( k4_xboole_0(X0,X0) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_39381,c_24298,c_34016])).

cnf(c_58121,plain,
    ( k4_xboole_0(sK4,sP4_iProver_split(sK2,sK3)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_58120,c_39584])).

cnf(c_60286,plain,
    ( k4_xboole_0(sK4,sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(sK3,sK2))) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_58715,c_34016,c_35069,c_39054,c_58121,c_59354])).

cnf(c_21150,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1745,c_0])).

cnf(c_53745,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X2,X0)) = sP4_iProver_split(X2,X0) ),
    inference(demodulation,[status(thm)],[c_21150,c_53685])).

cnf(c_53848,plain,
    ( sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(X0,X1)) = sP4_iProver_split(X0,X1) ),
    inference(superposition,[status(thm)],[c_34829,c_53745])).

cnf(c_60287,plain,
    ( k4_xboole_0(sK4,sP4_iProver_split(sK3,sK2)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_60286,c_53848])).

cnf(c_26781,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,X0),sK2),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k4_xboole_0(sK4,X0),sK2) ),
    inference(superposition,[status(thm)],[c_26587,c_3133])).

cnf(c_58759,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,sP4_iProver_split(k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK4,sK4))),sP4_iProver_split(sK2,sK3))),sK2) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,sP4_iProver_split(sK2,sK3)),sK2),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_58704,c_26781])).

cnf(c_60195,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,sP4_iProver_split(k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK4,sK4))),sP4_iProver_split(sK2,sK3))),sK2) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,sP4_iProver_split(sK2,sK3)),sK2),k4_xboole_0(X0,sP4_iProver_split(sK3,sK2))) ),
    inference(demodulation,[status(thm)],[c_58759,c_59877])).

cnf(c_12481,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(X0,sK5))) ),
    inference(superposition,[status(thm)],[c_1259,c_616])).

cnf(c_44690,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK5,sK5))) = k4_xboole_0(k4_xboole_0(sK5,sK5),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2914,c_12481])).

cnf(c_34507,plain,
    ( k4_xboole_0(sP1_iProver_split,sP1_iProver_split) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_34369,c_34016])).

cnf(c_44808,plain,
    ( k4_xboole_0(sK4,sK4) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_44690,c_34016,c_34383,c_34507,c_35069])).

cnf(c_60196,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(sK3,sK2))),sK2) = k4_xboole_0(sK2,k4_xboole_0(X0,sP4_iProver_split(sK3,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_60195,c_35069,c_39054,c_44129,c_44808,c_58121,c_59354])).

cnf(c_60197,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,sP4_iProver_split(sK3,sK2))) = sP4_iProver_split(sK2,k4_xboole_0(sK4,sP4_iProver_split(sK3,sK2))) ),
    inference(demodulation,[status(thm)],[c_60196,c_53685,c_53848])).

cnf(c_60288,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,sP4_iProver_split(sK3,sK2))) = sP4_iProver_split(sK2,sP1_iProver_split) ),
    inference(demodulation,[status(thm)],[c_60287,c_60197])).

cnf(c_59031,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(sK4,sK4),sK5)),sP4_iProver_split(sK2,sK3))),sK2) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,sP4_iProver_split(sK2,sK3)),sK2),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_58974,c_26781])).

cnf(c_60046,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(sK4,sK4),sK5)),sP4_iProver_split(sK2,sK3))),sK2) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,sP4_iProver_split(sK2,sK3)),sK2),k4_xboole_0(X1,sP4_iProver_split(sK3,sK2))) ),
    inference(demodulation,[status(thm)],[c_59031,c_59877])).

cnf(c_60047,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(sP1_iProver_split,sK5)),sP4_iProver_split(sK3,sK2))),sK2) = k4_xboole_0(sK2,k4_xboole_0(X1,sP4_iProver_split(sK3,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_60046,c_44129,c_44808,c_58121,c_59354])).

cnf(c_60048,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,sP4_iProver_split(sK3,sK2))) = sP5_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP5_iProver_split])],[c_60047])).

cnf(c_60291,plain,
    ( sP4_iProver_split(sK2,sP1_iProver_split) = sP5_iProver_split ),
    inference(demodulation,[status(thm)],[c_60288,c_60048])).

cnf(c_24618,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,k2_xboole_0(X0,sK4)))) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_23964,c_1329])).

cnf(c_24623,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,k2_xboole_0(X0,sK4)))) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_24618,c_152])).

cnf(c_24714,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(sK3,k2_xboole_0(X1,sK4))))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_24623,c_243])).

cnf(c_48448,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK3,k2_xboole_0(X0,sK4))),X1),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,k2_xboole_0(X0,sK4)))) ),
    inference(superposition,[status(thm)],[c_505,c_24714])).

cnf(c_48561,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK3,k2_xboole_0(X0,sK4))),X1),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_48448,c_24623])).

cnf(c_57635,plain,
    ( sP4_iProver_split(sP4_iProver_split(sK2,sK3),k4_xboole_0(sP4_iProver_split(k4_xboole_0(sK3,k2_xboole_0(X0,sK4)),sK2),X1)) = sP4_iProver_split(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_48561,c_53685])).

cnf(c_57636,plain,
    ( sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(sK4,X0)),sK2),X1),sK2)) = sP4_iProver_split(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_57635,c_53685,c_54100])).

cnf(c_24125,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,X0),k2_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1674,c_23749])).

cnf(c_24794,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,X0),k2_xboole_0(sK4,k2_xboole_0(X1,sK5))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_961,c_24125])).

cnf(c_2244,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(sK4,k2_xboole_0(X0,sK5)) ),
    inference(superposition,[status(thm)],[c_0,c_1329])).

cnf(c_24094,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X3,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_244,c_23749])).

cnf(c_24882,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,X1)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_24794,c_9,c_2244,c_24094])).

cnf(c_60699,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,X1)))) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_24882,c_24882,c_34016])).

cnf(c_60700,plain,
    ( k4_xboole_0(sK5,sP4_iProver_split(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),X1)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_60699,c_24882,c_53685])).

cnf(c_60701,plain,
    ( k4_xboole_0(sK5,sP4_iProver_split(sK3,sP4_iProver_split(X0,k2_xboole_0(sK2,X1)))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_60700,c_53685,c_54100])).

cnf(c_60702,plain,
    ( k4_xboole_0(sK5,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(X1,sK2)))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_60701,c_53685])).

cnf(c_60707,plain,
    ( k4_xboole_0(sK5,sP4_iProver_split(sK3,sP4_iProver_split(sK2,sK3))) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_57636,c_60702])).

cnf(c_60801,plain,
    ( k4_xboole_0(sK5,sP4_iProver_split(sK3,sP4_iProver_split(sK3,sK2))) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_60707,c_59354])).

cnf(c_53589,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_21035,c_3027])).

cnf(c_2948,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1862,c_6])).

cnf(c_2956,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2948,c_518])).

cnf(c_54012,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = sP4_iProver_split(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_53589,c_2956,c_53685])).

cnf(c_54013,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(X0,X1)) = sP4_iProver_split(X1,X0) ),
    inference(demodulation,[status(thm)],[c_54012,c_2956,c_53685])).

cnf(c_59052,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_58974,c_24125])).

cnf(c_59985,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),k2_xboole_0(X0,sP4_iProver_split(sK3,sK2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_59052,c_59877])).

cnf(c_59986,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK3,sK2)),k2_xboole_0(X0,sP4_iProver_split(sK3,sK2))) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_59985,c_34016,c_59354])).

cnf(c_35098,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,k4_xboole_0(X0,sP1_iProver_split)),k4_xboole_0(X0,sP1_iProver_split)) = k4_xboole_0(k2_xboole_0(sK5,k4_xboole_0(X0,sP1_iProver_split)),X0) ),
    inference(superposition,[status(thm)],[c_34829,c_679])).

cnf(c_23268,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) ),
    inference(superposition,[status(thm)],[c_598,c_625])).

cnf(c_23587,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_23268,c_598])).

cnf(c_35166,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(X0,sP1_iProver_split)) = k4_xboole_0(sK5,X0) ),
    inference(demodulation,[status(thm)],[c_35098,c_8,c_23587])).

cnf(c_37416,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(X0,sP1_iProver_split),X1)) = k4_xboole_0(k4_xboole_0(sK5,X0),X1) ),
    inference(superposition,[status(thm)],[c_35166,c_9])).

cnf(c_37427,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,sP1_iProver_split),sK5),k4_xboole_0(sK5,k4_xboole_0(sK5,X0))) = k4_xboole_0(X0,sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_35166,c_598])).

cnf(c_34772,plain,
    ( k2_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k2_xboole_0(X1,sK5))) = k4_xboole_0(k4_xboole_0(X0,X1),sK5) ),
    inference(superposition,[status(thm)],[c_9,c_34092])).

cnf(c_33912,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),sK5)) = k4_xboole_0(k4_xboole_0(X0,X1),sK5) ),
    inference(superposition,[status(thm)],[c_23749,c_20476])).

cnf(c_34078,plain,
    ( k2_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,X1),sK5)) = k4_xboole_0(k4_xboole_0(X0,X1),sK5) ),
    inference(demodulation,[status(thm)],[c_33912,c_34016])).

cnf(c_34079,plain,
    ( k2_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k2_xboole_0(X1,sK5))) = k4_xboole_0(X0,k2_xboole_0(X1,sK5)) ),
    inference(demodulation,[status(thm)],[c_34078,c_9])).

cnf(c_34854,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,sK5)) = k4_xboole_0(k4_xboole_0(X0,X1),sK5) ),
    inference(light_normalisation,[status(thm)],[c_34772,c_34079])).

cnf(c_37460,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sP1_iProver_split,sK5)),k4_xboole_0(sK5,k4_xboole_0(sK5,X0))) = k4_xboole_0(X0,sP1_iProver_split) ),
    inference(demodulation,[status(thm)],[c_37427,c_34854])).

cnf(c_37461,plain,
    ( k4_xboole_0(X0,sP1_iProver_split) = X0 ),
    inference(demodulation,[status(thm)],[c_37460,c_598,c_35092])).

cnf(c_37615,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(sK5,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_37416,c_37461])).

cnf(c_59987,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sP4_iProver_split(sK3,sK2),sP4_iProver_split(sP4_iProver_split(sK3,sK2),X0))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_59986,c_37615,c_53685])).

cnf(c_59988,plain,
    ( k4_xboole_0(sK5,sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sK3,sK2),X0),sP4_iProver_split(sK3,sK2))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_59987,c_53685])).

cnf(c_1946,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_1749])).

cnf(c_21440,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1946])).

cnf(c_56077,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = sP4_iProver_split(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_21440,c_21440,c_53685])).

cnf(c_56078,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X0,X1)) = sP4_iProver_split(X1,X0) ),
    inference(demodulation,[status(thm)],[c_56077,c_21440,c_53685])).

cnf(c_56091,plain,
    ( sP4_iProver_split(k1_xboole_0,sP4_iProver_split(X0,k2_xboole_0(X1,X0))) = sP4_iProver_split(k2_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_1862,c_56078])).

cnf(c_56412,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,X1),X0) = sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_56091,c_34016,c_53685,c_54013])).

cnf(c_56413,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,X1),X0) = sP4_iProver_split(X1,X0) ),
    inference(demodulation,[status(thm)],[c_56412,c_53848,c_54100])).

cnf(c_59989,plain,
    ( k4_xboole_0(sK5,sP4_iProver_split(X0,sP4_iProver_split(sK3,sK2))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_59988,c_56413])).

cnf(c_60802,plain,
    ( k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_60801,c_54013,c_59989])).

cnf(c_60803,plain,
    ( k4_xboole_0(sK5,sP4_iProver_split(sK3,sK2)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_60802,c_59354])).

cnf(c_61315,plain,
    ( sP4_iProver_split(sP5_iProver_split,sK3) = sP4_iProver_split(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_59968,c_59968,c_60291,c_60803])).

cnf(c_65208,plain,
    ( k4_xboole_0(sP4_iProver_split(sK2,k4_xboole_0(sK4,X0)),k4_xboole_0(X1,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X2))) = sP4_iProver_split(sK2,k4_xboole_0(sK4,X0)) ),
    inference(light_normalisation,[status(thm)],[c_65207,c_61315])).

cnf(c_65209,plain,
    ( k4_xboole_0(sP4_iProver_split(sK2,k4_xboole_0(sK4,X0)),k4_xboole_0(X1,sP4_iProver_split(sK3,sP4_iProver_split(X2,sP5_iProver_split)))) = sP4_iProver_split(sK2,k4_xboole_0(sK4,X0)) ),
    inference(demodulation,[status(thm)],[c_65208,c_54100])).

cnf(c_65238,plain,
    ( k4_xboole_0(sP4_iProver_split(sK2,sP1_iProver_split),k4_xboole_0(X0,sP4_iProver_split(sK3,sP4_iProver_split(X1,sP5_iProver_split)))) = sP4_iProver_split(sK2,k4_xboole_0(sK4,sP4_iProver_split(k4_xboole_0(sK4,sK5),sP4_iProver_split(sK5,X2)))) ),
    inference(superposition,[status(thm)],[c_63041,c_65209])).

cnf(c_23911,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK3)),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_22126])).

cnf(c_56780,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK3)),k2_xboole_0(sK3,sK2)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_23911,c_23911,c_34016])).

cnf(c_56781,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK3),sP4_iProver_split(sK2,sK3))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_56780,c_10745,c_23911,c_53685])).

cnf(c_56782,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(sP4_iProver_split(sK2,sK3),k4_xboole_0(X0,sK3))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_56781,c_53685])).

cnf(c_56783,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(X0,sK3),sK2))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_56782,c_54100])).

cnf(c_32567,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(sK3,sK2)))) = k2_xboole_0(k4_xboole_0(sK5,X0),sK2) ),
    inference(superposition,[status(thm)],[c_1761,c_6382])).

cnf(c_64961,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),k4_xboole_0(X1,k2_xboole_0(X2,sP4_iProver_split(sK3,sK2)))) = k2_xboole_0(k4_xboole_0(sK5,X0),sK2) ),
    inference(light_normalisation,[status(thm)],[c_32567,c_32567,c_59877])).

cnf(c_64962,plain,
    ( k4_xboole_0(sP4_iProver_split(sK2,k4_xboole_0(sK5,X0)),k4_xboole_0(X1,sP4_iProver_split(sP4_iProver_split(sK3,sK2),X2))) = sP4_iProver_split(sK2,k4_xboole_0(sK5,X0)) ),
    inference(demodulation,[status(thm)],[c_64961,c_53685])).

cnf(c_64963,plain,
    ( k4_xboole_0(sP4_iProver_split(sK2,k4_xboole_0(sK5,X0)),k4_xboole_0(X1,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X2))) = sP4_iProver_split(sK2,k4_xboole_0(sK5,X0)) ),
    inference(light_normalisation,[status(thm)],[c_64962,c_61315])).

cnf(c_64964,plain,
    ( k4_xboole_0(sP4_iProver_split(sK2,k4_xboole_0(sK5,X0)),k4_xboole_0(X1,sP4_iProver_split(sK3,sP4_iProver_split(X2,sP5_iProver_split)))) = sP4_iProver_split(sK2,k4_xboole_0(sK5,X0)) ),
    inference(demodulation,[status(thm)],[c_64963,c_54100])).

cnf(c_64988,plain,
    ( k4_xboole_0(sP4_iProver_split(sK2,sP1_iProver_split),k4_xboole_0(X0,sP4_iProver_split(sK3,sP4_iProver_split(X1,sP5_iProver_split)))) = sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK3),sK2)))) ),
    inference(superposition,[status(thm)],[c_56783,c_64964])).

cnf(c_65137,plain,
    ( sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK3),sK2)))) = k4_xboole_0(sP5_iProver_split,k4_xboole_0(X0,sP4_iProver_split(sK3,sP4_iProver_split(X1,sP5_iProver_split)))) ),
    inference(light_normalisation,[status(thm)],[c_64988,c_60291])).

cnf(c_53307,plain,
    ( k2_xboole_0(sP1_iProver_split,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_34829,c_21035])).

cnf(c_54586,plain,
    ( k2_xboole_0(sP1_iProver_split,k2_xboole_0(X0,X1)) = sP4_iProver_split(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_53307,c_53685])).

cnf(c_54587,plain,
    ( sP4_iProver_split(X0,X1) = sP4_iProver_split(X1,X0) ),
    inference(demodulation,[status(thm)],[c_54586,c_35092,c_53685])).

cnf(c_37846,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK5),X0),sK3)) = k2_xboole_0(sK2,sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_37775,c_617])).

cnf(c_34995,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK3,sK2),sK3)) = k2_xboole_0(sK2,sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_34235,c_617])).

cnf(c_35025,plain,
    ( k2_xboole_0(sK2,sP1_iProver_split) = sK2 ),
    inference(demodulation,[status(thm)],[c_34995,c_509,c_1749,c_14982])).

cnf(c_37870,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK5),X0),sK3)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_37846,c_35025])).

cnf(c_14666,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X0)),X2)) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) ),
    inference(superposition,[status(thm)],[c_8,c_617])).

cnf(c_14989,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X0)),X2)) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_14666,c_617])).

cnf(c_14990,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_14989,c_2993])).

cnf(c_37871,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK5,k2_xboole_0(X0,sK3))) = sK2 ),
    inference(demodulation,[status(thm)],[c_37870,c_9,c_14990])).

cnf(c_53492,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(X0,sK3)),X1),sK2) = k2_xboole_0(k4_xboole_0(sK5,k2_xboole_0(X0,sK3)),sK2) ),
    inference(superposition,[status(thm)],[c_37871,c_21035])).

cnf(c_39083,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,k2_xboole_0(X0,sK3)),sK2) = k2_xboole_0(sK2,k4_xboole_0(sK5,k2_xboole_0(X0,sK3))) ),
    inference(superposition,[status(thm)],[c_37871,c_959])).

cnf(c_39120,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,k2_xboole_0(X0,sK3)),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_39083,c_37871])).

cnf(c_54189,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(X0,sK3)),X1),sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_53492,c_39120])).

cnf(c_54190,plain,
    ( sP4_iProver_split(sK2,k4_xboole_0(sK5,k2_xboole_0(k2_xboole_0(X0,sK3),X1))) = sK2 ),
    inference(demodulation,[status(thm)],[c_54189,c_37615,c_53685])).

cnf(c_54191,plain,
    ( sP4_iProver_split(sK2,k4_xboole_0(sK5,k2_xboole_0(sK3,k2_xboole_0(X0,X1)))) = sK2 ),
    inference(demodulation,[status(thm)],[c_54190,c_3970])).

cnf(c_54192,plain,
    ( sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(k2_xboole_0(X0,X1),sK3))) = sK2 ),
    inference(demodulation,[status(thm)],[c_54191,c_53685])).

cnf(c_54193,plain,
    ( sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(sP4_iProver_split(X0,X1),sK3))) = sK2 ),
    inference(demodulation,[status(thm)],[c_54192,c_53685])).

cnf(c_54690,plain,
    ( sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(sK3,sP4_iProver_split(X0,X1)))) = sK2 ),
    inference(demodulation,[status(thm)],[c_54587,c_54193])).

cnf(c_65138,plain,
    ( k4_xboole_0(sP5_iProver_split,k4_xboole_0(X0,sP4_iProver_split(sK3,sP4_iProver_split(X1,sP5_iProver_split)))) = sK2 ),
    inference(demodulation,[status(thm)],[c_65137,c_54690])).

cnf(c_65379,plain,
    ( sP4_iProver_split(sK2,k4_xboole_0(sK4,sP4_iProver_split(k4_xboole_0(sK4,sK5),sP4_iProver_split(sK5,X0)))) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_65238,c_60291,c_65138])).

cnf(c_65380,plain,
    ( sP5_iProver_split = sK2 ),
    inference(demodulation,[status(thm)],[c_65379,c_60291,c_63041])).

cnf(c_153845,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,sK4),sP5_iProver_split)) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_42651,c_42651,c_52854,c_65380])).

cnf(c_8571,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(k4_xboole_0(sK5,sK4),X0)) = k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(sK5,sK4))) ),
    inference(superposition,[status(thm)],[c_6,c_4236])).

cnf(c_8637,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(sK5,sK4))) = k4_xboole_0(sK4,X0) ),
    inference(demodulation,[status(thm)],[c_8571,c_4236])).

cnf(c_14708,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1733,c_617])).

cnf(c_14920,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_14708,c_6])).

cnf(c_3801,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_3755])).

cnf(c_114158,plain,
    ( k4_xboole_0(sP4_iProver_split(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,sP4_iProver_split(X2,X1))) = X2 ),
    inference(demodulation,[status(thm)],[c_3801,c_53685])).

cnf(c_114474,plain,
    ( k2_xboole_0(X0,k4_xboole_0(sP4_iProver_split(k4_xboole_0(X1,X2),X0),X0)) = sP4_iProver_split(k4_xboole_0(X1,X2),X0) ),
    inference(superposition,[status(thm)],[c_114158,c_153])).

cnf(c_1049,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_11,c_8])).

cnf(c_2992,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_244,c_509])).

cnf(c_81266,plain,
    ( k4_xboole_0(sP4_iProver_split(k2_xboole_0(X0,X1),X2),X1) = k4_xboole_0(sP4_iProver_split(X0,X2),X1) ),
    inference(demodulation,[status(thm)],[c_1049,c_2992,c_53685])).

cnf(c_81267,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),X2) = k4_xboole_0(sP4_iProver_split(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_81266,c_53685,c_54100])).

cnf(c_81270,plain,
    ( k4_xboole_0(sP4_iProver_split(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(sP4_iProver_split(X2,X0),X0) ),
    inference(superposition,[status(thm)],[c_53745,c_81267])).

cnf(c_14699,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_505,c_617])).

cnf(c_14935,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_14699,c_6])).

cnf(c_48921,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_14935,c_509])).

cnf(c_49082,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_48921,c_9,c_509])).

cnf(c_73136,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) ),
    inference(superposition,[status(thm)],[c_8,c_49082])).

cnf(c_74075,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_73136,c_49082])).

cnf(c_74076,plain,
    ( k4_xboole_0(sP4_iProver_split(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_74075,c_53685])).

cnf(c_81941,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_81270,c_74076])).

cnf(c_114564,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,X1),X2) = k2_xboole_0(X2,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_114474,c_6,c_81941])).

cnf(c_115896,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_114564,c_0])).

cnf(c_116980,plain,
    ( sP4_iProver_split(k4_xboole_0(sP4_iProver_split(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,sP4_iProver_split(X2,X1))),X3) = k2_xboole_0(X2,X3) ),
    inference(superposition,[status(thm)],[c_114158,c_115896])).

cnf(c_117418,plain,
    ( sP4_iProver_split(X0,X1) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_116980,c_114158])).

cnf(c_149287,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = sP4_iProver_split(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_14920,c_14920,c_117418])).

cnf(c_149341,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(X0,k4_xboole_0(sK4,sK4))) = sP4_iProver_split(k4_xboole_0(sK5,sK4),X0) ),
    inference(superposition,[status(thm)],[c_8637,c_149287])).

cnf(c_149932,plain,
    ( sP4_iProver_split(k4_xboole_0(sK5,sK4),X0) = k2_xboole_0(k4_xboole_0(sK5,sK4),X0) ),
    inference(light_normalisation,[status(thm)],[c_149341,c_37461,c_44808])).

cnf(c_33427,plain,
    ( k2_xboole_0(X0,k4_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(sK4,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_17194,c_1749])).

cnf(c_713,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(sK3,sK2))) = k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_512,c_1])).

cnf(c_3322,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5)) = k4_xboole_0(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2914,c_713])).

cnf(c_3323,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5)) = sK5 ),
    inference(demodulation,[status(thm)],[c_3322,c_7])).

cnf(c_3129,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_3026])).

cnf(c_109280,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(k4_xboole_0(sK4,sK5),k2_xboole_0(sK3,sK2)))) = k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_3323,c_3129])).

cnf(c_2936,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK5),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2281,c_1862])).

cnf(c_109497,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,sK5)),k4_xboole_0(k2_xboole_0(sK2,sK5),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,sK5)) ),
    inference(superposition,[status(thm)],[c_2936,c_3129])).

cnf(c_110073,plain,
    ( k4_xboole_0(k4_xboole_0(sP4_iProver_split(sK3,sK2),k2_xboole_0(sP5_iProver_split,sK5)),k4_xboole_0(k2_xboole_0(sP5_iProver_split,sK5),sP1_iProver_split)) = k4_xboole_0(sP4_iProver_split(sK3,sK2),k2_xboole_0(sP5_iProver_split,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_109497,c_34016,c_59877,c_65380])).

cnf(c_20604,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_622,c_8])).

cnf(c_20628,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_20604,c_6,c_9,c_1862])).

cnf(c_52086,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_20628,c_20628,c_34016])).

cnf(c_52459,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),X3)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),sP1_iProver_split),X3) ),
    inference(superposition,[status(thm)],[c_52086,c_605])).

cnf(c_52470,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_52086,c_616])).

cnf(c_681,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_9,c_10])).

cnf(c_701,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_681,c_9])).

cnf(c_52492,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),sP1_iProver_split) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_52470,c_701])).

cnf(c_52507,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(demodulation,[status(thm)],[c_52459,c_52492])).

cnf(c_28190,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_9,c_696])).

cnf(c_28464,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
    inference(light_normalisation,[status(thm)],[c_28190,c_17153])).

cnf(c_17142,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),X3) ),
    inference(superposition,[status(thm)],[c_16936,c_605])).

cnf(c_17177,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),X3) ),
    inference(light_normalisation,[status(thm)],[c_17142,c_9])).

cnf(c_17178,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X2),k2_xboole_0(X1,X3))) ),
    inference(demodulation,[status(thm)],[c_17177,c_9,c_3970])).

cnf(c_28465,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_28464,c_9,c_17178])).

cnf(c_52508,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(light_normalisation,[status(thm)],[c_52507,c_17153,c_28465])).

cnf(c_39067,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(X1,sK3)))) = sK2 ),
    inference(superposition,[status(thm)],[c_11,c_37871])).

cnf(c_66817,plain,
    ( k2_xboole_0(sP5_iProver_split,k4_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(X1,sK3)))) = sP5_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_39067,c_39067,c_65380])).

cnf(c_66818,plain,
    ( sP4_iProver_split(k4_xboole_0(sK5,sP4_iProver_split(k2_xboole_0(X0,sK3),X1)),sP5_iProver_split) = sP5_iProver_split ),
    inference(demodulation,[status(thm)],[c_66817,c_53685])).

cnf(c_66819,plain,
    ( sP4_iProver_split(k4_xboole_0(sK5,sP4_iProver_split(X0,sP4_iProver_split(X1,sK3))),sP5_iProver_split) = sP5_iProver_split ),
    inference(demodulation,[status(thm)],[c_66818,c_53685,c_54100])).

cnf(c_66832,plain,
    ( k4_xboole_0(sK4,sP4_iProver_split(sK5,sP4_iProver_split(k4_xboole_0(sK5,sP4_iProver_split(X0,sP4_iProver_split(X1,sK3))),sP5_iProver_split))) = k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(sK5,sP5_iProver_split)) ),
    inference(superposition,[status(thm)],[c_66819,c_57991])).

cnf(c_66850,plain,
    ( k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(sK5,sP5_iProver_split)) = k4_xboole_0(sK4,sP4_iProver_split(sK5,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_66832,c_66819])).

cnf(c_66851,plain,
    ( k4_xboole_0(sP4_iProver_split(sK3,sK2),sP4_iProver_split(sK5,sP5_iProver_split)) = k4_xboole_0(sK4,sP4_iProver_split(sK5,sP5_iProver_split)) ),
    inference(light_normalisation,[status(thm)],[c_66850,c_59354])).

cnf(c_66852,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sK5,sP5_iProver_split)) = k4_xboole_0(sK4,sP4_iProver_split(sK5,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_66851,c_61315])).

cnf(c_110074,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sP4_iProver_split(sK5,sP5_iProver_split),k2_xboole_0(sP5_iProver_split,sK5))) = k4_xboole_0(sK4,sP4_iProver_split(sK5,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_110073,c_9,c_37461,c_52508,c_53685,c_61315,c_66852])).

cnf(c_39006,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(sK2,k2_xboole_0(X0,k2_xboole_0(X1,sK4)))) = sK5 ),
    inference(superposition,[status(thm)],[c_11,c_37861])).

cnf(c_66499,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(sP5_iProver_split,k2_xboole_0(X0,k2_xboole_0(X1,sK4)))) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_39006,c_39006,c_65380])).

cnf(c_66500,plain,
    ( sP4_iProver_split(k4_xboole_0(sP5_iProver_split,sP4_iProver_split(k2_xboole_0(X0,sK4),X1)),sK5) = sK5 ),
    inference(demodulation,[status(thm)],[c_66499,c_53685])).

cnf(c_66501,plain,
    ( sP4_iProver_split(k4_xboole_0(sP5_iProver_split,sP4_iProver_split(X0,sP4_iProver_split(X1,sK4))),sK5) = sK5 ),
    inference(demodulation,[status(thm)],[c_66500,c_53685,c_54100])).

cnf(c_56185,plain,
    ( sP4_iProver_split(k4_xboole_0(k4_xboole_0(X0,X1),sP4_iProver_split(X2,X0)),sP4_iProver_split(X2,X0)) = sP4_iProver_split(sP4_iProver_split(X2,X0),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_53745,c_56078])).

cnf(c_56206,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(k4_xboole_0(X0,X1),X2)) = sP4_iProver_split(X2,X0) ),
    inference(demodulation,[status(thm)],[c_56185,c_9,c_53745,c_54100])).

cnf(c_74657,plain,
    ( sP4_iProver_split(sP5_iProver_split,sK5) = sP4_iProver_split(sK5,sP5_iProver_split) ),
    inference(superposition,[status(thm)],[c_66501,c_56206])).

cnf(c_8591,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(k4_xboole_0(sK5,sK4),X0)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK4),X0),k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_4236,c_3027])).

cnf(c_2608,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_245])).

cnf(c_5761,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK2,sK5)),X1)) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1) ),
    inference(superposition,[status(thm)],[c_2298,c_11])).

cnf(c_5781,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK2,sK5)),X1)) = k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_5761,c_1512])).

cnf(c_2249,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(sK5,X1))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_243,c_1329])).

cnf(c_5782,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sK3,sK2)) ),
    inference(demodulation,[status(thm)],[c_5781,c_2249,c_2590,c_3970])).

cnf(c_8614,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK4),X0))) = k2_xboole_0(X0,k2_xboole_0(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_8591,c_2608,c_5782])).

cnf(c_8615,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK4),X0))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_8614,c_152])).

cnf(c_8688,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK4),X0))) = k4_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK4),X0))) ),
    inference(superposition,[status(thm)],[c_8615,c_8])).

cnf(c_76121,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sP4_iProver_split(sK3,sK2)),k2_xboole_0(sP5_iProver_split,k2_xboole_0(k4_xboole_0(sK5,sK4),X0))) = k4_xboole_0(sK3,k2_xboole_0(sP5_iProver_split,k2_xboole_0(k4_xboole_0(sK5,sK4),X0))) ),
    inference(light_normalisation,[status(thm)],[c_8688,c_8688,c_59877,c_65380])).

cnf(c_76122,plain,
    ( k4_xboole_0(sP4_iProver_split(sP4_iProver_split(sK3,sK2),X0),sP4_iProver_split(k2_xboole_0(k4_xboole_0(sK5,sK4),X0),sP5_iProver_split)) = k4_xboole_0(sK3,sP4_iProver_split(k2_xboole_0(k4_xboole_0(sK5,sK4),X0),sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_76121,c_53685])).

cnf(c_76123,plain,
    ( k4_xboole_0(sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X0),sP4_iProver_split(k2_xboole_0(k4_xboole_0(sK5,sK4),X0),sP5_iProver_split)) = k4_xboole_0(sK3,sP4_iProver_split(k2_xboole_0(k4_xboole_0(sK5,sK4),X0),sP5_iProver_split)) ),
    inference(light_normalisation,[status(thm)],[c_76122,c_61315])).

cnf(c_76124,plain,
    ( k4_xboole_0(sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)),sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,X0))) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,X0))) ),
    inference(demodulation,[status(thm)],[c_76123,c_53685,c_54100])).

cnf(c_39411,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK5),X1)))) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_10886,c_2244])).

cnf(c_39565,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK5),X1)))) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_39411,c_152])).

cnf(c_40473,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,sK5),X2))))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_39565,c_243])).

cnf(c_67460,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sP5_iProver_split,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,sK5),X2))))) = k2_xboole_0(X0,sP4_iProver_split(sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_40473,c_40473,c_59877,c_65380])).

cnf(c_67461,plain,
    ( sP4_iProver_split(sP4_iProver_split(k2_xboole_0(sP5_iProver_split,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK5),X1))),X2),sK3) = sP4_iProver_split(sK3,sP4_iProver_split(X2,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_67460,c_53685,c_54100,c_61315])).

cnf(c_67462,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,sK5),X2))),sP4_iProver_split(sK3,sP5_iProver_split)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_67461,c_53685,c_54100])).

cnf(c_1331,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(X0,X1))) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK3,sK2),X1)) ),
    inference(superposition,[status(thm)],[c_1044,c_243])).

cnf(c_1525,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) = k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
    inference(superposition,[status(thm)],[c_1237,c_243])).

cnf(c_16087,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK2,k2_xboole_0(sK3,X1))) = k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_1331,c_1525,c_3970])).

cnf(c_16088,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(X0,X1))) = k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2))) ),
    inference(demodulation,[status(thm)],[c_16087,c_1525,c_1703])).

cnf(c_26786,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(X0,k4_xboole_0(sK4,X1)))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_26587,c_16088])).

cnf(c_37109,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK4,X1))),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(sK4,X1))) ),
    inference(superposition,[status(thm)],[c_1733,c_26786])).

cnf(c_37241,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK4,X1))),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_37109,c_1525,c_14817,c_26587])).

cnf(c_65299,plain,
    ( k2_xboole_0(k4_xboole_0(sP4_iProver_split(sK2,k4_xboole_0(sK4,X0)),sP4_iProver_split(sK2,k4_xboole_0(sK4,X0))),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_65209,c_37241])).

cnf(c_65759,plain,
    ( k2_xboole_0(k4_xboole_0(sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK4,X0)),sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK4,X0))),sP4_iProver_split(sK3,sK2)) = sP4_iProver_split(sK3,sP5_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_65299,c_59877,c_65380])).

cnf(c_65760,plain,
    ( sP4_iProver_split(sK3,sP5_iProver_split) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(demodulation,[status(thm)],[c_65759,c_35092,c_39584,c_53685,c_61315])).

cnf(c_67463,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,sK5),X2))),sP4_iProver_split(sP5_iProver_split,sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)) ),
    inference(light_normalisation,[status(thm)],[c_67462,c_65760])).

cnf(c_67464,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X0,sK5))),sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X2)) = sP4_iProver_split(sK3,sP4_iProver_split(X2,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_67463,c_53685,c_54100])).

cnf(c_40469,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK5),X1))),k2_xboole_0(sK3,X2)) = k2_xboole_0(X2,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_39565,c_244])).

cnf(c_67315,plain,
    ( k2_xboole_0(k2_xboole_0(sP5_iProver_split,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK5),X1))),k2_xboole_0(sK3,X2)) = k2_xboole_0(X2,sP4_iProver_split(sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_40469,c_40469,c_59877,c_65380])).

cnf(c_67316,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,sK3),sP4_iProver_split(k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,sK5),X2)),sP5_iProver_split)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_67315,c_3970,c_53685,c_54100,c_61315])).

cnf(c_67317,plain,
    ( sP4_iProver_split(sK3,sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X0,sK5))),sP5_iProver_split),X2)) = sP4_iProver_split(sK3,sP4_iProver_split(X2,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_67316,c_53685,c_54100])).

cnf(c_67318,plain,
    ( sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,k4_xboole_0(X1,sP4_iProver_split(X2,k4_xboole_0(X1,sK5)))))) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_67317,c_54100])).

cnf(c_67346,plain,
    ( sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,k4_xboole_0(X1,sP4_iProver_split(X2,k4_xboole_0(X1,sK5)))))),sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split))) = sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,k4_xboole_0(X1,sP4_iProver_split(X2,k4_xboole_0(X1,sK5))))),sK3) ),
    inference(superposition,[status(thm)],[c_67318,c_56078])).

cnf(c_53512,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_21035,c_0])).

cnf(c_54150,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = sP4_iProver_split(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_53512,c_53685])).

cnf(c_54151,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X0,X2)) = sP4_iProver_split(X2,X0) ),
    inference(demodulation,[status(thm)],[c_54150,c_3970,c_53685])).

cnf(c_67359,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X0,sK5))),sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X2)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X2)) ),
    inference(demodulation,[status(thm)],[c_67346,c_54100,c_54151,c_65760])).

cnf(c_67360,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X0,sK5))),sP4_iProver_split(sK3,sP4_iProver_split(X2,sP5_iProver_split))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X2)) ),
    inference(demodulation,[status(thm)],[c_67359,c_54100])).

cnf(c_67465,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_67464,c_54100,c_67360])).

cnf(c_76125,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0)),sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,X0))) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,X0))) ),
    inference(light_normalisation,[status(thm)],[c_76124,c_67465])).

cnf(c_76137,plain,
    ( k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,sK5))) = k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sK5)),sP4_iProver_split(sP5_iProver_split,sK5)) ),
    inference(superposition,[status(thm)],[c_53745,c_76125])).

cnf(c_9863,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK5),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_8,c_5792])).

cnf(c_37492,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK2,sK5)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_9863,c_0])).

cnf(c_63315,plain,
    ( k2_xboole_0(sP4_iProver_split(sK3,sK2),k4_xboole_0(sK2,sK5)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(light_normalisation,[status(thm)],[c_37492,c_37492,c_59877,c_61315])).

cnf(c_63316,plain,
    ( sP4_iProver_split(k4_xboole_0(sK2,sK5),sP4_iProver_split(sP5_iProver_split,sK3)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(demodulation,[status(thm)],[c_63315,c_53685,c_61315])).

cnf(c_960,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_6,c_243])).

cnf(c_68488,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,X1),X2),X1) = sP4_iProver_split(X1,sP4_iProver_split(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_960,c_53685,c_54100])).

cnf(c_68504,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),sK2)) = sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),sK5) ),
    inference(superposition,[status(thm)],[c_63316,c_68488])).

cnf(c_69261,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),sP5_iProver_split)) = sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),sK5) ),
    inference(light_normalisation,[status(thm)],[c_68504,c_65380])).

cnf(c_69262,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sK5)) = sP4_iProver_split(sK5,sP4_iProver_split(sK3,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_69261,c_54100,c_56413,c_67465])).

cnf(c_3917,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK5),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) ),
    inference(superposition,[status(thm)],[c_2281,c_959])).

cnf(c_3984,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK5),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_3917,c_2281])).

cnf(c_4838,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,sK2),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_0,c_3984])).

cnf(c_30791,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_4838,c_0])).

cnf(c_17523,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK2,sK4),X0)) = k2_xboole_0(sK5,X0) ),
    inference(superposition,[status(thm)],[c_15328,c_11])).

cnf(c_49785,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) = k2_xboole_0(sK5,sK2) ),
    inference(superposition,[status(thm)],[c_598,c_17523])).

cnf(c_49909,plain,
    ( k2_xboole_0(sK5,k1_xboole_0) = k2_xboole_0(sK5,sK2) ),
    inference(light_normalisation,[status(thm)],[c_49785,c_15262])).

cnf(c_49910,plain,
    ( k2_xboole_0(sK5,sK2) = sK5 ),
    inference(demodulation,[status(thm)],[c_49909,c_518])).

cnf(c_62865,plain,
    ( k2_xboole_0(sP4_iProver_split(sK3,sK2),sK5) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(light_normalisation,[status(thm)],[c_30791,c_30791,c_49910,c_59877,c_61315])).

cnf(c_62866,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(sP5_iProver_split,sK3)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(demodulation,[status(thm)],[c_62865,c_53685,c_61315])).

cnf(c_69263,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sK5)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(light_normalisation,[status(thm)],[c_69262,c_62866,c_65760])).

cnf(c_76277,plain,
    ( k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,sK5))) = k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sP5_iProver_split,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_76137,c_69263])).

cnf(c_53449,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK5),X1),k2_xboole_0(X0,k2_xboole_0(sK5,k4_xboole_0(X2,sK4)))) = k2_xboole_0(k2_xboole_0(X0,sK5),k4_xboole_0(X2,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_15298,c_21035])).

cnf(c_21042,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X0,k2_xboole_0(X1,X3))) = k2_xboole_0(k2_xboole_0(X0,X1),X3) ),
    inference(superposition,[status(thm)],[c_11,c_1745])).

cnf(c_21328,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X0,k2_xboole_0(X1,X3))) = k2_xboole_0(X1,k2_xboole_0(X0,X3)) ),
    inference(demodulation,[status(thm)],[c_21042,c_3970])).

cnf(c_46553,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK5),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK5,k4_xboole_0(X1,sK4))) ),
    inference(superposition,[status(thm)],[c_15298,c_0])).

cnf(c_54290,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,sK4),sK5),X1) = sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,sK4),X1),sK5) ),
    inference(demodulation,[status(thm)],[c_53449,c_21328,c_46553,c_53685])).

cnf(c_54684,plain,
    ( sP4_iProver_split(sP4_iProver_split(sK5,k4_xboole_0(X0,sK4)),X1) = sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,sK4),X1),sK5) ),
    inference(demodulation,[status(thm)],[c_54587,c_54290])).

cnf(c_54706,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,sK4),sP4_iProver_split(X1,sK5)) = sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,sK4),X1),sK5) ),
    inference(demodulation,[status(thm)],[c_54684,c_54100])).

cnf(c_54924,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(k4_xboole_0(X0,sK4),X1)) = sP4_iProver_split(k4_xboole_0(X0,sK4),sP4_iProver_split(X1,sK5)) ),
    inference(demodulation,[status(thm)],[c_54920,c_54706])).

cnf(c_74812,plain,
    ( k4_xboole_0(sK4,sP4_iProver_split(sK5,sP4_iProver_split(k4_xboole_0(sK5,X0),X1))) = k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(X1,sK5)) ),
    inference(superposition,[status(thm)],[c_56206,c_57991])).

cnf(c_74856,plain,
    ( k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(X0,sK5)) = k4_xboole_0(sK4,sP4_iProver_split(X0,sK5)) ),
    inference(demodulation,[status(thm)],[c_74812,c_56206])).

cnf(c_74857,plain,
    ( k4_xboole_0(sP4_iProver_split(sK3,sK2),sP4_iProver_split(X0,sK5)) = k4_xboole_0(sK4,sP4_iProver_split(X0,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_74856,c_59354])).

cnf(c_74858,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(X0,sK5)) = k4_xboole_0(sK4,sP4_iProver_split(X0,sK5)) ),
    inference(demodulation,[status(thm)],[c_74857,c_61315])).

cnf(c_76278,plain,
    ( k4_xboole_0(sK3,sP4_iProver_split(sK5,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP5_iProver_split))) = k4_xboole_0(sK4,sP4_iProver_split(sP5_iProver_split,sK5)) ),
    inference(demodulation,[status(thm)],[c_76277,c_54924,c_74858])).

cnf(c_13657,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK2,sK4),sK4))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),sK4),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3349,c_12475])).

cnf(c_13710,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK2,sK4))) = k4_xboole_0(sK2,sK4) ),
    inference(demodulation,[status(thm)],[c_13657,c_8,c_9,c_518])).

cnf(c_962,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_153,c_243])).

cnf(c_72427,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(X0,X1)) = sP4_iProver_split(X0,X2) ),
    inference(demodulation,[status(thm)],[c_962,c_53685])).

cnf(c_72458,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK2,sK4),X0),k4_xboole_0(sK5,k4_xboole_0(sK2,sK4))) = sP4_iProver_split(sK5,X0) ),
    inference(superposition,[status(thm)],[c_13710,c_72427])).

cnf(c_52077,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK4,k4_xboole_0(sK2,sK2))) = k4_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_18162,c_16936])).

cnf(c_34373,plain,
    ( k4_xboole_0(sK2,sP1_iProver_split) = sK2 ),
    inference(superposition,[status(thm)],[c_34187,c_3133])).

cnf(c_14703,plain,
    ( k2_xboole_0(sK4,k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK4,k4_xboole_0(X0,sK5)) ),
    inference(superposition,[status(thm)],[c_1259,c_617])).

cnf(c_35001,plain,
    ( k2_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),sK5)) = k2_xboole_0(sK4,sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_34235,c_14703])).

cnf(c_35016,plain,
    ( k2_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = k2_xboole_0(sK4,sP1_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_35001,c_512])).

cnf(c_35017,plain,
    ( k2_xboole_0(sK4,sP1_iProver_split) = sK4 ),
    inference(demodulation,[status(thm)],[c_35016,c_1749])).

cnf(c_39080,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(X0,sK3)),sK2) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_37871,c_509])).

cnf(c_39084,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(X0,sK3)),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_37871,c_1862])).

cnf(c_39119,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(X0,sK3)),sK2) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_39084,c_34016])).

cnf(c_39123,plain,
    ( k4_xboole_0(sK2,sK2) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_39080,c_39119])).

cnf(c_52847,plain,
    ( k4_xboole_0(sK2,sK4) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_52077,c_34373,c_35017,c_39123,c_52081])).

cnf(c_72986,plain,
    ( sP4_iProver_split(sP4_iProver_split(sK2,X0),k4_xboole_0(sK5,sK2)) = sP4_iProver_split(sK5,X0) ),
    inference(light_normalisation,[status(thm)],[c_72458,c_52847])).

cnf(c_68517,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X2,k2_xboole_0(X1,X0))) = sP4_iProver_split(sP4_iProver_split(X1,X2),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3755,c_68488])).

cnf(c_53754,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X2,k2_xboole_0(X1,X0))) = sP4_iProver_split(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_509,c_53745])).

cnf(c_53990,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X2,sP4_iProver_split(X0,X1))) = sP4_iProver_split(X2,sP4_iProver_split(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_53754,c_53685])).

cnf(c_69185,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,X1),k4_xboole_0(X2,X0)) = sP4_iProver_split(X1,sP4_iProver_split(X2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_68517,c_53685,c_53990])).

cnf(c_72987,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(sK5,sP5_iProver_split)) = sP4_iProver_split(sK5,X0) ),
    inference(demodulation,[status(thm)],[c_72986,c_65380,c_69185])).

cnf(c_6408,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK5),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK2,sK5) ),
    inference(superposition,[status(thm)],[c_2281,c_3133])).

cnf(c_72646,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(k2_xboole_0(sK2,sK5),k2_xboole_0(sK2,sK5)),X0),k2_xboole_0(sK2,sK5)) = sP4_iProver_split(k2_xboole_0(sK2,sK5),X0) ),
    inference(superposition,[status(thm)],[c_6408,c_72427])).

cnf(c_72872,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(k2_xboole_0(sP5_iProver_split,sK5),k2_xboole_0(sP5_iProver_split,sK5)),X0),k2_xboole_0(sP5_iProver_split,sK5)) = sP4_iProver_split(k2_xboole_0(sP5_iProver_split,sK5),X0) ),
    inference(light_normalisation,[status(thm)],[c_72646,c_65380])).

cnf(c_6398,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK5),k4_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k2_xboole_0(X0,sK5) ),
    inference(superposition,[status(thm)],[c_961,c_3133])).

cnf(c_48976,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0))) = k4_xboole_0(X2,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_14935,c_16936])).

cnf(c_6410,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1749,c_3133])).

cnf(c_49022,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X2,k2_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_48976,c_6410])).

cnf(c_49023,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_49022,c_9,c_1862,c_34016])).

cnf(c_49402,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(X0,sK5)) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_6398,c_49023])).

cnf(c_68515,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(X1,X0)) = sP4_iProver_split(sP4_iProver_split(k1_xboole_0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1849,c_68488])).

cnf(c_53801,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(X1,X0)) = sP4_iProver_split(X1,X0) ),
    inference(superposition,[status(thm)],[c_6382,c_53745])).

cnf(c_69243,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP1_iProver_split,X0),X1) = sP4_iProver_split(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_68515,c_34016,c_53801])).

cnf(c_72873,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(X0,sP5_iProver_split)) = sP4_iProver_split(X0,sP4_iProver_split(sK5,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_72872,c_49402,c_53685,c_54923,c_68488,c_69243])).

cnf(c_72989,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(X0,sP5_iProver_split)) = sP4_iProver_split(sK5,X0) ),
    inference(demodulation,[status(thm)],[c_72987,c_72873])).

cnf(c_76279,plain,
    ( k4_xboole_0(sK3,sP4_iProver_split(sK5,k4_xboole_0(sK5,sK4))) = k4_xboole_0(sK4,sP4_iProver_split(sP5_iProver_split,sK5)) ),
    inference(demodulation,[status(thm)],[c_76278,c_72989])).

cnf(c_4240,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,sK4),sK4) = k4_xboole_0(sK5,sK4) ),
    inference(superposition,[status(thm)],[c_3765,c_3026])).

cnf(c_1943,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_1749])).

cnf(c_15292,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1)) = k2_xboole_0(X1,k2_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
    inference(superposition,[status(thm)],[c_14697,c_245])).

cnf(c_45051,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(sK3,sK2)))),k2_xboole_0(sK5,k4_xboole_0(X1,sK4))) = k2_xboole_0(sK5,k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_1943,c_15292])).

cnf(c_45225,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(sK3,sK2)))),k2_xboole_0(sK5,k4_xboole_0(X1,sK4))) = k2_xboole_0(sK5,k4_xboole_0(X1,sK4)) ),
    inference(demodulation,[status(thm)],[c_45051,c_14697])).

cnf(c_72065,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,sP4_iProver_split(sK3,sK2)))),k2_xboole_0(sK5,k4_xboole_0(X1,sK4))) = k2_xboole_0(sK5,k4_xboole_0(X1,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_45225,c_45225,c_59877])).

cnf(c_72066,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,sK4),sK5),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3))))) = sP4_iProver_split(k4_xboole_0(X0,sK4),sK5) ),
    inference(demodulation,[status(thm)],[c_72065,c_53685,c_61315])).

cnf(c_72075,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK5,sK4),sK5),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,sK3))))) = sP4_iProver_split(k4_xboole_0(k4_xboole_0(sK5,sK4),sK4),sK5) ),
    inference(superposition,[status(thm)],[c_4240,c_72066])).

cnf(c_72200,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK5,sK4),sK5),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,sK3))))) = sP4_iProver_split(k4_xboole_0(sK5,sK4),sK5) ),
    inference(light_normalisation,[status(thm)],[c_72075,c_4240])).

cnf(c_53274,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k2_xboole_0(X3,X1)) = k2_xboole_0(X1,X3) ),
    inference(superposition,[status(thm)],[c_16936,c_21035])).

cnf(c_54884,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X3)))) = sP4_iProver_split(X1,X0) ),
    inference(demodulation,[status(thm)],[c_53274,c_53685])).

cnf(c_24589,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(X1,sK4)))) = sK5 ),
    inference(superposition,[status(thm)],[c_11,c_23964])).

cnf(c_58209,plain,
    ( sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(k2_xboole_0(X0,sK4),X1)),sK5) = sK5 ),
    inference(demodulation,[status(thm)],[c_24589,c_53685])).

cnf(c_58210,plain,
    ( sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(X0,sP4_iProver_split(X1,sK4))),sK5) = sK5 ),
    inference(demodulation,[status(thm)],[c_58209,c_53685,c_54100])).

cnf(c_58218,plain,
    ( sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(X0,sP4_iProver_split(X1,sK4))),sK5) = sP4_iProver_split(k4_xboole_0(sK5,X2),sK5) ),
    inference(superposition,[status(thm)],[c_58210,c_53745])).

cnf(c_58223,plain,
    ( sP4_iProver_split(k4_xboole_0(sK5,X0),sK5) = sK5 ),
    inference(demodulation,[status(thm)],[c_58218,c_58210])).

cnf(c_72201,plain,
    ( sP4_iProver_split(sK5,k4_xboole_0(sK5,sK4)) = sK5 ),
    inference(demodulation,[status(thm)],[c_72200,c_54884,c_58223])).

cnf(c_76280,plain,
    ( k4_xboole_0(sK4,sP4_iProver_split(sP5_iProver_split,sK5)) = k4_xboole_0(sK3,sK5) ),
    inference(light_normalisation,[status(thm)],[c_76279,c_72201])).

cnf(c_110075,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sP4_iProver_split(sP5_iProver_split,sK5),k2_xboole_0(sP5_iProver_split,sK5))) = k4_xboole_0(sK3,sK5) ),
    inference(light_normalisation,[status(thm)],[c_110074,c_74657,c_76280])).

cnf(c_81357,plain,
    ( k2_xboole_0(k4_xboole_0(sP4_iProver_split(X0,X1),X2),k4_xboole_0(X2,k4_xboole_0(X2,sP4_iProver_split(X0,sP4_iProver_split(X1,X2))))) = sP4_iProver_split(X0,sP4_iProver_split(X1,X2)) ),
    inference(superposition,[status(thm)],[c_81267,c_598])).

cnf(c_4115,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_6,c_1672])).

cnf(c_4224,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_4115,c_1672])).

cnf(c_23180,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k4_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(k2_xboole_0(X0,X2),X3)) ),
    inference(superposition,[status(thm)],[c_1745,c_625])).

cnf(c_23712,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X0,X3)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_23180,c_9,c_1865,c_3970])).

cnf(c_56494,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X0,X3)))) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_23712,c_23712,c_34016])).

cnf(c_56495,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(k2_xboole_0(X1,k2_xboole_0(X0,X2)),X3)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_56494,c_23712,c_53685])).

cnf(c_56496,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,k2_xboole_0(X0,X3)))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_56495,c_53685,c_54100])).

cnf(c_56497,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,sP4_iProver_split(X3,X0)))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_56496,c_53685])).

cnf(c_56504,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,X0))) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_53745,c_56497])).

cnf(c_81806,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(X1,X2)) = k2_xboole_0(sP4_iProver_split(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_81357,c_4224,c_37461,c_53685,c_56504])).

cnf(c_110076,plain,
    ( k4_xboole_0(sK4,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK5,k2_xboole_0(sP5_iProver_split,sK5)))) = k4_xboole_0(sK3,sK5) ),
    inference(demodulation,[status(thm)],[c_110075,c_81806])).

cnf(c_72669,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK5,k4_xboole_0(sK2,sK4)),X0),k4_xboole_0(sK2,sK4)) = sP4_iProver_split(sK5,X0) ),
    inference(superposition,[status(thm)],[c_13710,c_72427])).

cnf(c_72817,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK5,sK2),X0),sK2) = sP4_iProver_split(sK5,X0) ),
    inference(light_normalisation,[status(thm)],[c_72669,c_52847])).

cnf(c_72818,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK5)) = sP4_iProver_split(sK5,X0) ),
    inference(demodulation,[status(thm)],[c_72817,c_65380,c_68488])).

cnf(c_1947,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_9,c_1749])).

cnf(c_86711,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,X2)),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_1947,c_53685])).

cnf(c_86793,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,k1_xboole_0)),X0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_86711])).

cnf(c_87355,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,sP1_iProver_split)),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_86793,c_7,c_34016])).

cnf(c_970,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_243,c_8])).

cnf(c_97420,plain,
    ( k4_xboole_0(sP4_iProver_split(k2_xboole_0(X0,X1),X2),sP4_iProver_split(X1,X2)) = k4_xboole_0(X0,sP4_iProver_split(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_970,c_53685])).

cnf(c_97421,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),sP4_iProver_split(X2,X1)) = k4_xboole_0(X0,sP4_iProver_split(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_97420,c_53685,c_54100])).

cnf(c_98333,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,X1),sP4_iProver_split(X1,k4_xboole_0(X1,sP4_iProver_split(X2,sP1_iProver_split)))) = k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X1,sP4_iProver_split(X2,sP1_iProver_split)))) ),
    inference(superposition,[status(thm)],[c_87355,c_97421])).

cnf(c_74794,plain,
    ( sP4_iProver_split(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = sP4_iProver_split(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_56206,c_53745])).

cnf(c_74880,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X0) = sP4_iProver_split(X0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_74794,c_9])).

cnf(c_56174,plain,
    ( sP4_iProver_split(k1_xboole_0,sP4_iProver_split(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X0)) = sP4_iProver_split(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_24299,c_56078])).

cnf(c_56237,plain,
    ( sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X0)) = sP4_iProver_split(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_56174,c_34016])).

cnf(c_56238,plain,
    ( sP4_iProver_split(X0,k4_xboole_0(X0,sP4_iProver_split(X1,X2))) = sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,X2)),X0) ),
    inference(demodulation,[status(thm)],[c_56237,c_53685,c_53848])).

cnf(c_72432,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,X1),X0),k4_xboole_0(X0,X1)) = sP4_iProver_split(X0,sP4_iProver_split(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_56078,c_72427])).

cnf(c_73041,plain,
    ( sP4_iProver_split(X0,k4_xboole_0(X0,X1)) = sP4_iProver_split(k4_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_72432,c_54013,c_56413])).

cnf(c_74881,plain,
    ( sP4_iProver_split(X0,k4_xboole_0(X0,sP4_iProver_split(X1,X2))) = sP4_iProver_split(X0,k4_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_74880,c_53685,c_56238,c_73041])).

cnf(c_97500,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(X1,X2),k4_xboole_0(X2,X3))),sP4_iProver_split(X1,X2)) = k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X2,X3),sP4_iProver_split(X1,X2))) ),
    inference(superposition,[status(thm)],[c_53745,c_97421])).

cnf(c_72723,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X2,X0)) = sP4_iProver_split(X0,X2) ),
    inference(superposition,[status(thm)],[c_72427,c_68488])).

cnf(c_72430,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,X1),k4_xboole_0(X1,X2)) = sP4_iProver_split(X1,sP4_iProver_split(X0,X1)) ),
    inference(superposition,[status(thm)],[c_53745,c_72427])).

cnf(c_73044,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,X1),k4_xboole_0(X1,X2)) = sP4_iProver_split(X0,X1) ),
    inference(demodulation,[status(thm)],[c_72430,c_53801,c_54100])).

cnf(c_81364,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(sP4_iProver_split(X0,X1),X2),X3) ),
    inference(superposition,[status(thm)],[c_81267,c_9])).

cnf(c_81794,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),sP4_iProver_split(X3,X2)) = k4_xboole_0(sP4_iProver_split(X0,X1),sP4_iProver_split(X3,X2)) ),
    inference(demodulation,[status(thm)],[c_81364,c_9,c_53685])).

cnf(c_97809,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,X1),sP4_iProver_split(X1,X2)) = k4_xboole_0(X0,sP4_iProver_split(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_97500,c_72723,c_73044,c_81794])).

cnf(c_98430,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X1,sP1_iProver_split),X1)) = k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X1,sP1_iProver_split))) ),
    inference(demodulation,[status(thm)],[c_98333,c_74881,c_97809])).

cnf(c_81356,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),k2_xboole_0(k4_xboole_0(sP4_iProver_split(X0,X1),X2),X3)) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,sP4_iProver_split(X0,sP4_iProver_split(X1,X2)))),X3) ),
    inference(superposition,[status(thm)],[c_81267,c_605])).

cnf(c_81807,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),sP4_iProver_split(X3,k4_xboole_0(sP4_iProver_split(X0,X1),X2))) = k4_xboole_0(X2,X3) ),
    inference(demodulation,[status(thm)],[c_81356,c_10745,c_37461,c_53685,c_56504])).

cnf(c_10783,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = X0 ),
    inference(superposition,[status(thm)],[c_605,c_1749])).

cnf(c_10891,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X2))) = X0 ),
    inference(demodulation,[status(thm)],[c_10783,c_9])).

cnf(c_81368,plain,
    ( k2_xboole_0(X0,k4_xboole_0(sP4_iProver_split(X1,sP4_iProver_split(X2,X0)),k2_xboole_0(k4_xboole_0(sP4_iProver_split(X1,X2),X0),X3))) = X0 ),
    inference(superposition,[status(thm)],[c_81267,c_10891])).

cnf(c_81792,plain,
    ( sP4_iProver_split(k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),sP4_iProver_split(X3,k4_xboole_0(sP4_iProver_split(X0,X1),X2))),X2) = X2 ),
    inference(demodulation,[status(thm)],[c_81368,c_53685])).

cnf(c_81816,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_81807,c_81792])).

cnf(c_98431,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(X1,X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_98430,c_37461,c_81816])).

cnf(c_110077,plain,
    ( k4_xboole_0(sK4,sK5) = k4_xboole_0(sK3,sK5) ),
    inference(demodulation,[status(thm)],[c_110076,c_53685,c_72818,c_72989,c_98431])).

cnf(c_110642,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK3,sK5),k4_xboole_0(k4_xboole_0(sK3,sK5),k2_xboole_0(sK3,sK2)))) = k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_109280,c_110077])).

cnf(c_110643,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK3,sK5),k4_xboole_0(k4_xboole_0(sK3,sK5),sP4_iProver_split(sK3,sK2)))) = k4_xboole_0(sP4_iProver_split(sK3,sK2),k4_xboole_0(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_110642,c_59877])).

cnf(c_6422,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
    inference(superposition,[status(thm)],[c_3027,c_3133])).

cnf(c_110644,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),k4_xboole_0(sK3,sK5)) = sK5 ),
    inference(demodulation,[status(thm)],[c_110643,c_9,c_6422,c_61315])).

cnf(c_3817,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_3755,c_9])).

cnf(c_117522,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(light_normalisation,[status(thm)],[c_3817,c_3817,c_117418])).

cnf(c_117523,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,X1),sP4_iProver_split(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(demodulation,[status(thm)],[c_117522,c_117418])).

cnf(c_117700,plain,
    ( k4_xboole_0(sP4_iProver_split(k4_xboole_0(sK3,sK5),sP4_iProver_split(sP5_iProver_split,sK3)),sP4_iProver_split(sK5,X0)) = k4_xboole_0(k4_xboole_0(sK3,sK5),X0) ),
    inference(superposition,[status(thm)],[c_110644,c_117523])).

cnf(c_115945,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK5,sP4_iProver_split(k4_xboole_0(X0,X1),sK2))) = k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(X0,X1),sK2)) ),
    inference(superposition,[status(thm)],[c_114564,c_5438])).

cnf(c_116058,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK5,sP4_iProver_split(k4_xboole_0(X0,X1),sP5_iProver_split))) = k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(X0,X1),sP5_iProver_split)) ),
    inference(light_normalisation,[status(thm)],[c_115945,c_65380])).

cnf(c_107236,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,X1),sP4_iProver_split(X2,X1)) = k4_xboole_0(X0,sP4_iProver_split(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_3028,c_53685])).

cnf(c_107363,plain,
    ( k2_xboole_0(k4_xboole_0(X0,sP4_iProver_split(X1,X2)),sP4_iProver_split(X1,X2)) = k2_xboole_0(sP4_iProver_split(X1,X2),sP4_iProver_split(X0,X2)) ),
    inference(superposition,[status(thm)],[c_107236,c_3027])).

cnf(c_107492,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,X1),X2) = sP4_iProver_split(X0,sP4_iProver_split(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_107363,c_4224,c_53685,c_53801,c_81806])).

cnf(c_116059,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,X1),sP5_iProver_split),sK5),sK3) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_116058,c_53685,c_107492])).

cnf(c_74718,plain,
    ( sP4_iProver_split(k2_xboole_0(X0,sK5),sP4_iProver_split(k2_xboole_0(X0,sK5),X1)) = sP4_iProver_split(X1,k2_xboole_0(X0,sK5)) ),
    inference(superposition,[status(thm)],[c_6398,c_56206])).

cnf(c_75013,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(sP4_iProver_split(sK5,sP4_iProver_split(X0,X1)),X1)) = sP4_iProver_split(X0,sP4_iProver_split(sK5,X1)) ),
    inference(demodulation,[status(thm)],[c_74718,c_53685,c_54013,c_54923])).

cnf(c_75014,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,sP4_iProver_split(X1,X0)),sK5) = sP4_iProver_split(X1,sP4_iProver_split(sK5,X0)) ),
    inference(demodulation,[status(thm)],[c_75013,c_54013,c_54923])).

cnf(c_75015,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,X1),sK5) = sP4_iProver_split(X0,sP4_iProver_split(sK5,X1)) ),
    inference(light_normalisation,[status(thm)],[c_75014,c_53801])).

cnf(c_110815,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK3,sK5),k4_xboole_0(k4_xboole_0(sK3,sK5),sP4_iProver_split(sP5_iProver_split,sK3)))) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(superposition,[status(thm)],[c_110644,c_598])).

cnf(c_110837,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK5),sP4_iProver_split(sP5_iProver_split,sK3)) = k4_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3)) ),
    inference(superposition,[status(thm)],[c_110644,c_49082])).

cnf(c_110881,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,sK3)))) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(demodulation,[status(thm)],[c_110815,c_110837])).

cnf(c_12492,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2)))) = k4_xboole_0(k2_xboole_0(X1,sK5),k4_xboole_0(k2_xboole_0(X1,sK5),k4_xboole_0(X0,sK4))) ),
    inference(superposition,[status(thm)],[c_961,c_616])).

cnf(c_76776,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(X1,sP4_iProver_split(sK3,sK2)))) = k4_xboole_0(k2_xboole_0(X1,sK5),k4_xboole_0(k2_xboole_0(X1,sK5),k4_xboole_0(X0,sK4))) ),
    inference(light_normalisation,[status(thm)],[c_12492,c_59877])).

cnf(c_76777,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK4,k4_xboole_0(X0,sP4_iProver_split(sP4_iProver_split(sK3,sK2),X1)))) = k4_xboole_0(sP4_iProver_split(sK5,X1),k4_xboole_0(sP4_iProver_split(sK5,X1),k4_xboole_0(X0,sK4))) ),
    inference(demodulation,[status(thm)],[c_76776,c_9,c_53685])).

cnf(c_76778,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK4,k4_xboole_0(X0,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X1)))) = k4_xboole_0(sP4_iProver_split(sK5,X1),k4_xboole_0(sP4_iProver_split(sK5,X1),k4_xboole_0(X0,sK4))) ),
    inference(light_normalisation,[status(thm)],[c_76777,c_61315])).

cnf(c_76779,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X1)),sK4)) = k4_xboole_0(sP4_iProver_split(sK5,X1),k4_xboole_0(sP4_iProver_split(sK5,X1),k4_xboole_0(X0,sK4))) ),
    inference(demodulation,[status(thm)],[c_76778,c_53685])).

cnf(c_76780,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(sK3,sP4_iProver_split(X1,sP5_iProver_split))),sK4)) = k4_xboole_0(sP4_iProver_split(sK5,X1),k4_xboole_0(sP4_iProver_split(sK5,X1),k4_xboole_0(X0,sK4))) ),
    inference(demodulation,[status(thm)],[c_76779,c_54100])).

cnf(c_76781,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X1))),sK4)) = k4_xboole_0(sP4_iProver_split(sK5,X1),k4_xboole_0(sP4_iProver_split(sK5,X1),k4_xboole_0(X0,sK4))) ),
    inference(demodulation,[status(thm)],[c_76780,c_67465])).

cnf(c_9909,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK5),X0),sK5)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_5792,c_961])).

cnf(c_76882,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(k2_xboole_0(sK2,sK5),sK4))),sK5)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_76781,c_9909])).

cnf(c_3923,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
    inference(superposition,[status(thm)],[c_3233,c_959])).

cnf(c_3981,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_3923,c_3233])).

cnf(c_2999,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK4) = k4_xboole_0(k2_xboole_0(X0,sK5),sK4) ),
    inference(superposition,[status(thm)],[c_961,c_509])).

cnf(c_6743,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK2,sK4),sK5),sK4) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK4) ),
    inference(superposition,[status(thm)],[c_3981,c_2999])).

cnf(c_6772,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK2,sK4),sK5),sK4) = k4_xboole_0(sK5,sK4) ),
    inference(light_normalisation,[status(thm)],[c_6743,c_1279])).

cnf(c_6773,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK5),sK4) = k4_xboole_0(sK5,sK4) ),
    inference(demodulation,[status(thm)],[c_6772,c_509,c_3970])).

cnf(c_77127,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sK5,sK4))),sK5)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(light_normalisation,[status(thm)],[c_76882,c_6773,c_59877,c_65380,c_65760])).

cnf(c_17086,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X1) = X1 ),
    inference(superposition,[status(thm)],[c_16936,c_505])).

cnf(c_77128,plain,
    ( sP4_iProver_split(sP5_iProver_split,sK3) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_77127,c_152,c_2244,c_17086])).

cnf(c_77129,plain,
    ( sP4_iProver_split(sP5_iProver_split,sK3) = k2_xboole_0(sK3,sP5_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_77128,c_59877,c_65380])).

cnf(c_77592,plain,
    ( sP4_iProver_split(sP5_iProver_split,sK3) = k2_xboole_0(sP5_iProver_split,sK3) ),
    inference(superposition,[status(thm)],[c_77129,c_0])).

cnf(c_79130,plain,
    ( k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_77592,c_1862])).

cnf(c_79167,plain,
    ( k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,sK3)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_79130,c_34016])).

cnf(c_110882,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK3,sK5),sP1_iProver_split)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(light_normalisation,[status(thm)],[c_110881,c_79167])).

cnf(c_49476,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),sP1_iProver_split) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_49023,c_3026])).

cnf(c_110883,plain,
    ( sP4_iProver_split(sP5_iProver_split,sK3) = k2_xboole_0(sK5,sK3) ),
    inference(demodulation,[status(thm)],[c_110882,c_6,c_49476,c_53685])).

cnf(c_111253,plain,
    ( k2_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3)) = k2_xboole_0(sK3,k2_xboole_0(sK5,X0)) ),
    inference(superposition,[status(thm)],[c_110883,c_244])).

cnf(c_15293,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK5,X1)) = k2_xboole_0(X1,k2_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
    inference(superposition,[status(thm)],[c_14697,c_244])).

cnf(c_111267,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),sP4_iProver_split(sP5_iProver_split,sK3)) = k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
    inference(superposition,[status(thm)],[c_110883,c_15293])).

cnf(c_111294,plain,
    ( k2_xboole_0(k4_xboole_0(X0,sP4_iProver_split(sK3,sK2)),sP4_iProver_split(sP5_iProver_split,sK3)) = k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
    inference(light_normalisation,[status(thm)],[c_111267,c_59877])).

cnf(c_111295,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,sK4),sP4_iProver_split(sK3,sK5)) = k2_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3)) ),
    inference(demodulation,[status(thm)],[c_111294,c_4224,c_53685,c_61315,c_107492])).

cnf(c_2010,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,k2_xboole_0(X0,X1))) = k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_1674,c_11])).

cnf(c_77579,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,sP4_iProver_split(sP5_iProver_split,sK3))) = k2_xboole_0(sK3,k2_xboole_0(sP5_iProver_split,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_77129,c_2010])).

cnf(c_17040,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(k2_xboole_0(sK3,sK2),X0))) = k4_xboole_0(X0,k4_xboole_0(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_3765,c_16936])).

cnf(c_8601,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK4),X0),k2_xboole_0(sK3,sK2)),k4_xboole_0(sK4,X0)) = k2_xboole_0(k4_xboole_0(sK5,sK4),X0) ),
    inference(superposition,[status(thm)],[c_4236,c_3755])).

cnf(c_8610,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK4),X0))),k4_xboole_0(sK4,X0)) = k2_xboole_0(k4_xboole_0(sK5,sK4),X0) ),
    inference(demodulation,[status(thm)],[c_8601,c_5782])).

cnf(c_8617,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK4,X0)) = k2_xboole_0(k4_xboole_0(sK5,sK4),X0) ),
    inference(demodulation,[status(thm)],[c_8615,c_8610])).

cnf(c_30957,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(sK3,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,sK4))) = k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_8617])).

cnf(c_8595,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_4236,c_505])).

cnf(c_31074,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(X0,k4_xboole_0(X0,sK4))) = k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(sK4,X0)) ),
    inference(light_normalisation,[status(thm)],[c_30957,c_8595])).

cnf(c_30972,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,sK2),X0),k2_xboole_0(sK3,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,sK4))) = k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) ),
    inference(superposition,[status(thm)],[c_17193,c_8617])).

cnf(c_31055,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK3,sK2),X0))),k4_xboole_0(X0,k4_xboole_0(X0,sK4))) = k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) ),
    inference(demodulation,[status(thm)],[c_30972,c_14817])).

cnf(c_1960,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X0,X1),X2))) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1749,c_11])).

cnf(c_31056,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(X0,k4_xboole_0(X0,sK4))) = k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) ),
    inference(demodulation,[status(thm)],[c_31055,c_1960])).

cnf(c_31075,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) = k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(sK4,X0)) ),
    inference(demodulation,[status(thm)],[c_31074,c_31056])).

cnf(c_61740,plain,
    ( k4_xboole_0(sP4_iProver_split(sK3,sK2),k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(sK4,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_17040,c_31075,c_59877])).

cnf(c_61741,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(k4_xboole_0(sK4,X0),k4_xboole_0(sK5,sK4))) = k4_xboole_0(X0,k4_xboole_0(X0,sK4)) ),
    inference(demodulation,[status(thm)],[c_61740,c_53685,c_61315])).

cnf(c_61762,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,k4_xboole_0(sK4,sP1_iProver_split)),k4_xboole_0(k2_xboole_0(sK5,k4_xboole_0(sK4,sP1_iProver_split)),sK4)) = k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sP1_iProver_split,k4_xboole_0(sK5,sK4))) ),
    inference(superposition,[status(thm)],[c_34829,c_61741])).

cnf(c_62059,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sP1_iProver_split,k4_xboole_0(sK5,sK4))) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_61762,c_1259,c_1279,c_3765,c_34383])).

cnf(c_62193,plain,
    ( k2_xboole_0(sK4,sP4_iProver_split(sP5_iProver_split,sK3)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(superposition,[status(thm)],[c_62059,c_505])).

cnf(c_77651,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sP5_iProver_split,sP4_iProver_split(sK3,sK2))) = k2_xboole_0(sK5,sP4_iProver_split(sP5_iProver_split,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_77579,c_59877,c_62193])).

cnf(c_74720,plain,
    ( sP4_iProver_split(k2_xboole_0(sK2,sK5),sP4_iProver_split(k2_xboole_0(sK2,sK5),X0)) = sP4_iProver_split(X0,k2_xboole_0(sK2,sK5)) ),
    inference(superposition,[status(thm)],[c_6408,c_56206])).

cnf(c_75007,plain,
    ( sP4_iProver_split(k2_xboole_0(sP5_iProver_split,sK5),sP4_iProver_split(k2_xboole_0(sP5_iProver_split,sK5),X0)) = sP4_iProver_split(X0,k2_xboole_0(sP5_iProver_split,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_74720,c_65380])).

cnf(c_75008,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(sP4_iProver_split(sK5,sP4_iProver_split(X0,sP5_iProver_split)),sP5_iProver_split)) = sP4_iProver_split(X0,sP4_iProver_split(sK5,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_75007,c_53685,c_54013,c_54923])).

cnf(c_75009,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(sP4_iProver_split(sK5,X0),sP5_iProver_split)) = sP4_iProver_split(X0,sP4_iProver_split(sK5,sP5_iProver_split)) ),
    inference(light_normalisation,[status(thm)],[c_75008,c_72989])).

cnf(c_75010,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,X0),sK5) = sP4_iProver_split(X0,sP4_iProver_split(sK5,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_75009,c_54013,c_54923,c_72989])).

cnf(c_75140,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,X0),sK5) = sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK5)) ),
    inference(demodulation,[status(thm)],[c_74657,c_75010])).

cnf(c_12452,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK5,sK3))) = k4_xboole_0(k4_xboole_0(sK5,sK3),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2914,c_616])).

cnf(c_12841,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK5,sK3))) = k4_xboole_0(sK5,sK3) ),
    inference(demodulation,[status(thm)],[c_12452,c_9,c_518])).

cnf(c_72456,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK5,sK3),X0),k4_xboole_0(sK2,k4_xboole_0(sK5,sK3))) = sP4_iProver_split(sK2,X0) ),
    inference(superposition,[status(thm)],[c_12841,c_72427])).

cnf(c_68584,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK5,sK3),X0),k4_xboole_0(sK2,k4_xboole_0(sK5,sK3))) = sP4_iProver_split(k4_xboole_0(sK2,k4_xboole_0(sK5,sK3)),sP4_iProver_split(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_12841,c_68488])).

cnf(c_68885,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK5,sK3),X0),k4_xboole_0(sP5_iProver_split,k4_xboole_0(sK5,sK3))) = sP4_iProver_split(k4_xboole_0(sP5_iProver_split,k4_xboole_0(sK5,sK3)),sP4_iProver_split(X0,sP5_iProver_split)) ),
    inference(light_normalisation,[status(thm)],[c_68584,c_65380])).

cnf(c_68886,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK5,sK3),X0),k4_xboole_0(sP5_iProver_split,k4_xboole_0(sK5,sK3))) = sP4_iProver_split(X0,sP5_iProver_split) ),
    inference(demodulation,[status(thm)],[c_68885,c_53745,c_54100])).

cnf(c_72992,plain,
    ( sP4_iProver_split(X0,sP5_iProver_split) = sP4_iProver_split(sP5_iProver_split,X0) ),
    inference(light_normalisation,[status(thm)],[c_72456,c_65380,c_68886])).

cnf(c_72995,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK5)) = sP4_iProver_split(sK5,X0) ),
    inference(demodulation,[status(thm)],[c_72992,c_72987])).

cnf(c_75144,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,X0),sK5) = sP4_iProver_split(sK5,X0) ),
    inference(light_normalisation,[status(thm)],[c_75140,c_72995])).

cnf(c_77652,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sK3,sK2),sP5_iProver_split),sK3) = sP4_iProver_split(sK5,sK3) ),
    inference(demodulation,[status(thm)],[c_77651,c_53685,c_75144])).

cnf(c_74652,plain,
    ( sP4_iProver_split(sK3,sK5) = sP4_iProver_split(sK5,sK3) ),
    inference(superposition,[status(thm)],[c_58210,c_56206])).

cnf(c_74655,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),sK2) = sP4_iProver_split(sK2,sP4_iProver_split(sP5_iProver_split,sK3)) ),
    inference(superposition,[status(thm)],[c_63316,c_56206])).

cnf(c_11563,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_8,c_7838])).

cnf(c_43113,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK2,sK4)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_11563,c_0])).

cnf(c_69451,plain,
    ( k2_xboole_0(sP4_iProver_split(sK3,sK2),sK2) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(light_normalisation,[status(thm)],[c_43113,c_43113,c_52847,c_59877,c_65380,c_65760])).

cnf(c_69452,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sP5_iProver_split,sK3)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(demodulation,[status(thm)],[c_69451,c_53685,c_61315,c_65380])).

cnf(c_75147,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),sP5_iProver_split) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(light_normalisation,[status(thm)],[c_74655,c_65380,c_69452])).

cnf(c_77653,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),sK3) = sP4_iProver_split(sK3,sK5) ),
    inference(light_normalisation,[status(thm)],[c_77652,c_61315,c_74652,c_75147])).

cnf(c_74645,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,X1),X1) = sP4_iProver_split(X1,sP4_iProver_split(X0,X1)) ),
    inference(superposition,[status(thm)],[c_53745,c_56206])).

cnf(c_75156,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,X1),X1) = sP4_iProver_split(X0,X1) ),
    inference(demodulation,[status(thm)],[c_74645,c_53801,c_54100])).

cnf(c_77654,plain,
    ( sP4_iProver_split(sP5_iProver_split,sK3) = sP4_iProver_split(sK3,sK5) ),
    inference(demodulation,[status(thm)],[c_77653,c_75156])).

cnf(c_13678,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4)))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_12475,c_6])).

cnf(c_11613,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),X0),sK5)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_7838,c_961])).

cnf(c_20532,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(X0,sK4)) = k4_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_11613,c_622])).

cnf(c_78727,plain,
    ( k2_xboole_0(k4_xboole_0(X0,sP4_iProver_split(sK3,sK2)),k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4)))) = k4_xboole_0(X0,sK4) ),
    inference(light_normalisation,[status(thm)],[c_13678,c_13678,c_20532,c_59877])).

cnf(c_78728,plain,
    ( sP4_iProver_split(k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))),k4_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3))) = k4_xboole_0(X0,sK4) ),
    inference(demodulation,[status(thm)],[c_78727,c_53685,c_61315])).

cnf(c_1043,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_6,c_11])).

cnf(c_1058,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_1043,c_11])).

cnf(c_2570,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_245])).

cnf(c_82099,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,k4_xboole_0(X1,X2)),X2) = sP4_iProver_split(X1,sP4_iProver_split(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_1058,c_2570,c_53685,c_54100])).

cnf(c_82116,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))))) = sP4_iProver_split(k4_xboole_0(X0,sK4),sP4_iProver_split(sP5_iProver_split,sK3)) ),
    inference(superposition,[status(thm)],[c_78728,c_82099])).

cnf(c_82902,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))),sP5_iProver_split))) = sP4_iProver_split(k4_xboole_0(X0,sK4),sP4_iProver_split(sP5_iProver_split,sK3)) ),
    inference(demodulation,[status(thm)],[c_82116,c_54100])).

cnf(c_82903,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4)))))) = sP4_iProver_split(k4_xboole_0(X0,sK4),sP4_iProver_split(sP5_iProver_split,sK3)) ),
    inference(demodulation,[status(thm)],[c_82902,c_67465])).

cnf(c_81395,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,sK5)),k2_xboole_0(k4_xboole_0(sP4_iProver_split(X0,X1),sK5),X2)))) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_81267,c_39565])).

cnf(c_81701,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sP5_iProver_split,k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,sK5)),k2_xboole_0(k4_xboole_0(sP4_iProver_split(X0,X1),sK5),X2)))) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(light_normalisation,[status(thm)],[c_81395,c_59877,c_65380,c_65760])).

cnf(c_81702,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,sK5)),k2_xboole_0(k4_xboole_0(sP4_iProver_split(X0,X1),sK5),X2)),sP5_iProver_split),sK3) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(demodulation,[status(thm)],[c_81701,c_53685])).

cnf(c_81703,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,sK5)),sP4_iProver_split(X2,k4_xboole_0(sP4_iProver_split(X0,X1),sK5))))) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(demodulation,[status(thm)],[c_81702,c_53685,c_54100])).

cnf(c_81814,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k4_xboole_0(sK5,X0))) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(demodulation,[status(thm)],[c_81807,c_81703])).

cnf(c_82904,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,sK4),sP4_iProver_split(sP5_iProver_split,sK3)) = sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3)) ),
    inference(demodulation,[status(thm)],[c_82903,c_81814])).

cnf(c_111296,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3)) = k2_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_111295,c_77654,c_82904])).

cnf(c_111316,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3)) = k2_xboole_0(sK3,k2_xboole_0(sK5,X0)) ),
    inference(demodulation,[status(thm)],[c_111253,c_111296])).

cnf(c_111317,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,sK5),sK3) = sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3)) ),
    inference(demodulation,[status(thm)],[c_111316,c_53685])).

cnf(c_116060,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(sK3,sP4_iProver_split(sK5,sP5_iProver_split))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_116059,c_75015,c_107492,c_111317])).

cnf(c_81376,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),k4_xboole_0(sP4_iProver_split(X0,X1),X2)) = k4_xboole_0(X2,k4_xboole_0(X2,sP4_iProver_split(X0,sP4_iProver_split(X1,X2)))) ),
    inference(superposition,[status(thm)],[c_81267,c_1])).

cnf(c_81749,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),k4_xboole_0(sP4_iProver_split(X0,X1),X2)) = X2 ),
    inference(demodulation,[status(thm)],[c_81376,c_37461,c_56504])).

cnf(c_5752,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(sK2,sK5))),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) ),
    inference(superposition,[status(thm)],[c_1733,c_2298])).

cnf(c_5790,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(sK2,sK5))),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_5752,c_2281])).

cnf(c_81438,plain,
    ( k2_xboole_0(k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,k2_xboole_0(sK2,sK5))),k4_xboole_0(sP4_iProver_split(X0,X1),k2_xboole_0(sK2,sK5))),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_81267,c_5790])).

cnf(c_81577,plain,
    ( k2_xboole_0(k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,k2_xboole_0(sP5_iProver_split,sK5))),k4_xboole_0(sP4_iProver_split(X0,X1),k2_xboole_0(sP5_iProver_split,sK5))),sP4_iProver_split(sK3,sK2)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(light_normalisation,[status(thm)],[c_81438,c_59877,c_65380,c_65760])).

cnf(c_73249,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK2,sK4)),sK5) = k4_xboole_0(X0,sK5) ),
    inference(superposition,[status(thm)],[c_13710,c_49082])).

cnf(c_73861,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK2),sK5) = k4_xboole_0(X0,sK5) ),
    inference(light_normalisation,[status(thm)],[c_73249,c_52847])).

cnf(c_73862,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sP5_iProver_split,sK5)) = k4_xboole_0(X0,sK5) ),
    inference(demodulation,[status(thm)],[c_73861,c_34854,c_65380])).

cnf(c_73863,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(sK5,sP5_iProver_split)) = k4_xboole_0(X0,sK5) ),
    inference(demodulation,[status(thm)],[c_73862,c_53685])).

cnf(c_81578,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(sK5,sP5_iProver_split))),k4_xboole_0(sP4_iProver_split(X0,X1),sK5))) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(demodulation,[status(thm)],[c_81577,c_53685,c_61315,c_73863])).

cnf(c_81579,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(sP5_iProver_split,sK5))),k4_xboole_0(sP4_iProver_split(X0,X1),sK5))) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(light_normalisation,[status(thm)],[c_81578,c_74657])).

cnf(c_74694,plain,
    ( sP4_iProver_split(k2_xboole_0(sK2,sK5),sP4_iProver_split(k1_xboole_0,X0)) = sP4_iProver_split(X0,k2_xboole_0(sK2,sK5)) ),
    inference(superposition,[status(thm)],[c_2936,c_56206])).

cnf(c_75073,plain,
    ( sP4_iProver_split(k2_xboole_0(sP5_iProver_split,sK5),sP4_iProver_split(sP1_iProver_split,X0)) = sP4_iProver_split(X0,k2_xboole_0(sP5_iProver_split,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_74694,c_34016,c_65380])).

cnf(c_72447,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,X1),k4_xboole_0(X0,k2_xboole_0(X2,k2_xboole_0(X3,X0)))) = sP4_iProver_split(X0,X1) ),
    inference(superposition,[status(thm)],[c_6382,c_72427])).

cnf(c_2949,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1862,c_9])).

cnf(c_2955,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2949,c_960])).

cnf(c_53700,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = sP4_iProver_split(X2,X0) ),
    inference(demodulation,[status(thm)],[c_53685,c_21035])).

cnf(c_53742,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,X1),k4_xboole_0(X0,X2)) = sP4_iProver_split(X1,X0) ),
    inference(demodulation,[status(thm)],[c_53700,c_53685])).

cnf(c_73021,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(k1_xboole_0,X1)) = sP4_iProver_split(X1,X0) ),
    inference(demodulation,[status(thm)],[c_72447,c_2955,c_53742,c_54100])).

cnf(c_73022,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(sP1_iProver_split,X1)) = sP4_iProver_split(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_73021,c_34016])).

cnf(c_75074,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(sP4_iProver_split(sP1_iProver_split,X0),sP5_iProver_split)) = sP4_iProver_split(X0,sP4_iProver_split(sK5,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_75073,c_53685,c_54923,c_73022])).

cnf(c_72642,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,X0),X1),X0) = sP4_iProver_split(X0,X1) ),
    inference(superposition,[status(thm)],[c_6382,c_72427])).

cnf(c_72880,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP1_iProver_split,X0),X1) = sP4_iProver_split(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_72642,c_39584])).

cnf(c_75075,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(sP5_iProver_split,X0)) = sP4_iProver_split(X0,sP4_iProver_split(sK5,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_75074,c_72880,c_72989])).

cnf(c_75139,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(sP5_iProver_split,X0)) = sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK5)) ),
    inference(demodulation,[status(thm)],[c_74657,c_75075])).

cnf(c_74743,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(k4_xboole_0(sK2,sK4),X0)) = sP4_iProver_split(X0,sK5) ),
    inference(superposition,[status(thm)],[c_13710,c_56206])).

cnf(c_74953,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(sK2,X0)) = sP4_iProver_split(X0,sK5) ),
    inference(light_normalisation,[status(thm)],[c_74743,c_52847])).

cnf(c_74954,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(sP5_iProver_split,X0)) = sP4_iProver_split(X0,sK5) ),
    inference(demodulation,[status(thm)],[c_74953,c_65380])).

cnf(c_75145,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK5)) = sP4_iProver_split(X0,sK5) ),
    inference(demodulation,[status(thm)],[c_75139,c_74954])).

cnf(c_81580,plain,
    ( sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,sK5)),k4_xboole_0(sP4_iProver_split(X0,X1),sK5)),sP5_iProver_split)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(demodulation,[status(thm)],[c_81579,c_54100,c_75145])).

cnf(c_81753,plain,
    ( sP4_iProver_split(sK3,sP4_iProver_split(sK5,sP5_iProver_split)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(demodulation,[status(thm)],[c_81749,c_81580])).

cnf(c_81770,plain,
    ( sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,sK5)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(light_normalisation,[status(thm)],[c_81753,c_74657])).

cnf(c_116061,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(sP5_iProver_split,sK3)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k4_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_116060,c_74657,c_81770])).

cnf(c_117968,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k4_xboole_0(sK3,sK5))),sP4_iProver_split(sK5,X0)) = k4_xboole_0(sK3,sP4_iProver_split(sK5,X0)) ),
    inference(demodulation,[status(thm)],[c_117700,c_9,c_116061,c_117418])).

cnf(c_74830,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k4_xboole_0(sK3,X0))) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(superposition,[status(thm)],[c_56206,c_67465])).

cnf(c_98328,plain,
    ( k4_xboole_0(sK4,sP4_iProver_split(sK5,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,sP1_iProver_split)),X0))) = k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(sK5,X0)) ),
    inference(superposition,[status(thm)],[c_87355,c_57991])).

cnf(c_98436,plain,
    ( k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(sK5,X0)) = k4_xboole_0(sK4,sP4_iProver_split(sK5,X0)) ),
    inference(demodulation,[status(thm)],[c_98328,c_87355])).

cnf(c_98437,plain,
    ( k4_xboole_0(sP4_iProver_split(sK3,sK2),sP4_iProver_split(sK5,X0)) = k4_xboole_0(sK4,sP4_iProver_split(sK5,X0)) ),
    inference(light_normalisation,[status(thm)],[c_98436,c_59354])).

cnf(c_98438,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sK5,X0)) = k4_xboole_0(sK4,sP4_iProver_split(sK5,X0)) ),
    inference(demodulation,[status(thm)],[c_98437,c_61315])).

cnf(c_117969,plain,
    ( k4_xboole_0(sK3,sP4_iProver_split(sK5,X0)) = k4_xboole_0(sK4,sP4_iProver_split(sK5,X0)) ),
    inference(demodulation,[status(thm)],[c_117968,c_74830,c_98438])).

cnf(c_116938,plain,
    ( sP4_iProver_split(k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),k4_xboole_0(sK3,sK5)),X0) = k2_xboole_0(sK5,X0) ),
    inference(superposition,[status(thm)],[c_110644,c_115896])).

cnf(c_118735,plain,
    ( sP4_iProver_split(sK5,X0) = k2_xboole_0(sK5,X0) ),
    inference(light_normalisation,[status(thm)],[c_116938,c_110644])).

cnf(c_151023,plain,
    ( sP4_iProver_split(X0,k4_xboole_0(sK3,sP4_iProver_split(sK5,k4_xboole_0(sK4,X0)))) = X0 ),
    inference(demodulation,[status(thm)],[c_33427,c_117418,c_117969,c_118735])).

cnf(c_151136,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k4_xboole_0(sK3,sP4_iProver_split(sK5,k4_xboole_0(sK4,sP5_iProver_split))))),sP4_iProver_split(k4_xboole_0(sK5,sK4),sP5_iProver_split)) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sP4_iProver_split(sK5,k4_xboole_0(sK4,sP5_iProver_split)))))) ),
    inference(superposition,[status(thm)],[c_151023,c_76125])).

cnf(c_151140,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k4_xboole_0(sK3,sP4_iProver_split(sK5,k4_xboole_0(sK4,sP5_iProver_split))))),sP4_iProver_split(k4_xboole_0(sK5,sK4),sP5_iProver_split)) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_151136,c_151023])).

cnf(c_76128,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sP5_iProver_split,sK3)),sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,sK2))) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,sK2))) ),
    inference(superposition,[status(thm)],[c_61315,c_76125])).

cnf(c_76296,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,sP5_iProver_split))) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,sP5_iProver_split))) ),
    inference(light_normalisation,[status(thm)],[c_76128,c_65380,c_69452])).

cnf(c_72452,plain,
    ( sP4_iProver_split(sP4_iProver_split(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),X1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),k2_xboole_0(sK3,sK2))) = sP4_iProver_split(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),X1) ),
    inference(superposition,[status(thm)],[c_6412,c_72427])).

cnf(c_73008,plain,
    ( sP4_iProver_split(sP4_iProver_split(k2_xboole_0(k4_xboole_0(sK5,X0),sP5_iProver_split),X1),k1_xboole_0) = sP4_iProver_split(k2_xboole_0(k4_xboole_0(sK5,X0),sP5_iProver_split),X1) ),
    inference(light_normalisation,[status(thm)],[c_72452,c_2939,c_65380])).

cnf(c_68511,plain,
    ( sP4_iProver_split(k1_xboole_0,sP4_iProver_split(X0,X1)) = sP4_iProver_split(sP4_iProver_split(X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_68488])).

cnf(c_69252,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,X1),sP1_iProver_split) = sP4_iProver_split(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_68511,c_34016,c_53848])).

cnf(c_73009,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,sP5_iProver_split),k4_xboole_0(sK5,X1)) = sP4_iProver_split(k4_xboole_0(sK5,X1),sP4_iProver_split(X0,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_73008,c_34016,c_53685,c_54100,c_69252])).

cnf(c_73010,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(k4_xboole_0(sK5,X0),X1)) = sP4_iProver_split(k4_xboole_0(sK5,X0),sP4_iProver_split(X1,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_73009,c_54100])).

cnf(c_76297,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP5_iProver_split))) = k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP5_iProver_split))) ),
    inference(demodulation,[status(thm)],[c_76296,c_73010])).

cnf(c_76298,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(k4_xboole_0(sK5,sK4),sP5_iProver_split)) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_76297,c_53801])).

cnf(c_109498,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(k4_xboole_0(sK5,X0),sK2)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) ),
    inference(superposition,[status(thm)],[c_2939,c_3129])).

cnf(c_42589,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) ),
    inference(superposition,[status(thm)],[c_0,c_2099])).

cnf(c_2091,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_0,c_1761])).

cnf(c_2426,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) = k4_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) ),
    inference(superposition,[status(thm)],[c_2091,c_8])).

cnf(c_42717,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) ),
    inference(light_normalisation,[status(thm)],[c_42589,c_2426])).

cnf(c_42725,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) = k4_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) ),
    inference(demodulation,[status(thm)],[c_42717,c_2099])).

cnf(c_110067,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sP5_iProver_split),sP1_iProver_split)) = k4_xboole_0(sK3,k2_xboole_0(sP5_iProver_split,k4_xboole_0(sK5,X0))) ),
    inference(light_normalisation,[status(thm)],[c_109498,c_34016,c_42725,c_65380])).

cnf(c_110068,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sP4_iProver_split(k4_xboole_0(sK5,X0),sK2),k2_xboole_0(k4_xboole_0(sK5,X0),sP5_iProver_split))) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,X0),sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_110067,c_9,c_37461,c_52508,c_53685])).

cnf(c_110069,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sP4_iProver_split(k4_xboole_0(sK5,X0),sP5_iProver_split),k2_xboole_0(k4_xboole_0(sK5,X0),sP5_iProver_split))) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,X0),sP5_iProver_split)) ),
    inference(light_normalisation,[status(thm)],[c_110068,c_65380])).

cnf(c_110070,plain,
    ( k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,X0),sP4_iProver_split(sP5_iProver_split,k2_xboole_0(k4_xboole_0(sK5,X0),sP5_iProver_split)))) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,X0),sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_110069,c_81806])).

cnf(c_110071,plain,
    ( k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(k4_xboole_0(sK5,X0),k4_xboole_0(sK5,X0)))) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,X0),sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_110070,c_53685,c_54013,c_73010])).

cnf(c_98364,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,sP1_iProver_split),X0) = X0 ),
    inference(superposition,[status(thm)],[c_87355,c_87355])).

cnf(c_98401,plain,
    ( sP4_iProver_split(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_98364,c_37461])).

cnf(c_110072,plain,
    ( k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK5,X0))) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,X0),sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_110071,c_98401])).

cnf(c_49466,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(sP1_iProver_split,X2) ),
    inference(superposition,[status(thm)],[c_49023,c_9])).

cnf(c_49518,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_49466,c_9,c_34425])).

cnf(c_74311,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,sP4_iProver_split(X2,k4_xboole_0(X0,X1)))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_49518,c_9,c_53685])).

cnf(c_74312,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(sP4_iProver_split(X1,k4_xboole_0(X0,X2)),X2)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_74311,c_53685])).

cnf(c_74313,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_74312,c_54100])).

cnf(c_74508,plain,
    ( k2_xboole_0(k4_xboole_0(X0,sP1_iProver_split),sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2))) = sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2)) ),
    inference(superposition,[status(thm)],[c_74313,c_1733])).

cnf(c_74518,plain,
    ( k2_xboole_0(k4_xboole_0(sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2)),X0),k4_xboole_0(X0,sP1_iProver_split)) = sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2)) ),
    inference(superposition,[status(thm)],[c_74313,c_598])).

cnf(c_74629,plain,
    ( k2_xboole_0(k4_xboole_0(sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2)),X0),X0) = sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_74518,c_37461])).

cnf(c_74630,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2)) = k2_xboole_0(sP4_iProver_split(X1,X2),X0) ),
    inference(demodulation,[status(thm)],[c_74629,c_4224,c_74076])).

cnf(c_74631,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2)) = sP4_iProver_split(X0,sP4_iProver_split(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_74630,c_53685])).

cnf(c_75203,plain,
    ( k2_xboole_0(X0,sP4_iProver_split(X0,sP4_iProver_split(X1,X2))) = sP4_iProver_split(X0,sP4_iProver_split(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_74508,c_37461,c_74631])).

cnf(c_112025,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(X1,X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_3240,c_3240,c_53685,c_75203,c_81806])).

cnf(c_112026,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,X1),X2) = sP4_iProver_split(X2,sP4_iProver_split(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_112025,c_53685])).

cnf(c_112167,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),sP4_iProver_split(X3,X0)) = k4_xboole_0(sP4_iProver_split(X2,X1),sP4_iProver_split(X3,X0)) ),
    inference(superposition,[status(thm)],[c_112026,c_107236])).

cnf(c_3435,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK4,sK2)) = k4_xboole_0(sK5,k2_xboole_0(sK4,sK2)) ),
    inference(superposition,[status(thm)],[c_3226,c_8])).

cnf(c_3625,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK4,sK2)) = k4_xboole_0(sK5,k2_xboole_0(sK4,sK2)) ),
    inference(superposition,[status(thm)],[c_3452,c_509])).

cnf(c_3343,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK4,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_0,c_3233])).

cnf(c_3529,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK4,sK2)) = k4_xboole_0(sK3,k2_xboole_0(sK4,sK2)) ),
    inference(superposition,[status(thm)],[c_3343,c_8])).

cnf(c_3644,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK4,sK2)) = k4_xboole_0(sK5,k2_xboole_0(sK4,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_3625,c_3529])).

cnf(c_112872,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),k2_xboole_0(sK4,sP5_iProver_split)) = k4_xboole_0(sK3,k2_xboole_0(sK4,sP5_iProver_split)) ),
    inference(light_normalisation,[status(thm)],[c_3435,c_3435,c_3644,c_65380,c_77592])).

cnf(c_1446,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK4,X0)) = k4_xboole_0(k4_xboole_0(sK5,sK4),X0) ),
    inference(superposition,[status(thm)],[c_1279,c_9])).

cnf(c_1454,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK4,X0)) = k4_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
    inference(demodulation,[status(thm)],[c_1446,c_9])).

cnf(c_86470,plain,
    ( k4_xboole_0(sP4_iProver_split(sK3,sK2),k2_xboole_0(sK4,X0)) = k4_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1454,c_1454,c_59877])).

cnf(c_86471,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(X0,sK4)) = k4_xboole_0(sK5,sP4_iProver_split(X0,sK4)) ),
    inference(demodulation,[status(thm)],[c_86470,c_53685,c_61315])).

cnf(c_112873,plain,
    ( k4_xboole_0(sK5,sP4_iProver_split(sP5_iProver_split,sK4)) = k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,sK4)) ),
    inference(demodulation,[status(thm)],[c_112872,c_53685,c_86471])).

cnf(c_148655,plain,
    ( sP4_iProver_split(X0,k4_xboole_0(X1,sP4_iProver_split(X0,X2))) = sP4_iProver_split(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_14690,c_117418])).

cnf(c_148701,plain,
    ( sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,sK4))) = sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK5,sK4)) ),
    inference(superposition,[status(thm)],[c_112873,c_148655])).

cnf(c_149099,plain,
    ( sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK5,sK4)) = sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_148701,c_148655])).

cnf(c_151141,plain,
    ( k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sK4))) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_151140,c_74830,c_76298,c_110072,c_112167,c_149099])).

cnf(c_153846,plain,
    ( k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sK4))) = sK4 ),
    inference(demodulation,[status(thm)],[c_153845,c_149932,c_151141])).

cnf(c_153873,plain,
    ( k2_xboole_0(sK4,k4_xboole_0(sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sK4)),k4_xboole_0(sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sK4)),sK3))) = sK3 ),
    inference(superposition,[status(thm)],[c_153846,c_598])).

cnf(c_153888,plain,
    ( k4_xboole_0(k2_xboole_0(sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sK4)),sK3),sK4) = sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_153846,c_3755])).

cnf(c_1322,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sK5,X0)),X0) = k4_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
    inference(superposition,[status(thm)],[c_1044,c_8])).

cnf(c_1361,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),X0) = k4_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
    inference(light_normalisation,[status(thm)],[c_1322,c_1329])).

cnf(c_126943,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sP5_iProver_split,X0)),X0) = k4_xboole_0(sP4_iProver_split(sK3,sK2),X0) ),
    inference(light_normalisation,[status(thm)],[c_1361,c_1361,c_59877,c_65380])).

cnf(c_126944,plain,
    ( k4_xboole_0(sP4_iProver_split(sK3,k2_xboole_0(sP5_iProver_split,X0)),X0) = k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),X0) ),
    inference(demodulation,[status(thm)],[c_126943,c_2992,c_61315,c_117418])).

cnf(c_105094,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,k4_xboole_0(X1,X2)),X2) = sP4_iProver_split(X2,sP4_iProver_split(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_2570,c_53685,c_54100])).

cnf(c_105145,plain,
    ( sP4_iProver_split(k2_xboole_0(sK3,sK2),sP4_iProver_split(X0,k2_xboole_0(sK3,sK2))) = sP4_iProver_split(sP4_iProver_split(X0,sP1_iProver_split),k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_34235,c_105094])).

cnf(c_105828,plain,
    ( sP4_iProver_split(sP4_iProver_split(sK3,sK2),sP4_iProver_split(X0,sP4_iProver_split(sK3,sK2))) = sP4_iProver_split(sP4_iProver_split(X0,sP1_iProver_split),sP4_iProver_split(sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_105145,c_59877])).

cnf(c_1684,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK4,X1)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_961,c_244])).

cnf(c_16762,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,sK5),k2_xboole_0(sK4,k2_xboole_0(X0,sK5))) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_1684,c_1684])).

cnf(c_10458,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,X0)) ),
    inference(superposition,[status(thm)],[c_6337,c_519])).

cnf(c_1951,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)))) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_713,c_1749])).

cnf(c_1275,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_1259,c_715])).

cnf(c_1433,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) = k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_1275,c_8])).

cnf(c_1442,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_1433,c_1347])).

cnf(c_1965,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)))) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_1951,c_1442])).

cnf(c_1966,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),sK5) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_1965,c_7,c_1853])).

cnf(c_5136,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,X0)) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
    inference(superposition,[status(thm)],[c_1966,c_11])).

cnf(c_1680,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_1275,c_244])).

cnf(c_5152,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,X0)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_5136,c_1680,c_1703,c_3970])).

cnf(c_10509,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_10458,c_5152])).

cnf(c_16774,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_16762,c_152,c_2244,c_10509])).

cnf(c_17974,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k2_xboole_0(X1,k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) ),
    inference(superposition,[status(thm)],[c_16774,c_245])).

cnf(c_63503,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(X1,sP4_iProver_split(sK3,sK2))) = k2_xboole_0(X1,k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_17974,c_17974,c_59877])).

cnf(c_2260,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1)) = k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),X1) ),
    inference(superposition,[status(thm)],[c_1329,c_11])).

cnf(c_63504,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sK3,sK2),X0),sP4_iProver_split(k2_xboole_0(sK2,X1),sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,k2_xboole_0(X1,sK2))) ),
    inference(demodulation,[status(thm)],[c_63503,c_2260,c_53685,c_54100])).

cnf(c_63505,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X0),sP4_iProver_split(k2_xboole_0(sK2,X1),sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,k2_xboole_0(X1,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_63504,c_61315])).

cnf(c_23951,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_22126,c_9])).

cnf(c_56171,plain,
    ( sP4_iProver_split(k1_xboole_0,sP4_iProver_split(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = sP4_iProver_split(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK3) ),
    inference(superposition,[status(thm)],[c_23951,c_56078])).

cnf(c_56245,plain,
    ( sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = sP4_iProver_split(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK3) ),
    inference(light_normalisation,[status(thm)],[c_56171,c_34016])).

cnf(c_56246,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(sK3,k2_xboole_0(sK3,sK2))) = sP4_iProver_split(sK3,sP4_iProver_split(k2_xboole_0(sK3,sK2),X0)) ),
    inference(demodulation,[status(thm)],[c_56245,c_53685,c_53848,c_54100])).

cnf(c_56247,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(sK2,sK3)) = sP4_iProver_split(sP4_iProver_split(X0,sK2),sK3) ),
    inference(demodulation,[status(thm)],[c_56246,c_53685,c_53801,c_54013,c_54100])).

cnf(c_63506,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,sP5_iProver_split),sP4_iProver_split(sP4_iProver_split(X1,sP4_iProver_split(sK2,sK3)),sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,X1))) ),
    inference(demodulation,[status(thm)],[c_63505,c_53685,c_54100,c_56247])).

cnf(c_63507,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,sP5_iProver_split),sP4_iProver_split(sP4_iProver_split(X1,sP4_iProver_split(sK3,sK2)),sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,X1))) ),
    inference(light_normalisation,[status(thm)],[c_63506,c_59354])).

cnf(c_63508,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sK3,sK2),sP4_iProver_split(sK3,X0)),X1)) = sP4_iProver_split(sK3,sP4_iProver_split(X1,sP4_iProver_split(sK2,X0))) ),
    inference(demodulation,[status(thm)],[c_63507,c_54100])).

cnf(c_63509,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sK3,X0)),X1)) = sP4_iProver_split(sK3,sP4_iProver_split(X1,sP4_iProver_split(sK2,X0))) ),
    inference(light_normalisation,[status(thm)],[c_63508,c_61315])).

cnf(c_57032,plain,
    ( k2_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,X3))),k4_xboole_0(X2,sP1_iProver_split)) = sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,X3))) ),
    inference(superposition,[status(thm)],[c_56983,c_1943])).

cnf(c_57128,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,sP4_iProver_split(X0,X3)))) = sP4_iProver_split(X1,sP4_iProver_split(X2,sP4_iProver_split(X0,X3))) ),
    inference(demodulation,[status(thm)],[c_57032,c_37461,c_53685])).

cnf(c_63510,plain,
    ( sP4_iProver_split(sP4_iProver_split(sK3,X0),sP4_iProver_split(X1,sP4_iProver_split(sP5_iProver_split,sK3))) = sP4_iProver_split(sK3,sP4_iProver_split(X1,sP4_iProver_split(sK2,X0))) ),
    inference(demodulation,[status(thm)],[c_63509,c_54100,c_57128])).

cnf(c_63512,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3))) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,sK2))) ),
    inference(superposition,[status(thm)],[c_61315,c_63510])).

cnf(c_82130,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(k2_xboole_0(X1,X0),X2)) = sP4_iProver_split(sP4_iProver_split(X2,k1_xboole_0),k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1862,c_82099])).

cnf(c_53755,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(X1,k2_xboole_0(X0,X2))) = sP4_iProver_split(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_3755,c_53745])).

cnf(c_53989,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,X0))) = sP4_iProver_split(X1,sP4_iProver_split(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_53755,c_53685])).

cnf(c_82862,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,sP1_iProver_split),sP4_iProver_split(X1,X2)) = sP4_iProver_split(X2,sP4_iProver_split(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_82130,c_34016,c_53685,c_53989,c_54100])).

cnf(c_105829,plain,
    ( sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,sK2))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)) ),
    inference(demodulation,[status(thm)],[c_105828,c_54100,c_61315,c_63512,c_65380,c_82862])).

cnf(c_16204,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,k2_xboole_0(X0,X1)),k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2)))) = k2_xboole_0(k2_xboole_0(sK5,k2_xboole_0(X0,X1)),sK4) ),
    inference(superposition,[status(thm)],[c_16088,c_519])).

cnf(c_16352,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,k2_xboole_0(X0,X1)),k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2)))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_16204,c_1259,c_3970,c_5782])).

cnf(c_68336,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,k2_xboole_0(X0,X1)),k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sP5_iProver_split)))) = k2_xboole_0(sK3,k2_xboole_0(sP5_iProver_split,k2_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_16352,c_16352,c_65380])).

cnf(c_68337,plain,
    ( sP4_iProver_split(sP4_iProver_split(k2_xboole_0(sK3,k2_xboole_0(X0,sP5_iProver_split)),X1),sP4_iProver_split(k2_xboole_0(X1,X0),sK5)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k2_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_68336,c_3970,c_53685,c_54100])).

cnf(c_68338,plain,
    ( sP4_iProver_split(sP4_iProver_split(k2_xboole_0(sK3,k2_xboole_0(X0,sP5_iProver_split)),X1),sP4_iProver_split(sP4_iProver_split(X0,X1),sK5)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_68337,c_53685])).

cnf(c_68339,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,k2_xboole_0(X1,sP5_iProver_split)),sP4_iProver_split(sP4_iProver_split(X0,sP4_iProver_split(sK5,X1)),sK3)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_68338,c_53685,c_54100])).

cnf(c_68340,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,X0),sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sK5,X0),sP4_iProver_split(sK3,X1)),X1)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_68339,c_53685,c_54100])).

cnf(c_68341,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sK3,X1),sP4_iProver_split(X1,sP4_iProver_split(sK5,X0))),sP5_iProver_split)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_68340,c_54100])).

cnf(c_68342,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(X1,sP4_iProver_split(sK5,X0)),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X1)))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_68341,c_54100])).

cnf(c_68343,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(sK5,X0),sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X1)),X1))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_68342,c_54100])).

cnf(c_68344,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0)),X0),X1)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_68343,c_53989,c_54923])).

cnf(c_68345,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_68344,c_54100])).

cnf(c_56547,plain,
    ( k2_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,X3))),k4_xboole_0(X3,sP1_iProver_split)) = sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,X3))) ),
    inference(superposition,[status(thm)],[c_56497,c_1943])).

cnf(c_56643,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,sP4_iProver_split(X3,X0)))) = sP4_iProver_split(X1,sP4_iProver_split(X2,sP4_iProver_split(X3,X0))) ),
    inference(demodulation,[status(thm)],[c_56547,c_37461,c_53685])).

cnf(c_68346,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X1)))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_68345,c_56643])).

cnf(c_68354,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(k4_xboole_0(sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(sK4,X1)),sK2),X2),sK2)))) = sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK2,sK3)))) ),
    inference(superposition,[status(thm)],[c_57636,c_68346])).

cnf(c_63513,plain,
    ( sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,sP4_iProver_split(k4_xboole_0(sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(sK4,X1)),sK2),X2),sK2)))) = sP4_iProver_split(sP4_iProver_split(sK2,sK3),sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3))) ),
    inference(superposition,[status(thm)],[c_57636,c_63510])).

cnf(c_63569,plain,
    ( sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,sP4_iProver_split(k4_xboole_0(sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(sK4,X1)),sK2),X2),sK2)))) = sP4_iProver_split(sP4_iProver_split(sK3,sK2),sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3))) ),
    inference(light_normalisation,[status(thm)],[c_63513,c_59354])).

cnf(c_63570,plain,
    ( sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(k4_xboole_0(sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(sK4,X1)),sK2),X2),sK2))) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,sK2))) ),
    inference(demodulation,[status(thm)],[c_63569,c_53801,c_63510])).

cnf(c_68415,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sK2)))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,sK2)))) ),
    inference(light_normalisation,[status(thm)],[c_68354,c_59354,c_63570])).

cnf(c_63521,plain,
    ( sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sK2,sK5),sP4_iProver_split(sK2,X0))) = sP4_iProver_split(sP4_iProver_split(sK3,X0),sP4_iProver_split(sP5_iProver_split,sK3)) ),
    inference(superposition,[status(thm)],[c_63316,c_63510])).

cnf(c_56096,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,k2_xboole_0(X1,X2)),sP4_iProver_split(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))) = sP4_iProver_split(k2_xboole_0(X1,X2),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_625,c_56078])).

cnf(c_56402,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(X0,X1),X2)) = sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(X2,X0),X0),X1) ),
    inference(demodulation,[status(thm)],[c_56096,c_53685,c_54100,c_54151])).

cnf(c_56403,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(X0,X1),X1),X2) = sP4_iProver_split(X2,sP4_iProver_split(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_56402,c_53989,c_54100])).

cnf(c_56404,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,X1),sP4_iProver_split(X2,X0)) = sP4_iProver_split(X2,sP4_iProver_split(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_56403,c_54100])).

cnf(c_63541,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_63521,c_54151,c_56404])).

cnf(c_68416,plain,
    ( sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sP5_iProver_split))) = sP4_iProver_split(sP4_iProver_split(X0,sK3),sP5_iProver_split) ),
    inference(demodulation,[status(thm)],[c_68415,c_54013,c_57128,c_63541,c_65380,c_68346])).

cnf(c_68417,plain,
    ( sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sP5_iProver_split))) = sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,X0)) ),
    inference(demodulation,[status(thm)],[c_68416,c_54100])).

cnf(c_105830,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,X0)) ),
    inference(light_normalisation,[status(thm)],[c_105829,c_65380,c_68417])).

cnf(c_126945,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)),X0) = k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),X0) ),
    inference(demodulation,[status(thm)],[c_126944,c_105830,c_117418])).

cnf(c_127092,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0)),sK3)),sP4_iProver_split(k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))),sK4)) = k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0)),sK3)),sK4))) ),
    inference(superposition,[status(thm)],[c_126945,c_76781])).

cnf(c_105138,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,k4_xboole_0(X1,k2_xboole_0(X2,X3))),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)) = sP4_iProver_split(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),sP4_iProver_split(X0,X1)) ),
    inference(superposition,[status(thm)],[c_696,c_105094])).

cnf(c_105855,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,X2)),sP4_iProver_split(sP4_iProver_split(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))),X3)) = sP4_iProver_split(k4_xboole_0(X0,k4_xboole_0(X0,X2)),sP4_iProver_split(sP4_iProver_split(X3,X0),X1)) ),
    inference(demodulation,[status(thm)],[c_105138,c_53685,c_54100])).

cnf(c_82224,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,k4_xboole_0(X1,X2)),sP4_iProver_split(X1,X3)) = sP4_iProver_split(sP4_iProver_split(X3,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_49082,c_82099])).

cnf(c_82492,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,k4_xboole_0(X1,X2)),sP4_iProver_split(X1,X3)) = sP4_iProver_split(X0,sP4_iProver_split(X1,X3)) ),
    inference(demodulation,[status(thm)],[c_82224,c_82099])).

cnf(c_82138,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,k4_xboole_0(X1,k2_xboole_0(X2,X3))),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)) = sP4_iProver_split(X1,sP4_iProver_split(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),X0)) ),
    inference(superposition,[status(thm)],[c_696,c_82099])).

cnf(c_82838,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,X2)),sP4_iProver_split(sP4_iProver_split(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))),X3)) = sP4_iProver_split(sP4_iProver_split(X3,X1),X0) ),
    inference(demodulation,[status(thm)],[c_82138,c_53685,c_54100,c_56206])).

cnf(c_82839,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,X2)),sP4_iProver_split(k4_xboole_0(X0,k4_xboole_0(X0,X2)),sP4_iProver_split(X3,X1))) = sP4_iProver_split(X1,sP4_iProver_split(X0,X3)) ),
    inference(demodulation,[status(thm)],[c_82838,c_54100])).

cnf(c_105856,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(X0,sP4_iProver_split(X1,X2))) = sP4_iProver_split(X1,sP4_iProver_split(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_105855,c_54100,c_82492,c_82839])).

cnf(c_23957,plain,
    ( k2_xboole_0(sK4,k4_xboole_0(k4_xboole_0(sK3,X0),sK5)) = k2_xboole_0(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_22126,c_14703])).

cnf(c_23965,plain,
    ( k2_xboole_0(sK4,k4_xboole_0(sK3,k2_xboole_0(X0,sK5))) = sK4 ),
    inference(demodulation,[status(thm)],[c_23957,c_9,c_518])).

cnf(c_25926,plain,
    ( k2_xboole_0(sK4,k4_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(X1,sK5)))) = sK4 ),
    inference(superposition,[status(thm)],[c_11,c_23965])).

cnf(c_60821,plain,
    ( sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(k2_xboole_0(X0,sK5),X1)),sK4) = sK4 ),
    inference(demodulation,[status(thm)],[c_25926,c_53685])).

cnf(c_60822,plain,
    ( sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(sK5,sP4_iProver_split(X0,X1))),sK4) = sK4 ),
    inference(demodulation,[status(thm)],[c_60821,c_53685,c_54923])).

cnf(c_117597,plain,
    ( k4_xboole_0(sP4_iProver_split(sP4_iProver_split(sK5,sP4_iProver_split(X0,X1)),sK3),sK4) = k4_xboole_0(sP4_iProver_split(sK5,sP4_iProver_split(X0,X1)),sK4) ),
    inference(superposition,[status(thm)],[c_60822,c_117523])).

cnf(c_111260,plain,
    ( k2_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK5)) ),
    inference(superposition,[status(thm)],[c_110883,c_245])).

cnf(c_111309,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK5)) ),
    inference(demodulation,[status(thm)],[c_111260,c_111296])).

cnf(c_111310,plain,
    ( sP4_iProver_split(sP4_iProver_split(sK5,X0),sK3) = sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3)) ),
    inference(demodulation,[status(thm)],[c_111309,c_53685])).

cnf(c_118257,plain,
    ( k4_xboole_0(sP4_iProver_split(sP4_iProver_split(X0,X1),sP4_iProver_split(sP5_iProver_split,sK3)),sK4) = k4_xboole_0(sP4_iProver_split(sK5,sP4_iProver_split(X0,X1)),sK4) ),
    inference(demodulation,[status(thm)],[c_117597,c_111310])).

cnf(c_118258,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X1)),sK4) = k4_xboole_0(sP4_iProver_split(sK5,sP4_iProver_split(X0,X1)),sK4) ),
    inference(demodulation,[status(thm)],[c_118257,c_107492])).

cnf(c_110796,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sK5),X0),sK5) = sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X0) ),
    inference(superposition,[status(thm)],[c_110644,c_72427])).

cnf(c_12500,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2)))) = k4_xboole_0(k2_xboole_0(sK4,X1),k4_xboole_0(k2_xboole_0(sK4,X1),k4_xboole_0(X0,sK5))) ),
    inference(superposition,[status(thm)],[c_1674,c_616])).

cnf(c_77666,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(X0,k2_xboole_0(X1,sP4_iProver_split(sK3,sK2)))) = k4_xboole_0(k2_xboole_0(sK4,X1),k4_xboole_0(k2_xboole_0(sK4,X1),k4_xboole_0(X0,sK5))) ),
    inference(light_normalisation,[status(thm)],[c_12500,c_59877])).

cnf(c_77667,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK5,k4_xboole_0(X0,sP4_iProver_split(sP4_iProver_split(sK3,sK2),X1)))) = k4_xboole_0(sP4_iProver_split(X1,sK4),k4_xboole_0(sP4_iProver_split(X1,sK4),k4_xboole_0(X0,sK5))) ),
    inference(demodulation,[status(thm)],[c_77666,c_9,c_53685])).

cnf(c_77668,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK5,k4_xboole_0(X0,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X1)))) = k4_xboole_0(sP4_iProver_split(X1,sK4),k4_xboole_0(sP4_iProver_split(X1,sK4),k4_xboole_0(X0,sK5))) ),
    inference(light_normalisation,[status(thm)],[c_77667,c_61315])).

cnf(c_77669,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X1)),sK5)) = k4_xboole_0(sP4_iProver_split(X1,sK4),k4_xboole_0(sP4_iProver_split(X1,sK4),k4_xboole_0(X0,sK5))) ),
    inference(demodulation,[status(thm)],[c_77668,c_53685])).

cnf(c_77670,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(sK3,sP4_iProver_split(X1,sP5_iProver_split))),sK5)) = k4_xboole_0(sP4_iProver_split(X1,sK4),k4_xboole_0(sP4_iProver_split(X1,sK4),k4_xboole_0(X0,sK5))) ),
    inference(demodulation,[status(thm)],[c_77669,c_54100])).

cnf(c_77671,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X1))),sK5)) = k4_xboole_0(sP4_iProver_split(X1,sK4),k4_xboole_0(sP4_iProver_split(X1,sK4),k4_xboole_0(X0,sK5))) ),
    inference(demodulation,[status(thm)],[c_77670,c_67465])).

cnf(c_77710,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),sP4_iProver_split(k4_xboole_0(k2_xboole_0(sK3,sK2),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))),sK5)) = k4_xboole_0(sP4_iProver_split(X0,sK4),k4_xboole_0(sP4_iProver_split(X0,sK4),k4_xboole_0(sK4,sK5))) ),
    inference(superposition,[status(thm)],[c_512,c_77671])).

cnf(c_77846,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(X0,k2_xboole_0(sK5,sP4_iProver_split(X1,sK4)))) = k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X1))),sK5)) ),
    inference(superposition,[status(thm)],[c_77671,c_616])).

cnf(c_77870,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X1))),sK5)) = k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,sK4)),sK5)) ),
    inference(demodulation,[status(thm)],[c_77846,c_17153,c_53685])).

cnf(c_77713,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,sK2),sP4_iProver_split(k4_xboole_0(k2_xboole_0(sK4,sK2),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))),sK5)) = k4_xboole_0(sP4_iProver_split(X0,sK4),k4_xboole_0(sP4_iProver_split(X0,sK4),k4_xboole_0(sK4,sK5))) ),
    inference(superposition,[status(thm)],[c_3643,c_77671])).

cnf(c_78154,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,sP5_iProver_split),sP4_iProver_split(k4_xboole_0(k2_xboole_0(sK4,sP5_iProver_split),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))),sK5)) = k4_xboole_0(sP4_iProver_split(X0,sK4),k4_xboole_0(sP4_iProver_split(X0,sK4),k4_xboole_0(sK4,sK5))) ),
    inference(light_normalisation,[status(thm)],[c_77713,c_65380])).

cnf(c_63169,plain,
    ( sP4_iProver_split(sP1_iProver_split,sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_63041,c_58210])).

cnf(c_11579,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),X0),k2_xboole_0(sK3,sK2)) = k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_7838,c_8])).

cnf(c_11628,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),X0),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11579,c_9,c_1862,c_3028])).

cnf(c_43342,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),X0),k2_xboole_0(sK3,sK2)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_11628,c_11628,c_34016])).

cnf(c_43371,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK4,sK2),X0),k2_xboole_0(sK3,sK2)) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_0,c_43342])).

cnf(c_69493,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK4,sP5_iProver_split),X0),sP4_iProver_split(sK3,sK2)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_43371,c_43371,c_59877,c_65380])).

cnf(c_69494,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK4),k2_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_69493,c_9,c_53685,c_61315])).

cnf(c_69495,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK4),sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X0)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_69494,c_53685])).

cnf(c_69496,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK4),sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_69495,c_54100])).

cnf(c_69497,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK4),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_69496,c_67465])).

cnf(c_32558,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(sK5,k4_xboole_0(X0,sK4))))) = k4_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_14697,c_6382])).

cnf(c_70430,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sP4_iProver_split(sK3,sK2)),k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(sK5,k4_xboole_0(X0,sK4))))) = k4_xboole_0(X0,sP4_iProver_split(sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_32558,c_32558,c_59877])).

cnf(c_70431,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),k4_xboole_0(X1,sP4_iProver_split(k2_xboole_0(sK5,k4_xboole_0(X0,sK4)),X2)))) = k4_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3)) ),
    inference(demodulation,[status(thm)],[c_70430,c_9,c_53685,c_61315])).

cnf(c_70432,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X1,sP4_iProver_split(k2_xboole_0(sK5,k4_xboole_0(X0,sK4)),X2)),sP4_iProver_split(sP5_iProver_split,sK3))) = k4_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3)) ),
    inference(demodulation,[status(thm)],[c_70431,c_53685])).

cnf(c_70433,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X1,sP4_iProver_split(sK5,sP4_iProver_split(X2,k4_xboole_0(X0,sK4)))),sP4_iProver_split(sP5_iProver_split,sK3))) = k4_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3)) ),
    inference(demodulation,[status(thm)],[c_70432,c_53685,c_54100])).

cnf(c_2100,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),k2_xboole_0(sK3,X1)) = k2_xboole_0(X1,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_1761,c_244])).

cnf(c_3006,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK5) = k4_xboole_0(k2_xboole_0(sK4,X0),sK5) ),
    inference(superposition,[status(thm)],[c_1674,c_509])).

cnf(c_20265,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)),sK5) = k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK3,sK2)),sK5) ),
    inference(superposition,[status(thm)],[c_2100,c_3006])).

cnf(c_3812,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,sK5)),k1_xboole_0) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_2936,c_3755])).

cnf(c_2615,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,sK5)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_1275,c_245])).

cnf(c_3829,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_3812,c_7,c_2615])).

cnf(c_20312,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)),sK5) = k4_xboole_0(sK4,sK5) ),
    inference(light_normalisation,[status(thm)],[c_20265,c_512,c_3829])).

cnf(c_70517,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sP5_iProver_split,sK3)),sK2)),sK5) = k4_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_70433,c_20312])).

cnf(c_37807,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK5,sK2),X0),k2_xboole_0(sK3,sK2)) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_0,c_37775])).

cnf(c_65786,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,X0),sP4_iProver_split(sK3,sK2)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_37807,c_37807,c_49910,c_59877])).

cnf(c_65787,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_65786,c_37615,c_61315])).

cnf(c_65788,plain,
    ( k4_xboole_0(sK5,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X0)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_65787,c_53685])).

cnf(c_65789,plain,
    ( k4_xboole_0(sK5,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_65788,c_54100])).

cnf(c_66838,plain,
    ( k4_xboole_0(sK5,sP4_iProver_split(sK3,sP5_iProver_split)) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_66819,c_65789])).

cnf(c_66845,plain,
    ( k4_xboole_0(sK5,sP4_iProver_split(sP5_iProver_split,sK3)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_66838,c_65760])).

cnf(c_71206,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sP1_iProver_split,sP5_iProver_split)),sK5) = k4_xboole_0(sK4,sK5) ),
    inference(light_normalisation,[status(thm)],[c_70517,c_65380,c_66845])).

cnf(c_71207,plain,
    ( k4_xboole_0(sP4_iProver_split(k2_xboole_0(sP1_iProver_split,sP5_iProver_split),sK4),sK5) = k4_xboole_0(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_71206,c_53685])).

cnf(c_71208,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK4),sK5) = k4_xboole_0(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_71207,c_35092])).

cnf(c_78155,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,sK4),k4_xboole_0(sP4_iProver_split(X0,sK4),k4_xboole_0(sK4,sK5))) = k4_xboole_0(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_78154,c_53685,c_63169,c_69497,c_71208])).

cnf(c_78182,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),sP4_iProver_split(k4_xboole_0(k2_xboole_0(sK3,sK2),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))),sK5)) = k4_xboole_0(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_77710,c_77870,c_78155])).

cnf(c_78183,plain,
    ( k4_xboole_0(sP4_iProver_split(sK3,sK2),sP4_iProver_split(k4_xboole_0(sP4_iProver_split(sK3,sK2),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))),sK5)) = k4_xboole_0(sK4,sK5) ),
    inference(light_normalisation,[status(thm)],[c_78182,c_59877])).

cnf(c_74331,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),sP4_iProver_split(k4_xboole_0(X1,X0),sP4_iProver_split(X0,X2))) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_509,c_74313])).

cnf(c_75599,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,X1),sP4_iProver_split(X0,sP4_iProver_split(X1,X2))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_74331,c_53685,c_74631])).

cnf(c_78184,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sK5) = k4_xboole_0(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_78183,c_61315,c_63169,c_75599])).

cnf(c_759,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(sK3,sK2))),k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(sK3,sK2))))) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_713,c_153])).

cnf(c_708,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5))) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK5) ),
    inference(superposition,[status(thm)],[c_512,c_10])).

cnf(c_718,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)))) = k4_xboole_0(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_708,c_512,c_713])).

cnf(c_763,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(sK3,sK2))),k4_xboole_0(sK4,sK5)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_759,c_718])).

cnf(c_965,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(sK3,sK2))),k2_xboole_0(X0,k4_xboole_0(sK4,sK5))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_763,c_243])).

cnf(c_46141,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,sK3),k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK5,sK3)),sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12841,c_2909])).

cnf(c_46177,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,sK3),k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK5,sK3)),sK2)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_46141,c_34016])).

cnf(c_46178,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_46177,c_505,c_37615])).

cnf(c_86419,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(X0,k4_xboole_0(sK4,sK5))) = k2_xboole_0(X0,sP4_iProver_split(sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_965,c_965,c_39054,c_46178,c_59877])).

cnf(c_86420,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK4,sK5),X0),sK5) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_86419,c_53685,c_54100,c_61315])).

cnf(c_86421,plain,
    ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK4,sK5),X0),sK5) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_86420,c_67465])).

cnf(c_110909,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0)) = sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X0) ),
    inference(light_normalisation,[status(thm)],[c_110796,c_78184,c_86421])).

cnf(c_118259,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X1))),sK4) = k4_xboole_0(sP4_iProver_split(sK5,sP4_iProver_split(X0,X1)),sK4) ),
    inference(demodulation,[status(thm)],[c_118258,c_110909])).

cnf(c_116942,plain,
    ( sP4_iProver_split(k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sP1_iProver_split,k4_xboole_0(sK5,sK4))),X0) = k2_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_62059,c_115896])).

cnf(c_118730,plain,
    ( sP4_iProver_split(sK4,X0) = k2_xboole_0(sK4,X0) ),
    inference(light_normalisation,[status(thm)],[c_116942,c_62059])).

cnf(c_120099,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,X1),sK4) = sP4_iProver_split(sK4,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_118730,c_114564])).

cnf(c_1330,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK4,k2_xboole_0(sK5,X1))) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1044,c_243])).

cnf(c_1359,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,X1))) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_1330,c_1329])).

cnf(c_1256,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(X1,sK5))) = k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_961,c_243])).

cnf(c_14332,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,X1)) = k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(X1,sK5))) ),
    inference(superposition,[status(thm)],[c_1256,c_245])).

cnf(c_2638,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) = k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(X1,sK5))) ),
    inference(superposition,[status(thm)],[c_245,c_1329])).

cnf(c_14397,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_14332,c_2638])).

cnf(c_126238,plain,
    ( k2_xboole_0(sP4_iProver_split(sK3,sK2),sP4_iProver_split(X0,X1)) = k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sP5_iProver_split,X1))) ),
    inference(light_normalisation,[status(thm)],[c_1359,c_14397,c_59877,c_65380,c_117418])).

cnf(c_105333,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,k4_xboole_0(X1,sP5_iProver_split)))) = sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,X1))) ),
    inference(superposition,[status(thm)],[c_105094,c_67465])).

cnf(c_82299,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,k4_xboole_0(X1,sP5_iProver_split)))) = sP4_iProver_split(sK3,sP4_iProver_split(X1,sP4_iProver_split(sP5_iProver_split,X0))) ),
    inference(superposition,[status(thm)],[c_82099,c_67465])).

cnf(c_17970,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,X1)))) = k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2))) ),
    inference(superposition,[status(thm)],[c_16774,c_243])).

cnf(c_62619,plain,
    ( k2_xboole_0(sP4_iProver_split(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,X1)))) = k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_17970,c_17970,c_59877])).

cnf(c_62620,plain,
    ( sP4_iProver_split(sP4_iProver_split(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),X1),sP4_iProver_split(sP5_iProver_split,sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(X1,k2_xboole_0(X0,sK2))) ),
    inference(demodulation,[status(thm)],[c_62619,c_53685,c_54100,c_61315])).

cnf(c_62621,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sP4_iProver_split(X0,k2_xboole_0(sK2,X1)),sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,X1))) ),
    inference(demodulation,[status(thm)],[c_62620,c_53685,c_54100,c_56404])).

cnf(c_62622,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(k2_xboole_0(sK2,X0),sP4_iProver_split(sK3,X1))) = sP4_iProver_split(sK3,sP4_iProver_split(X1,sP4_iProver_split(sK2,X0))) ),
    inference(demodulation,[status(thm)],[c_62621,c_54100])).

cnf(c_62623,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK2,sP4_iProver_split(sP4_iProver_split(sK3,X0),X1))) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,X1))) ),
    inference(demodulation,[status(thm)],[c_62622,c_53685,c_54100])).

cnf(c_62624,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK2,sP4_iProver_split(X0,sP4_iProver_split(X1,sK3)))) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,X1))) ),
    inference(demodulation,[status(thm)],[c_62623,c_54100])).

cnf(c_963,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK5,sK4)) ),
    inference(superposition,[status(thm)],[c_715,c_243])).

cnf(c_1282,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(X0,sK4)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_1259,c_243])).

cnf(c_4142,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k2_xboole_0(X0,sK4),sK5) ),
    inference(superposition,[status(thm)],[c_1282,c_1672])).

cnf(c_1046,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(k2_xboole_0(sK3,sK2),X0)) = k2_xboole_0(k2_xboole_0(sK5,sK4),X0) ),
    inference(superposition,[status(thm)],[c_715,c_11])).

cnf(c_1055,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,k2_xboole_0(sK5,X0))) = k2_xboole_0(k2_xboole_0(sK5,sK4),X0) ),
    inference(demodulation,[status(thm)],[c_1044,c_1046])).

cnf(c_2437,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
    inference(light_normalisation,[status(thm)],[c_1055,c_1055,c_1259,c_1525])).

cnf(c_2441,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
    inference(superposition,[status(thm)],[c_243,c_2437])).

cnf(c_4205,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_4142,c_2244,c_2441,c_3970])).

cnf(c_78990,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(X0,sP4_iProver_split(sK3,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_963,c_1259,c_4205,c_59877])).

cnf(c_78991,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sK3,sK2),X0),sK5) = sP4_iProver_split(sK2,sP4_iProver_split(X0,sK3)) ),
    inference(demodulation,[status(thm)],[c_78990,c_53685,c_54100,c_59877])).

cnf(c_53297,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK3)) = k2_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_23951,c_21035])).

cnf(c_54791,plain,
    ( k2_xboole_0(sP1_iProver_split,k2_xboole_0(X0,sK3)) = k2_xboole_0(sK3,X0) ),
    inference(light_normalisation,[status(thm)],[c_53297,c_34016])).

cnf(c_54792,plain,
    ( sP4_iProver_split(sK3,X0) = sP4_iProver_split(X0,sK3) ),
    inference(demodulation,[status(thm)],[c_54791,c_35092,c_53685])).

cnf(c_26782,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK4,X0),sK2),k2_xboole_0(X1,sK3)) = k2_xboole_0(X1,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_26587,c_245])).

cnf(c_53480,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK3),X1),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k2_xboole_0(X0,sK3),k2_xboole_0(k4_xboole_0(sK4,X2),sK2)) ),
    inference(superposition,[status(thm)],[c_26782,c_21035])).

cnf(c_37050,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK3),k2_xboole_0(k4_xboole_0(sK4,X1),sK2)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_26782,c_0])).

cnf(c_54224,plain,
    ( sP4_iProver_split(sP4_iProver_split(sK2,X0),sK3) = sP4_iProver_split(sP4_iProver_split(sK2,sK3),X0) ),
    inference(demodulation,[status(thm)],[c_53480,c_21328,c_37050,c_53685])).

cnf(c_54638,plain,
    ( sP4_iProver_split(sP4_iProver_split(sK3,sK2),X0) = sP4_iProver_split(sP4_iProver_split(sK2,X0),sK3) ),
    inference(demodulation,[status(thm)],[c_54587,c_54224])).

cnf(c_54718,plain,
    ( sP4_iProver_split(sK2,sP4_iProver_split(X0,sK3)) = sP4_iProver_split(sP4_iProver_split(sK2,X0),sK3) ),
    inference(demodulation,[status(thm)],[c_54638,c_54100])).

cnf(c_54795,plain,
    ( sP4_iProver_split(sK2,sP4_iProver_split(X0,sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_54792,c_54718])).

cnf(c_78992,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X0),sK5) = sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,X0)) ),
    inference(light_normalisation,[status(thm)],[c_78991,c_54795,c_61315,c_65380])).

cnf(c_65792,plain,
    ( sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(sK5,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)))) = sP4_iProver_split(sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)),sK5) ),
    inference(superposition,[status(thm)],[c_65789,c_56078])).

cnf(c_65825,plain,
    ( k2_xboole_0(sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)),sP1_iProver_split) = k2_xboole_0(sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)),sK5) ),
    inference(superposition,[status(thm)],[c_65789,c_6])).

cnf(c_35091,plain,
    ( k2_xboole_0(X0,sP1_iProver_split) = X0 ),
    inference(superposition,[status(thm)],[c_34829,c_1749])).

cnf(c_65852,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split))) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_65825,c_35091,c_53685])).

cnf(c_65879,plain,
    ( sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split))) = sP4_iProver_split(sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)),sK5) ),
    inference(demodulation,[status(thm)],[c_65792,c_65852])).

cnf(c_65880,plain,
    ( sP4_iProver_split(sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)),sK5) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_65879,c_53848,c_54100])).

cnf(c_78993,plain,
    ( sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,X0)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_78992,c_54100,c_65880,c_75015])).

cnf(c_78994,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0)) = sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,X0)) ),
    inference(light_normalisation,[status(thm)],[c_78993,c_67465])).

cnf(c_78999,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(sK2,sP4_iProver_split(X0,sP4_iProver_split(X1,sK3))))) = sP4_iProver_split(sK3,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,X1)))) ),
    inference(superposition,[status(thm)],[c_62624,c_78994])).

cnf(c_79096,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sP4_iProver_split(X1,sK3))))) = sP4_iProver_split(sK3,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,X1)))) ),
    inference(light_normalisation,[status(thm)],[c_78999,c_65380])).

cnf(c_68512,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(X1,k2_xboole_0(X2,X0))) = sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X2,X0),X1),X0) ),
    inference(superposition,[status(thm)],[c_8,c_68488])).

cnf(c_69250,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(X1,k2_xboole_0(X2,X0))) = sP4_iProver_split(X0,sP4_iProver_split(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_68512,c_68488])).

cnf(c_69251,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(X0,X2))) = sP4_iProver_split(X0,sP4_iProver_split(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_69250,c_53685])).

cnf(c_74520,plain,
    ( k4_xboole_0(k2_xboole_0(sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2)),X0),sP1_iProver_split) = sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2)) ),
    inference(superposition,[status(thm)],[c_74313,c_3755])).

cnf(c_75191,plain,
    ( k4_xboole_0(k2_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),X0),sP1_iProver_split) = sP4_iProver_split(X0,sP4_iProver_split(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_74520,c_74631])).

cnf(c_56549,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,X3))),sP1_iProver_split) = sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,X3))) ),
    inference(superposition,[status(thm)],[c_56497,c_3026])).

cnf(c_75192,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(X0,sP4_iProver_split(X1,X2))) = sP4_iProver_split(X0,sP4_iProver_split(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_75191,c_37461,c_53685,c_56549])).

cnf(c_79097,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sP4_iProver_split(X1,sK3))) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,X1))) ),
    inference(demodulation,[status(thm)],[c_79096,c_53989,c_69251,c_75192])).

cnf(c_82323,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,k4_xboole_0(X1,sP5_iProver_split)))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X1,sP4_iProver_split(X0,sK3))) ),
    inference(demodulation,[status(thm)],[c_82299,c_79097])).

cnf(c_105361,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sP4_iProver_split(X1,sK3))) = sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_105333,c_82323])).

cnf(c_126239,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(sK3,k2_xboole_0(sP5_iProver_split,X1))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X1,sP4_iProver_split(X0,sK3))) ),
    inference(demodulation,[status(thm)],[c_126238,c_65380,c_81806,c_105361,c_117418])).

cnf(c_126240,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X1,sK3))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X1,sP4_iProver_split(X0,sK3))) ),
    inference(demodulation,[status(thm)],[c_126239,c_105830,c_117418])).

cnf(c_126320,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(X0,sK3),sP5_iProver_split),X1) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sP4_iProver_split(X1,sK3))) ),
    inference(superposition,[status(thm)],[c_126240,c_112026])).

cnf(c_70518,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sP5_iProver_split,sK3)),sK2),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_70433,c_2100])).

cnf(c_71203,plain,
    ( k2_xboole_0(k2_xboole_0(sP1_iProver_split,sP5_iProver_split),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,sP4_iProver_split(sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_70518,c_59877,c_65380,c_66845])).

cnf(c_71204,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,sK3),sP5_iProver_split) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)) ),
    inference(demodulation,[status(thm)],[c_71203,c_3970,c_35092,c_53685,c_54100,c_61315])).

cnf(c_71205,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,sK3),sP5_iProver_split) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_71204,c_67465])).

cnf(c_126568,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0)),X1) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sP4_iProver_split(X1,sK3))) ),
    inference(light_normalisation,[status(thm)],[c_126320,c_71205])).

cnf(c_127105,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sK3))),sP4_iProver_split(sK4,k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))))) = k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sP4_iProver_split(sK5,sP4_iProver_split(X0,sK3)),sK4))) ),
    inference(demodulation,[status(thm)],[c_127092,c_105856,c_118259,c_120099,c_126568])).

cnf(c_3636,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK2,sK5)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_3452,c_11])).

cnf(c_12521,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK5),k4_xboole_0(k2_xboole_0(sK2,sK5),k4_xboole_0(X0,sK4))) = k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_3636,c_616])).

cnf(c_12808,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK5),k4_xboole_0(k2_xboole_0(sK2,sK5),k4_xboole_0(X0,sK4))) = k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
    inference(demodulation,[status(thm)],[c_12475,c_12521])).

cnf(c_58404,plain,
    ( k4_xboole_0(sP4_iProver_split(sK5,sK2),k4_xboole_0(sP4_iProver_split(sK5,sK2),k4_xboole_0(X0,sK4))) = k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
    inference(demodulation,[status(thm)],[c_12808,c_53685])).

cnf(c_17100,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK5,X1))),sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_16936,c_1761])).

cnf(c_58473,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))),sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_58404,c_17100])).

cnf(c_58474,plain,
    ( sP4_iProver_split(sP4_iProver_split(sK2,k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)))),sK3) = sP4_iProver_split(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_58473,c_1761,c_53685])).

cnf(c_53298,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(sK5,X1))) = k2_xboole_0(k4_xboole_0(sK5,X1),X0) ),
    inference(superposition,[status(thm)],[c_24125,c_21035])).

cnf(c_54786,plain,
    ( k2_xboole_0(sP1_iProver_split,k2_xboole_0(X0,k4_xboole_0(sK5,X1))) = k2_xboole_0(k4_xboole_0(sK5,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_53298,c_34016])).

cnf(c_54787,plain,
    ( sP4_iProver_split(k4_xboole_0(sK5,X0),X1) = sP4_iProver_split(X1,k4_xboole_0(sK5,X0)) ),
    inference(demodulation,[status(thm)],[c_54786,c_35092,c_53685])).

cnf(c_8692,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK4),X0)),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8615,c_1862])).

cnf(c_31542,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK4),X0)),k2_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(sK5,sK4),X1),X0),k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1955,c_8692])).

cnf(c_16137,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(X1,sK5))))) = k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(sK3,sK2)),sK2))) ),
    inference(superposition,[status(thm)],[c_1256,c_16088])).

cnf(c_14329,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,X1)) = k2_xboole_0(sK4,k2_xboole_0(X1,k2_xboole_0(X0,sK5))) ),
    inference(superposition,[status(thm)],[c_1256,c_244])).

cnf(c_14400,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(X1,sK5))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_14329,c_14397])).

cnf(c_16427,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))))) = k2_xboole_0(X1,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK2))) ),
    inference(light_normalisation,[status(thm)],[c_16137,c_14400])).

cnf(c_2444,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
    inference(superposition,[status(thm)],[c_0,c_2437])).

cnf(c_7789,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(X0,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_245,c_3353])).

cnf(c_16428,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK5,X1),k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_16427,c_1512,c_1525,c_2444,c_7789])).

cnf(c_4139,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(k2_xboole_0(sK5,X0),sK4) ),
    inference(superposition,[status(thm)],[c_1329,c_1672])).

cnf(c_4208,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(demodulation,[status(thm)],[c_4139,c_1259,c_3970])).

cnf(c_1326,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
    inference(superposition,[status(thm)],[c_1044,c_6])).

cnf(c_14516,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_1326,c_1703,c_3970])).

cnf(c_14520,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK2)) = k2_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) ),
    inference(superposition,[status(thm)],[c_8,c_14516])).

cnf(c_14588,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK2)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_14520,c_14516])).

cnf(c_14589,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,X0),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_14588,c_1512,c_7789])).

cnf(c_16429,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sK3,sK2)) = k2_xboole_0(X1,k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) ),
    inference(demodulation,[status(thm)],[c_16428,c_4208,c_14397,c_14589])).

cnf(c_23154,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_11,c_625])).

cnf(c_31696,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK5,sK4)),k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(k4_xboole_0(sK5,sK4),X1),sK2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_31542,c_16429,c_23154])).

cnf(c_31697,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK5,sK4)),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_31696,c_9,c_1761])).

cnf(c_53305,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(sK5,sK4)))) = k2_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK5,sK4)),X0) ),
    inference(superposition,[status(thm)],[c_31697,c_21035])).

cnf(c_54756,plain,
    ( k2_xboole_0(sP1_iProver_split,k2_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(sK5,sK4)))) = k2_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK5,sK4)),X0) ),
    inference(light_normalisation,[status(thm)],[c_53305,c_34016])).

cnf(c_54757,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,sK2),k4_xboole_0(sK5,sK4)) = sP4_iProver_split(k2_xboole_0(sK2,k4_xboole_0(sK5,sK4)),X0) ),
    inference(demodulation,[status(thm)],[c_54756,c_3970,c_35092,c_53685])).

cnf(c_54758,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,sK2),k4_xboole_0(sK5,sK4)) = sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK5,sK4),sK2),X0) ),
    inference(demodulation,[status(thm)],[c_54757,c_53685])).

cnf(c_54788,plain,
    ( sP4_iProver_split(sP4_iProver_split(sK2,k4_xboole_0(sK5,sK4)),X0) = sP4_iProver_split(sP4_iProver_split(X0,sK2),k4_xboole_0(sK5,sK4)) ),
    inference(demodulation,[status(thm)],[c_54787,c_54758])).

cnf(c_54790,plain,
    ( sP4_iProver_split(sK2,sP4_iProver_split(k4_xboole_0(sK5,sK4),X0)) = sP4_iProver_split(sP4_iProver_split(sK2,k4_xboole_0(sK5,sK4)),X0) ),
    inference(demodulation,[status(thm)],[c_54788,c_54100])).

cnf(c_58475,plain,
    ( sP4_iProver_split(sK2,sP4_iProver_split(k4_xboole_0(sK5,sK4),sK3)) = sP4_iProver_split(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_58474,c_10,c_54100,c_54790])).

cnf(c_76096,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(k4_xboole_0(sK5,sK4),sK3)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(light_normalisation,[status(thm)],[c_58475,c_58475,c_59354,c_65380,c_65760])).

cnf(c_79002,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sK3))) = sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,sK3)) ),
    inference(superposition,[status(thm)],[c_76096,c_78994])).

cnf(c_79083,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sK3))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sK3)) ),
    inference(demodulation,[status(thm)],[c_79002,c_78994])).

cnf(c_74832,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sK5,X0),X1))) = sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X1)),sK5) ),
    inference(superposition,[status(thm)],[c_56206,c_68346])).

cnf(c_74839,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sK5,X0),X1))) = sP4_iProver_split(X1,sP4_iProver_split(sP4_iProver_split(sK5,sP5_iProver_split),sK3)) ),
    inference(demodulation,[status(thm)],[c_74832,c_54100])).

cnf(c_74840,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sK5,X0),X1))) = sP4_iProver_split(X1,sP4_iProver_split(sK5,sP4_iProver_split(sK3,sP5_iProver_split))) ),
    inference(demodulation,[status(thm)],[c_74839,c_54923])).

cnf(c_74841,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sK5,X0),X1))) = sP4_iProver_split(X1,sP4_iProver_split(sP5_iProver_split,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_74840,c_62866,c_65760])).

cnf(c_79084,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sK3)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
    inference(demodulation,[status(thm)],[c_79083,c_53801,c_74841,c_76096])).

cnf(c_2012,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),X0))) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1674,c_505])).

cnf(c_5243,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),X0)),sK5) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK5) ),
    inference(superposition,[status(thm)],[c_2012,c_509])).

cnf(c_5267,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),X0)),sK5) = k4_xboole_0(sK4,sK5) ),
    inference(light_normalisation,[status(thm)],[c_5243,c_512])).

cnf(c_9791,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,sK3),sK5) = k4_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_3755,c_5267])).

cnf(c_113679,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,sK3),sK5) = k4_xboole_0(sK3,sK5) ),
    inference(light_normalisation,[status(thm)],[c_9791,c_9791,c_110077])).

cnf(c_113680,plain,
    ( k4_xboole_0(sP4_iProver_split(sK3,sK4),sK5) = k4_xboole_0(sK3,sK5) ),
    inference(demodulation,[status(thm)],[c_113679,c_9791,c_53685])).

cnf(c_113728,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(sK3,sK4))) = sP4_iProver_split(sP4_iProver_split(X0,k4_xboole_0(sK3,sK5)),sK5) ),
    inference(superposition,[status(thm)],[c_113680,c_105094])).

cnf(c_68545,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2)))) = sP4_iProver_split(sP4_iProver_split(k4_xboole_0(k2_xboole_0(sK4,X1),sK5),X0),sK5) ),
    inference(superposition,[status(thm)],[c_3006,c_68488])).

cnf(c_69042,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2)))) = sP4_iProver_split(sK5,sP4_iProver_split(X0,k2_xboole_0(sK4,X1))) ),
    inference(demodulation,[status(thm)],[c_68545,c_68488])).

cnf(c_69043,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(X0,k2_xboole_0(X1,sP4_iProver_split(sK3,sK2)))) = sP4_iProver_split(sK5,sP4_iProver_split(X0,k2_xboole_0(sK4,X1))) ),
    inference(light_normalisation,[status(thm)],[c_69042,c_59877])).

cnf(c_69044,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(sK3,sK2),X1))) = sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(X1,sK4))) ),
    inference(demodulation,[status(thm)],[c_69043,c_53685])).

cnf(c_69045,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X1))) = sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(X1,sK4))) ),
    inference(light_normalisation,[status(thm)],[c_69044,c_61315])).

cnf(c_69046,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(sK3,sP4_iProver_split(X1,sP5_iProver_split)))) = sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(X1,sK4))) ),
    inference(demodulation,[status(thm)],[c_69045,c_54100])).

cnf(c_69047,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,X1))) = sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(X1,sK4))) ),
    inference(demodulation,[status(thm)],[c_69046,c_67465,c_68346])).

cnf(c_113776,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(X0,sK3)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)) ),
    inference(demodulation,[status(thm)],[c_113728,c_53801,c_69047,c_105094])).

cnf(c_120019,plain,
    ( k4_xboole_0(sP4_iProver_split(sK4,X0),X0) = k4_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_118730,c_8])).

cnf(c_120921,plain,
    ( k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sP4_iProver_split(sK4,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))),sK4))) = k4_xboole_0(sP4_iProver_split(sK4,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))),sP4_iProver_split(k4_xboole_0(sK4,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))),sK4)) ),
    inference(superposition,[status(thm)],[c_120019,c_76781])).

cnf(c_8699,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK4),X0)),k2_xboole_0(X1,sK3)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_8615,c_245])).

cnf(c_58237,plain,
    ( sP4_iProver_split(sP4_iProver_split(sK3,X0),sP4_iProver_split(k2_xboole_0(k4_xboole_0(sK5,sK4),X1),sK2)) = sP4_iProver_split(X1,sP4_iProver_split(X0,k2_xboole_0(sK3,sK2))) ),
    inference(demodulation,[status(thm)],[c_8699,c_53685,c_54100])).

cnf(c_58238,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sK2,X1)),sK3)) = sP4_iProver_split(X1,sP4_iProver_split(X0,sP4_iProver_split(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_58237,c_53685,c_54100])).

cnf(c_58239,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(sK2,X1),sP4_iProver_split(sK3,k4_xboole_0(sK5,sK4)))) = sP4_iProver_split(X1,sP4_iProver_split(X0,sP4_iProver_split(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_58238,c_54100])).

cnf(c_53232,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,sK4),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
    inference(superposition,[status(thm)],[c_1279,c_21035])).

cnf(c_1991,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(sK5,X1)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_1674,c_244])).

cnf(c_18676,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,X0),k2_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k2_xboole_0(sK4,X1),sK5) ),
    inference(superposition,[status(thm)],[c_1749,c_1991])).

cnf(c_4141,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k2_xboole_0(sK4,X0),sK5) ),
    inference(superposition,[status(thm)],[c_1674,c_1672])).

cnf(c_4206,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,X0),sK5) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_4141,c_4205])).

cnf(c_18907,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,X0),k2_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X1)) ),
    inference(demodulation,[status(thm)],[c_18676,c_4206])).

cnf(c_54970,plain,
    ( sP4_iProver_split(sP4_iProver_split(X0,sK3),sK2) = sP4_iProver_split(sP4_iProver_split(X0,sK2),sK3) ),
    inference(demodulation,[status(thm)],[c_53232,c_3970,c_18907,c_53685])).

cnf(c_2934,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1674,c_1862])).

cnf(c_4536,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(k2_xboole_0(sK5,X0),k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1329,c_2934])).

cnf(c_881,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,X0),k4_xboole_0(sK4,k2_xboole_0(sK5,X0))) = k2_xboole_0(k2_xboole_0(sK5,X0),k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_717,c_6])).

cnf(c_882,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,X0),k2_xboole_0(sK3,sK2)) = k2_xboole_0(k2_xboole_0(sK5,X0),sK4) ),
    inference(demodulation,[status(thm)],[c_881,c_6])).

cnf(c_4594,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(k2_xboole_0(sK5,X0),sK4)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4536,c_882])).

cnf(c_4595,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(X0,k2_xboole_0(sK5,sK4))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4594,c_3970])).

cnf(c_4596,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4595,c_1259])).

cnf(c_53252,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,X1)))) = k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X1)),X0) ),
    inference(superposition,[status(thm)],[c_4596,c_21035])).

cnf(c_28692,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),X1) = k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(X0,sK5),X1)) ),
    inference(superposition,[status(thm)],[c_2244,c_11])).

cnf(c_16239,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(X0,sK2),X1)) = k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_16088,c_245])).

cnf(c_16315,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(X0,X1))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_16239,c_1525,c_3970])).

cnf(c_28751,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X1)),X0) ),
    inference(demodulation,[status(thm)],[c_28692,c_2260,c_3970,c_16315])).

cnf(c_54929,plain,
    ( k2_xboole_0(sP1_iProver_split,k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,X1)))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_53252,c_28751,c_34016])).

cnf(c_54930,plain,
    ( sP4_iProver_split(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),X1) = sP4_iProver_split(sP4_iProver_split(k2_xboole_0(X1,X0),sK2),sK3) ),
    inference(demodulation,[status(thm)],[c_54929,c_35092,c_53685])).

cnf(c_54931,plain,
    ( sP4_iProver_split(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),X1) = sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(X0,X1),sK2),sK3) ),
    inference(light_normalisation,[status(thm)],[c_54930,c_53685])).

cnf(c_54932,plain,
    ( sP4_iProver_split(sP4_iProver_split(k2_xboole_0(sK2,X0),sK3),X1) = sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(X0,X1),sK2),sK3) ),
    inference(demodulation,[status(thm)],[c_54931,c_53685])).

cnf(c_54933,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(X0,sK2),sK3),X1) = sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(X0,X1),sK2),sK3) ),
    inference(demodulation,[status(thm)],[c_54932,c_53685])).

cnf(c_54971,plain,
    ( sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(X0,sK3),sK2),X1) = sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(X0,X1),sK2),sK3) ),
    inference(demodulation,[status(thm)],[c_54970,c_54933])).

cnf(c_54974,plain,
    ( sP4_iProver_split(sP4_iProver_split(sK2,X0),sP4_iProver_split(sK3,X1)) = sP4_iProver_split(sK2,sP4_iProver_split(X1,sP4_iProver_split(X0,sK3))) ),
    inference(demodulation,[status(thm)],[c_54971,c_54100,c_54970])).

cnf(c_58240,plain,
    ( sP4_iProver_split(X0,sP4_iProver_split(sK2,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(X1,sK3)))) = sP4_iProver_split(X1,sP4_iProver_split(X0,sP4_iProver_split(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_58239,c_54974])).

cnf(c_60827,plain,
    ( sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK5,sP4_iProver_split(sK2,sK3)))),sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_58240,c_60822])).

cnf(c_3408,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,sK2),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_2936])).

cnf(c_56120,plain,
    ( sP4_iProver_split(k1_xboole_0,sP4_iProver_split(k2_xboole_0(sK5,sK2),k2_xboole_0(sK3,sK2))) = sP4_iProver_split(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,sK2)) ),
    inference(superposition,[status(thm)],[c_3408,c_56078])).

cnf(c_56350,plain,
    ( sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(sK5,k2_xboole_0(sK3,sK2))) = sP4_iProver_split(k2_xboole_0(sK3,sK2),sK5) ),
    inference(light_normalisation,[status(thm)],[c_56120,c_34016,c_49910])).

cnf(c_56351,plain,
    ( sP4_iProver_split(sK5,sP4_iProver_split(sK2,sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(sK5,sK2)) ),
    inference(demodulation,[status(thm)],[c_56350,c_53685,c_53848,c_54100])).

cnf(c_60860,plain,
    ( sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK3,sP4_iProver_split(sK5,sK2)))),sK4) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_60827,c_56351])).

cnf(c_56508,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(X1,sP4_iProver_split(X0,X2))) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_56078,c_56497])).

cnf(c_60861,plain,
    ( sP4_iProver_split(sP1_iProver_split,sK4) = sK4 ),
    inference(demodulation,[status(thm)],[c_60860,c_56508])).

cnf(c_74349,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(k2_xboole_0(sK3,sK2),X0))) = sP1_iProver_split ),
    inference(superposition,[status(thm)],[c_34235,c_74313])).

cnf(c_75555,plain,
    ( k4_xboole_0(sP4_iProver_split(sK3,sK2),sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(sP4_iProver_split(sK3,sK2),X0))) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_74349,c_59877])).

cnf(c_75556,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sP4_iProver_split(sK3,sK2),X0)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_75555,c_53848,c_56508,c_61315])).

cnf(c_75557,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X0)) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_75556,c_61315])).

cnf(c_67345,plain,
    ( k4_xboole_0(sK4,sP4_iProver_split(sK5,sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,k4_xboole_0(X1,sP4_iProver_split(X2,k4_xboole_0(X1,sK5)))))))) = k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(sK5,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)))) ),
    inference(superposition,[status(thm)],[c_67318,c_57991])).

cnf(c_67361,plain,
    ( k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(sK5,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)))) = k4_xboole_0(sK4,sP4_iProver_split(sK5,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)))) ),
    inference(demodulation,[status(thm)],[c_67345,c_67318])).

cnf(c_67362,plain,
    ( k4_xboole_0(sP4_iProver_split(sK3,sK2),sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split))) = k4_xboole_0(sK4,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split))) ),
    inference(light_normalisation,[status(thm)],[c_67361,c_59354,c_65852])).

cnf(c_67363,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split))) = k4_xboole_0(sK4,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split))) ),
    inference(demodulation,[status(thm)],[c_67362,c_61315])).

cnf(c_40485,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK5),X1)),k4_xboole_0(X2,k2_xboole_0(sK3,sK2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK5),X1)) ),
    inference(superposition,[status(thm)],[c_39565,c_6382])).

cnf(c_71439,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK5),X1)),k4_xboole_0(X2,sP4_iProver_split(sK3,sK2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK5),X1)) ),
    inference(light_normalisation,[status(thm)],[c_40485,c_40485,c_59877])).

cnf(c_71440,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sP4_iProver_split(X1,k4_xboole_0(X0,sK5)),k4_xboole_0(X2,sP4_iProver_split(sP5_iProver_split,sK3)))) = k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X0,sK5))) ),
    inference(demodulation,[status(thm)],[c_71439,c_9,c_52508,c_53685,c_61315])).

cnf(c_71441,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X1,sP4_iProver_split(sP5_iProver_split,sK3)),sP4_iProver_split(X2,k4_xboole_0(X0,sK5)))) = k4_xboole_0(X0,sP4_iProver_split(X2,k4_xboole_0(X0,sK5))) ),
    inference(demodulation,[status(thm)],[c_71440,c_53685])).

cnf(c_72719,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,k4_xboole_0(X0,sK5)),X1),k4_xboole_0(X0,sK5))) = k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X2,sP4_iProver_split(sP5_iProver_split,sK3)),sP4_iProver_split(X0,X1))) ),
    inference(superposition,[status(thm)],[c_72427,c_71441])).

cnf(c_72727,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X1,sP4_iProver_split(sP5_iProver_split,sK3)),sP4_iProver_split(X0,X2))) = k4_xboole_0(X0,sP4_iProver_split(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_72719,c_72427])).

cnf(c_72728,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(X0,X1)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_72727,c_56508])).

cnf(c_75558,plain,
    ( k4_xboole_0(sK4,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split))) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_75557,c_54100,c_67363,c_72728])).

cnf(c_75559,plain,
    ( k4_xboole_0(sK4,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))) = sP1_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_75558,c_67465])).

cnf(c_105159,plain,
    ( sP4_iProver_split(k2_xboole_0(sK3,sK2),sP4_iProver_split(X0,k2_xboole_0(sK2,sK4))) = sP4_iProver_split(sP4_iProver_split(X0,k1_xboole_0),k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_3349,c_105094])).

cnf(c_105767,plain,
    ( sP4_iProver_split(sP4_iProver_split(sK3,sK2),sP4_iProver_split(X0,k2_xboole_0(sP5_iProver_split,sK4))) = sP4_iProver_split(sP4_iProver_split(X0,sP1_iProver_split),sP4_iProver_split(sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_105159,c_34016,c_59877,c_65380])).

cnf(c_105768,plain,
    ( sP4_iProver_split(sK3,sP4_iProver_split(sP4_iProver_split(X0,sP4_iProver_split(sK4,sP5_iProver_split)),sP5_iProver_split)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)) ),
    inference(demodulation,[status(thm)],[c_105767,c_53685,c_54100,c_61315,c_65380,c_82862])).

cnf(c_43412,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),X0),sK3)) = k2_xboole_0(sK2,sP1_iProver_split) ),
    inference(superposition,[status(thm)],[c_43342,c_617])).

cnf(c_43437,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),X0),sK3)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_43412,c_35025])).

cnf(c_43438,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK4,k2_xboole_0(X0,sK3))) = sK2 ),
    inference(demodulation,[status(thm)],[c_43437,c_9,c_14990])).

cnf(c_43510,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(X1,sK3)))) = sK2 ),
    inference(superposition,[status(thm)],[c_11,c_43438])).

cnf(c_69736,plain,
    ( k2_xboole_0(sP5_iProver_split,k4_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(X1,sK3)))) = sP5_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_43510,c_43510,c_65380])).

cnf(c_69737,plain,
    ( sP4_iProver_split(k4_xboole_0(sK4,sP4_iProver_split(k2_xboole_0(X0,sK3),X1)),sP5_iProver_split) = sP5_iProver_split ),
    inference(demodulation,[status(thm)],[c_69736,c_53685])).

cnf(c_69738,plain,
    ( sP4_iProver_split(k4_xboole_0(sK4,sP4_iProver_split(X0,sP4_iProver_split(X1,sK3))),sP5_iProver_split) = sP5_iProver_split ),
    inference(demodulation,[status(thm)],[c_69737,c_53685,c_54100])).

cnf(c_74660,plain,
    ( sP4_iProver_split(sK4,sP5_iProver_split) = sP4_iProver_split(sP5_iProver_split,sK4) ),
    inference(superposition,[status(thm)],[c_69738,c_56206])).

cnf(c_105769,plain,
    ( sP4_iProver_split(sK3,sP4_iProver_split(sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK4)),sP5_iProver_split)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_105768,c_74660])).

cnf(c_105770,plain,
    ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK4),sP4_iProver_split(X0,sK3))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)) ),
    inference(demodulation,[status(thm)],[c_105769,c_54100,c_67465,c_79097])).

cnf(c_105771,plain,
    ( sP4_iProver_split(sK4,sP4_iProver_split(sP4_iProver_split(X0,sK3),sP5_iProver_split)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)) ),
    inference(demodulation,[status(thm)],[c_105770,c_53989,c_54100])).

cnf(c_105772,plain,
    ( sP4_iProver_split(sK4,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_105771,c_71205])).

cnf(c_120937,plain,
    ( k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)),sK4))) = k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)),sK4) ),
    inference(light_normalisation,[status(thm)],[c_120921,c_60861,c_75559,c_105772])).

cnf(c_127106,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3)),sP4_iProver_split(sK4,k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))))) = k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)),sK4) ),
    inference(light_normalisation,[status(thm)],[c_127105,c_79084,c_113776,c_120937])).

cnf(c_120108,plain,
    ( sP4_iProver_split(sK4,sP1_iProver_split) = sK4 ),
    inference(superposition,[status(thm)],[c_118730,c_35017])).

cnf(c_8589,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK5,sK4)))) = k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,sK4)) ),
    inference(superposition,[status(thm)],[c_1943,c_4236])).

cnf(c_8623,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK5,sK4)))) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_8589,c_3765])).

cnf(c_73231,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK4),sK4) = k4_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_8623,c_49082])).

cnf(c_124054,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK5),sK4),sK4) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK4) ),
    inference(superposition,[status(thm)],[c_2999,c_73231])).

cnf(c_124238,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK4) = k4_xboole_0(k2_xboole_0(X0,sK5),sK4) ),
    inference(demodulation,[status(thm)],[c_124054,c_73231])).

cnf(c_3005,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK4) = k4_xboole_0(k2_xboole_0(sK5,X0),sK4) ),
    inference(superposition,[status(thm)],[c_1237,c_509])).

cnf(c_115838,plain,
    ( sP4_iProver_split(k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),k4_xboole_0(sK3,sK5)),X0) = k2_xboole_0(X0,sK5) ),
    inference(superposition,[status(thm)],[c_110644,c_114564])).

cnf(c_116293,plain,
    ( sP4_iProver_split(sK5,X0) = k2_xboole_0(X0,sK5) ),
    inference(light_normalisation,[status(thm)],[c_115838,c_110644])).

cnf(c_124239,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sP4_iProver_split(sK3,sK2)),sK4) = k4_xboole_0(sP4_iProver_split(sK5,X0),sK4) ),
    inference(light_normalisation,[status(thm)],[c_124238,c_3005,c_59877,c_116293])).

cnf(c_124240,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(sK3,sK2)),sK4) = k4_xboole_0(sP4_iProver_split(sK5,X0),sK4) ),
    inference(demodulation,[status(thm)],[c_124239,c_117418])).

cnf(c_124241,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3)),sK4) = k4_xboole_0(sP4_iProver_split(sK5,X0),sK4) ),
    inference(light_normalisation,[status(thm)],[c_124240,c_61315])).

cnf(c_127107,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)),sK4) = k4_xboole_0(sP4_iProver_split(sK5,X0),sK4) ),
    inference(demodulation,[status(thm)],[c_127106,c_75599,c_120108,c_124241])).

cnf(c_153927,plain,
    ( k4_xboole_0(sP4_iProver_split(sK5,k4_xboole_0(sK3,sK4)),sK4) = sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_153888,c_81806,c_127107])).

cnf(c_21180,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),sK5),sK4) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK4) ),
    inference(superposition,[status(thm)],[c_1745,c_2999])).

cnf(c_21207,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),sK5),sK4) = k4_xboole_0(sK5,sK4) ),
    inference(light_normalisation,[status(thm)],[c_21180,c_1279])).

cnf(c_117020,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_115896,c_519])).

cnf(c_109627,plain,
    ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(k4_xboole_0(X0,X1),X2)) = sP4_iProver_split(X2,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3129,c_56206])).

cnf(c_118614,plain,
    ( sP4_iProver_split(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),X0) ),
    inference(light_normalisation,[status(thm)],[c_117020,c_109627,c_114564])).

cnf(c_145827,plain,
    ( k4_xboole_0(sP4_iProver_split(sK5,k4_xboole_0(sK3,X0)),sK4) = k4_xboole_0(sK5,sK4) ),
    inference(demodulation,[status(thm)],[c_21207,c_118614])).

cnf(c_153928,plain,
    ( sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK5,sK4) ),
    inference(demodulation,[status(thm)],[c_153927,c_145827])).

cnf(c_154415,plain,
    ( k2_xboole_0(sK4,k4_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(k4_xboole_0(sK5,sK4),sK3))) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_153873,c_153928])).

cnf(c_6435,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X0)),X3)) = k4_xboole_0(X0,X3) ),
    inference(superposition,[status(thm)],[c_3133,c_9])).

cnf(c_129406,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X2,k2_xboole_0(X3,X0)))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_6435,c_118614])).

cnf(c_129407,plain,
    ( k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X2,sP4_iProver_split(X3,X0)))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_129406,c_117418])).

cnf(c_129451,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,sK4),sP4_iProver_split(X0,sK4)) = k4_xboole_0(k4_xboole_0(sK5,sK4),X0) ),
    inference(superposition,[status(thm)],[c_62059,c_129407])).

cnf(c_74725,plain,
    ( sP4_iProver_split(sK4,sP4_iProver_split(sK4,X0)) = sP4_iProver_split(X0,sK4) ),
    inference(superposition,[status(thm)],[c_8623,c_56206])).

cnf(c_4349,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,sK4),k2_xboole_0(sK4,X0)) = k4_xboole_0(k4_xboole_0(sK5,sK4),X0) ),
    inference(superposition,[status(thm)],[c_4240,c_9])).

cnf(c_4361,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,sK4),k2_xboole_0(sK4,X0)) = k4_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
    inference(demodulation,[status(thm)],[c_4349,c_9])).

cnf(c_121190,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,sK4),sP4_iProver_split(sK4,X0)) = k4_xboole_0(sK5,sP4_iProver_split(sK4,X0)) ),
    inference(light_normalisation,[status(thm)],[c_4361,c_4361,c_118730])).

cnf(c_124932,plain,
    ( k4_xboole_0(sK5,sP4_iProver_split(sK4,sP4_iProver_split(sK4,X0))) = k4_xboole_0(k4_xboole_0(sK5,sK4),sP4_iProver_split(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_74725,c_121190])).

cnf(c_124982,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,sK4),sP4_iProver_split(X0,sK4)) = k4_xboole_0(sK5,sP4_iProver_split(X0,sK4)) ),
    inference(demodulation,[status(thm)],[c_124932,c_74725])).

cnf(c_129768,plain,
    ( k4_xboole_0(sK5,sP4_iProver_split(X0,sK4)) = k4_xboole_0(k4_xboole_0(sK5,sK4),X0) ),
    inference(light_normalisation,[status(thm)],[c_129451,c_124982])).

cnf(c_154416,plain,
    ( sP4_iProver_split(sK4,k4_xboole_0(sK5,sP4_iProver_split(k4_xboole_0(k4_xboole_0(sK5,sK4),sK3),sK4))) = sK3 ),
    inference(demodulation,[status(thm)],[c_154415,c_118730,c_129768])).

cnf(c_148706,plain,
    ( sP4_iProver_split(sK4,k4_xboole_0(sK5,sP4_iProver_split(sK4,X0))) = sP4_iProver_split(sK4,k4_xboole_0(k4_xboole_0(sK5,sK4),X0)) ),
    inference(superposition,[status(thm)],[c_121190,c_148655])).

cnf(c_149092,plain,
    ( sP4_iProver_split(sK4,k4_xboole_0(k4_xboole_0(sK5,sK4),X0)) = sP4_iProver_split(sK4,k4_xboole_0(sK5,X0)) ),
    inference(demodulation,[status(thm)],[c_148706,c_148655])).

cnf(c_149093,plain,
    ( sP4_iProver_split(sK4,k4_xboole_0(sK5,sP4_iProver_split(X0,sK4))) = sP4_iProver_split(sK4,k4_xboole_0(sK5,X0)) ),
    inference(light_normalisation,[status(thm)],[c_149092,c_129768])).

cnf(c_154417,plain,
    ( sP4_iProver_split(sK4,k4_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK5,sK4),sK3))) = sK3 ),
    inference(demodulation,[status(thm)],[c_154416,c_120099,c_148655,c_149093])).

cnf(c_127453,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = sP4_iProver_split(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_6242,c_6242,c_114564])).

cnf(c_127454,plain,
    ( sP4_iProver_split(X0,k4_xboole_0(X1,sP4_iProver_split(X2,X0))) = sP4_iProver_split(k4_xboole_0(X1,X2),X0) ),
    inference(demodulation,[status(thm)],[c_127453,c_6242,c_117418,c_118614])).

cnf(c_148765,plain,
    ( sP4_iProver_split(X0,k4_xboole_0(X1,k4_xboole_0(X2,sP4_iProver_split(X3,X0)))) = sP4_iProver_split(X0,k4_xboole_0(X1,sP4_iProver_split(k4_xboole_0(X2,X3),X0))) ),
    inference(superposition,[status(thm)],[c_127454,c_148655])).

cnf(c_148994,plain,
    ( sP4_iProver_split(X0,k4_xboole_0(X1,k4_xboole_0(X2,sP4_iProver_split(X3,X0)))) = sP4_iProver_split(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X0) ),
    inference(demodulation,[status(thm)],[c_148765,c_127454])).

cnf(c_154418,plain,
    ( sP4_iProver_split(k4_xboole_0(sK5,k4_xboole_0(sK5,sK3)),sK4) = sK3 ),
    inference(demodulation,[status(thm)],[c_154417,c_129768,c_148994])).

cnf(c_110841,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sK3) = k4_xboole_0(sK5,sK3) ),
    inference(superposition,[status(thm)],[c_110644,c_49082])).

cnf(c_77583,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sK3) = k4_xboole_0(sP5_iProver_split,sK3) ),
    inference(superposition,[status(thm)],[c_77129,c_509])).

cnf(c_110847,plain,
    ( k4_xboole_0(sP5_iProver_split,sK3) = k4_xboole_0(sK5,sK3) ),
    inference(light_normalisation,[status(thm)],[c_110841,c_77583])).

cnf(c_10722,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))),X2) ),
    inference(superposition,[status(thm)],[c_8,c_605])).

cnf(c_10961,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_10722,c_9,c_3133])).

cnf(c_132189,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
    inference(light_normalisation,[status(thm)],[c_10961,c_10961,c_117418])).

cnf(c_132190,plain,
    ( k4_xboole_0(sP4_iProver_split(X0,X1),sP4_iProver_split(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_132189,c_118614])).

cnf(c_16961,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k4_xboole_0(sK4,sK5))) = k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK3,sK2),X0))) ),
    inference(superposition,[status(thm)],[c_512,c_16936])).

cnf(c_61352,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sP4_iProver_split(sK3,sK2),X0))) = k4_xboole_0(sP4_iProver_split(sK3,sK2),k2_xboole_0(X0,k4_xboole_0(sK4,sK5))) ),
    inference(light_normalisation,[status(thm)],[c_16961,c_16961,c_59877])).

cnf(c_61353,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(k4_xboole_0(sK4,sK5),X0)) = k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),X0))) ),
    inference(demodulation,[status(thm)],[c_61352,c_53685,c_61315])).

cnf(c_132484,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),k4_xboole_0(sP5_iProver_split,sK3)))) = k4_xboole_0(sK3,k4_xboole_0(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_132190,c_61353])).

cnf(c_14,negated_conjecture,
    ( r1_xboole_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_95,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK5 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_14])).

cnf(c_96,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) ),
    inference(unflattening,[status(thm)],[c_95])).

cnf(c_236,plain,
    ( r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_96])).

cnf(c_582,plain,
    ( r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1,c_236])).

cnf(c_15263,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_238,c_582])).

cnf(c_77582,plain,
    ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),k4_xboole_0(sP5_iProver_split,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_77129,c_3755])).

cnf(c_132505,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sP5_iProver_split,sK3)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_132484,c_15263,c_77582,c_110077,c_110847])).

cnf(c_132506,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sP5_iProver_split,sK3)) = sP1_iProver_split ),
    inference(demodulation,[status(thm)],[c_132505,c_34016])).

cnf(c_154419,plain,
    ( sK4 = sK3 ),
    inference(light_normalisation,[status(thm)],[c_154418,c_60861,c_110847,c_132506])).

cnf(c_156,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_249,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_156])).

cnf(c_250,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_155,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_163,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_155])).

cnf(c_13,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_154419,c_250,c_163,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:41:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 55.01/7.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.01/7.50  
% 55.01/7.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.01/7.50  
% 55.01/7.50  ------  iProver source info
% 55.01/7.50  
% 55.01/7.50  git: date: 2020-06-30 10:37:57 +0100
% 55.01/7.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.01/7.50  git: non_committed_changes: false
% 55.01/7.50  git: last_make_outside_of_git: false
% 55.01/7.50  
% 55.01/7.50  ------ 
% 55.01/7.50  
% 55.01/7.50  ------ Input Options
% 55.01/7.50  
% 55.01/7.50  --out_options                           all
% 55.01/7.50  --tptp_safe_out                         true
% 55.01/7.50  --problem_path                          ""
% 55.01/7.50  --include_path                          ""
% 55.01/7.50  --clausifier                            res/vclausify_rel
% 55.01/7.50  --clausifier_options                    ""
% 55.01/7.50  --stdin                                 false
% 55.01/7.50  --stats_out                             all
% 55.01/7.50  
% 55.01/7.50  ------ General Options
% 55.01/7.50  
% 55.01/7.50  --fof                                   false
% 55.01/7.50  --time_out_real                         305.
% 55.01/7.50  --time_out_virtual                      -1.
% 55.01/7.50  --symbol_type_check                     false
% 55.01/7.50  --clausify_out                          false
% 55.01/7.50  --sig_cnt_out                           false
% 55.01/7.50  --trig_cnt_out                          false
% 55.01/7.50  --trig_cnt_out_tolerance                1.
% 55.01/7.50  --trig_cnt_out_sk_spl                   false
% 55.01/7.50  --abstr_cl_out                          false
% 55.01/7.50  
% 55.01/7.50  ------ Global Options
% 55.01/7.50  
% 55.01/7.50  --schedule                              default
% 55.01/7.50  --add_important_lit                     false
% 55.01/7.50  --prop_solver_per_cl                    1000
% 55.01/7.50  --min_unsat_core                        false
% 55.01/7.50  --soft_assumptions                      false
% 55.01/7.50  --soft_lemma_size                       3
% 55.01/7.50  --prop_impl_unit_size                   0
% 55.01/7.50  --prop_impl_unit                        []
% 55.01/7.50  --share_sel_clauses                     true
% 55.01/7.50  --reset_solvers                         false
% 55.01/7.50  --bc_imp_inh                            [conj_cone]
% 55.01/7.50  --conj_cone_tolerance                   3.
% 55.01/7.50  --extra_neg_conj                        none
% 55.01/7.50  --large_theory_mode                     true
% 55.01/7.50  --prolific_symb_bound                   200
% 55.01/7.50  --lt_threshold                          2000
% 55.01/7.50  --clause_weak_htbl                      true
% 55.01/7.50  --gc_record_bc_elim                     false
% 55.01/7.50  
% 55.01/7.50  ------ Preprocessing Options
% 55.01/7.50  
% 55.01/7.50  --preprocessing_flag                    true
% 55.01/7.50  --time_out_prep_mult                    0.1
% 55.01/7.50  --splitting_mode                        input
% 55.01/7.50  --splitting_grd                         true
% 55.01/7.50  --splitting_cvd                         false
% 55.01/7.50  --splitting_cvd_svl                     false
% 55.01/7.50  --splitting_nvd                         32
% 55.01/7.50  --sub_typing                            true
% 55.01/7.50  --prep_gs_sim                           true
% 55.01/7.50  --prep_unflatten                        true
% 55.01/7.50  --prep_res_sim                          true
% 55.01/7.50  --prep_upred                            true
% 55.01/7.50  --prep_sem_filter                       exhaustive
% 55.01/7.50  --prep_sem_filter_out                   false
% 55.01/7.50  --pred_elim                             true
% 55.01/7.50  --res_sim_input                         true
% 55.01/7.50  --eq_ax_congr_red                       true
% 55.01/7.50  --pure_diseq_elim                       true
% 55.01/7.50  --brand_transform                       false
% 55.01/7.50  --non_eq_to_eq                          false
% 55.01/7.50  --prep_def_merge                        true
% 55.01/7.50  --prep_def_merge_prop_impl              false
% 55.01/7.50  --prep_def_merge_mbd                    true
% 55.01/7.50  --prep_def_merge_tr_red                 false
% 55.01/7.50  --prep_def_merge_tr_cl                  false
% 55.01/7.50  --smt_preprocessing                     true
% 55.01/7.50  --smt_ac_axioms                         fast
% 55.01/7.50  --preprocessed_out                      false
% 55.01/7.50  --preprocessed_stats                    false
% 55.01/7.50  
% 55.01/7.50  ------ Abstraction refinement Options
% 55.01/7.50  
% 55.01/7.50  --abstr_ref                             []
% 55.01/7.50  --abstr_ref_prep                        false
% 55.01/7.50  --abstr_ref_until_sat                   false
% 55.01/7.50  --abstr_ref_sig_restrict                funpre
% 55.01/7.50  --abstr_ref_af_restrict_to_split_sk     false
% 55.01/7.50  --abstr_ref_under                       []
% 55.01/7.50  
% 55.01/7.50  ------ SAT Options
% 55.01/7.50  
% 55.01/7.50  --sat_mode                              false
% 55.01/7.50  --sat_fm_restart_options                ""
% 55.01/7.50  --sat_gr_def                            false
% 55.01/7.50  --sat_epr_types                         true
% 55.01/7.50  --sat_non_cyclic_types                  false
% 55.01/7.50  --sat_finite_models                     false
% 55.01/7.50  --sat_fm_lemmas                         false
% 55.01/7.50  --sat_fm_prep                           false
% 55.01/7.50  --sat_fm_uc_incr                        true
% 55.01/7.50  --sat_out_model                         small
% 55.01/7.50  --sat_out_clauses                       false
% 55.01/7.50  
% 55.01/7.50  ------ QBF Options
% 55.01/7.50  
% 55.01/7.50  --qbf_mode                              false
% 55.01/7.50  --qbf_elim_univ                         false
% 55.01/7.50  --qbf_dom_inst                          none
% 55.01/7.50  --qbf_dom_pre_inst                      false
% 55.01/7.50  --qbf_sk_in                             false
% 55.01/7.50  --qbf_pred_elim                         true
% 55.01/7.50  --qbf_split                             512
% 55.01/7.50  
% 55.01/7.50  ------ BMC1 Options
% 55.01/7.50  
% 55.01/7.50  --bmc1_incremental                      false
% 55.01/7.50  --bmc1_axioms                           reachable_all
% 55.01/7.50  --bmc1_min_bound                        0
% 55.01/7.50  --bmc1_max_bound                        -1
% 55.01/7.50  --bmc1_max_bound_default                -1
% 55.01/7.50  --bmc1_symbol_reachability              true
% 55.01/7.50  --bmc1_property_lemmas                  false
% 55.01/7.50  --bmc1_k_induction                      false
% 55.01/7.50  --bmc1_non_equiv_states                 false
% 55.01/7.50  --bmc1_deadlock                         false
% 55.01/7.50  --bmc1_ucm                              false
% 55.01/7.50  --bmc1_add_unsat_core                   none
% 55.01/7.50  --bmc1_unsat_core_children              false
% 55.01/7.50  --bmc1_unsat_core_extrapolate_axioms    false
% 55.01/7.50  --bmc1_out_stat                         full
% 55.01/7.50  --bmc1_ground_init                      false
% 55.01/7.50  --bmc1_pre_inst_next_state              false
% 55.01/7.50  --bmc1_pre_inst_state                   false
% 55.01/7.50  --bmc1_pre_inst_reach_state             false
% 55.01/7.50  --bmc1_out_unsat_core                   false
% 55.01/7.50  --bmc1_aig_witness_out                  false
% 55.01/7.50  --bmc1_verbose                          false
% 55.01/7.50  --bmc1_dump_clauses_tptp                false
% 55.01/7.50  --bmc1_dump_unsat_core_tptp             false
% 55.01/7.50  --bmc1_dump_file                        -
% 55.01/7.50  --bmc1_ucm_expand_uc_limit              128
% 55.01/7.50  --bmc1_ucm_n_expand_iterations          6
% 55.01/7.50  --bmc1_ucm_extend_mode                  1
% 55.01/7.50  --bmc1_ucm_init_mode                    2
% 55.01/7.50  --bmc1_ucm_cone_mode                    none
% 55.01/7.50  --bmc1_ucm_reduced_relation_type        0
% 55.01/7.50  --bmc1_ucm_relax_model                  4
% 55.01/7.50  --bmc1_ucm_full_tr_after_sat            true
% 55.01/7.50  --bmc1_ucm_expand_neg_assumptions       false
% 55.01/7.50  --bmc1_ucm_layered_model                none
% 55.01/7.50  --bmc1_ucm_max_lemma_size               10
% 55.01/7.50  
% 55.01/7.50  ------ AIG Options
% 55.01/7.50  
% 55.01/7.50  --aig_mode                              false
% 55.01/7.50  
% 55.01/7.50  ------ Instantiation Options
% 55.01/7.50  
% 55.01/7.50  --instantiation_flag                    true
% 55.01/7.50  --inst_sos_flag                         true
% 55.01/7.50  --inst_sos_phase                        true
% 55.01/7.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.01/7.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.01/7.50  --inst_lit_sel_side                     num_symb
% 55.01/7.50  --inst_solver_per_active                1400
% 55.01/7.50  --inst_solver_calls_frac                1.
% 55.01/7.50  --inst_passive_queue_type               priority_queues
% 55.01/7.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.01/7.50  --inst_passive_queues_freq              [25;2]
% 55.01/7.50  --inst_dismatching                      true
% 55.01/7.50  --inst_eager_unprocessed_to_passive     true
% 55.01/7.50  --inst_prop_sim_given                   true
% 55.01/7.50  --inst_prop_sim_new                     false
% 55.01/7.50  --inst_subs_new                         false
% 55.01/7.50  --inst_eq_res_simp                      false
% 55.01/7.50  --inst_subs_given                       false
% 55.01/7.50  --inst_orphan_elimination               true
% 55.01/7.50  --inst_learning_loop_flag               true
% 55.01/7.50  --inst_learning_start                   3000
% 55.01/7.50  --inst_learning_factor                  2
% 55.01/7.50  --inst_start_prop_sim_after_learn       3
% 55.01/7.50  --inst_sel_renew                        solver
% 55.01/7.50  --inst_lit_activity_flag                true
% 55.01/7.50  --inst_restr_to_given                   false
% 55.01/7.50  --inst_activity_threshold               500
% 55.01/7.50  --inst_out_proof                        true
% 55.01/7.50  
% 55.01/7.50  ------ Resolution Options
% 55.01/7.50  
% 55.01/7.50  --resolution_flag                       true
% 55.01/7.50  --res_lit_sel                           adaptive
% 55.01/7.50  --res_lit_sel_side                      none
% 55.01/7.50  --res_ordering                          kbo
% 55.01/7.50  --res_to_prop_solver                    active
% 55.01/7.50  --res_prop_simpl_new                    false
% 55.01/7.50  --res_prop_simpl_given                  true
% 55.01/7.50  --res_passive_queue_type                priority_queues
% 55.01/7.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.01/7.50  --res_passive_queues_freq               [15;5]
% 55.01/7.50  --res_forward_subs                      full
% 55.01/7.50  --res_backward_subs                     full
% 55.01/7.50  --res_forward_subs_resolution           true
% 55.01/7.50  --res_backward_subs_resolution          true
% 55.01/7.50  --res_orphan_elimination                true
% 55.01/7.50  --res_time_limit                        2.
% 55.01/7.50  --res_out_proof                         true
% 55.01/7.50  
% 55.01/7.50  ------ Superposition Options
% 55.01/7.50  
% 55.01/7.50  --superposition_flag                    true
% 55.01/7.50  --sup_passive_queue_type                priority_queues
% 55.01/7.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.01/7.50  --sup_passive_queues_freq               [8;1;4]
% 55.01/7.50  --demod_completeness_check              fast
% 55.01/7.50  --demod_use_ground                      true
% 55.01/7.50  --sup_to_prop_solver                    passive
% 55.01/7.50  --sup_prop_simpl_new                    true
% 55.01/7.50  --sup_prop_simpl_given                  true
% 55.01/7.50  --sup_fun_splitting                     true
% 55.01/7.50  --sup_smt_interval                      50000
% 55.01/7.50  
% 55.01/7.50  ------ Superposition Simplification Setup
% 55.01/7.50  
% 55.01/7.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.01/7.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.01/7.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.01/7.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.01/7.50  --sup_full_triv                         [TrivRules;PropSubs]
% 55.01/7.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.01/7.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.01/7.50  --sup_immed_triv                        [TrivRules]
% 55.01/7.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.01/7.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.01/7.50  --sup_immed_bw_main                     []
% 55.01/7.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.01/7.50  --sup_input_triv                        [Unflattening;TrivRules]
% 55.01/7.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.01/7.50  --sup_input_bw                          []
% 55.01/7.50  
% 55.01/7.50  ------ Combination Options
% 55.01/7.50  
% 55.01/7.50  --comb_res_mult                         3
% 55.01/7.50  --comb_sup_mult                         2
% 55.01/7.50  --comb_inst_mult                        10
% 55.01/7.50  
% 55.01/7.50  ------ Debug Options
% 55.01/7.50  
% 55.01/7.50  --dbg_backtrace                         false
% 55.01/7.50  --dbg_dump_prop_clauses                 false
% 55.01/7.50  --dbg_dump_prop_clauses_file            -
% 55.01/7.50  --dbg_out_stat                          false
% 55.01/7.50  ------ Parsing...
% 55.01/7.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.01/7.50  
% 55.01/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 55.01/7.50  
% 55.01/7.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.01/7.50  
% 55.01/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.01/7.50  ------ Proving...
% 55.01/7.50  ------ Problem Properties 
% 55.01/7.50  
% 55.01/7.50  
% 55.01/7.50  clauses                                 16
% 55.01/7.50  conjectures                             2
% 55.01/7.50  EPR                                     1
% 55.01/7.50  Horn                                    15
% 55.01/7.50  unary                                   14
% 55.01/7.50  binary                                  2
% 55.01/7.50  lits                                    18
% 55.01/7.50  lits eq                                 13
% 55.01/7.50  fd_pure                                 0
% 55.01/7.50  fd_pseudo                               0
% 55.01/7.50  fd_cond                                 1
% 55.01/7.50  fd_pseudo_cond                          0
% 55.01/7.50  AC symbols                              1
% 55.01/7.50  
% 55.01/7.50  ------ Schedule dynamic 5 is on 
% 55.01/7.50  
% 55.01/7.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 55.01/7.50  
% 55.01/7.50  
% 55.01/7.50  ------ 
% 55.01/7.50  Current options:
% 55.01/7.50  ------ 
% 55.01/7.50  
% 55.01/7.50  ------ Input Options
% 55.01/7.50  
% 55.01/7.50  --out_options                           all
% 55.01/7.50  --tptp_safe_out                         true
% 55.01/7.50  --problem_path                          ""
% 55.01/7.50  --include_path                          ""
% 55.01/7.50  --clausifier                            res/vclausify_rel
% 55.01/7.50  --clausifier_options                    ""
% 55.01/7.50  --stdin                                 false
% 55.01/7.50  --stats_out                             all
% 55.01/7.50  
% 55.01/7.50  ------ General Options
% 55.01/7.50  
% 55.01/7.50  --fof                                   false
% 55.01/7.50  --time_out_real                         305.
% 55.01/7.50  --time_out_virtual                      -1.
% 55.01/7.50  --symbol_type_check                     false
% 55.01/7.50  --clausify_out                          false
% 55.01/7.50  --sig_cnt_out                           false
% 55.01/7.50  --trig_cnt_out                          false
% 55.01/7.50  --trig_cnt_out_tolerance                1.
% 55.01/7.50  --trig_cnt_out_sk_spl                   false
% 55.01/7.50  --abstr_cl_out                          false
% 55.01/7.50  
% 55.01/7.50  ------ Global Options
% 55.01/7.50  
% 55.01/7.50  --schedule                              default
% 55.01/7.50  --add_important_lit                     false
% 55.01/7.50  --prop_solver_per_cl                    1000
% 55.01/7.50  --min_unsat_core                        false
% 55.01/7.50  --soft_assumptions                      false
% 55.01/7.50  --soft_lemma_size                       3
% 55.01/7.50  --prop_impl_unit_size                   0
% 55.01/7.50  --prop_impl_unit                        []
% 55.01/7.50  --share_sel_clauses                     true
% 55.01/7.50  --reset_solvers                         false
% 55.01/7.50  --bc_imp_inh                            [conj_cone]
% 55.01/7.50  --conj_cone_tolerance                   3.
% 55.01/7.50  --extra_neg_conj                        none
% 55.01/7.50  --large_theory_mode                     true
% 55.01/7.50  --prolific_symb_bound                   200
% 55.01/7.50  --lt_threshold                          2000
% 55.01/7.50  --clause_weak_htbl                      true
% 55.01/7.50  --gc_record_bc_elim                     false
% 55.01/7.50  
% 55.01/7.50  ------ Preprocessing Options
% 55.01/7.50  
% 55.01/7.50  --preprocessing_flag                    true
% 55.01/7.50  --time_out_prep_mult                    0.1
% 55.01/7.50  --splitting_mode                        input
% 55.01/7.50  --splitting_grd                         true
% 55.01/7.50  --splitting_cvd                         false
% 55.01/7.50  --splitting_cvd_svl                     false
% 55.01/7.50  --splitting_nvd                         32
% 55.01/7.50  --sub_typing                            true
% 55.01/7.50  --prep_gs_sim                           true
% 55.01/7.50  --prep_unflatten                        true
% 55.01/7.50  --prep_res_sim                          true
% 55.01/7.50  --prep_upred                            true
% 55.01/7.50  --prep_sem_filter                       exhaustive
% 55.01/7.50  --prep_sem_filter_out                   false
% 55.01/7.50  --pred_elim                             true
% 55.01/7.50  --res_sim_input                         true
% 55.01/7.50  --eq_ax_congr_red                       true
% 55.01/7.50  --pure_diseq_elim                       true
% 55.01/7.50  --brand_transform                       false
% 55.01/7.50  --non_eq_to_eq                          false
% 55.01/7.50  --prep_def_merge                        true
% 55.01/7.50  --prep_def_merge_prop_impl              false
% 55.01/7.50  --prep_def_merge_mbd                    true
% 55.01/7.50  --prep_def_merge_tr_red                 false
% 55.01/7.50  --prep_def_merge_tr_cl                  false
% 55.01/7.50  --smt_preprocessing                     true
% 55.01/7.50  --smt_ac_axioms                         fast
% 55.01/7.50  --preprocessed_out                      false
% 55.01/7.50  --preprocessed_stats                    false
% 55.01/7.50  
% 55.01/7.50  ------ Abstraction refinement Options
% 55.01/7.50  
% 55.01/7.50  --abstr_ref                             []
% 55.01/7.50  --abstr_ref_prep                        false
% 55.01/7.50  --abstr_ref_until_sat                   false
% 55.01/7.50  --abstr_ref_sig_restrict                funpre
% 55.01/7.50  --abstr_ref_af_restrict_to_split_sk     false
% 55.01/7.50  --abstr_ref_under                       []
% 55.01/7.50  
% 55.01/7.50  ------ SAT Options
% 55.01/7.50  
% 55.01/7.50  --sat_mode                              false
% 55.01/7.50  --sat_fm_restart_options                ""
% 55.01/7.50  --sat_gr_def                            false
% 55.01/7.50  --sat_epr_types                         true
% 55.01/7.50  --sat_non_cyclic_types                  false
% 55.01/7.50  --sat_finite_models                     false
% 55.01/7.50  --sat_fm_lemmas                         false
% 55.01/7.50  --sat_fm_prep                           false
% 55.01/7.50  --sat_fm_uc_incr                        true
% 55.01/7.50  --sat_out_model                         small
% 55.01/7.50  --sat_out_clauses                       false
% 55.01/7.50  
% 55.01/7.50  ------ QBF Options
% 55.01/7.50  
% 55.01/7.50  --qbf_mode                              false
% 55.01/7.50  --qbf_elim_univ                         false
% 55.01/7.50  --qbf_dom_inst                          none
% 55.01/7.50  --qbf_dom_pre_inst                      false
% 55.01/7.50  --qbf_sk_in                             false
% 55.01/7.50  --qbf_pred_elim                         true
% 55.01/7.50  --qbf_split                             512
% 55.01/7.50  
% 55.01/7.50  ------ BMC1 Options
% 55.01/7.50  
% 55.01/7.50  --bmc1_incremental                      false
% 55.01/7.50  --bmc1_axioms                           reachable_all
% 55.01/7.50  --bmc1_min_bound                        0
% 55.01/7.50  --bmc1_max_bound                        -1
% 55.01/7.50  --bmc1_max_bound_default                -1
% 55.01/7.50  --bmc1_symbol_reachability              true
% 55.01/7.50  --bmc1_property_lemmas                  false
% 55.01/7.50  --bmc1_k_induction                      false
% 55.01/7.50  --bmc1_non_equiv_states                 false
% 55.01/7.50  --bmc1_deadlock                         false
% 55.01/7.50  --bmc1_ucm                              false
% 55.01/7.50  --bmc1_add_unsat_core                   none
% 55.01/7.50  --bmc1_unsat_core_children              false
% 55.01/7.50  --bmc1_unsat_core_extrapolate_axioms    false
% 55.01/7.50  --bmc1_out_stat                         full
% 55.01/7.50  --bmc1_ground_init                      false
% 55.01/7.50  --bmc1_pre_inst_next_state              false
% 55.01/7.50  --bmc1_pre_inst_state                   false
% 55.01/7.50  --bmc1_pre_inst_reach_state             false
% 55.01/7.50  --bmc1_out_unsat_core                   false
% 55.01/7.50  --bmc1_aig_witness_out                  false
% 55.01/7.50  --bmc1_verbose                          false
% 55.01/7.50  --bmc1_dump_clauses_tptp                false
% 55.01/7.50  --bmc1_dump_unsat_core_tptp             false
% 55.01/7.50  --bmc1_dump_file                        -
% 55.01/7.50  --bmc1_ucm_expand_uc_limit              128
% 55.01/7.50  --bmc1_ucm_n_expand_iterations          6
% 55.01/7.50  --bmc1_ucm_extend_mode                  1
% 55.01/7.50  --bmc1_ucm_init_mode                    2
% 55.01/7.50  --bmc1_ucm_cone_mode                    none
% 55.01/7.50  --bmc1_ucm_reduced_relation_type        0
% 55.01/7.50  --bmc1_ucm_relax_model                  4
% 55.01/7.50  --bmc1_ucm_full_tr_after_sat            true
% 55.01/7.50  --bmc1_ucm_expand_neg_assumptions       false
% 55.01/7.50  --bmc1_ucm_layered_model                none
% 55.01/7.50  --bmc1_ucm_max_lemma_size               10
% 55.01/7.50  
% 55.01/7.50  ------ AIG Options
% 55.01/7.50  
% 55.01/7.50  --aig_mode                              false
% 55.01/7.50  
% 55.01/7.50  ------ Instantiation Options
% 55.01/7.50  
% 55.01/7.50  --instantiation_flag                    true
% 55.01/7.50  --inst_sos_flag                         true
% 55.01/7.50  --inst_sos_phase                        true
% 55.01/7.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.01/7.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.01/7.50  --inst_lit_sel_side                     none
% 55.01/7.50  --inst_solver_per_active                1400
% 55.01/7.50  --inst_solver_calls_frac                1.
% 55.01/7.50  --inst_passive_queue_type               priority_queues
% 55.01/7.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.01/7.50  --inst_passive_queues_freq              [25;2]
% 55.01/7.50  --inst_dismatching                      true
% 55.01/7.50  --inst_eager_unprocessed_to_passive     true
% 55.01/7.50  --inst_prop_sim_given                   true
% 55.01/7.50  --inst_prop_sim_new                     false
% 55.01/7.50  --inst_subs_new                         false
% 55.01/7.50  --inst_eq_res_simp                      false
% 55.01/7.50  --inst_subs_given                       false
% 55.01/7.50  --inst_orphan_elimination               true
% 55.01/7.50  --inst_learning_loop_flag               true
% 55.01/7.50  --inst_learning_start                   3000
% 55.01/7.50  --inst_learning_factor                  2
% 55.01/7.50  --inst_start_prop_sim_after_learn       3
% 55.01/7.50  --inst_sel_renew                        solver
% 55.01/7.50  --inst_lit_activity_flag                true
% 55.01/7.50  --inst_restr_to_given                   false
% 55.01/7.50  --inst_activity_threshold               500
% 55.01/7.50  --inst_out_proof                        true
% 55.01/7.50  
% 55.01/7.50  ------ Resolution Options
% 55.01/7.50  
% 55.01/7.50  --resolution_flag                       false
% 55.01/7.50  --res_lit_sel                           adaptive
% 55.01/7.50  --res_lit_sel_side                      none
% 55.01/7.50  --res_ordering                          kbo
% 55.01/7.50  --res_to_prop_solver                    active
% 55.01/7.50  --res_prop_simpl_new                    false
% 55.01/7.50  --res_prop_simpl_given                  true
% 55.01/7.50  --res_passive_queue_type                priority_queues
% 55.01/7.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.01/7.50  --res_passive_queues_freq               [15;5]
% 55.01/7.50  --res_forward_subs                      full
% 55.01/7.50  --res_backward_subs                     full
% 55.01/7.50  --res_forward_subs_resolution           true
% 55.01/7.50  --res_backward_subs_resolution          true
% 55.01/7.50  --res_orphan_elimination                true
% 55.01/7.50  --res_time_limit                        2.
% 55.01/7.50  --res_out_proof                         true
% 55.01/7.50  
% 55.01/7.50  ------ Superposition Options
% 55.01/7.50  
% 55.01/7.50  --superposition_flag                    true
% 55.01/7.50  --sup_passive_queue_type                priority_queues
% 55.01/7.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.01/7.50  --sup_passive_queues_freq               [8;1;4]
% 55.01/7.50  --demod_completeness_check              fast
% 55.01/7.50  --demod_use_ground                      true
% 55.01/7.50  --sup_to_prop_solver                    passive
% 55.01/7.50  --sup_prop_simpl_new                    true
% 55.01/7.50  --sup_prop_simpl_given                  true
% 55.01/7.50  --sup_fun_splitting                     true
% 55.01/7.50  --sup_smt_interval                      50000
% 55.01/7.50  
% 55.01/7.50  ------ Superposition Simplification Setup
% 55.01/7.50  
% 55.01/7.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.01/7.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.01/7.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.01/7.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.01/7.50  --sup_full_triv                         [TrivRules;PropSubs]
% 55.01/7.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.01/7.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.01/7.50  --sup_immed_triv                        [TrivRules]
% 55.01/7.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.01/7.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.01/7.50  --sup_immed_bw_main                     []
% 55.01/7.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.01/7.50  --sup_input_triv                        [Unflattening;TrivRules]
% 55.01/7.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.01/7.50  --sup_input_bw                          []
% 55.01/7.50  
% 55.01/7.50  ------ Combination Options
% 55.01/7.50  
% 55.01/7.50  --comb_res_mult                         3
% 55.01/7.50  --comb_sup_mult                         2
% 55.01/7.50  --comb_inst_mult                        10
% 55.01/7.50  
% 55.01/7.50  ------ Debug Options
% 55.01/7.50  
% 55.01/7.50  --dbg_backtrace                         false
% 55.01/7.50  --dbg_dump_prop_clauses                 false
% 55.01/7.50  --dbg_dump_prop_clauses_file            -
% 55.01/7.50  --dbg_out_stat                          false
% 55.01/7.50  
% 55.01/7.50  
% 55.01/7.50  
% 55.01/7.50  
% 55.01/7.50  ------ Proving...
% 55.01/7.50  
% 55.01/7.50  
% 55.01/7.50  % SZS status Theorem for theBenchmark.p
% 55.01/7.50  
% 55.01/7.50  % SZS output start CNFRefutation for theBenchmark.p
% 55.01/7.50  
% 55.01/7.50  fof(f14,axiom,(
% 55.01/7.50    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 55.01/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.01/7.50  
% 55.01/7.50  fof(f42,plain,(
% 55.01/7.50    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 55.01/7.50    inference(cnf_transformation,[],[f14])).
% 55.01/7.50  
% 55.01/7.50  fof(f12,axiom,(
% 55.01/7.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 55.01/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.01/7.50  
% 55.01/7.50  fof(f40,plain,(
% 55.01/7.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 55.01/7.50    inference(cnf_transformation,[],[f12])).
% 55.01/7.50  
% 55.01/7.50  fof(f51,plain,(
% 55.01/7.50    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 55.01/7.50    inference(definition_unfolding,[],[f42,f40])).
% 55.01/7.50  
% 55.01/7.50  fof(f13,axiom,(
% 55.01/7.50    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 55.01/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.01/7.50  
% 55.01/7.50  fof(f41,plain,(
% 55.01/7.50    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 55.01/7.50    inference(cnf_transformation,[],[f13])).
% 55.01/7.50  
% 55.01/7.50  fof(f1,axiom,(
% 55.01/7.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 55.01/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.01/7.50  
% 55.01/7.50  fof(f29,plain,(
% 55.01/7.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 55.01/7.50    inference(cnf_transformation,[],[f1])).
% 55.01/7.50  
% 55.01/7.50  fof(f7,axiom,(
% 55.01/7.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 55.01/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.01/7.50  
% 55.01/7.50  fof(f35,plain,(
% 55.01/7.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 55.01/7.50    inference(cnf_transformation,[],[f7])).
% 55.01/7.50  
% 55.01/7.50  fof(f15,conjecture,(
% 55.01/7.50    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 55.01/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.01/7.50  
% 55.01/7.50  fof(f16,negated_conjecture,(
% 55.01/7.50    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 55.01/7.50    inference(negated_conjecture,[],[f15])).
% 55.01/7.50  
% 55.01/7.50  fof(f21,plain,(
% 55.01/7.50    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 55.01/7.50    inference(ennf_transformation,[],[f16])).
% 55.01/7.50  
% 55.01/7.50  fof(f22,plain,(
% 55.01/7.50    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 55.01/7.50    inference(flattening,[],[f21])).
% 55.01/7.50  
% 55.01/7.50  fof(f27,plain,(
% 55.01/7.50    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK3 != sK4 & r1_xboole_0(sK5,sK3) & r1_xboole_0(sK4,sK2) & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5))),
% 55.01/7.50    introduced(choice_axiom,[])).
% 55.01/7.50  
% 55.01/7.50  fof(f28,plain,(
% 55.01/7.50    sK3 != sK4 & r1_xboole_0(sK5,sK3) & r1_xboole_0(sK4,sK2) & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5)),
% 55.01/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f27])).
% 55.01/7.50  
% 55.01/7.50  fof(f43,plain,(
% 55.01/7.50    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5)),
% 55.01/7.50    inference(cnf_transformation,[],[f28])).
% 55.01/7.50  
% 55.01/7.50  fof(f9,axiom,(
% 55.01/7.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 55.01/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.01/7.50  
% 55.01/7.50  fof(f37,plain,(
% 55.01/7.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 55.01/7.50    inference(cnf_transformation,[],[f9])).
% 55.01/7.50  
% 55.01/7.50  fof(f2,axiom,(
% 55.01/7.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 55.01/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.01/7.50  
% 55.01/7.50  fof(f30,plain,(
% 55.01/7.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 55.01/7.50    inference(cnf_transformation,[],[f2])).
% 55.01/7.50  
% 55.01/7.50  fof(f47,plain,(
% 55.01/7.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 55.01/7.50    inference(definition_unfolding,[],[f30,f40,f40])).
% 55.01/7.50  
% 55.01/7.50  fof(f8,axiom,(
% 55.01/7.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 55.01/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.01/7.50  
% 55.01/7.50  fof(f36,plain,(
% 55.01/7.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 55.01/7.50    inference(cnf_transformation,[],[f8])).
% 55.01/7.50  
% 55.01/7.50  fof(f10,axiom,(
% 55.01/7.50    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 55.01/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.01/7.50  
% 55.01/7.50  fof(f38,plain,(
% 55.01/7.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 55.01/7.50    inference(cnf_transformation,[],[f10])).
% 55.01/7.50  
% 55.01/7.50  fof(f11,axiom,(
% 55.01/7.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 55.01/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.01/7.50  
% 55.01/7.50  fof(f39,plain,(
% 55.01/7.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 55.01/7.50    inference(cnf_transformation,[],[f11])).
% 55.01/7.50  
% 55.01/7.50  fof(f50,plain,(
% 55.01/7.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 55.01/7.50    inference(definition_unfolding,[],[f39,f40])).
% 55.01/7.50  
% 55.01/7.50  fof(f3,axiom,(
% 55.01/7.50    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 55.01/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.01/7.50  
% 55.01/7.50  fof(f17,plain,(
% 55.01/7.50    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 55.01/7.50    inference(rectify,[],[f3])).
% 55.01/7.50  
% 55.01/7.50  fof(f31,plain,(
% 55.01/7.50    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 55.01/7.50    inference(cnf_transformation,[],[f17])).
% 55.01/7.50  
% 55.01/7.50  fof(f5,axiom,(
% 55.01/7.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 55.01/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.01/7.50  
% 55.01/7.50  fof(f20,plain,(
% 55.01/7.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 55.01/7.50    inference(ennf_transformation,[],[f5])).
% 55.01/7.50  
% 55.01/7.50  fof(f25,plain,(
% 55.01/7.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 55.01/7.50    introduced(choice_axiom,[])).
% 55.01/7.50  
% 55.01/7.50  fof(f26,plain,(
% 55.01/7.50    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 55.01/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f25])).
% 55.01/7.50  
% 55.01/7.50  fof(f34,plain,(
% 55.01/7.50    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 55.01/7.50    inference(cnf_transformation,[],[f26])).
% 55.01/7.50  
% 55.01/7.50  fof(f4,axiom,(
% 55.01/7.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 55.01/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.01/7.50  
% 55.01/7.50  fof(f18,plain,(
% 55.01/7.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 55.01/7.50    inference(rectify,[],[f4])).
% 55.01/7.50  
% 55.01/7.50  fof(f19,plain,(
% 55.01/7.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 55.01/7.50    inference(ennf_transformation,[],[f18])).
% 55.01/7.50  
% 55.01/7.50  fof(f23,plain,(
% 55.01/7.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 55.01/7.50    introduced(choice_axiom,[])).
% 55.01/7.50  
% 55.01/7.50  fof(f24,plain,(
% 55.01/7.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 55.01/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f23])).
% 55.01/7.50  
% 55.01/7.50  fof(f33,plain,(
% 55.01/7.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 55.01/7.50    inference(cnf_transformation,[],[f24])).
% 55.01/7.50  
% 55.01/7.50  fof(f48,plain,(
% 55.01/7.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 55.01/7.50    inference(definition_unfolding,[],[f33,f40])).
% 55.01/7.50  
% 55.01/7.50  fof(f44,plain,(
% 55.01/7.50    r1_xboole_0(sK4,sK2)),
% 55.01/7.50    inference(cnf_transformation,[],[f28])).
% 55.01/7.50  
% 55.01/7.50  fof(f45,plain,(
% 55.01/7.50    r1_xboole_0(sK5,sK3)),
% 55.01/7.50    inference(cnf_transformation,[],[f28])).
% 55.01/7.50  
% 55.01/7.50  fof(f46,plain,(
% 55.01/7.50    sK3 != sK4),
% 55.01/7.50    inference(cnf_transformation,[],[f28])).
% 55.01/7.50  
% 55.01/7.50  cnf(c_12,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 55.01/7.50      inference(cnf_transformation,[],[f51]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_11,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 55.01/7.50      inference(cnf_transformation,[],[f41]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_0,plain,
% 55.01/7.50      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 55.01/7.50      inference(cnf_transformation,[],[f29]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_153,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 55.01/7.50      inference(theory_normalisation,[status(thm)],[c_12,c_11,c_0]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_6,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 55.01/7.50      inference(cnf_transformation,[],[f35]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_505,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_153,c_6]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_16,negated_conjecture,
% 55.01/7.50      ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ),
% 55.01/7.50      inference(cnf_transformation,[],[f43]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_152,negated_conjecture,
% 55.01/7.50      ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK4,sK5) ),
% 55.01/7.50      inference(theory_normalisation,[status(thm)],[c_16,c_11,c_0]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_243,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_11,c_0]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_961,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK4,k2_xboole_0(X0,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_152,c_243]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1249,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) = k2_xboole_0(sK4,k2_xboole_0(X0,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_961,c_243]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1758,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) = k2_xboole_0(sK4,sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_505,c_1249]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1761,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_1758,c_152]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_8,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 55.01/7.50      inference(cnf_transformation,[],[f37]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2099,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1761,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_511,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_6,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_509,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 55.01/7.50      inference(cnf_transformation,[],[f47]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3021,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_509,c_1]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_7,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 55.01/7.50      inference(cnf_transformation,[],[f36]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_517,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_8,c_7]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_518,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_517,c_7]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1070,plain,
% 55.01/7.50      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_518,c_0]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1145,plain,
% 55.01/7.50      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1070,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1757,plain,
% 55.01/7.50      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_505,c_518]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1849,plain,
% 55.01/7.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_1145,c_1757]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_9,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 55.01/7.50      inference(cnf_transformation,[],[f38]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1857,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1849,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1865,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_1857,c_1757]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3026,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_3021,c_7,c_511,c_1865]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3755,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_511,c_511,c_3026]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3765,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,sK4)) = sK4 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_152,c_3755]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_4236,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(k4_xboole_0(sK5,sK4),X0)) = k4_xboole_0(sK4,X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3765,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_42651,plain,
% 55.01/7.50      ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,sK4),sK2)) = k4_xboole_0(sK4,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_2099,c_4236]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_618,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_9,c_1]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_621,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_618,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_617,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_9,c_6]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_14690,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_0,c_617]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_16936,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_621,c_14690]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_17109,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,sK4)))) = k4_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_16936,c_4236]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_17193,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,sK4)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_17109,c_3765]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_18162,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_8,c_17193]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_10,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 55.01/7.50      inference(cnf_transformation,[],[f50]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_679,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1,c_10]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_52071,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,sK2))) = k4_xboole_0(sK4,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_18162,c_679]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1861,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1849,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1862,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_1861,c_6]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2909,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_6,c_1862]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_6029,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK5),sK4),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_961,c_2909]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_244,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_11,c_0]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1674,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_152,c_244]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_615,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(X0,X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_9,c_153]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_622,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_615,c_9,c_617]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_20476,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))),k4_xboole_0(X0,sK5)) = k4_xboole_0(X0,sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1674,c_622]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_33909,plain,
% 55.01/7.50      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK5),sK4),sK5)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK5),sK4),sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_6029,c_20476]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_33984,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(X0,sK5)) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_20476,c_1862]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1745,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_505,c_11]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_21186,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK3,X0),sK5)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1745,c_961]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1990,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK4,X0)) = k4_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1674,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_22107,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),sK5),k2_xboole_0(sK3,sK2)),k2_xboole_0(sK3,sK2)) = k4_xboole_0(sK5,k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK3,X0),sK5))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_21186,c_1990]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_22124,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),sK5),k2_xboole_0(sK3,sK2)),k2_xboole_0(sK3,sK2)) = k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_22107,c_21186]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2914,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_152,c_1862]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_22125,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),sK5),k2_xboole_0(sK3,sK2)),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_22124,c_2914]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2,plain,
% 55.01/7.50      ( k2_xboole_0(X0,X0) = X0 ),
% 55.01/7.50      inference(cnf_transformation,[],[f31]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1672,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_2,c_244]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_512,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),sK5) = k4_xboole_0(sK4,sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_152,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_709,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,X0)) = k4_xboole_0(k4_xboole_0(sK4,sK5),X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_512,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_717,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,X0)) = k4_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_709,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3019,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k2_xboole_0(X1,X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_509,c_153]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3027,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_3019,c_6,c_511]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_6250,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sK4,k2_xboole_0(sK5,X0)),k2_xboole_0(sK5,X0)) = k2_xboole_0(k2_xboole_0(sK5,X0),k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_717,c_3027]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_6336,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK5,X0),k2_xboole_0(sK3,sK2)) = k2_xboole_0(k2_xboole_0(sK5,X0),sK4) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_6250,c_3027]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_714,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK5,k4_xboole_0(sK4,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_512,c_6]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_715,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK5,sK4) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_714,c_6]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1251,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k2_xboole_0(sK5,sK5)) = k2_xboole_0(sK5,sK4) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_961,c_715]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1259,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,sK4) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_1251,c_2,c_152]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_959,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_2,c_243]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3929,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_959,c_11]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_516,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_8,c_6]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_519,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_516,c_6]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3207,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_519,c_11]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3240,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_3207,c_11]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3970,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_3929,c_3240]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_6337,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK5,X0),k2_xboole_0(sK3,sK2)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_6336,c_1259,c_3970]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_10442,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK3,sK2)) = k2_xboole_0(k2_xboole_0(sK5,X0),k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1672,c_6337]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_10525,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK3,sK2)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_10442,c_6337]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_22126,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(sK3,X0),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_22125,c_8,c_10525]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_14697,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK5,k4_xboole_0(X0,sK4)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_152,c_617]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_23958,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK3,X0),sK4)) = k2_xboole_0(sK5,k1_xboole_0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_22126,c_14697]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_23964,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k4_xboole_0(sK3,k2_xboole_0(X0,sK4))) = sK5 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_23958,c_9,c_518]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_616,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_9,c_1]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_24608,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(sK3,k2_xboole_0(X0,sK4)),k4_xboole_0(k4_xboole_0(sK3,k2_xboole_0(X0,sK4)),k4_xboole_0(X1,sK5))) = k4_xboole_0(k4_xboole_0(X1,sK5),k4_xboole_0(X1,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_23964,c_616]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3133,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_9,c_3026]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_24615,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(sK3,k2_xboole_0(X0,sK4)),k4_xboole_0(X1,sK5)) = k4_xboole_0(sK3,k2_xboole_0(X0,sK4)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_23964,c_3133]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_24626,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(sK3,k2_xboole_0(X0,sK4)),k4_xboole_0(sK3,k2_xboole_0(X0,sK4))) = k4_xboole_0(k4_xboole_0(X1,sK5),k4_xboole_0(X1,sK5)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_24608,c_24615]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_24627,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(X0,sK5)) = sP1_iProver_split ),
% 55.01/7.50      inference(splitting,
% 55.01/7.50                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 55.01/7.50                [c_24626]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34016,plain,
% 55.01/7.50      ( sP1_iProver_split = k1_xboole_0 ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_33984,c_24627]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34083,plain,
% 55.01/7.50      ( k2_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK5),sK4),sK5)) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK5),sK4),sK5) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_33909,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_21184,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK3,X0))) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1745,c_1674]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_608,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_8,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_625,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_608,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_23356,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK3,X1)))) = k4_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_21184,c_625]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_23456,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK3,sK2)) = k4_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_23356,c_21184]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34084,plain,
% 55.01/7.50      ( k2_xboole_0(sP1_iProver_split,k4_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK4,sK5))) = k4_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_34083,c_9,c_152,c_23456]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34085,plain,
% 55.01/7.50      ( k2_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k4_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_34084,c_152,c_23456]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1749,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_505,c_0]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34187,plain,
% 55.01/7.50      ( k4_xboole_0(sP1_iProver_split,k2_xboole_0(sK3,sK2)) = sP1_iProver_split ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_34085,c_1749]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_6389,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = sK4 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1259,c_3133]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34383,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,sP1_iProver_split) = sK4 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_34187,c_6389]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_52075,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_18162,c_1]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_5,plain,
% 55.01/7.50      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 55.01/7.50      inference(cnf_transformation,[],[f34]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_238,plain,
% 55.01/7.50      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 55.01/7.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3,plain,
% 55.01/7.50      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 55.01/7.50      | ~ r1_xboole_0(X1,X2) ),
% 55.01/7.50      inference(cnf_transformation,[],[f48]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_15,negated_conjecture,
% 55.01/7.50      ( r1_xboole_0(sK4,sK2) ),
% 55.01/7.50      inference(cnf_transformation,[],[f44]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_104,plain,
% 55.01/7.50      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 55.01/7.50      | sK2 != X2
% 55.01/7.50      | sK4 != X1 ),
% 55.01/7.50      inference(resolution_lifted,[status(thm)],[c_3,c_15]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_105,plain,
% 55.01/7.50      ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) ),
% 55.01/7.50      inference(unflattening,[status(thm)],[c_104]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_235,plain,
% 55.01/7.50      ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) != iProver_top ),
% 55.01/7.50      inference(predicate_to_equality,[status(thm)],[c_105]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_15262,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_238,c_235]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_52081,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,k4_xboole_0(sK3,sK2)) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_52075,c_15262,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_52854,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,sK2) = sK4 ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_52071,c_34383,c_52081]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2927,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_961,c_1862]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_33903,plain,
% 55.01/7.50      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X0,sK5),sK5)) = k4_xboole_0(k2_xboole_0(X0,sK5),sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_2927,c_20476]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34091,plain,
% 55.01/7.50      ( k2_xboole_0(sP1_iProver_split,k4_xboole_0(k2_xboole_0(X0,sK5),sK5)) = k4_xboole_0(k2_xboole_0(X0,sK5),sK5) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_33903,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34092,plain,
% 55.01/7.50      ( k2_xboole_0(sP1_iProver_split,k4_xboole_0(X0,sK5)) = k4_xboole_0(X0,sK5) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_34091,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34788,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,sK5),k2_xboole_0(k4_xboole_0(X0,sK5),X1)) = k4_xboole_0(sP1_iProver_split,k2_xboole_0(k4_xboole_0(X0,sK5),X1)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_34092,c_625]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_687,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_10,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_696,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_687,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34343,plain,
% 55.01/7.50      ( k4_xboole_0(sP1_iProver_split,k2_xboole_0(k2_xboole_0(sK3,sK2),X0)) = k4_xboole_0(sP1_iProver_split,k2_xboole_0(k4_xboole_0(sP1_iProver_split,sP1_iProver_split),X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_34187,c_696]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_597,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1,c_6]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_598,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_597,c_505]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_23157,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X0,X2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_505,c_625]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_23749,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_23157,c_9,c_1865]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_24101,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_598,c_23749]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_24299,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X0) = k1_xboole_0 ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_24101,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34369,plain,
% 55.01/7.50      ( k4_xboole_0(sP1_iProver_split,sP1_iProver_split) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_34187,c_24299]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34396,plain,
% 55.01/7.50      ( k4_xboole_0(sP1_iProver_split,sP1_iProver_split) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_34369,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34345,plain,
% 55.01/7.50      ( k4_xboole_0(sP1_iProver_split,k2_xboole_0(sP1_iProver_split,X0)) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_34187,c_23749]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34420,plain,
% 55.01/7.50      ( k4_xboole_0(sP1_iProver_split,k2_xboole_0(sP1_iProver_split,X0)) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_34345,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34421,plain,
% 55.01/7.50      ( k4_xboole_0(sP1_iProver_split,k2_xboole_0(k2_xboole_0(sK3,sK2),X0)) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_34343,c_34396,c_34420]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34422,plain,
% 55.01/7.50      ( k4_xboole_0(sP1_iProver_split,k2_xboole_0(sK2,k2_xboole_0(sK3,X0))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_34421,c_3970]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1700,plain,
% 55.01/7.50      ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK4,k2_xboole_0(X0,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_244,c_961]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1703,plain,
% 55.01/7.50      ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_1700,c_1249]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34423,plain,
% 55.01/7.50      ( k4_xboole_0(sP1_iProver_split,k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_34422,c_1703]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34360,plain,
% 55.01/7.50      ( k4_xboole_0(sP1_iProver_split,k2_xboole_0(k2_xboole_0(sK3,sK2),X0)) = k4_xboole_0(sP1_iProver_split,X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_34187,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34402,plain,
% 55.01/7.50      ( k4_xboole_0(sP1_iProver_split,k2_xboole_0(sK2,k2_xboole_0(sK3,X0))) = k4_xboole_0(sP1_iProver_split,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_34360,c_3970]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34403,plain,
% 55.01/7.50      ( k4_xboole_0(sP1_iProver_split,k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) = k4_xboole_0(sP1_iProver_split,X0) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_34402,c_1703]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34425,plain,
% 55.01/7.50      ( k4_xboole_0(sP1_iProver_split,X0) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_34423,c_34403]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34835,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,sK5),k2_xboole_0(k4_xboole_0(X0,sK5),X1)) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_34788,c_9,c_34425]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_21035,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X0,X2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_0,c_1745]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53529,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X3)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_21035,c_21035]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53683,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = sP4_iProver_split(X0,X1) ),
% 55.01/7.50      inference(splitting,
% 55.01/7.50                [splitting(split),new_symbols(definition,[sP4_iProver_split])],
% 55.01/7.50                [c_53529]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_245,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_11,c_0]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34178,plain,
% 55.01/7.50      ( k2_xboole_0(sP1_iProver_split,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1)) = k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_34085,c_245]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53599,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sP1_iProver_split,k2_xboole_0(X1,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_21035,c_34178]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34793,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(k4_xboole_0(X0,sK5),sP1_iProver_split)) = sP1_iProver_split ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_34092,c_3755]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_17153,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_16936,c_616]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34829,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(sK5,k4_xboole_0(X0,sP1_iProver_split))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_34793,c_9,c_17153]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_35092,plain,
% 55.01/7.50      ( k2_xboole_0(sP1_iProver_split,X0) = X0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_34829,c_505]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53636,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k2_xboole_0(X1,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_53599,c_3970,c_35092]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53685,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,X1) = k2_xboole_0(X1,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_53683,c_53636]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_63039,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(sK5,sP4_iProver_split(X1,k4_xboole_0(X0,sK5)))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_34835,c_9,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_63040,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(sP4_iProver_split(X1,k4_xboole_0(X0,sK5)),sK5)) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_63039,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53518,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X2,X0),X3)) = k2_xboole_0(X3,k2_xboole_0(X0,X2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_21035,c_245]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1958,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1749,c_244]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54099,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_53518,c_1958,c_3970,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54100,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,X1),X2) = sP4_iProver_split(X1,sP4_iProver_split(X2,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_54099,c_3970,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_63041,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,sK5),sP4_iProver_split(sK5,X1))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_63040,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1955,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,X2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1749,c_11]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_26518,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK4,X0),sK2)) = k2_xboole_0(sK4,sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1955,c_1249]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_26587,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK4,X0),sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_26518,c_152]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_6382,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X0)))) = X0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_11,c_3133]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_32645,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,X0),sK2),k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(sK3,sK2)))) = k2_xboole_0(k4_xboole_0(sK4,X0),sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_26587,c_6382]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_15297,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(X1,k2_xboole_0(sK5,k4_xboole_0(X0,sK4)))) = k4_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_14697,c_3133]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_58973,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(sP4_iProver_split(sK2,sK3),k4_xboole_0(X1,sP4_iProver_split(k4_xboole_0(X0,sK4),sK5)))) = k4_xboole_0(X0,sP4_iProver_split(sK2,sK3)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_15297,c_9,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_58974,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X1,sP4_iProver_split(k4_xboole_0(X0,sK4),sK5)),sP4_iProver_split(sK2,sK3))) = k4_xboole_0(X0,sP4_iProver_split(sK2,sK3)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_58973,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1044,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_152,c_11]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1329,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1044,c_11]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3229,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = k2_xboole_0(sK4,sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_519,c_1329]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3233,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_3229,c_152]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3353,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,sK4))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3233,c_243]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_7786,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),X0),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_505,c_3353]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_7838,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),X0),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_7786,c_3233]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_11611,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK2,sK4),X0))) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_7838,c_1674]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59085,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK2,sK4),sP4_iProver_split(sK2,sK3)))) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_58974,c_11611]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_12475,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_152,c_616]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_13677,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4)))) = k4_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_12475,c_3026]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_58703,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(sP4_iProver_split(sK2,sK3),k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))))) = k4_xboole_0(X0,sP4_iProver_split(sK2,sK3)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_13677,c_9,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_58704,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))),sP4_iProver_split(sK2,sK3))) = k4_xboole_0(X0,sP4_iProver_split(sK2,sK3)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_58703,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_6412,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k4_xboole_0(sK5,X0),sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1761,c_3133]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_58772,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))),sP4_iProver_split(sK2,sK3))),sK2) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),sK2),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_58704,c_6412]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_14669,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = k2_xboole_0(X0,k4_xboole_0(X2,k2_xboole_0(X1,X0))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_509,c_617]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_14981,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = k2_xboole_0(X0,k4_xboole_0(X2,X1)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_14669,c_617]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2993,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_245,c_509]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_14982,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_14981,c_2993,c_3970]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1733,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1,c_505]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2102,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK5,X1),sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1761,c_243]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_23026,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),X1),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_505,c_2102]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_23118,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),X1),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_23026,c_1761]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_35485,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),X1))) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_23118,c_1674]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_38300,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK2,X0))) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1733,c_35485]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59112,plain,
% 55.01/7.50      ( sP4_iProver_split(sK2,sK3) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_59085,c_11611,c_14982,c_38300,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59341,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))),sP4_iProver_split(sK2,sK3))),sK2) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),sK2),k4_xboole_0(X0,sP4_iProver_split(sK2,sK3))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_58772,c_59112]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_17105,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(sK3,sK2),sK5))) = k4_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK3,sK2),X0))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_16936,c_717]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1253,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(X0,sK5)) = k4_xboole_0(sK4,k2_xboole_0(X0,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_961,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_14675,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),X0)) = k2_xboole_0(sK5,k4_xboole_0(sK4,k2_xboole_0(X0,sK5))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1253,c_617]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_14973,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),X0)) = k2_xboole_0(sK5,k4_xboole_0(sK4,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_14675,c_617]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_14974,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) = k2_xboole_0(sK5,k4_xboole_0(sK4,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_14973,c_509]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_17194,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK4,sK5))) = k4_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(sK4,X0))) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_17105,c_512,c_14974]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_43985,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(sK4,sK5))),sK2),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK4,sK5))),sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_17194,c_6412]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1250,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK4,k2_xboole_0(sK5,sK5))) = k4_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(sK3,sK2))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_961,c_717]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1260,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK4,k2_xboole_0(sK5,sK5))) = k4_xboole_0(sK4,k2_xboole_0(sK5,sK4)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_1250,c_715]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_972,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK5,X1))) = k4_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(X0,X1))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_243,c_717]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1261,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) = k4_xboole_0(sK4,k2_xboole_0(sK5,sK4)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_1260,c_2,c_152,c_972]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1347,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) = k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_1261,c_1259,c_1261]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1853,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_1849,c_1347]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3226,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k2_xboole_0(sK4,sK2)) = k2_xboole_0(sK2,sK3) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_519,c_1674]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3436,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK4,sK2),k2_xboole_0(sK2,sK3)) = k2_xboole_0(k2_xboole_0(sK4,sK2),sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3226,c_519]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3213,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_519,c_244]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3452,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK4,sK2),sK5) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_3436,c_3213,c_3233]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3627,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK4,sK2),sK5) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3452,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3643,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK4,sK2),sK5) = k4_xboole_0(sK4,sK5) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_3627,c_512]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_4337,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k2_xboole_0(sK4,sK2)) = k2_xboole_0(sK5,k4_xboole_0(sK4,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3643,c_6]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3632,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k2_xboole_0(sK4,sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3452,c_0]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_4338,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k4_xboole_0(sK4,sK5)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_4337,c_3632]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_44127,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,sK2),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK4,sK5))),sK2) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_43985,c_1853,c_4338]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3147,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3026,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_28777,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X2,X0),X1)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_6,c_3147]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_29031,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_28777,c_3147]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_44128,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sK5,sK5),sK2) = sK2 ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_44127,c_1070,c_3133,c_29031]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_35069,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,sK5) = sP1_iProver_split ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1749,c_34829]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_44129,plain,
% 55.01/7.50      ( k2_xboole_0(sP1_iProver_split,sK2) = sK2 ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_44128,c_35069]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_605,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_10787,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) = X1 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_605,c_153]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_10886,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)),X1) = X1 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_10787,c_6,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_39445,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1)))) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_10886,c_1674]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_55753,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1)),sK4),sK5) = sP4_iProver_split(sK2,sK3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_39445,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_55754,plain,
% 55.01/7.50      ( sP4_iProver_split(sK4,sP4_iProver_split(sK5,k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))))) = sP4_iProver_split(sK2,sK3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_55753,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_55755,plain,
% 55.01/7.50      ( sP4_iProver_split(sK4,sP4_iProver_split(sK5,k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X0,sP4_iProver_split(sK2,sK3)))))) = sP4_iProver_split(sK2,sK3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_55754,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_24104,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_622,c_23749]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_24294,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_24104,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_24295,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X0,X2)))) = k1_xboole_0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_24294,c_3970]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_24296,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X0,X3))))) = k1_xboole_0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_24295,c_3970]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_24297,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X0)))) = k1_xboole_0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_24296,c_6]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56980,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X0)))) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_24297,c_24297,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56981,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(k2_xboole_0(X1,k2_xboole_0(X2,X0)),X3)) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_56980,c_24297,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56982,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,k2_xboole_0(X3,X0)))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_56981,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56983,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,sP4_iProver_split(X0,X3)))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_56982,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56991,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,sP4_iProver_split(X0,sP4_iProver_split(sK2,sK3))) = sP1_iProver_split ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_55755,c_56983]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59342,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3))),k4_xboole_0(X0,sP4_iProver_split(sK2,sK3))) = sK2 ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_59341,c_44129,c_53685,c_56991]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59044,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(sK5,sK4),sK5)),sP4_iProver_split(sK2,sK3))),sK2) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),sK2),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_58974,c_6412]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59216,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),sK2),k4_xboole_0(X0,sP4_iProver_split(sK2,sK3))) = k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),sK2) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_59044,c_58974,c_59112]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59217,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3))),k4_xboole_0(X0,sP4_iProver_split(sK2,sK3))) = sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_59216,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59343,plain,
% 55.01/7.50      ( sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3))) = sK2 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_59342,c_59217]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_23033,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK5,X1),sK2))),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,X1),sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1733,c_2102]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2246,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) = k2_xboole_0(sK4,sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_2,c_1329]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2281,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_2246,c_152]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2294,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK2,sK5),X0)) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_2281,c_11]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2590,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK2,sK5),X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_2281,c_245]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_5438,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK5,k2_xboole_0(sK2,X0))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_2294,c_1703,c_2590,c_3970]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_14800,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK5,k2_xboole_0(sK2,k4_xboole_0(X0,X1)))) = k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,sK2)),sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_617,c_5438]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2298,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,sK5))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_2281,c_243]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_5747,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK5,k2_xboole_0(sK2,X0))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_244,c_2298]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_6242,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(X2,k4_xboole_0(X0,X1)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_9,c_3027]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_14817,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_14800,c_5747,c_6242]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_23114,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK5,X1),sK2))),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_23033,c_1761,c_14817]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59065,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),sK2))),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_58974,c_23114]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59168,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),sK2))),sP4_iProver_split(sK2,sK3)) = sP4_iProver_split(sK2,sK3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_59065,c_59112]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59169,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sK2,sK3),k4_xboole_0(X0,k4_xboole_0(X0,sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)))))) = sP4_iProver_split(sK2,sK3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_59168,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59353,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sK2,sK3),k4_xboole_0(X0,k4_xboole_0(X0,sK2))) = sP4_iProver_split(sK2,sK3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_59343,c_59169]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53206,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1,c_21035]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_4949,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1733,c_243]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54999,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,X0))) = sP4_iProver_split(X1,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_53206,c_4949,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59354,plain,
% 55.01/7.50      ( sP4_iProver_split(sK2,sK3) = sP4_iProver_split(sK3,sK2) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_59353,c_54999]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59876,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK2,sK4),sP4_iProver_split(sK3,sK2)))) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_59085,c_59354]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59877,plain,
% 55.01/7.50      ( sP4_iProver_split(sK3,sK2) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_59876,c_11611,c_14982,c_38300,c_53685,c_59354]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_65206,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,X0),sK2),k4_xboole_0(X1,k2_xboole_0(X2,sP4_iProver_split(sK3,sK2)))) = k2_xboole_0(k4_xboole_0(sK4,X0),sK2) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_32645,c_32645,c_59877]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_65207,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK2,k4_xboole_0(sK4,X0)),k4_xboole_0(X1,sP4_iProver_split(sP4_iProver_split(sK3,sK2),X2))) = sP4_iProver_split(sK2,k4_xboole_0(sK4,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_65206,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59058,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_58974,c_1761]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59966,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),sK2)) = sP4_iProver_split(sK3,sK2) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_59058,c_59877]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59967,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK3,sK2)),sK2)) = sP4_iProver_split(sK3,sK2) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_59966,c_59354]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59968,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(sK3,sK2))),sK3) = sP4_iProver_split(sK3,sK2) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_59967,c_1761,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_58715,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,sP4_iProver_split(k4_xboole_0(sK5,k4_xboole_0(sK5,k1_xboole_0)),sP4_iProver_split(sK2,sK3))) = k4_xboole_0(sK4,sP4_iProver_split(sK2,sK3)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1849,c_58704]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_5745,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK5),X0),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_505,c_2298]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_5792,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK5),X0),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_5745,c_2281]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_9878,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK5),X0),k2_xboole_0(sK3,sK2)) = k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_5792,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3017,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_509,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3028,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_3017,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_9921,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK5),X0),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_9878,c_9,c_1862,c_3028]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_37775,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK5),X0),k2_xboole_0(sK3,sK2)) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_9921,c_9921,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_37853,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK5),X0),sK4)) = k2_xboole_0(sK5,sP1_iProver_split) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_37775,c_14697]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34144,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sP1_iProver_split,k1_xboole_0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1849,c_34085]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34234,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sP1_iProver_split,sP1_iProver_split) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_34144,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3348,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK2)) = k2_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3233,c_519]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3352,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3233,c_244]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3356,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK2,sK4),sK3) = k2_xboole_0(sK2,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_3348,c_3352]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3357,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK2,sK4),sK3) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_3356,c_2,c_1703]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_23219,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,X0)) = k4_xboole_0(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3357,c_625]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_7327,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK3,X0)) = k4_xboole_0(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3352,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1695,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X0)) = k4_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_244,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_7376,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_7327,c_1695]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_23651,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_23219,c_7376]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34235,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_34234,c_2,c_23651]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_35002,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK3,sK2),sK4)) = k2_xboole_0(sK5,sP1_iProver_split) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_34235,c_14697]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1279,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),sK4) = k4_xboole_0(sK5,sK4) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1259,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_35014,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k4_xboole_0(sK5,sK4)) = k2_xboole_0(sK5,sP1_iProver_split) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_35002,c_1279]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_35015,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,sP1_iProver_split) = sK5 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_35014,c_1749]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_37860,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK5),X0),sK4)) = sK5 ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_37853,c_35015]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_37861,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k4_xboole_0(sK2,k2_xboole_0(X0,sK4))) = sK5 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_37860,c_9,c_14982]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_39016,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK2,k2_xboole_0(X0,sK4)),sK5)) = sK5 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_37861,c_3755]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_39021,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(sK2,k2_xboole_0(X0,sK4)),sK5) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_37861,c_1862]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_39049,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(sK2,k2_xboole_0(X0,sK4)),sK5) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_39021,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_39054,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,sP1_iProver_split) = sK5 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_39016,c_39049]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_39447,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1)),sK5)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_10886,c_961]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_55934,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sK5,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1))),sK4) = sP4_iProver_split(sK2,sK3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_39447,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2939,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1761,c_1862]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_4689,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),k2_xboole_0(k2_xboole_0(sK3,sK2),X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_2939,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_4702,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(sK5,X0),k2_xboole_0(sK2,k2_xboole_0(sK3,X1))) = k1_xboole_0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_4689,c_625,c_1757,c_3970]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_4703,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2)))) = k1_xboole_0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_4702,c_9,c_1703]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53253,plain,
% 55.01/7.50      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK5)) = k2_xboole_0(sK5,X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_4703,c_21035]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_15298,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(X1,sK5)) = k2_xboole_0(X1,k2_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_14697,c_245]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_46509,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(sK5,k4_xboole_0(sK2,sK4))) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1862,c_15298]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3349,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3233,c_1862]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_15277,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK2,sK4),sK4)) = k2_xboole_0(sK5,k1_xboole_0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3349,c_14697]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_15328,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k4_xboole_0(sK2,sK4)) = sK5 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_15277,c_8,c_518]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_46655,plain,
% 55.01/7.50      ( k2_xboole_0(sP1_iProver_split,k2_xboole_0(X0,sK5)) = k2_xboole_0(X0,sK5) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_46509,c_15328,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54919,plain,
% 55.01/7.50      ( k2_xboole_0(X0,sK5) = k2_xboole_0(sK5,X0) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_53253,c_34016,c_46655]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54920,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,X0) = sP4_iProver_split(X0,sK5) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_54919,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_20583,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK5),sK4),k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK5),sK4),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_6029,c_622]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1237,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_0,c_961]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1512,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1)) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1237,c_11]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_20656,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK5),sK4),k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1))),k1_xboole_0) = k1_xboole_0 ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_20583,c_1512,c_6029]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_20657,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1)))) = k1_xboole_0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_20656,c_9,c_518]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3935,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_959,c_245]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3971,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_3970,c_3935]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_20658,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(sK5,X0),sK4))) = k1_xboole_0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_20657,c_3971]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_20659,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK5,sK4)))) = k1_xboole_0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_20658,c_3970]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_20660,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k1_xboole_0 ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_20659,c_1259]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53294,plain,
% 55.01/7.50      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,sK5))) = k2_xboole_0(k2_xboole_0(X1,sK5),X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_20660,c_21035]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54858,plain,
% 55.01/7.50      ( k2_xboole_0(sP1_iProver_split,k2_xboole_0(X0,k2_xboole_0(X1,sK5))) = k2_xboole_0(k2_xboole_0(X1,sK5),X0) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_53294,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54859,plain,
% 55.01/7.50      ( sP4_iProver_split(k2_xboole_0(X0,sK5),X1) = sP4_iProver_split(sP4_iProver_split(X1,X0),sK5) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_54858,c_3970,c_35092,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54860,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sK5,X0),X1) = sP4_iProver_split(sP4_iProver_split(X1,X0),sK5) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_54859,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54923,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(X0,X1)) = sP4_iProver_split(sP4_iProver_split(sK5,X1),X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_54920,c_54860]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_55935,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(sK4,k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))))) = sP4_iProver_split(sK2,sK3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_55934,c_53685,c_54923]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_55936,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(sK4,k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X0,sP4_iProver_split(sK2,sK3)))))) = sP4_iProver_split(sK2,sK3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_55935,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_878,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(k2_xboole_0(sK5,X0),X1)) = k4_xboole_0(k4_xboole_0(sK4,k2_xboole_0(sK5,X0)),X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_717,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_883,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(k2_xboole_0(sK5,X0),X1)) = k4_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_878,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_57989,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK2,sK3),k2_xboole_0(X0,k2_xboole_0(sK5,X1))) = k4_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(sK5,X1))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_883,c_3970,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_57990,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(k2_xboole_0(sK5,X0),X1)) = k4_xboole_0(sK4,sP4_iProver_split(k2_xboole_0(sK5,X0),X1)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_57989,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_57991,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(sK5,sP4_iProver_split(X0,X1))) = k4_xboole_0(sK4,sP4_iProver_split(sK5,sP4_iProver_split(X0,X1))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_57990,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_57995,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,sP4_iProver_split(sK5,sP4_iProver_split(sK4,k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X0,sP4_iProver_split(sK2,sK3))))))) = k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(sK2,sK3)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_55936,c_57991]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_58120,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(sK2,sK3)) = k4_xboole_0(sK4,sP4_iProver_split(sK2,sK3)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_57995,c_55936]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_39381,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)),X1) = k4_xboole_0(X1,X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_10886,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_24102,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1733,c_23749]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_10745,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1,c_605]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_24298,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)),X1) = k1_xboole_0 ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_24102,c_10745]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_39584,plain,
% 55.01/7.50      ( k4_xboole_0(X0,X0) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_39381,c_24298,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_58121,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,sP4_iProver_split(sK2,sK3)) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_58120,c_39584]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_60286,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(sK3,sK2))) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_58715,c_34016,c_35069,c_39054,c_58121,c_59354]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_21150,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(X0,X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1745,c_0]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53745,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X2,X0)) = sP4_iProver_split(X2,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_21150,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53848,plain,
% 55.01/7.50      ( sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(X0,X1)) = sP4_iProver_split(X0,X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_34829,c_53745]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_60287,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,sP4_iProver_split(sK3,sK2)) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_60286,c_53848]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_26781,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,X0),sK2),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k4_xboole_0(sK4,X0),sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_26587,c_3133]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_58759,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sK4,sP4_iProver_split(k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK4,sK4))),sP4_iProver_split(sK2,sK3))),sK2) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,sP4_iProver_split(sK2,sK3)),sK2),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_58704,c_26781]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_60195,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sK4,sP4_iProver_split(k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK4,sK4))),sP4_iProver_split(sK2,sK3))),sK2) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,sP4_iProver_split(sK2,sK3)),sK2),k4_xboole_0(X0,sP4_iProver_split(sK3,sK2))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_58759,c_59877]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_12481,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(X0,sK5))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1259,c_616]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_44690,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK5,sK5))) = k4_xboole_0(k4_xboole_0(sK5,sK5),k1_xboole_0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_2914,c_12481]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34507,plain,
% 55.01/7.50      ( k4_xboole_0(sP1_iProver_split,sP1_iProver_split) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_34369,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_44808,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,sK4) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_44690,c_34016,c_34383,c_34507,c_35069]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_60196,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sK4,sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(sK3,sK2))),sK2) = k4_xboole_0(sK2,k4_xboole_0(X0,sP4_iProver_split(sK3,sK2))) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_60195,c_35069,c_39054,c_44129,c_44808,c_58121,c_59354]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_60197,plain,
% 55.01/7.50      ( k4_xboole_0(sK2,k4_xboole_0(X0,sP4_iProver_split(sK3,sK2))) = sP4_iProver_split(sK2,k4_xboole_0(sK4,sP4_iProver_split(sK3,sK2))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_60196,c_53685,c_53848]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_60288,plain,
% 55.01/7.50      ( k4_xboole_0(sK2,k4_xboole_0(X0,sP4_iProver_split(sK3,sK2))) = sP4_iProver_split(sK2,sP1_iProver_split) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_60287,c_60197]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59031,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sK4,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(sK4,sK4),sK5)),sP4_iProver_split(sK2,sK3))),sK2) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,sP4_iProver_split(sK2,sK3)),sK2),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_58974,c_26781]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_60046,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sK4,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(sK4,sK4),sK5)),sP4_iProver_split(sK2,sK3))),sK2) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,sP4_iProver_split(sK2,sK3)),sK2),k4_xboole_0(X1,sP4_iProver_split(sK3,sK2))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_59031,c_59877]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_60047,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sK4,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(sP1_iProver_split,sK5)),sP4_iProver_split(sK3,sK2))),sK2) = k4_xboole_0(sK2,k4_xboole_0(X1,sP4_iProver_split(sK3,sK2))) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_60046,c_44129,c_44808,c_58121,c_59354]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_60048,plain,
% 55.01/7.50      ( k4_xboole_0(sK2,k4_xboole_0(X0,sP4_iProver_split(sK3,sK2))) = sP5_iProver_split ),
% 55.01/7.50      inference(splitting,
% 55.01/7.50                [splitting(split),new_symbols(definition,[sP5_iProver_split])],
% 55.01/7.50                [c_60047]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_60291,plain,
% 55.01/7.50      ( sP4_iProver_split(sK2,sP1_iProver_split) = sP5_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_60288,c_60048]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_24618,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,k2_xboole_0(X0,sK4)))) = k2_xboole_0(sK4,sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_23964,c_1329]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_24623,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,k2_xboole_0(X0,sK4)))) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_24618,c_152]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_24714,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(sK3,k2_xboole_0(X1,sK4))))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_24623,c_243]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_48448,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK3,k2_xboole_0(X0,sK4))),X1),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK3,k2_xboole_0(X0,sK4)))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_505,c_24714]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_48561,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK3,k2_xboole_0(X0,sK4))),X1),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_48448,c_24623]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_57635,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sK2,sK3),k4_xboole_0(sP4_iProver_split(k4_xboole_0(sK3,k2_xboole_0(X0,sK4)),sK2),X1)) = sP4_iProver_split(sK2,sK3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_48561,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_57636,plain,
% 55.01/7.50      ( sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(sK4,X0)),sK2),X1),sK2)) = sP4_iProver_split(sK2,sK3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_57635,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_24125,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(sK5,X0),k2_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1674,c_23749]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_24794,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(sK5,X0),k2_xboole_0(sK4,k2_xboole_0(X1,sK5))) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_961,c_24125]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2244,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(sK4,k2_xboole_0(X0,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_0,c_1329]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_24094,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k2_xboole_0(X3,X0))) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_244,c_23749]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_24882,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,X1)))) = k1_xboole_0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_24794,c_9,c_2244,c_24094]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_60699,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,X1)))) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_24882,c_24882,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_60700,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,sP4_iProver_split(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),X1)) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_60699,c_24882,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_60701,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,sP4_iProver_split(sK3,sP4_iProver_split(X0,k2_xboole_0(sK2,X1)))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_60700,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_60702,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(X1,sK2)))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_60701,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_60707,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,sP4_iProver_split(sK3,sP4_iProver_split(sK2,sK3))) = sP1_iProver_split ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_57636,c_60702]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_60801,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,sP4_iProver_split(sK3,sP4_iProver_split(sK3,sK2))) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_60707,c_59354]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53589,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_21035,c_3027]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2948,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1862,c_6]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2956,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_2948,c_518]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54012,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = sP4_iProver_split(X0,X1) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_53589,c_2956,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54013,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(X0,X1)) = sP4_iProver_split(X1,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_54012,c_2956,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59052,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_58974,c_24125]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59985,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)),k2_xboole_0(X0,sP4_iProver_split(sK3,sK2))) = k1_xboole_0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_59052,c_59877]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59986,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sK3,sK2)),k2_xboole_0(X0,sP4_iProver_split(sK3,sK2))) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_59985,c_34016,c_59354]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_35098,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK5,k4_xboole_0(X0,sP1_iProver_split)),k4_xboole_0(X0,sP1_iProver_split)) = k4_xboole_0(k2_xboole_0(sK5,k4_xboole_0(X0,sP1_iProver_split)),X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_34829,c_679]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_23268,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_598,c_625]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_23587,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_23268,c_598]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_35166,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,k4_xboole_0(X0,sP1_iProver_split)) = k4_xboole_0(sK5,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_35098,c_8,c_23587]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_37416,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(X0,sP1_iProver_split),X1)) = k4_xboole_0(k4_xboole_0(sK5,X0),X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_35166,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_37427,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,sP1_iProver_split),sK5),k4_xboole_0(sK5,k4_xboole_0(sK5,X0))) = k4_xboole_0(X0,sP1_iProver_split) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_35166,c_598]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34772,plain,
% 55.01/7.50      ( k2_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k2_xboole_0(X1,sK5))) = k4_xboole_0(k4_xboole_0(X0,X1),sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_9,c_34092]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_33912,plain,
% 55.01/7.50      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,X1),sK5)) = k4_xboole_0(k4_xboole_0(X0,X1),sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_23749,c_20476]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34078,plain,
% 55.01/7.50      ( k2_xboole_0(sP1_iProver_split,k4_xboole_0(k4_xboole_0(X0,X1),sK5)) = k4_xboole_0(k4_xboole_0(X0,X1),sK5) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_33912,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34079,plain,
% 55.01/7.50      ( k2_xboole_0(sP1_iProver_split,k4_xboole_0(X0,k2_xboole_0(X1,sK5))) = k4_xboole_0(X0,k2_xboole_0(X1,sK5)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_34078,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34854,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(X1,sK5)) = k4_xboole_0(k4_xboole_0(X0,X1),sK5) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_34772,c_34079]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_37460,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sP1_iProver_split,sK5)),k4_xboole_0(sK5,k4_xboole_0(sK5,X0))) = k4_xboole_0(X0,sP1_iProver_split) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_37427,c_34854]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_37461,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP1_iProver_split) = X0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_37460,c_598,c_35092]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_37615,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,k2_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(sK5,X0),X1) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_37416,c_37461]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59987,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,k2_xboole_0(sP4_iProver_split(sK3,sK2),sP4_iProver_split(sP4_iProver_split(sK3,sK2),X0))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_59986,c_37615,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59988,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sK3,sK2),X0),sP4_iProver_split(sK3,sK2))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_59987,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1946,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_8,c_1749]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_21440,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_0,c_1946]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56077,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = sP4_iProver_split(X0,X1) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_21440,c_21440,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56078,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X0,X1)) = sP4_iProver_split(X1,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_56077,c_21440,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56091,plain,
% 55.01/7.50      ( sP4_iProver_split(k1_xboole_0,sP4_iProver_split(X0,k2_xboole_0(X1,X0))) = sP4_iProver_split(k2_xboole_0(X1,X0),X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1862,c_56078]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56412,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,X1),X0) = sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(X1,X0)) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_56091,c_34016,c_53685,c_54013]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56413,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,X1),X0) = sP4_iProver_split(X1,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_56412,c_53848,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_59989,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,sP4_iProver_split(X0,sP4_iProver_split(sK3,sK2))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_59988,c_56413]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_60802,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,sP4_iProver_split(sK2,sK3)) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_60801,c_54013,c_59989]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_60803,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,sP4_iProver_split(sK3,sK2)) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_60802,c_59354]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_61315,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,sK3) = sP4_iProver_split(sK3,sK2) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_59968,c_59968,c_60291,c_60803]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_65208,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK2,k4_xboole_0(sK4,X0)),k4_xboole_0(X1,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X2))) = sP4_iProver_split(sK2,k4_xboole_0(sK4,X0)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_65207,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_65209,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK2,k4_xboole_0(sK4,X0)),k4_xboole_0(X1,sP4_iProver_split(sK3,sP4_iProver_split(X2,sP5_iProver_split)))) = sP4_iProver_split(sK2,k4_xboole_0(sK4,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_65208,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_65238,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK2,sP1_iProver_split),k4_xboole_0(X0,sP4_iProver_split(sK3,sP4_iProver_split(X1,sP5_iProver_split)))) = sP4_iProver_split(sK2,k4_xboole_0(sK4,sP4_iProver_split(k4_xboole_0(sK4,sK5),sP4_iProver_split(sK5,X2)))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_63041,c_65209]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_23911,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK3)),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1,c_22126]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56780,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK3)),k2_xboole_0(sK3,sK2)) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_23911,c_23911,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56781,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK3),sP4_iProver_split(sK2,sK3))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_56780,c_10745,c_23911,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56782,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(sP4_iProver_split(sK2,sK3),k4_xboole_0(X0,sK3))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_56781,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56783,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(X0,sK3),sK2))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_56782,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_32567,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(sK3,sK2)))) = k2_xboole_0(k4_xboole_0(sK5,X0),sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1761,c_6382]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_64961,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),k4_xboole_0(X1,k2_xboole_0(X2,sP4_iProver_split(sK3,sK2)))) = k2_xboole_0(k4_xboole_0(sK5,X0),sK2) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_32567,c_32567,c_59877]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_64962,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK2,k4_xboole_0(sK5,X0)),k4_xboole_0(X1,sP4_iProver_split(sP4_iProver_split(sK3,sK2),X2))) = sP4_iProver_split(sK2,k4_xboole_0(sK5,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_64961,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_64963,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK2,k4_xboole_0(sK5,X0)),k4_xboole_0(X1,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X2))) = sP4_iProver_split(sK2,k4_xboole_0(sK5,X0)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_64962,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_64964,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK2,k4_xboole_0(sK5,X0)),k4_xboole_0(X1,sP4_iProver_split(sK3,sP4_iProver_split(X2,sP5_iProver_split)))) = sP4_iProver_split(sK2,k4_xboole_0(sK5,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_64963,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_64988,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK2,sP1_iProver_split),k4_xboole_0(X0,sP4_iProver_split(sK3,sP4_iProver_split(X1,sP5_iProver_split)))) = sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK3),sK2)))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_56783,c_64964]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_65137,plain,
% 55.01/7.50      ( sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK3),sK2)))) = k4_xboole_0(sP5_iProver_split,k4_xboole_0(X0,sP4_iProver_split(sK3,sP4_iProver_split(X1,sP5_iProver_split)))) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_64988,c_60291]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53307,plain,
% 55.01/7.50      ( k2_xboole_0(sP1_iProver_split,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_34829,c_21035]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54586,plain,
% 55.01/7.50      ( k2_xboole_0(sP1_iProver_split,k2_xboole_0(X0,X1)) = sP4_iProver_split(X0,X1) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_53307,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54587,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,X1) = sP4_iProver_split(X1,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_54586,c_35092,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_37846,plain,
% 55.01/7.50      ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK5),X0),sK3)) = k2_xboole_0(sK2,sP1_iProver_split) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_37775,c_617]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34995,plain,
% 55.01/7.50      ( k2_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK3,sK2),sK3)) = k2_xboole_0(sK2,sP1_iProver_split) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_34235,c_617]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_35025,plain,
% 55.01/7.50      ( k2_xboole_0(sK2,sP1_iProver_split) = sK2 ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_34995,c_509,c_1749,c_14982]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_37870,plain,
% 55.01/7.50      ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK5),X0),sK3)) = sK2 ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_37846,c_35025]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_14666,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X0)),X2)) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_8,c_617]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_14989,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X0)),X2)) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_14666,c_617]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_14990,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_14989,c_2993]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_37871,plain,
% 55.01/7.50      ( k2_xboole_0(sK2,k4_xboole_0(sK5,k2_xboole_0(X0,sK3))) = sK2 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_37870,c_9,c_14990]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53492,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(X0,sK3)),X1),sK2) = k2_xboole_0(k4_xboole_0(sK5,k2_xboole_0(X0,sK3)),sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_37871,c_21035]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_39083,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sK5,k2_xboole_0(X0,sK3)),sK2) = k2_xboole_0(sK2,k4_xboole_0(sK5,k2_xboole_0(X0,sK3))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_37871,c_959]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_39120,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sK5,k2_xboole_0(X0,sK3)),sK2) = sK2 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_39083,c_37871]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54189,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(X0,sK3)),X1),sK2) = sK2 ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_53492,c_39120]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54190,plain,
% 55.01/7.50      ( sP4_iProver_split(sK2,k4_xboole_0(sK5,k2_xboole_0(k2_xboole_0(X0,sK3),X1))) = sK2 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_54189,c_37615,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54191,plain,
% 55.01/7.50      ( sP4_iProver_split(sK2,k4_xboole_0(sK5,k2_xboole_0(sK3,k2_xboole_0(X0,X1)))) = sK2 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_54190,c_3970]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54192,plain,
% 55.01/7.50      ( sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(k2_xboole_0(X0,X1),sK3))) = sK2 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_54191,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54193,plain,
% 55.01/7.50      ( sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(sP4_iProver_split(X0,X1),sK3))) = sK2 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_54192,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54690,plain,
% 55.01/7.50      ( sP4_iProver_split(sK2,k4_xboole_0(sK5,sP4_iProver_split(sK3,sP4_iProver_split(X0,X1)))) = sK2 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_54587,c_54193]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_65138,plain,
% 55.01/7.50      ( k4_xboole_0(sP5_iProver_split,k4_xboole_0(X0,sP4_iProver_split(sK3,sP4_iProver_split(X1,sP5_iProver_split)))) = sK2 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_65137,c_54690]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_65379,plain,
% 55.01/7.50      ( sP4_iProver_split(sK2,k4_xboole_0(sK4,sP4_iProver_split(k4_xboole_0(sK4,sK5),sP4_iProver_split(sK5,X0)))) = sK2 ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_65238,c_60291,c_65138]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_65380,plain,
% 55.01/7.50      ( sP5_iProver_split = sK2 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_65379,c_60291,c_63041]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_153845,plain,
% 55.01/7.50      ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,sK4),sP5_iProver_split)) = sK4 ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_42651,c_42651,c_52854,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_8571,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(k4_xboole_0(sK5,sK4),X0)) = k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(sK5,sK4))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_6,c_4236]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_8637,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(sK5,sK4))) = k4_xboole_0(sK4,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_8571,c_4236]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_14708,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1733,c_617]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_14920,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k2_xboole_0(X0,X1) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_14708,c_6]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3801,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_9,c_3755]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_114158,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,sP4_iProver_split(X2,X1))) = X2 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_3801,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_114474,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k4_xboole_0(sP4_iProver_split(k4_xboole_0(X1,X2),X0),X0)) = sP4_iProver_split(k4_xboole_0(X1,X2),X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_114158,c_153]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1049,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_11,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2992,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_244,c_509]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81266,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(k2_xboole_0(X0,X1),X2),X1) = k4_xboole_0(sP4_iProver_split(X0,X2),X1) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_1049,c_2992,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81267,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),X2) = k4_xboole_0(sP4_iProver_split(X0,X1),X2) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_81266,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81270,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(sP4_iProver_split(X2,X0),X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_53745,c_81267]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_14699,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_505,c_617]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_14935,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(X0,X1) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_14699,c_6]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_48921,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_14935,c_509]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_49082,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_48921,c_9,c_509]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_73136,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_8,c_49082]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74075,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_73136,c_49082]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74076,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(X2,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_74075,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81941,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_81270,c_74076]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_114564,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,X1),X2) = k2_xboole_0(X2,k4_xboole_0(X0,X1)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_114474,c_6,c_81941]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_115896,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_114564,c_0]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_116980,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(sP4_iProver_split(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,sP4_iProver_split(X2,X1))),X3) = k2_xboole_0(X2,X3) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_114158,c_115896]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_117418,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,X1) = k2_xboole_0(X0,X1) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_116980,c_114158]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_149287,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = sP4_iProver_split(X0,X1) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_14920,c_14920,c_117418]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_149341,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(X0,k4_xboole_0(sK4,sK4))) = sP4_iProver_split(k4_xboole_0(sK5,sK4),X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_8637,c_149287]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_149932,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(sK5,sK4),X0) = k2_xboole_0(k4_xboole_0(sK5,sK4),X0) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_149341,c_37461,c_44808]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_33427,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k4_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(sK4,X0)))) = X0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_17194,c_1749]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_713,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(sK3,sK2))) = k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_512,c_1]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3322,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5)) = k4_xboole_0(sK5,k1_xboole_0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_2914,c_713]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3323,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5)) = sK5 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_3322,c_7]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3129,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1,c_3026]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_109280,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(k4_xboole_0(sK4,sK5),k2_xboole_0(sK3,sK2)))) = k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3323,c_3129]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2936,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK2,sK5),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_2281,c_1862]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_109497,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,sK5)),k4_xboole_0(k2_xboole_0(sK2,sK5),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_2936,c_3129]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_110073,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(sP4_iProver_split(sK3,sK2),k2_xboole_0(sP5_iProver_split,sK5)),k4_xboole_0(k2_xboole_0(sP5_iProver_split,sK5),sP1_iProver_split)) = k4_xboole_0(sP4_iProver_split(sK3,sK2),k2_xboole_0(sP5_iProver_split,sK5)) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_109497,c_34016,c_59877,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_20604,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_622,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_20628,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_20604,c_6,c_9,c_1862]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_52086,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_20628,c_20628,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_52459,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),X3)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),sP1_iProver_split),X3) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_52086,c_605]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_52470,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),sP1_iProver_split) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_52086,c_616]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_681,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_9,c_10]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_701,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_681,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_52492,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),sP1_iProver_split) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_52470,c_701]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_52507,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_52459,c_52492]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_28190,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_9,c_696]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_28464,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),X3)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_28190,c_17153]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_17142,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),X3) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_16936,c_605]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_17177,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),X3) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_17142,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_17178,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X2),k2_xboole_0(X1,X3))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_17177,c_9,c_3970]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_28465,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_28464,c_9,c_17178]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_52508,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_52507,c_17153,c_28465]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_39067,plain,
% 55.01/7.50      ( k2_xboole_0(sK2,k4_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(X1,sK3)))) = sK2 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_11,c_37871]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_66817,plain,
% 55.01/7.50      ( k2_xboole_0(sP5_iProver_split,k4_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(X1,sK3)))) = sP5_iProver_split ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_39067,c_39067,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_66818,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(sK5,sP4_iProver_split(k2_xboole_0(X0,sK3),X1)),sP5_iProver_split) = sP5_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_66817,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_66819,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(sK5,sP4_iProver_split(X0,sP4_iProver_split(X1,sK3))),sP5_iProver_split) = sP5_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_66818,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_66832,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,sP4_iProver_split(sK5,sP4_iProver_split(k4_xboole_0(sK5,sP4_iProver_split(X0,sP4_iProver_split(X1,sK3))),sP5_iProver_split))) = k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(sK5,sP5_iProver_split)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_66819,c_57991]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_66850,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(sK5,sP5_iProver_split)) = k4_xboole_0(sK4,sP4_iProver_split(sK5,sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_66832,c_66819]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_66851,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK3,sK2),sP4_iProver_split(sK5,sP5_iProver_split)) = k4_xboole_0(sK4,sP4_iProver_split(sK5,sP5_iProver_split)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_66850,c_59354]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_66852,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sK5,sP5_iProver_split)) = k4_xboole_0(sK4,sP4_iProver_split(sK5,sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_66851,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_110074,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,k2_xboole_0(sP4_iProver_split(sK5,sP5_iProver_split),k2_xboole_0(sP5_iProver_split,sK5))) = k4_xboole_0(sK4,sP4_iProver_split(sK5,sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_110073,c_9,c_37461,c_52508,c_53685,c_61315,c_66852]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_39006,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k4_xboole_0(sK2,k2_xboole_0(X0,k2_xboole_0(X1,sK4)))) = sK5 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_11,c_37861]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_66499,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k4_xboole_0(sP5_iProver_split,k2_xboole_0(X0,k2_xboole_0(X1,sK4)))) = sK5 ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_39006,c_39006,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_66500,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(sP5_iProver_split,sP4_iProver_split(k2_xboole_0(X0,sK4),X1)),sK5) = sK5 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_66499,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_66501,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(sP5_iProver_split,sP4_iProver_split(X0,sP4_iProver_split(X1,sK4))),sK5) = sK5 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_66500,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56185,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(k4_xboole_0(X0,X1),sP4_iProver_split(X2,X0)),sP4_iProver_split(X2,X0)) = sP4_iProver_split(sP4_iProver_split(X2,X0),k4_xboole_0(X0,X1)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_53745,c_56078]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56206,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(k4_xboole_0(X0,X1),X2)) = sP4_iProver_split(X2,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_56185,c_9,c_53745,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74657,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,sK5) = sP4_iProver_split(sK5,sP5_iProver_split) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_66501,c_56206]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_8591,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(k4_xboole_0(sK5,sK4),X0)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK4),X0),k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_4236,c_3027]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2608,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_6,c_245]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_5761,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK2,sK5)),X1)) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_2298,c_11]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_5781,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK2,sK5)),X1)) = k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_5761,c_1512]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2249,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(sK5,X1))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_243,c_1329]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_5782,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_5781,c_2249,c_2590,c_3970]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_8614,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK4),X0))) = k2_xboole_0(X0,k2_xboole_0(sK4,sK5)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_8591,c_2608,c_5782]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_8615,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK4),X0))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_8614,c_152]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_8688,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK4),X0))) = k4_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK4),X0))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_8615,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_76121,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,sP4_iProver_split(sK3,sK2)),k2_xboole_0(sP5_iProver_split,k2_xboole_0(k4_xboole_0(sK5,sK4),X0))) = k4_xboole_0(sK3,k2_xboole_0(sP5_iProver_split,k2_xboole_0(k4_xboole_0(sK5,sK4),X0))) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_8688,c_8688,c_59877,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_76122,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP4_iProver_split(sK3,sK2),X0),sP4_iProver_split(k2_xboole_0(k4_xboole_0(sK5,sK4),X0),sP5_iProver_split)) = k4_xboole_0(sK3,sP4_iProver_split(k2_xboole_0(k4_xboole_0(sK5,sK4),X0),sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_76121,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_76123,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X0),sP4_iProver_split(k2_xboole_0(k4_xboole_0(sK5,sK4),X0),sP5_iProver_split)) = k4_xboole_0(sK3,sP4_iProver_split(k2_xboole_0(k4_xboole_0(sK5,sK4),X0),sP5_iProver_split)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_76122,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_76124,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)),sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,X0))) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,X0))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_76123,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_39411,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK5),X1)))) = k2_xboole_0(sK4,sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_10886,c_2244]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_39565,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK5),X1)))) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_39411,c_152]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_40473,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,sK5),X2))))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_39565,c_243]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_67460,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sP5_iProver_split,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,sK5),X2))))) = k2_xboole_0(X0,sP4_iProver_split(sK3,sK2)) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_40473,c_40473,c_59877,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_67461,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k2_xboole_0(sP5_iProver_split,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK5),X1))),X2),sK3) = sP4_iProver_split(sK3,sP4_iProver_split(X2,sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_67460,c_53685,c_54100,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_67462,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,sK5),X2))),sP4_iProver_split(sK3,sP5_iProver_split)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_67461,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1331,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(X0,X1))) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK3,sK2),X1)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1044,c_243]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1525,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) = k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1237,c_243]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_16087,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(sK2,k2_xboole_0(sK3,X1))) = k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(X0,X1))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_1331,c_1525,c_3970]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_16088,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(X0,X1))) = k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_16087,c_1525,c_1703]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_26786,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(X0,k4_xboole_0(sK4,X1)))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_26587,c_16088]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_37109,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK4,X1))),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(sK4,X1))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1733,c_26786]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_37241,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK4,X1))),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_37109,c_1525,c_14817,c_26587]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_65299,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sP4_iProver_split(sK2,k4_xboole_0(sK4,X0)),sP4_iProver_split(sK2,k4_xboole_0(sK4,X0))),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_65209,c_37241]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_65759,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK4,X0)),sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK4,X0))),sP4_iProver_split(sK3,sK2)) = sP4_iProver_split(sK3,sP5_iProver_split) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_65299,c_59877,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_65760,plain,
% 55.01/7.50      ( sP4_iProver_split(sK3,sP5_iProver_split) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_65759,c_35092,c_39584,c_53685,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_67463,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,sK5),X2))),sP4_iProver_split(sP5_iProver_split,sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_67462,c_65760]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_67464,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X0,sK5))),sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X2)) = sP4_iProver_split(sK3,sP4_iProver_split(X2,sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_67463,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_40469,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK5),X1))),k2_xboole_0(sK3,X2)) = k2_xboole_0(X2,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_39565,c_244]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_67315,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sP5_iProver_split,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK5),X1))),k2_xboole_0(sK3,X2)) = k2_xboole_0(X2,sP4_iProver_split(sK3,sK2)) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_40469,c_40469,c_59877,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_67316,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,sK3),sP4_iProver_split(k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,sK5),X2)),sP5_iProver_split)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_67315,c_3970,c_53685,c_54100,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_67317,plain,
% 55.01/7.50      ( sP4_iProver_split(sK3,sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X0,sK5))),sP5_iProver_split),X2)) = sP4_iProver_split(sK3,sP4_iProver_split(X2,sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_67316,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_67318,plain,
% 55.01/7.50      ( sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,k4_xboole_0(X1,sP4_iProver_split(X2,k4_xboole_0(X1,sK5)))))) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_67317,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_67346,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,k4_xboole_0(X1,sP4_iProver_split(X2,k4_xboole_0(X1,sK5)))))),sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split))) = sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,k4_xboole_0(X1,sP4_iProver_split(X2,k4_xboole_0(X1,sK5))))),sK3) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_67318,c_56078]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53512,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = k2_xboole_0(X1,X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_21035,c_0]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54150,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = sP4_iProver_split(X0,X1) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_53512,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54151,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X0,X2)) = sP4_iProver_split(X2,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_54150,c_3970,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_67359,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X0,sK5))),sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X2)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X2)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_67346,c_54100,c_54151,c_65760]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_67360,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X0,sK5))),sP4_iProver_split(sK3,sP4_iProver_split(X2,sP5_iProver_split))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X2)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_67359,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_67465,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_67464,c_54100,c_67360]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_76125,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0)),sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,X0))) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,X0))) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_76124,c_67465]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_76137,plain,
% 55.01/7.50      ( k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,sK5))) = k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sK5)),sP4_iProver_split(sP5_iProver_split,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_53745,c_76125]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_9863,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sK2,sK5),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_8,c_5792]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_37492,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK2,sK5)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_9863,c_0]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_63315,plain,
% 55.01/7.50      ( k2_xboole_0(sP4_iProver_split(sK3,sK2),k4_xboole_0(sK2,sK5)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_37492,c_37492,c_59877,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_63316,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(sK2,sK5),sP4_iProver_split(sP5_iProver_split,sK3)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_63315,c_53685,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_960,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_6,c_243]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68488,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,X1),X2),X1) = sP4_iProver_split(X1,sP4_iProver_split(X2,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_960,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68504,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),sK2)) = sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_63316,c_68488]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_69261,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),sP5_iProver_split)) = sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),sK5) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_68504,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_69262,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sK5)) = sP4_iProver_split(sK5,sP4_iProver_split(sK3,sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_69261,c_54100,c_56413,c_67465]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3917,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK2,sK5),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_2281,c_959]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3984,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK2,sK5),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_3917,c_2281]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_4838,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK5,sK2),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_0,c_3984]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_30791,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_4838,c_0]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_17523,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK2,sK4),X0)) = k2_xboole_0(sK5,X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_15328,c_11]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_49785,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) = k2_xboole_0(sK5,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_598,c_17523]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_49909,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k1_xboole_0) = k2_xboole_0(sK5,sK2) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_49785,c_15262]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_49910,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,sK2) = sK5 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_49909,c_518]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_62865,plain,
% 55.01/7.50      ( k2_xboole_0(sP4_iProver_split(sK3,sK2),sK5) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_30791,c_30791,c_49910,c_59877,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_62866,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(sP5_iProver_split,sK3)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_62865,c_53685,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_69263,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sK5)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_69262,c_62866,c_65760]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_76277,plain,
% 55.01/7.50      ( k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,sK5))) = k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sP5_iProver_split,sK5)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_76137,c_69263]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53449,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK5),X1),k2_xboole_0(X0,k2_xboole_0(sK5,k4_xboole_0(X2,sK4)))) = k2_xboole_0(k2_xboole_0(X0,sK5),k4_xboole_0(X2,k2_xboole_0(sK3,sK2))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_15298,c_21035]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_21042,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X0,k2_xboole_0(X1,X3))) = k2_xboole_0(k2_xboole_0(X0,X1),X3) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_11,c_1745]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_21328,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X0,k2_xboole_0(X1,X3))) = k2_xboole_0(X1,k2_xboole_0(X0,X3)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_21042,c_3970]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_46553,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(X0,sK5),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK5,k4_xboole_0(X1,sK4))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_15298,c_0]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54290,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,sK4),sK5),X1) = sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,sK4),X1),sK5) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_53449,c_21328,c_46553,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54684,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sK5,k4_xboole_0(X0,sK4)),X1) = sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,sK4),X1),sK5) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_54587,c_54290]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54706,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,sK4),sP4_iProver_split(X1,sK5)) = sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,sK4),X1),sK5) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_54684,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54924,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(k4_xboole_0(X0,sK4),X1)) = sP4_iProver_split(k4_xboole_0(X0,sK4),sP4_iProver_split(X1,sK5)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_54920,c_54706]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74812,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,sP4_iProver_split(sK5,sP4_iProver_split(k4_xboole_0(sK5,X0),X1))) = k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(X1,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_56206,c_57991]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74856,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(X0,sK5)) = k4_xboole_0(sK4,sP4_iProver_split(X0,sK5)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_74812,c_56206]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74857,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK3,sK2),sP4_iProver_split(X0,sK5)) = k4_xboole_0(sK4,sP4_iProver_split(X0,sK5)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_74856,c_59354]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74858,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(X0,sK5)) = k4_xboole_0(sK4,sP4_iProver_split(X0,sK5)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_74857,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_76278,plain,
% 55.01/7.50      ( k4_xboole_0(sK3,sP4_iProver_split(sK5,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP5_iProver_split))) = k4_xboole_0(sK4,sP4_iProver_split(sP5_iProver_split,sK5)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_76277,c_54924,c_74858]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_13657,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK2,sK4),sK4))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),sK4),k1_xboole_0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3349,c_12475]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_13710,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK2,sK4))) = k4_xboole_0(sK2,sK4) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_13657,c_8,c_9,c_518]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_962,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k2_xboole_0(X2,X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_153,c_243]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72427,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(X0,X1)) = sP4_iProver_split(X0,X2) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_962,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72458,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK2,sK4),X0),k4_xboole_0(sK5,k4_xboole_0(sK2,sK4))) = sP4_iProver_split(sK5,X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_13710,c_72427]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_52077,plain,
% 55.01/7.50      ( k4_xboole_0(sK2,k2_xboole_0(sK4,k4_xboole_0(sK2,sK2))) = k4_xboole_0(sK2,k4_xboole_0(sK4,k4_xboole_0(sK3,sK2))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_18162,c_16936]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_34373,plain,
% 55.01/7.50      ( k4_xboole_0(sK2,sP1_iProver_split) = sK2 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_34187,c_3133]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_14703,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK4,k4_xboole_0(X0,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1259,c_617]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_35001,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),sK5)) = k2_xboole_0(sK4,sP1_iProver_split) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_34235,c_14703]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_35016,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k4_xboole_0(sK4,sK5)) = k2_xboole_0(sK4,sP1_iProver_split) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_35001,c_512]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_35017,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,sP1_iProver_split) = sK4 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_35016,c_1749]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_39080,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(X0,sK3)),sK2) = k4_xboole_0(sK2,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_37871,c_509]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_39084,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(X0,sK3)),sK2) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_37871,c_1862]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_39119,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(X0,sK3)),sK2) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_39084,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_39123,plain,
% 55.01/7.50      ( k4_xboole_0(sK2,sK2) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_39080,c_39119]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_52847,plain,
% 55.01/7.50      ( k4_xboole_0(sK2,sK4) = sK2 ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_52077,c_34373,c_35017,c_39123,c_52081]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72986,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sK2,X0),k4_xboole_0(sK5,sK2)) = sP4_iProver_split(sK5,X0) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_72458,c_52847]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68517,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X2,k2_xboole_0(X1,X0))) = sP4_iProver_split(sP4_iProver_split(X1,X2),k4_xboole_0(X0,X1)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3755,c_68488]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53754,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X2,k2_xboole_0(X1,X0))) = sP4_iProver_split(X2,k2_xboole_0(X1,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_509,c_53745]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53990,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X2,sP4_iProver_split(X0,X1))) = sP4_iProver_split(X2,sP4_iProver_split(X0,X1)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_53754,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_69185,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,X1),k4_xboole_0(X2,X0)) = sP4_iProver_split(X1,sP4_iProver_split(X2,X0)) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_68517,c_53685,c_53990]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72987,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(sK5,sP5_iProver_split)) = sP4_iProver_split(sK5,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_72986,c_65380,c_69185]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_6408,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK2,sK5),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK2,sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_2281,c_3133]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72646,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(k2_xboole_0(sK2,sK5),k2_xboole_0(sK2,sK5)),X0),k2_xboole_0(sK2,sK5)) = sP4_iProver_split(k2_xboole_0(sK2,sK5),X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_6408,c_72427]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72872,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(k2_xboole_0(sP5_iProver_split,sK5),k2_xboole_0(sP5_iProver_split,sK5)),X0),k2_xboole_0(sP5_iProver_split,sK5)) = sP4_iProver_split(k2_xboole_0(sP5_iProver_split,sK5),X0) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_72646,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_6398,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,sK5),k4_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k2_xboole_0(X0,sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_961,c_3133]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_48976,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0))) = k4_xboole_0(X2,k2_xboole_0(X0,X2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_14935,c_16936]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_6410,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k4_xboole_0(X0,X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1749,c_3133]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_49022,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X2,k2_xboole_0(X0,X2)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_48976,c_6410]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_49023,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_49022,c_9,c_1862,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_49402,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(X0,sK5)) = sP1_iProver_split ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_6398,c_49023]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68515,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(X1,X0)) = sP4_iProver_split(sP4_iProver_split(k1_xboole_0,X1),X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1849,c_68488]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53801,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(X1,X0)) = sP4_iProver_split(X1,X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_6382,c_53745]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_69243,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sP1_iProver_split,X0),X1) = sP4_iProver_split(X0,X1) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_68515,c_34016,c_53801]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72873,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(X0,sP5_iProver_split)) = sP4_iProver_split(X0,sP4_iProver_split(sK5,sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_72872,c_49402,c_53685,c_54923,c_68488,c_69243]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72989,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(X0,sP5_iProver_split)) = sP4_iProver_split(sK5,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_72987,c_72873]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_76279,plain,
% 55.01/7.50      ( k4_xboole_0(sK3,sP4_iProver_split(sK5,k4_xboole_0(sK5,sK4))) = k4_xboole_0(sK4,sP4_iProver_split(sP5_iProver_split,sK5)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_76278,c_72989]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_4240,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(sK5,sK4),sK4) = k4_xboole_0(sK5,sK4) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3765,c_3026]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1943,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1,c_1749]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_15292,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1)) = k2_xboole_0(X1,k2_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_14697,c_245]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_45051,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(sK3,sK2)))),k2_xboole_0(sK5,k4_xboole_0(X1,sK4))) = k2_xboole_0(sK5,k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1943,c_15292]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_45225,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(sK3,sK2)))),k2_xboole_0(sK5,k4_xboole_0(X1,sK4))) = k2_xboole_0(sK5,k4_xboole_0(X1,sK4)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_45051,c_14697]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72065,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,sP4_iProver_split(sK3,sK2)))),k2_xboole_0(sK5,k4_xboole_0(X1,sK4))) = k2_xboole_0(sK5,k4_xboole_0(X1,sK4)) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_45225,c_45225,c_59877]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72066,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,sK4),sK5),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3))))) = sP4_iProver_split(k4_xboole_0(X0,sK4),sK5) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_72065,c_53685,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72075,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK5,sK4),sK5),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,sK3))))) = sP4_iProver_split(k4_xboole_0(k4_xboole_0(sK5,sK4),sK4),sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_4240,c_72066]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72200,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK5,sK4),sK5),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,sK3))))) = sP4_iProver_split(k4_xboole_0(sK5,sK4),sK5) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_72075,c_4240]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53274,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),k2_xboole_0(X3,X1)) = k2_xboole_0(X1,X3) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_16936,c_21035]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_54884,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X3)))) = sP4_iProver_split(X1,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_53274,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_24589,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k4_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(X1,sK4)))) = sK5 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_11,c_23964]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_58209,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(k2_xboole_0(X0,sK4),X1)),sK5) = sK5 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_24589,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_58210,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(X0,sP4_iProver_split(X1,sK4))),sK5) = sK5 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_58209,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_58218,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(X0,sP4_iProver_split(X1,sK4))),sK5) = sP4_iProver_split(k4_xboole_0(sK5,X2),sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_58210,c_53745]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_58223,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(sK5,X0),sK5) = sK5 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_58218,c_58210]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72201,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,k4_xboole_0(sK5,sK4)) = sK5 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_72200,c_54884,c_58223]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_76280,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,sP4_iProver_split(sP5_iProver_split,sK5)) = k4_xboole_0(sK3,sK5) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_76279,c_72201]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_110075,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,k2_xboole_0(sP4_iProver_split(sP5_iProver_split,sK5),k2_xboole_0(sP5_iProver_split,sK5))) = k4_xboole_0(sK3,sK5) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_110074,c_74657,c_76280]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81357,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sP4_iProver_split(X0,X1),X2),k4_xboole_0(X2,k4_xboole_0(X2,sP4_iProver_split(X0,sP4_iProver_split(X1,X2))))) = sP4_iProver_split(X0,sP4_iProver_split(X1,X2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_81267,c_598]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_4115,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_6,c_1672]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_4224,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_4115,c_1672]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_23180,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X2),X3)) = k4_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(k2_xboole_0(X0,X2),X3)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1745,c_625]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_23712,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X0,X3)))) = k1_xboole_0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_23180,c_9,c_1865,c_3970]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56494,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X0,X3)))) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_23712,c_23712,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56495,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(k2_xboole_0(X1,k2_xboole_0(X0,X2)),X3)) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_56494,c_23712,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56496,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,k2_xboole_0(X0,X3)))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_56495,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56497,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,sP4_iProver_split(X3,X0)))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_56496,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56504,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,X0))) = sP1_iProver_split ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_53745,c_56497]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81806,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(X1,X2)) = k2_xboole_0(sP4_iProver_split(X0,X1),X2) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_81357,c_4224,c_37461,c_53685,c_56504]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_110076,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK5,k2_xboole_0(sP5_iProver_split,sK5)))) = k4_xboole_0(sK3,sK5) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_110075,c_81806]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72669,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK5,k4_xboole_0(sK2,sK4)),X0),k4_xboole_0(sK2,sK4)) = sP4_iProver_split(sK5,X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_13710,c_72427]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72817,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK5,sK2),X0),sK2) = sP4_iProver_split(sK5,X0) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_72669,c_52847]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72818,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK5)) = sP4_iProver_split(sK5,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_72817,c_65380,c_68488]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1947,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_9,c_1749]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_86711,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,X2)),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,X2) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_1947,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_86793,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,k1_xboole_0)),X0) = k4_xboole_0(X0,k1_xboole_0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_7,c_86711]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_87355,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,sP1_iProver_split)),X0) = X0 ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_86793,c_7,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_970,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_243,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_97420,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(k2_xboole_0(X0,X1),X2),sP4_iProver_split(X1,X2)) = k4_xboole_0(X0,sP4_iProver_split(X1,X2)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_970,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_97421,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),sP4_iProver_split(X2,X1)) = k4_xboole_0(X0,sP4_iProver_split(X2,X1)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_97420,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_98333,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(X0,X1),sP4_iProver_split(X1,k4_xboole_0(X1,sP4_iProver_split(X2,sP1_iProver_split)))) = k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X1,sP4_iProver_split(X2,sP1_iProver_split)))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_87355,c_97421]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74794,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = sP4_iProver_split(X0,k4_xboole_0(X0,X1)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_56206,c_53745]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74880,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X0) = sP4_iProver_split(X0,k4_xboole_0(X0,X1)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_74794,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56174,plain,
% 55.01/7.50      ( sP4_iProver_split(k1_xboole_0,sP4_iProver_split(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X0)) = sP4_iProver_split(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_24299,c_56078]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56237,plain,
% 55.01/7.50      ( sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X0)) = sP4_iProver_split(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_56174,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56238,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,k4_xboole_0(X0,sP4_iProver_split(X1,X2))) = sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,X2)),X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_56237,c_53685,c_53848]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72432,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,X1),X0),k4_xboole_0(X0,X1)) = sP4_iProver_split(X0,sP4_iProver_split(X0,k4_xboole_0(X0,X1))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_56078,c_72427]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_73041,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,k4_xboole_0(X0,X1)) = sP4_iProver_split(k4_xboole_0(X0,X1),X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_72432,c_54013,c_56413]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74881,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,k4_xboole_0(X0,sP4_iProver_split(X1,X2))) = sP4_iProver_split(X0,k4_xboole_0(X0,X2)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_74880,c_53685,c_56238,c_73041]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_97500,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(X1,X2),k4_xboole_0(X2,X3))),sP4_iProver_split(X1,X2)) = k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X2,X3),sP4_iProver_split(X1,X2))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_53745,c_97421]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72723,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X2,X0)) = sP4_iProver_split(X0,X2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_72427,c_68488]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72430,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,X1),k4_xboole_0(X1,X2)) = sP4_iProver_split(X1,sP4_iProver_split(X0,X1)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_53745,c_72427]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_73044,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,X1),k4_xboole_0(X1,X2)) = sP4_iProver_split(X0,X1) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_72430,c_53801,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81364,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(sP4_iProver_split(X0,X1),X2),X3) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_81267,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81794,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),sP4_iProver_split(X3,X2)) = k4_xboole_0(sP4_iProver_split(X0,X1),sP4_iProver_split(X3,X2)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_81364,c_9,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_97809,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(X0,X1),sP4_iProver_split(X1,X2)) = k4_xboole_0(X0,sP4_iProver_split(X2,X1)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_97500,c_72723,c_73044,c_81794]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_98430,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X1,sP1_iProver_split),X1)) = k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X1,sP1_iProver_split))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_98333,c_74881,c_97809]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81356,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),k2_xboole_0(k4_xboole_0(sP4_iProver_split(X0,X1),X2),X3)) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,sP4_iProver_split(X0,sP4_iProver_split(X1,X2)))),X3) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_81267,c_605]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81807,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),sP4_iProver_split(X3,k4_xboole_0(sP4_iProver_split(X0,X1),X2))) = k4_xboole_0(X2,X3) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_81356,c_10745,c_37461,c_53685,c_56504]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_10783,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = X0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_605,c_1749]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_10891,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X2))) = X0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_10783,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81368,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k4_xboole_0(sP4_iProver_split(X1,sP4_iProver_split(X2,X0)),k2_xboole_0(k4_xboole_0(sP4_iProver_split(X1,X2),X0),X3))) = X0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_81267,c_10891]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81792,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),sP4_iProver_split(X3,k4_xboole_0(sP4_iProver_split(X0,X1),X2))),X2) = X2 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_81368,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81816,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,X1),X0) = X0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_81807,c_81792]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_98431,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(X1,X1)) = k4_xboole_0(X0,X1) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_98430,c_37461,c_81816]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_110077,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,sK5) = k4_xboole_0(sK3,sK5) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_110076,c_53685,c_72818,c_72989,c_98431]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_110642,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK3,sK5),k4_xboole_0(k4_xboole_0(sK3,sK5),k2_xboole_0(sK3,sK2)))) = k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK3,sK5)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_109280,c_110077]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_110643,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK3,sK5),k4_xboole_0(k4_xboole_0(sK3,sK5),sP4_iProver_split(sK3,sK2)))) = k4_xboole_0(sP4_iProver_split(sK3,sK2),k4_xboole_0(sK3,sK5)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_110642,c_59877]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_6422,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3027,c_3133]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_110644,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),k4_xboole_0(sK3,sK5)) = sK5 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_110643,c_9,c_6422,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3817,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3755,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_117522,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_3817,c_3817,c_117418]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_117523,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(X0,X1),sP4_iProver_split(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_117522,c_117418]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_117700,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(k4_xboole_0(sK3,sK5),sP4_iProver_split(sP5_iProver_split,sK3)),sP4_iProver_split(sK5,X0)) = k4_xboole_0(k4_xboole_0(sK3,sK5),X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_110644,c_117523]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_115945,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK5,sP4_iProver_split(k4_xboole_0(X0,X1),sK2))) = k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(X0,X1),sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_114564,c_5438]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_116058,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK5,sP4_iProver_split(k4_xboole_0(X0,X1),sP5_iProver_split))) = k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(X0,X1),sP5_iProver_split)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_115945,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_107236,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(X0,X1),sP4_iProver_split(X2,X1)) = k4_xboole_0(X0,sP4_iProver_split(X2,X1)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_3028,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_107363,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,sP4_iProver_split(X1,X2)),sP4_iProver_split(X1,X2)) = k2_xboole_0(sP4_iProver_split(X1,X2),sP4_iProver_split(X0,X2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_107236,c_3027]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_107492,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,X1),X2) = sP4_iProver_split(X0,sP4_iProver_split(X2,X1)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_107363,c_4224,c_53685,c_53801,c_81806]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_116059,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,X1),sP5_iProver_split),sK5),sK3) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k4_xboole_0(X0,X1))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_116058,c_53685,c_107492]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74718,plain,
% 55.01/7.50      ( sP4_iProver_split(k2_xboole_0(X0,sK5),sP4_iProver_split(k2_xboole_0(X0,sK5),X1)) = sP4_iProver_split(X1,k2_xboole_0(X0,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_6398,c_56206]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_75013,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(sP4_iProver_split(sK5,sP4_iProver_split(X0,X1)),X1)) = sP4_iProver_split(X0,sP4_iProver_split(sK5,X1)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_74718,c_53685,c_54013,c_54923]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_75014,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,sP4_iProver_split(X1,X0)),sK5) = sP4_iProver_split(X1,sP4_iProver_split(sK5,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_75013,c_54013,c_54923]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_75015,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,X1),sK5) = sP4_iProver_split(X0,sP4_iProver_split(sK5,X1)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_75014,c_53801]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_110815,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK3,sK5),k4_xboole_0(k4_xboole_0(sK3,sK5),sP4_iProver_split(sP5_iProver_split,sK3)))) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_110644,c_598]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_110837,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,sK5),sP4_iProver_split(sP5_iProver_split,sK3)) = k4_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_110644,c_49082]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_110881,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK3,sK5),k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,sK3)))) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_110815,c_110837]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_12492,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2)))) = k4_xboole_0(k2_xboole_0(X1,sK5),k4_xboole_0(k2_xboole_0(X1,sK5),k4_xboole_0(X0,sK4))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_961,c_616]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_76776,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(X1,sP4_iProver_split(sK3,sK2)))) = k4_xboole_0(k2_xboole_0(X1,sK5),k4_xboole_0(k2_xboole_0(X1,sK5),k4_xboole_0(X0,sK4))) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_12492,c_59877]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_76777,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(sK4,k4_xboole_0(X0,sP4_iProver_split(sP4_iProver_split(sK3,sK2),X1)))) = k4_xboole_0(sP4_iProver_split(sK5,X1),k4_xboole_0(sP4_iProver_split(sK5,X1),k4_xboole_0(X0,sK4))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_76776,c_9,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_76778,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(sK4,k4_xboole_0(X0,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X1)))) = k4_xboole_0(sP4_iProver_split(sK5,X1),k4_xboole_0(sP4_iProver_split(sK5,X1),k4_xboole_0(X0,sK4))) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_76777,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_76779,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X1)),sK4)) = k4_xboole_0(sP4_iProver_split(sK5,X1),k4_xboole_0(sP4_iProver_split(sK5,X1),k4_xboole_0(X0,sK4))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_76778,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_76780,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(sK3,sP4_iProver_split(X1,sP5_iProver_split))),sK4)) = k4_xboole_0(sP4_iProver_split(sK5,X1),k4_xboole_0(sP4_iProver_split(sK5,X1),k4_xboole_0(X0,sK4))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_76779,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_76781,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X1))),sK4)) = k4_xboole_0(sP4_iProver_split(sK5,X1),k4_xboole_0(sP4_iProver_split(sK5,X1),k4_xboole_0(X0,sK4))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_76780,c_67465]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_9909,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK5),X0),sK5)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_5792,c_961]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_76882,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(k2_xboole_0(sK2,sK5),sK4))),sK5)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_76781,c_9909]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3923,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3233,c_959]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3981,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_3923,c_3233]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2999,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK4) = k4_xboole_0(k2_xboole_0(X0,sK5),sK4) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_961,c_509]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_6743,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK2,sK4),sK5),sK4) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK4) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3981,c_2999]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_6772,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK2,sK4),sK5),sK4) = k4_xboole_0(sK5,sK4) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_6743,c_1279]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_6773,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK2,sK5),sK4) = k4_xboole_0(sK5,sK4) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_6772,c_509,c_3970]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_77127,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sK5,sK4))),sK5)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_76882,c_6773,c_59877,c_65380,c_65760]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_17086,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X1) = X1 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_16936,c_505]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_77128,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,sK3) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_77127,c_152,c_2244,c_17086]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_77129,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,sK3) = k2_xboole_0(sK3,sP5_iProver_split) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_77128,c_59877,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_77592,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,sK3) = k2_xboole_0(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_77129,c_0]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_79130,plain,
% 55.01/7.50      ( k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,sK3)) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_77592,c_1862]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_79167,plain,
% 55.01/7.50      ( k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,sK3)) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_79130,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_110882,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK3,sK5),sP1_iProver_split)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_110881,c_79167]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_49476,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),sP1_iProver_split) = k4_xboole_0(X0,X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_49023,c_3026]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_110883,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,sK3) = k2_xboole_0(sK5,sK3) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_110882,c_6,c_49476,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_111253,plain,
% 55.01/7.50      ( k2_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3)) = k2_xboole_0(sK3,k2_xboole_0(sK5,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_110883,c_244]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_15293,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK5,X1)) = k2_xboole_0(X1,k2_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_14697,c_244]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_111267,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),sP4_iProver_split(sP5_iProver_split,sK3)) = k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_110883,c_15293]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_111294,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,sP4_iProver_split(sK3,sK2)),sP4_iProver_split(sP5_iProver_split,sK3)) = k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_111267,c_59877]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_111295,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,sK4),sP4_iProver_split(sK3,sK5)) = k2_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_111294,c_4224,c_53685,c_61315,c_107492]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2010,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k2_xboole_0(sK4,k2_xboole_0(X0,X1))) = k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1674,c_11]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_77579,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k2_xboole_0(sK4,sP4_iProver_split(sP5_iProver_split,sK3))) = k2_xboole_0(sK3,k2_xboole_0(sP5_iProver_split,k2_xboole_0(sK3,sK2))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_77129,c_2010]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_17040,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(k2_xboole_0(sK3,sK2),X0))) = k4_xboole_0(X0,k4_xboole_0(X0,sK4)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3765,c_16936]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_8601,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK4),X0),k2_xboole_0(sK3,sK2)),k4_xboole_0(sK4,X0)) = k2_xboole_0(k4_xboole_0(sK5,sK4),X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_4236,c_3755]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_8610,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK4),X0))),k4_xboole_0(sK4,X0)) = k2_xboole_0(k4_xboole_0(sK5,sK4),X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_8601,c_5782]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_8617,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK4,X0)) = k2_xboole_0(k4_xboole_0(sK5,sK4),X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_8615,c_8610]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_30957,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(sK3,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,sK4))) = k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(sK4,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1,c_8617]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_8595,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_4236,c_505]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_31074,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(X0,k4_xboole_0(X0,sK4))) = k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(sK4,X0)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_30957,c_8595]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_30972,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,sK2),X0),k2_xboole_0(sK3,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,sK4))) = k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_17193,c_8617]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_31055,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK3,sK2),X0))),k4_xboole_0(X0,k4_xboole_0(X0,sK4))) = k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_30972,c_14817]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1960,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X0,X1),X2))) = k2_xboole_0(X0,X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1749,c_11]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_31056,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(X0,k4_xboole_0(X0,sK4))) = k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_31055,c_1960]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_31075,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(k2_xboole_0(sK3,sK2),X0)) = k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(sK4,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_31074,c_31056]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_61740,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK3,sK2),k2_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(sK4,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,sK4)) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_17040,c_31075,c_59877]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_61741,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(k4_xboole_0(sK4,X0),k4_xboole_0(sK5,sK4))) = k4_xboole_0(X0,k4_xboole_0(X0,sK4)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_61740,c_53685,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_61762,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK5,k4_xboole_0(sK4,sP1_iProver_split)),k4_xboole_0(k2_xboole_0(sK5,k4_xboole_0(sK4,sP1_iProver_split)),sK4)) = k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sP1_iProver_split,k4_xboole_0(sK5,sK4))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_34829,c_61741]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_62059,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sP1_iProver_split,k4_xboole_0(sK5,sK4))) = sK4 ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_61762,c_1259,c_1279,c_3765,c_34383]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_62193,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,sP4_iProver_split(sP5_iProver_split,sK3)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_62059,c_505]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_77651,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sP5_iProver_split,sP4_iProver_split(sK3,sK2))) = k2_xboole_0(sK5,sP4_iProver_split(sP5_iProver_split,sK3)) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_77579,c_59877,c_62193]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74720,plain,
% 55.01/7.50      ( sP4_iProver_split(k2_xboole_0(sK2,sK5),sP4_iProver_split(k2_xboole_0(sK2,sK5),X0)) = sP4_iProver_split(X0,k2_xboole_0(sK2,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_6408,c_56206]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_75007,plain,
% 55.01/7.50      ( sP4_iProver_split(k2_xboole_0(sP5_iProver_split,sK5),sP4_iProver_split(k2_xboole_0(sP5_iProver_split,sK5),X0)) = sP4_iProver_split(X0,k2_xboole_0(sP5_iProver_split,sK5)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_74720,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_75008,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(sP4_iProver_split(sK5,sP4_iProver_split(X0,sP5_iProver_split)),sP5_iProver_split)) = sP4_iProver_split(X0,sP4_iProver_split(sK5,sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_75007,c_53685,c_54013,c_54923]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_75009,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(sP4_iProver_split(sK5,X0),sP5_iProver_split)) = sP4_iProver_split(X0,sP4_iProver_split(sK5,sP5_iProver_split)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_75008,c_72989]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_75010,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,X0),sK5) = sP4_iProver_split(X0,sP4_iProver_split(sK5,sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_75009,c_54013,c_54923,c_72989]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_75140,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,X0),sK5) = sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK5)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_74657,c_75010]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_12452,plain,
% 55.01/7.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK5,sK3))) = k4_xboole_0(k4_xboole_0(sK5,sK3),k1_xboole_0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_2914,c_616]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_12841,plain,
% 55.01/7.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK5,sK3))) = k4_xboole_0(sK5,sK3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_12452,c_9,c_518]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72456,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK5,sK3),X0),k4_xboole_0(sK2,k4_xboole_0(sK5,sK3))) = sP4_iProver_split(sK2,X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_12841,c_72427]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68584,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK5,sK3),X0),k4_xboole_0(sK2,k4_xboole_0(sK5,sK3))) = sP4_iProver_split(k4_xboole_0(sK2,k4_xboole_0(sK5,sK3)),sP4_iProver_split(X0,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_12841,c_68488]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68885,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK5,sK3),X0),k4_xboole_0(sP5_iProver_split,k4_xboole_0(sK5,sK3))) = sP4_iProver_split(k4_xboole_0(sP5_iProver_split,k4_xboole_0(sK5,sK3)),sP4_iProver_split(X0,sP5_iProver_split)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_68584,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68886,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK5,sK3),X0),k4_xboole_0(sP5_iProver_split,k4_xboole_0(sK5,sK3))) = sP4_iProver_split(X0,sP5_iProver_split) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_68885,c_53745,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72992,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP5_iProver_split) = sP4_iProver_split(sP5_iProver_split,X0) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_72456,c_65380,c_68886]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72995,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK5)) = sP4_iProver_split(sK5,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_72992,c_72987]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_75144,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,X0),sK5) = sP4_iProver_split(sK5,X0) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_75140,c_72995]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_77652,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sK3,sK2),sP5_iProver_split),sK3) = sP4_iProver_split(sK5,sK3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_77651,c_53685,c_75144]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74652,plain,
% 55.01/7.50      ( sP4_iProver_split(sK3,sK5) = sP4_iProver_split(sK5,sK3) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_58210,c_56206]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74655,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),sK2) = sP4_iProver_split(sK2,sP4_iProver_split(sP5_iProver_split,sK3)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_63316,c_56206]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_11563,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_8,c_7838]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_43113,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK2,sK4)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_11563,c_0]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_69451,plain,
% 55.01/7.50      ( k2_xboole_0(sP4_iProver_split(sK3,sK2),sK2) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_43113,c_43113,c_52847,c_59877,c_65380,c_65760]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_69452,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sP5_iProver_split,sK3)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_69451,c_53685,c_61315,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_75147,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),sP5_iProver_split) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_74655,c_65380,c_69452]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_77653,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),sK3) = sP4_iProver_split(sK3,sK5) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_77652,c_61315,c_74652,c_75147]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74645,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,X1),X1) = sP4_iProver_split(X1,sP4_iProver_split(X0,X1)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_53745,c_56206]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_75156,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,X1),X1) = sP4_iProver_split(X0,X1) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_74645,c_53801,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_77654,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,sK3) = sP4_iProver_split(sK3,sK5) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_77653,c_75156]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_13678,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4)))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(X0,sK4)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_12475,c_6]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_11613,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),X0),sK5)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_7838,c_961]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_20532,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(X0,sK4)) = k4_xboole_0(X0,sK4) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_11613,c_622]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_78727,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,sP4_iProver_split(sK3,sK2)),k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4)))) = k4_xboole_0(X0,sK4) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_13678,c_13678,c_20532,c_59877]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_78728,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))),k4_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3))) = k4_xboole_0(X0,sK4) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_78727,c_53685,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1043,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_6,c_11]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1058,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_1043,c_11]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2570,plain,
% 55.01/7.50      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_6,c_245]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_82099,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,k4_xboole_0(X1,X2)),X2) = sP4_iProver_split(X1,sP4_iProver_split(X2,X0)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_1058,c_2570,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_82116,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))))) = sP4_iProver_split(k4_xboole_0(X0,sK4),sP4_iProver_split(sP5_iProver_split,sK3)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_78728,c_82099]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_82902,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))),sP5_iProver_split))) = sP4_iProver_split(k4_xboole_0(X0,sK4),sP4_iProver_split(sP5_iProver_split,sK3)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_82116,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_82903,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4)))))) = sP4_iProver_split(k4_xboole_0(X0,sK4),sP4_iProver_split(sP5_iProver_split,sK3)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_82902,c_67465]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81395,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,sK5)),k2_xboole_0(k4_xboole_0(sP4_iProver_split(X0,X1),sK5),X2)))) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_81267,c_39565]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81701,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sP5_iProver_split,k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,sK5)),k2_xboole_0(k4_xboole_0(sP4_iProver_split(X0,X1),sK5),X2)))) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_81395,c_59877,c_65380,c_65760]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81702,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,sK5)),k2_xboole_0(k4_xboole_0(sP4_iProver_split(X0,X1),sK5),X2)),sP5_iProver_split),sK3) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_81701,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81703,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,sK5)),sP4_iProver_split(X2,k4_xboole_0(sP4_iProver_split(X0,X1),sK5))))) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_81702,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81814,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k4_xboole_0(sK5,X0))) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_81807,c_81703]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_82904,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,sK4),sP4_iProver_split(sP5_iProver_split,sK3)) = sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_82903,c_81814]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_111296,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3)) = k2_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3)) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_111295,c_77654,c_82904]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_111316,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3)) = k2_xboole_0(sK3,k2_xboole_0(sK5,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_111253,c_111296]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_111317,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,sK5),sK3) = sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_111316,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_116060,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(sK3,sP4_iProver_split(sK5,sP5_iProver_split))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k4_xboole_0(X0,X1))) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_116059,c_75015,c_107492,c_111317]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81376,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),k4_xboole_0(sP4_iProver_split(X0,X1),X2)) = k4_xboole_0(X2,k4_xboole_0(X2,sP4_iProver_split(X0,sP4_iProver_split(X1,X2)))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_81267,c_1]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81749,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),k4_xboole_0(sP4_iProver_split(X0,X1),X2)) = X2 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_81376,c_37461,c_56504]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_5752,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(sK2,sK5))),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1733,c_2298]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_5790,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(sK2,sK5))),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_5752,c_2281]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81438,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,k2_xboole_0(sK2,sK5))),k4_xboole_0(sP4_iProver_split(X0,X1),k2_xboole_0(sK2,sK5))),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_81267,c_5790]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81577,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,k2_xboole_0(sP5_iProver_split,sK5))),k4_xboole_0(sP4_iProver_split(X0,X1),k2_xboole_0(sP5_iProver_split,sK5))),sP4_iProver_split(sK3,sK2)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_81438,c_59877,c_65380,c_65760]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_73249,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK2,sK4)),sK5) = k4_xboole_0(X0,sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_13710,c_49082]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_73861,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,sK2),sK5) = k4_xboole_0(X0,sK5) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_73249,c_52847]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_73862,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(sP5_iProver_split,sK5)) = k4_xboole_0(X0,sK5) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_73861,c_34854,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_73863,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(sK5,sP5_iProver_split)) = k4_xboole_0(X0,sK5) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_73862,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81578,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(sK5,sP5_iProver_split))),k4_xboole_0(sP4_iProver_split(X0,X1),sK5))) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_81577,c_53685,c_61315,c_73863]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81579,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(sP5_iProver_split,sK5))),k4_xboole_0(sP4_iProver_split(X0,X1),sK5))) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_81578,c_74657]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74694,plain,
% 55.01/7.50      ( sP4_iProver_split(k2_xboole_0(sK2,sK5),sP4_iProver_split(k1_xboole_0,X0)) = sP4_iProver_split(X0,k2_xboole_0(sK2,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_2936,c_56206]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_75073,plain,
% 55.01/7.50      ( sP4_iProver_split(k2_xboole_0(sP5_iProver_split,sK5),sP4_iProver_split(sP1_iProver_split,X0)) = sP4_iProver_split(X0,k2_xboole_0(sP5_iProver_split,sK5)) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_74694,c_34016,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72447,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,X1),k4_xboole_0(X0,k2_xboole_0(X2,k2_xboole_0(X3,X0)))) = sP4_iProver_split(X0,X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_6382,c_72427]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2949,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1862,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2955,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_2949,c_960]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53700,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = sP4_iProver_split(X2,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_53685,c_21035]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53742,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,X1),k4_xboole_0(X0,X2)) = sP4_iProver_split(X1,X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_53700,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_73021,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(k1_xboole_0,X1)) = sP4_iProver_split(X1,X0) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_72447,c_2955,c_53742,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_73022,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(sP1_iProver_split,X1)) = sP4_iProver_split(X1,X0) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_73021,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_75074,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(sP4_iProver_split(sP1_iProver_split,X0),sP5_iProver_split)) = sP4_iProver_split(X0,sP4_iProver_split(sK5,sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_75073,c_53685,c_54923,c_73022]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72642,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,X0),X1),X0) = sP4_iProver_split(X0,X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_6382,c_72427]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72880,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sP1_iProver_split,X0),X1) = sP4_iProver_split(X1,X0) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_72642,c_39584]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_75075,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(sP5_iProver_split,X0)) = sP4_iProver_split(X0,sP4_iProver_split(sK5,sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_75074,c_72880,c_72989]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_75139,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(sP5_iProver_split,X0)) = sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK5)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_74657,c_75075]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74743,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(k4_xboole_0(sK2,sK4),X0)) = sP4_iProver_split(X0,sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_13710,c_56206]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74953,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(sK2,X0)) = sP4_iProver_split(X0,sK5) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_74743,c_52847]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74954,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(sP5_iProver_split,X0)) = sP4_iProver_split(X0,sK5) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_74953,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_75145,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK5)) = sP4_iProver_split(X0,sK5) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_75139,c_74954]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81580,plain,
% 55.01/7.50      ( sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,sK5)),k4_xboole_0(sP4_iProver_split(X0,X1),sK5)),sP5_iProver_split)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_81579,c_54100,c_75145]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81753,plain,
% 55.01/7.50      ( sP4_iProver_split(sK3,sP4_iProver_split(sK5,sP5_iProver_split)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_81749,c_81580]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_81770,plain,
% 55.01/7.50      ( sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,sK5)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_81753,c_74657]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_116061,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(sP5_iProver_split,sK3)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k4_xboole_0(X0,X1))) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_116060,c_74657,c_81770]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_117968,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k4_xboole_0(sK3,sK5))),sP4_iProver_split(sK5,X0)) = k4_xboole_0(sK3,sP4_iProver_split(sK5,X0)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_117700,c_9,c_116061,c_117418]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74830,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k4_xboole_0(sK3,X0))) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_56206,c_67465]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_98328,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,sP4_iProver_split(sK5,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,sP1_iProver_split)),X0))) = k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(sK5,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_87355,c_57991]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_98436,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(sK5,X0)) = k4_xboole_0(sK4,sP4_iProver_split(sK5,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_98328,c_87355]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_98437,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK3,sK2),sP4_iProver_split(sK5,X0)) = k4_xboole_0(sK4,sP4_iProver_split(sK5,X0)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_98436,c_59354]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_98438,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sK5,X0)) = k4_xboole_0(sK4,sP4_iProver_split(sK5,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_98437,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_117969,plain,
% 55.01/7.50      ( k4_xboole_0(sK3,sP4_iProver_split(sK5,X0)) = k4_xboole_0(sK4,sP4_iProver_split(sK5,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_117968,c_74830,c_98438]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_116938,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),k4_xboole_0(sK3,sK5)),X0) = k2_xboole_0(sK5,X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_110644,c_115896]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_118735,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,X0) = k2_xboole_0(sK5,X0) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_116938,c_110644]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_151023,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,k4_xboole_0(sK3,sP4_iProver_split(sK5,k4_xboole_0(sK4,X0)))) = X0 ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_33427,c_117418,c_117969,c_118735]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_151136,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k4_xboole_0(sK3,sP4_iProver_split(sK5,k4_xboole_0(sK4,sP5_iProver_split))))),sP4_iProver_split(k4_xboole_0(sK5,sK4),sP5_iProver_split)) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sP4_iProver_split(sK5,k4_xboole_0(sK4,sP5_iProver_split)))))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_151023,c_76125]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_151140,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k4_xboole_0(sK3,sP4_iProver_split(sK5,k4_xboole_0(sK4,sP5_iProver_split))))),sP4_iProver_split(k4_xboole_0(sK5,sK4),sP5_iProver_split)) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_151136,c_151023]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_76128,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sP5_iProver_split,sK3)),sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,sK2))) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,sK2))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_61315,c_76125]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_76296,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,sP5_iProver_split))) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sP5_iProver_split,sP5_iProver_split))) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_76128,c_65380,c_69452]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_72452,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),X1),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),k2_xboole_0(sK3,sK2))) = sP4_iProver_split(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_6412,c_72427]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_73008,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k2_xboole_0(k4_xboole_0(sK5,X0),sP5_iProver_split),X1),k1_xboole_0) = sP4_iProver_split(k2_xboole_0(k4_xboole_0(sK5,X0),sP5_iProver_split),X1) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_72452,c_2939,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68511,plain,
% 55.01/7.50      ( sP4_iProver_split(k1_xboole_0,sP4_iProver_split(X0,X1)) = sP4_iProver_split(sP4_iProver_split(X1,X0),k1_xboole_0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_7,c_68488]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_69252,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,X1),sP1_iProver_split) = sP4_iProver_split(X1,X0) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_68511,c_34016,c_53848]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_73009,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,sP5_iProver_split),k4_xboole_0(sK5,X1)) = sP4_iProver_split(k4_xboole_0(sK5,X1),sP4_iProver_split(X0,sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_73008,c_34016,c_53685,c_54100,c_69252]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_73010,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(k4_xboole_0(sK5,X0),X1)) = sP4_iProver_split(k4_xboole_0(sK5,X0),sP4_iProver_split(X1,sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_73009,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_76297,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP5_iProver_split))) = k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP5_iProver_split))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_76296,c_73010]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_76298,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(k4_xboole_0(sK5,sK4),sP5_iProver_split)) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_76297,c_53801]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_109498,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(k4_xboole_0(sK5,X0),sK2)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),k1_xboole_0)) = k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_2939,c_3129]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_42589,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_0,c_2099]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2091,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_0,c_1761]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2426,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) = k4_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_2091,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_42717,plain,
% 55.01/7.50      ( k4_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_42589,c_2426]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_42725,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(k4_xboole_0(sK5,X0),sK2)) = k4_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_42717,c_2099]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_110067,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sP5_iProver_split),sP1_iProver_split)) = k4_xboole_0(sK3,k2_xboole_0(sP5_iProver_split,k4_xboole_0(sK5,X0))) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_109498,c_34016,c_42725,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_110068,plain,
% 55.01/7.50      ( k4_xboole_0(sK3,k2_xboole_0(sP4_iProver_split(k4_xboole_0(sK5,X0),sK2),k2_xboole_0(k4_xboole_0(sK5,X0),sP5_iProver_split))) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,X0),sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_110067,c_9,c_37461,c_52508,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_110069,plain,
% 55.01/7.50      ( k4_xboole_0(sK3,k2_xboole_0(sP4_iProver_split(k4_xboole_0(sK5,X0),sP5_iProver_split),k2_xboole_0(k4_xboole_0(sK5,X0),sP5_iProver_split))) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,X0),sP5_iProver_split)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_110068,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_110070,plain,
% 55.01/7.50      ( k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,X0),sP4_iProver_split(sP5_iProver_split,k2_xboole_0(k4_xboole_0(sK5,X0),sP5_iProver_split)))) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,X0),sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_110069,c_81806]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_110071,plain,
% 55.01/7.50      ( k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(k4_xboole_0(sK5,X0),k4_xboole_0(sK5,X0)))) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,X0),sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_110070,c_53685,c_54013,c_73010]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_98364,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,sP1_iProver_split),X0) = X0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_87355,c_87355]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_98401,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,X0) = X0 ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_98364,c_37461]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_110072,plain,
% 55.01/7.50      ( k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK5,X0))) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,X0),sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_110071,c_98401]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_49466,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(sP1_iProver_split,X2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_49023,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_49518,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_49466,c_9,c_34425]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74311,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(X1,sP4_iProver_split(X2,k4_xboole_0(X0,X1)))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_49518,c_9,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74312,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(sP4_iProver_split(X1,k4_xboole_0(X0,X2)),X2)) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_74311,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74313,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_74312,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74508,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(X0,sP1_iProver_split),sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2))) = sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_74313,c_1733]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74518,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2)),X0),k4_xboole_0(X0,sP1_iProver_split)) = sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_74313,c_598]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74629,plain,
% 55.01/7.50      ( k2_xboole_0(k4_xboole_0(sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2)),X0),X0) = sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_74518,c_37461]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74630,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2)) = k2_xboole_0(sP4_iProver_split(X1,X2),X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_74629,c_4224,c_74076]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_74631,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2)) = sP4_iProver_split(X0,sP4_iProver_split(X1,X2)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_74630,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_75203,plain,
% 55.01/7.50      ( k2_xboole_0(X0,sP4_iProver_split(X0,sP4_iProver_split(X1,X2))) = sP4_iProver_split(X0,sP4_iProver_split(X1,X2)) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_74508,c_37461,c_74631]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_112025,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(X1,X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_3240,c_3240,c_53685,c_75203,c_81806]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_112026,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,X1),X2) = sP4_iProver_split(X2,sP4_iProver_split(X1,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_112025,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_112167,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),sP4_iProver_split(X3,X0)) = k4_xboole_0(sP4_iProver_split(X2,X1),sP4_iProver_split(X3,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_112026,c_107236]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3435,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK4,sK2)) = k4_xboole_0(sK5,k2_xboole_0(sK4,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3226,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3625,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK4,sK2)) = k4_xboole_0(sK5,k2_xboole_0(sK4,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3452,c_509]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3343,plain,
% 55.01/7.50      ( k2_xboole_0(sK3,k2_xboole_0(sK4,sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_0,c_3233]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3529,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK4,sK2)) = k4_xboole_0(sK3,k2_xboole_0(sK4,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3343,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3644,plain,
% 55.01/7.50      ( k4_xboole_0(sK3,k2_xboole_0(sK4,sK2)) = k4_xboole_0(sK5,k2_xboole_0(sK4,sK2)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_3625,c_3529]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_112872,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),k2_xboole_0(sK4,sP5_iProver_split)) = k4_xboole_0(sK3,k2_xboole_0(sK4,sP5_iProver_split)) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_3435,c_3435,c_3644,c_65380,c_77592]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1446,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK4,X0)) = k4_xboole_0(k4_xboole_0(sK5,sK4),X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1279,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1454,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK4,X0)) = k4_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_1446,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_86470,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK3,sK2),k2_xboole_0(sK4,X0)) = k4_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_1454,c_1454,c_59877]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_86471,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(X0,sK4)) = k4_xboole_0(sK5,sP4_iProver_split(X0,sK4)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_86470,c_53685,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_112873,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,sP4_iProver_split(sP5_iProver_split,sK4)) = k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,sK4)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_112872,c_53685,c_86471]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_148655,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,k4_xboole_0(X1,sP4_iProver_split(X0,X2))) = sP4_iProver_split(X0,k4_xboole_0(X1,X2)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_14690,c_117418]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_148701,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,sK4))) = sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK5,sK4)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_112873,c_148655]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_149099,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK5,sK4)) = sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sK4)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_148701,c_148655]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_151141,plain,
% 55.01/7.50      ( k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sK4))) = k4_xboole_0(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP5_iProver_split)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_151140,c_74830,c_76298,c_110072,c_112167,c_149099]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_153846,plain,
% 55.01/7.50      ( k4_xboole_0(sK3,sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sK4))) = sK4 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_153845,c_149932,c_151141]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_153873,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k4_xboole_0(sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sK4)),k4_xboole_0(sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sK4)),sK3))) = sK3 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_153846,c_598]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_153888,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sK4)),sK3),sK4) = sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sK4)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_153846,c_3755]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1322,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sK5,X0)),X0) = k4_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1044,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1361,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),X0) = k4_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_1322,c_1329]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_126943,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sP5_iProver_split,X0)),X0) = k4_xboole_0(sP4_iProver_split(sK3,sK2),X0) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_1361,c_1361,c_59877,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_126944,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sK3,k2_xboole_0(sP5_iProver_split,X0)),X0) = k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),X0) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_126943,c_2992,c_61315,c_117418]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_105094,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,k4_xboole_0(X1,X2)),X2) = sP4_iProver_split(X2,sP4_iProver_split(X0,X1)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_2570,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_105145,plain,
% 55.01/7.50      ( sP4_iProver_split(k2_xboole_0(sK3,sK2),sP4_iProver_split(X0,k2_xboole_0(sK3,sK2))) = sP4_iProver_split(sP4_iProver_split(X0,sP1_iProver_split),k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_34235,c_105094]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_105828,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sK3,sK2),sP4_iProver_split(X0,sP4_iProver_split(sK3,sK2))) = sP4_iProver_split(sP4_iProver_split(X0,sP1_iProver_split),sP4_iProver_split(sK3,sK2)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_105145,c_59877]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1684,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK4,X1)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_961,c_244]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_16762,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK4,sK5),k2_xboole_0(sK4,k2_xboole_0(X0,sK5))) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1684,c_1684]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_10458,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_6337,c_519]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1951,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)))) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_713,c_1749]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1275,plain,
% 55.01/7.50      ( k2_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_1259,c_715]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1433,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) = k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1275,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1442,plain,
% 55.01/7.50      ( k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_1433,c_1347]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1965,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)))) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_1951,c_1442]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1966,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK3,sK2),sK5) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_1965,c_7,c_1853]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_5136,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,X0)) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1966,c_11]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_1680,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1275,c_244]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_5152,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,X0)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_5136,c_1680,c_1703,c_3970]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_10509,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_10458,c_5152]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_16774,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_16762,c_152,c_2244,c_10509]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_17974,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k2_xboole_0(X1,k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_16774,c_245]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_63503,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(X1,sP4_iProver_split(sK3,sK2))) = k2_xboole_0(X1,k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_17974,c_17974,c_59877]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2260,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1)) = k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1329,c_11]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_63504,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sK3,sK2),X0),sP4_iProver_split(k2_xboole_0(sK2,X1),sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,k2_xboole_0(X1,sK2))) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_63503,c_2260,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_63505,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X0),sP4_iProver_split(k2_xboole_0(sK2,X1),sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,k2_xboole_0(X1,sK2))) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_63504,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_23951,plain,
% 55.01/7.50      ( k4_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_22126,c_9]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56171,plain,
% 55.01/7.50      ( sP4_iProver_split(k1_xboole_0,sP4_iProver_split(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = sP4_iProver_split(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK3) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_23951,c_56078]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56245,plain,
% 55.01/7.50      ( sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(sK3,k2_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = sP4_iProver_split(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK3) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_56171,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56246,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(sK3,k2_xboole_0(sK3,sK2))) = sP4_iProver_split(sK3,sP4_iProver_split(k2_xboole_0(sK3,sK2),X0)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_56245,c_53685,c_53848,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56247,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(sK2,sK3)) = sP4_iProver_split(sP4_iProver_split(X0,sK2),sK3) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_56246,c_53685,c_53801,c_54013,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_63506,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,sP5_iProver_split),sP4_iProver_split(sP4_iProver_split(X1,sP4_iProver_split(sK2,sK3)),sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,X1))) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_63505,c_53685,c_54100,c_56247]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_63507,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,sP5_iProver_split),sP4_iProver_split(sP4_iProver_split(X1,sP4_iProver_split(sK3,sK2)),sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,X1))) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_63506,c_59354]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_63508,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sK3,sK2),sP4_iProver_split(sK3,X0)),X1)) = sP4_iProver_split(sK3,sP4_iProver_split(X1,sP4_iProver_split(sK2,X0))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_63507,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_63509,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sK3,X0)),X1)) = sP4_iProver_split(sK3,sP4_iProver_split(X1,sP4_iProver_split(sK2,X0))) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_63508,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_57032,plain,
% 55.01/7.50      ( k2_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,X3))),k4_xboole_0(X2,sP1_iProver_split)) = sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,X3))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_56983,c_1943]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_57128,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,sP4_iProver_split(X0,X3)))) = sP4_iProver_split(X1,sP4_iProver_split(X2,sP4_iProver_split(X0,X3))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_57032,c_37461,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_63510,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sK3,X0),sP4_iProver_split(X1,sP4_iProver_split(sP5_iProver_split,sK3))) = sP4_iProver_split(sK3,sP4_iProver_split(X1,sP4_iProver_split(sK2,X0))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_63509,c_54100,c_57128]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_63512,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3))) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,sK2))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_61315,c_63510]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_82130,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(k2_xboole_0(X1,X0),X2)) = sP4_iProver_split(sP4_iProver_split(X2,k1_xboole_0),k2_xboole_0(X1,X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1862,c_82099]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53755,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(X1,k2_xboole_0(X0,X2))) = sP4_iProver_split(X1,k2_xboole_0(X0,X2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3755,c_53745]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_53989,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,X0))) = sP4_iProver_split(X1,sP4_iProver_split(X2,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_53755,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_82862,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,sP1_iProver_split),sP4_iProver_split(X1,X2)) = sP4_iProver_split(X2,sP4_iProver_split(X0,X1)) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_82130,c_34016,c_53685,c_53989,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_105829,plain,
% 55.01/7.50      ( sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,sK2))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_105828,c_54100,c_61315,c_63512,c_65380,c_82862]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_16204,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK5,k2_xboole_0(X0,X1)),k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2)))) = k2_xboole_0(k2_xboole_0(sK5,k2_xboole_0(X0,X1)),sK4) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_16088,c_519]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_16352,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK5,k2_xboole_0(X0,X1)),k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2)))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_16204,c_1259,c_3970,c_5782]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68336,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK5,k2_xboole_0(X0,X1)),k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sP5_iProver_split)))) = k2_xboole_0(sK3,k2_xboole_0(sP5_iProver_split,k2_xboole_0(X0,X1))) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_16352,c_16352,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68337,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k2_xboole_0(sK3,k2_xboole_0(X0,sP5_iProver_split)),X1),sP4_iProver_split(k2_xboole_0(X1,X0),sK5)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,k2_xboole_0(X1,X0))) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_68336,c_3970,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68338,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k2_xboole_0(sK3,k2_xboole_0(X0,sP5_iProver_split)),X1),sP4_iProver_split(sP4_iProver_split(X0,X1),sK5)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,X1))) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_68337,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68339,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,k2_xboole_0(X1,sP5_iProver_split)),sP4_iProver_split(sP4_iProver_split(X0,sP4_iProver_split(sK5,X1)),sK3)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X1,X0))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_68338,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68340,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,X0),sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sK5,X0),sP4_iProver_split(sK3,X1)),X1)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,X1))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_68339,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68341,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sK3,X1),sP4_iProver_split(X1,sP4_iProver_split(sK5,X0))),sP5_iProver_split)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,X1))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_68340,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68342,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(X1,sP4_iProver_split(sK5,X0)),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X1)))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,X1))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_68341,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68343,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(sK5,X0),sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X1)),X1))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,X1))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_68342,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68344,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0)),X0),X1)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X1,X0))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_68343,c_53989,c_54923]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68345,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X1,X0))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_68344,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56547,plain,
% 55.01/7.50      ( k2_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,X3))),k4_xboole_0(X3,sP1_iProver_split)) = sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,X3))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_56497,c_1943]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56643,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,sP4_iProver_split(X3,X0)))) = sP4_iProver_split(X1,sP4_iProver_split(X2,sP4_iProver_split(X3,X0))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_56547,c_37461,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68346,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X1)))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,X1))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_68345,c_56643]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68354,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(k4_xboole_0(sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(sK4,X1)),sK2),X2),sK2)))) = sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK2,sK3)))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_57636,c_68346]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_63513,plain,
% 55.01/7.50      ( sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,sP4_iProver_split(k4_xboole_0(sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(sK4,X1)),sK2),X2),sK2)))) = sP4_iProver_split(sP4_iProver_split(sK2,sK3),sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_57636,c_63510]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_63569,plain,
% 55.01/7.50      ( sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,sP4_iProver_split(k4_xboole_0(sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(sK4,X1)),sK2),X2),sK2)))) = sP4_iProver_split(sP4_iProver_split(sK3,sK2),sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3))) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_63513,c_59354]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_63570,plain,
% 55.01/7.50      ( sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(k4_xboole_0(sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(sK4,X1)),sK2),X2),sK2))) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,sK2))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_63569,c_53801,c_63510]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68415,plain,
% 55.01/7.50      ( sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sK2)))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,sK2)))) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_68354,c_59354,c_63570]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_63521,plain,
% 55.01/7.50      ( sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sK2,sK5),sP4_iProver_split(sK2,X0))) = sP4_iProver_split(sP4_iProver_split(sK3,X0),sP4_iProver_split(sP5_iProver_split,sK3)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_63316,c_63510]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56096,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,k2_xboole_0(X1,X2)),sP4_iProver_split(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2))) = sP4_iProver_split(k2_xboole_0(X1,X2),k2_xboole_0(X0,X1)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_625,c_56078]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56402,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(X0,X1),X2)) = sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(X2,X0),X0),X1) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_56096,c_53685,c_54100,c_54151]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56403,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(X0,X1),X1),X2) = sP4_iProver_split(X2,sP4_iProver_split(X0,X1)) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_56402,c_53989,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_56404,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,X1),sP4_iProver_split(X2,X0)) = sP4_iProver_split(X2,sP4_iProver_split(X1,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_56403,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_63541,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sK2)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_63521,c_54151,c_56404]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68416,plain,
% 55.01/7.50      ( sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sP5_iProver_split))) = sP4_iProver_split(sP4_iProver_split(X0,sK3),sP5_iProver_split) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_68415,c_54013,c_57128,c_63541,c_65380,c_68346]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_68417,plain,
% 55.01/7.50      ( sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sP5_iProver_split))) = sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,X0)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_68416,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_105830,plain,
% 55.01/7.50      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,X0)) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_105829,c_65380,c_68417]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_126945,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)),X0) = k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),X0) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_126944,c_105830,c_117418]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_127092,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0)),sK3)),sP4_iProver_split(k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))),sK4)) = k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0)),sK3)),sK4))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_126945,c_76781]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_105138,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,k4_xboole_0(X1,k2_xboole_0(X2,X3))),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)) = sP4_iProver_split(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),sP4_iProver_split(X0,X1)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_696,c_105094]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_105855,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,X2)),sP4_iProver_split(sP4_iProver_split(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))),X3)) = sP4_iProver_split(k4_xboole_0(X0,k4_xboole_0(X0,X2)),sP4_iProver_split(sP4_iProver_split(X3,X0),X1)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_105138,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_82224,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,k4_xboole_0(X1,X2)),sP4_iProver_split(X1,X3)) = sP4_iProver_split(sP4_iProver_split(X3,k4_xboole_0(X0,X1)),X1) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_49082,c_82099]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_82492,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,k4_xboole_0(X1,X2)),sP4_iProver_split(X1,X3)) = sP4_iProver_split(X0,sP4_iProver_split(X1,X3)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_82224,c_82099]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_82138,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(X0,k4_xboole_0(X1,k2_xboole_0(X2,X3))),k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)) = sP4_iProver_split(X1,sP4_iProver_split(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),X0)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_696,c_82099]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_82838,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,X2)),sP4_iProver_split(sP4_iProver_split(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))),X3)) = sP4_iProver_split(sP4_iProver_split(X3,X1),X0) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_82138,c_53685,c_54100,c_56206]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_82839,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,X2)),sP4_iProver_split(k4_xboole_0(X0,k4_xboole_0(X0,X2)),sP4_iProver_split(X3,X1))) = sP4_iProver_split(X1,sP4_iProver_split(X0,X3)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_82838,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_105856,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(X0,sP4_iProver_split(X1,X2))) = sP4_iProver_split(X1,sP4_iProver_split(X0,X2)) ),
% 55.01/7.50      inference(demodulation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_105855,c_54100,c_82492,c_82839]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_23957,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k4_xboole_0(k4_xboole_0(sK3,X0),sK5)) = k2_xboole_0(sK4,k1_xboole_0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_22126,c_14703]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_23965,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k4_xboole_0(sK3,k2_xboole_0(X0,sK5))) = sK4 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_23957,c_9,c_518]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_25926,plain,
% 55.01/7.50      ( k2_xboole_0(sK4,k4_xboole_0(sK3,k2_xboole_0(X0,k2_xboole_0(X1,sK5)))) = sK4 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_11,c_23965]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_60821,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(k2_xboole_0(X0,sK5),X1)),sK4) = sK4 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_25926,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_60822,plain,
% 55.01/7.50      ( sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(sK5,sP4_iProver_split(X0,X1))),sK4) = sK4 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_60821,c_53685,c_54923]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_117597,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP4_iProver_split(sK5,sP4_iProver_split(X0,X1)),sK3),sK4) = k4_xboole_0(sP4_iProver_split(sK5,sP4_iProver_split(X0,X1)),sK4) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_60822,c_117523]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_111260,plain,
% 55.01/7.50      ( k2_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_110883,c_245]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_111309,plain,
% 55.01/7.50      ( sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK5)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_111260,c_111296]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_111310,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(sK5,X0),sK3) = sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_111309,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_118257,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP4_iProver_split(X0,X1),sP4_iProver_split(sP5_iProver_split,sK3)),sK4) = k4_xboole_0(sP4_iProver_split(sK5,sP4_iProver_split(X0,X1)),sK4) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_117597,c_111310]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_118258,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X1)),sK4) = k4_xboole_0(sP4_iProver_split(sK5,sP4_iProver_split(X0,X1)),sK4) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_118257,c_107492]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_110796,plain,
% 55.01/7.50      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sK5),X0),sK5) = sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X0) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_110644,c_72427]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_12500,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2)))) = k4_xboole_0(k2_xboole_0(sK4,X1),k4_xboole_0(k2_xboole_0(sK4,X1),k4_xboole_0(X0,sK5))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1674,c_616]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_77666,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(X0,k2_xboole_0(X1,sP4_iProver_split(sK3,sK2)))) = k4_xboole_0(k2_xboole_0(sK4,X1),k4_xboole_0(k2_xboole_0(sK4,X1),k4_xboole_0(X0,sK5))) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_12500,c_59877]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_77667,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(sK5,k4_xboole_0(X0,sP4_iProver_split(sP4_iProver_split(sK3,sK2),X1)))) = k4_xboole_0(sP4_iProver_split(X1,sK4),k4_xboole_0(sP4_iProver_split(X1,sK4),k4_xboole_0(X0,sK5))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_77666,c_9,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_77668,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(sK5,k4_xboole_0(X0,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X1)))) = k4_xboole_0(sP4_iProver_split(X1,sK4),k4_xboole_0(sP4_iProver_split(X1,sK4),k4_xboole_0(X0,sK5))) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_77667,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_77669,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X1)),sK5)) = k4_xboole_0(sP4_iProver_split(X1,sK4),k4_xboole_0(sP4_iProver_split(X1,sK4),k4_xboole_0(X0,sK5))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_77668,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_77670,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(sK3,sP4_iProver_split(X1,sP5_iProver_split))),sK5)) = k4_xboole_0(sP4_iProver_split(X1,sK4),k4_xboole_0(sP4_iProver_split(X1,sK4),k4_xboole_0(X0,sK5))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_77669,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_77671,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X1))),sK5)) = k4_xboole_0(sP4_iProver_split(X1,sK4),k4_xboole_0(sP4_iProver_split(X1,sK4),k4_xboole_0(X0,sK5))) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_77670,c_67465]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_77710,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK3,sK2),sP4_iProver_split(k4_xboole_0(k2_xboole_0(sK3,sK2),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))),sK5)) = k4_xboole_0(sP4_iProver_split(X0,sK4),k4_xboole_0(sP4_iProver_split(X0,sK4),k4_xboole_0(sK4,sK5))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_512,c_77671]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_77846,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(X0,k2_xboole_0(sK5,sP4_iProver_split(X1,sK4)))) = k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X1))),sK5)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_77671,c_616]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_77870,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X1))),sK5)) = k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X0,sP4_iProver_split(X1,sK4)),sK5)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_77846,c_17153,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_77713,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK4,sK2),sP4_iProver_split(k4_xboole_0(k2_xboole_0(sK4,sK2),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))),sK5)) = k4_xboole_0(sP4_iProver_split(X0,sK4),k4_xboole_0(sP4_iProver_split(X0,sK4),k4_xboole_0(sK4,sK5))) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_3643,c_77671]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_78154,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK4,sP5_iProver_split),sP4_iProver_split(k4_xboole_0(k2_xboole_0(sK4,sP5_iProver_split),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))),sK5)) = k4_xboole_0(sP4_iProver_split(X0,sK4),k4_xboole_0(sP4_iProver_split(X0,sK4),k4_xboole_0(sK4,sK5))) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_77713,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_63169,plain,
% 55.01/7.50      ( sP4_iProver_split(sP1_iProver_split,sK5) = sK5 ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_63041,c_58210]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_11579,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),X0),k2_xboole_0(sK3,sK2)) = k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_7838,c_8]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_11628,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),X0),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_11579,c_9,c_1862,c_3028]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_43342,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),X0),k2_xboole_0(sK3,sK2)) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_11628,c_11628,c_34016]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_43371,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK4,sK2),X0),k2_xboole_0(sK3,sK2)) = sP1_iProver_split ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_0,c_43342]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_69493,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK4,sP5_iProver_split),X0),sP4_iProver_split(sK3,sK2)) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_43371,c_43371,c_59877,c_65380]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_69494,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK4),k2_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_69493,c_9,c_53685,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_69495,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK4),sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X0)) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_69494,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_69496,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK4),sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_69495,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_69497,plain,
% 55.01/7.50      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK4),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_69496,c_67465]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_32558,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(sK5,k4_xboole_0(X0,sK4))))) = k4_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_14697,c_6382]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_70430,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(X0,sP4_iProver_split(sK3,sK2)),k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(sK5,k4_xboole_0(X0,sK4))))) = k4_xboole_0(X0,sP4_iProver_split(sK3,sK2)) ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_32558,c_32558,c_59877]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_70431,plain,
% 55.01/7.50      ( k4_xboole_0(X0,k2_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),k4_xboole_0(X1,sP4_iProver_split(k2_xboole_0(sK5,k4_xboole_0(X0,sK4)),X2)))) = k4_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_70430,c_9,c_53685,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_70432,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X1,sP4_iProver_split(k2_xboole_0(sK5,k4_xboole_0(X0,sK4)),X2)),sP4_iProver_split(sP5_iProver_split,sK3))) = k4_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_70431,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_70433,plain,
% 55.01/7.50      ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X1,sP4_iProver_split(sK5,sP4_iProver_split(X2,k4_xboole_0(X0,sK4)))),sP4_iProver_split(sP5_iProver_split,sK3))) = k4_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3)) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_70432,c_53685,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2100,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK5,X0),sK2),k2_xboole_0(sK3,X1)) = k2_xboole_0(X1,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1761,c_244]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3006,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK5) = k4_xboole_0(k2_xboole_0(sK4,X0),sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1674,c_509]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_20265,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)),sK5) = k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK3,sK2)),sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_2100,c_3006]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3812,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,sK5)),k1_xboole_0) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_2936,c_3755]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_2615,plain,
% 55.01/7.50      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,sK5)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_1275,c_245]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_3829,plain,
% 55.01/7.50      ( k2_xboole_0(sK2,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_3812,c_7,c_2615]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_20312,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK5,X0),sK2)),sK5) = k4_xboole_0(sK4,sK5) ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_20265,c_512,c_3829]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_70517,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sP5_iProver_split,sK3)),sK2)),sK5) = k4_xboole_0(sK4,sK5) ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_70433,c_20312]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_37807,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK5,sK2),X0),k2_xboole_0(sK3,sK2)) = sP1_iProver_split ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_0,c_37775]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_65786,plain,
% 55.01/7.50      ( k4_xboole_0(k4_xboole_0(sK5,X0),sP4_iProver_split(sK3,sK2)) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,
% 55.01/7.50                [status(thm)],
% 55.01/7.50                [c_37807,c_37807,c_49910,c_59877]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_65787,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,k2_xboole_0(X0,sP4_iProver_split(sP5_iProver_split,sK3))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_65786,c_37615,c_61315]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_65788,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X0)) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_65787,c_53685]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_65789,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split))) = sP1_iProver_split ),
% 55.01/7.50      inference(demodulation,[status(thm)],[c_65788,c_54100]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_66838,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,sP4_iProver_split(sK3,sP5_iProver_split)) = sP1_iProver_split ),
% 55.01/7.50      inference(superposition,[status(thm)],[c_66819,c_65789]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_66845,plain,
% 55.01/7.50      ( k4_xboole_0(sK5,sP4_iProver_split(sP5_iProver_split,sK3)) = sP1_iProver_split ),
% 55.01/7.50      inference(light_normalisation,[status(thm)],[c_66838,c_65760]) ).
% 55.01/7.50  
% 55.01/7.50  cnf(c_71206,plain,
% 55.01/7.50      ( k4_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sP1_iProver_split,sP5_iProver_split)),sK5) = k4_xboole_0(sK4,sK5) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_70517,c_65380,c_66845]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_71207,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(k2_xboole_0(sP1_iProver_split,sP5_iProver_split),sK4),sK5) = k4_xboole_0(sK4,sK5) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_71206,c_53685]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_71208,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK4),sK5) = k4_xboole_0(sK4,sK5) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_71207,c_35092]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_78155,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(X0,sK4),k4_xboole_0(sP4_iProver_split(X0,sK4),k4_xboole_0(sK4,sK5))) = k4_xboole_0(sK4,sK5) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_78154,c_53685,c_63169,c_69497,c_71208]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_78182,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sK3,sK2),sP4_iProver_split(k4_xboole_0(k2_xboole_0(sK3,sK2),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))),sK5)) = k4_xboole_0(sK4,sK5) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_77710,c_77870,c_78155]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_78183,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(sK3,sK2),sP4_iProver_split(k4_xboole_0(sP4_iProver_split(sK3,sK2),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))),sK5)) = k4_xboole_0(sK4,sK5) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_78182,c_59877]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_74331,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(X0,X1),sP4_iProver_split(k4_xboole_0(X1,X0),sP4_iProver_split(X0,X2))) = sP1_iProver_split ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_509,c_74313]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_75599,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(X0,X1),sP4_iProver_split(X0,sP4_iProver_split(X1,X2))) = sP1_iProver_split ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_74331,c_53685,c_74631]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_78184,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sK5) = k4_xboole_0(sK4,sK5) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_78183,c_61315,c_63169,c_75599]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_759,plain,
% 55.01/7.51      ( k2_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(sK3,sK2))),k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(sK3,sK2))))) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_713,c_153]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_708,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5))) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK5) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_512,c_10]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_718,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)))) = k4_xboole_0(sK4,sK5) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_708,c_512,c_713]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_763,plain,
% 55.01/7.51      ( k2_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(sK3,sK2))),k4_xboole_0(sK4,sK5)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_759,c_718]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_965,plain,
% 55.01/7.51      ( k2_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(sK3,sK2))),k2_xboole_0(X0,k4_xboole_0(sK4,sK5))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_763,c_243]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_46141,plain,
% 55.01/7.51      ( k4_xboole_0(k4_xboole_0(sK5,sK3),k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK5,sK3)),sK2)) = k1_xboole_0 ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_12841,c_2909]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_46177,plain,
% 55.01/7.51      ( k4_xboole_0(k4_xboole_0(sK5,sK3),k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK5,sK3)),sK2)) = sP1_iProver_split ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_46141,c_34016]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_46178,plain,
% 55.01/7.51      ( k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = sP1_iProver_split ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_46177,c_505,c_37615]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_86419,plain,
% 55.01/7.51      ( k2_xboole_0(sK5,k2_xboole_0(X0,k4_xboole_0(sK4,sK5))) = k2_xboole_0(X0,sP4_iProver_split(sK3,sK2)) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_965,c_965,c_39054,c_46178,c_59877]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_86420,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK4,sK5),X0),sK5) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_86419,c_53685,c_54100,c_61315]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_86421,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK4,sK5),X0),sK5) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0)) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_86420,c_67465]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_110909,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0)) = sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X0) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_110796,c_78184,c_86421]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_118259,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X1))),sK4) = k4_xboole_0(sP4_iProver_split(sK5,sP4_iProver_split(X0,X1)),sK4) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_118258,c_110909]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_116942,plain,
% 55.01/7.51      ( sP4_iProver_split(k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sP1_iProver_split,k4_xboole_0(sK5,sK4))),X0) = k2_xboole_0(sK4,X0) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_62059,c_115896]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_118730,plain,
% 55.01/7.51      ( sP4_iProver_split(sK4,X0) = k2_xboole_0(sK4,X0) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_116942,c_62059]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_120099,plain,
% 55.01/7.51      ( sP4_iProver_split(k4_xboole_0(X0,X1),sK4) = sP4_iProver_split(sK4,k4_xboole_0(X0,X1)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_118730,c_114564]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_1330,plain,
% 55.01/7.51      ( k2_xboole_0(X0,k2_xboole_0(sK4,k2_xboole_0(sK5,X1))) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,X1)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_1044,c_243]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_1359,plain,
% 55.01/7.51      ( k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,X1))) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,X1)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_1330,c_1329]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_1256,plain,
% 55.01/7.51      ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(X1,sK5))) = k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_961,c_243]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_14332,plain,
% 55.01/7.51      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,X1)) = k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(X1,sK5))) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_1256,c_245]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_2638,plain,
% 55.01/7.51      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) = k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(X1,sK5))) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_245,c_1329]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_14397,plain,
% 55.01/7.51      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,X1)) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_14332,c_2638]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_126238,plain,
% 55.01/7.51      ( k2_xboole_0(sP4_iProver_split(sK3,sK2),sP4_iProver_split(X0,X1)) = k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sP5_iProver_split,X1))) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_1359,c_14397,c_59877,c_65380,c_117418]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_105333,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,k4_xboole_0(X1,sP5_iProver_split)))) = sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,X1))) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_105094,c_67465]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_82299,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,k4_xboole_0(X1,sP5_iProver_split)))) = sP4_iProver_split(sK3,sP4_iProver_split(X1,sP4_iProver_split(sP5_iProver_split,X0))) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_82099,c_67465]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_17970,plain,
% 55.01/7.51      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,X1)))) = k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2))) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_16774,c_243]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_62619,plain,
% 55.01/7.51      ( k2_xboole_0(sP4_iProver_split(sK3,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,X1)))) = k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK2))) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_17970,c_17970,c_59877]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_62620,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),X1),sP4_iProver_split(sP5_iProver_split,sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(X1,k2_xboole_0(X0,sK2))) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_62619,c_53685,c_54100,c_61315]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_62621,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sP4_iProver_split(X0,k2_xboole_0(sK2,X1)),sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,X1))) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_62620,c_53685,c_54100,c_56404]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_62622,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(k2_xboole_0(sK2,X0),sP4_iProver_split(sK3,X1))) = sP4_iProver_split(sK3,sP4_iProver_split(X1,sP4_iProver_split(sK2,X0))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_62621,c_54100]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_62623,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK2,sP4_iProver_split(sP4_iProver_split(sK3,X0),X1))) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,X1))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_62622,c_53685,c_54100]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_62624,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK2,sP4_iProver_split(X0,sP4_iProver_split(X1,sK3)))) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,X1))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_62623,c_54100]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_963,plain,
% 55.01/7.51      ( k2_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK5,sK4)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_715,c_243]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_1282,plain,
% 55.01/7.51      ( k2_xboole_0(sK5,k2_xboole_0(X0,sK4)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_1259,c_243]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_4142,plain,
% 55.01/7.51      ( k2_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k2_xboole_0(X0,sK4),sK5) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_1282,c_1672]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_1046,plain,
% 55.01/7.51      ( k2_xboole_0(sK5,k2_xboole_0(k2_xboole_0(sK3,sK2),X0)) = k2_xboole_0(k2_xboole_0(sK5,sK4),X0) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_715,c_11]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_1055,plain,
% 55.01/7.51      ( k2_xboole_0(sK5,k2_xboole_0(sK4,k2_xboole_0(sK5,X0))) = k2_xboole_0(k2_xboole_0(sK5,sK4),X0) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_1044,c_1046]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_2437,plain,
% 55.01/7.51      ( k2_xboole_0(sK5,k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_1055,c_1055,c_1259,c_1525]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_2441,plain,
% 55.01/7.51      ( k2_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_243,c_2437]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_4205,plain,
% 55.01/7.51      ( k2_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_4142,c_2244,c_2441,c_3970]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_78990,plain,
% 55.01/7.51      ( k2_xboole_0(sK5,k2_xboole_0(X0,sP4_iProver_split(sK3,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_963,c_1259,c_4205,c_59877]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_78991,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sK3,sK2),X0),sK5) = sP4_iProver_split(sK2,sP4_iProver_split(X0,sK3)) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_78990,c_53685,c_54100,c_59877]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_53297,plain,
% 55.01/7.51      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK3)) = k2_xboole_0(sK3,X0) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_23951,c_21035]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_54791,plain,
% 55.01/7.51      ( k2_xboole_0(sP1_iProver_split,k2_xboole_0(X0,sK3)) = k2_xboole_0(sK3,X0) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_53297,c_34016]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_54792,plain,
% 55.01/7.51      ( sP4_iProver_split(sK3,X0) = sP4_iProver_split(X0,sK3) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_54791,c_35092,c_53685]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_26782,plain,
% 55.01/7.51      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK4,X0),sK2),k2_xboole_0(X1,sK3)) = k2_xboole_0(X1,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_26587,c_245]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_53480,plain,
% 55.01/7.51      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK3),X1),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k2_xboole_0(X0,sK3),k2_xboole_0(k4_xboole_0(sK4,X2),sK2)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_26782,c_21035]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_37050,plain,
% 55.01/7.51      ( k2_xboole_0(k2_xboole_0(X0,sK3),k2_xboole_0(k4_xboole_0(sK4,X1),sK2)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_26782,c_0]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_54224,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(sK2,X0),sK3) = sP4_iProver_split(sP4_iProver_split(sK2,sK3),X0) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_53480,c_21328,c_37050,c_53685]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_54638,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(sK3,sK2),X0) = sP4_iProver_split(sP4_iProver_split(sK2,X0),sK3) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_54587,c_54224]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_54718,plain,
% 55.01/7.51      ( sP4_iProver_split(sK2,sP4_iProver_split(X0,sK3)) = sP4_iProver_split(sP4_iProver_split(sK2,X0),sK3) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_54638,c_54100]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_54795,plain,
% 55.01/7.51      ( sP4_iProver_split(sK2,sP4_iProver_split(X0,sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(sK2,X0)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_54792,c_54718]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_78992,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X0),sK5) = sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,X0)) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_78991,c_54795,c_61315,c_65380]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_65792,plain,
% 55.01/7.51      ( sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(sK5,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)))) = sP4_iProver_split(sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)),sK5) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_65789,c_56078]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_65825,plain,
% 55.01/7.51      ( k2_xboole_0(sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)),sP1_iProver_split) = k2_xboole_0(sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)),sK5) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_65789,c_6]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_35091,plain,
% 55.01/7.51      ( k2_xboole_0(X0,sP1_iProver_split) = X0 ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_34829,c_1749]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_65852,plain,
% 55.01/7.51      ( sP4_iProver_split(sK5,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split))) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_65825,c_35091,c_53685]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_65879,plain,
% 55.01/7.51      ( sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split))) = sP4_iProver_split(sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)),sK5) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_65792,c_65852]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_65880,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)),sK5) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_65879,c_53848,c_54100]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_78993,plain,
% 55.01/7.51      ( sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,X0)) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_78992,c_54100,c_65880,c_75015]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_78994,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0)) = sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,X0)) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_78993,c_67465]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_78999,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(sK2,sP4_iProver_split(X0,sP4_iProver_split(X1,sK3))))) = sP4_iProver_split(sK3,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK2,X1)))) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_62624,c_78994]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_79096,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sP4_iProver_split(X1,sK3))))) = sP4_iProver_split(sK3,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,X1)))) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_78999,c_65380]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_68512,plain,
% 55.01/7.51      ( sP4_iProver_split(X0,sP4_iProver_split(X1,k2_xboole_0(X2,X0))) = sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X2,X0),X1),X0) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_8,c_68488]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_69250,plain,
% 55.01/7.51      ( sP4_iProver_split(X0,sP4_iProver_split(X1,k2_xboole_0(X2,X0))) = sP4_iProver_split(X0,sP4_iProver_split(X1,X2)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_68512,c_68488]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_69251,plain,
% 55.01/7.51      ( sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(X0,X2))) = sP4_iProver_split(X0,sP4_iProver_split(X1,X2)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_69250,c_53685]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_74520,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2)),X0),sP1_iProver_split) = sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(X1,X2)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_74313,c_3755]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_75191,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,X2)),X0),sP1_iProver_split) = sP4_iProver_split(X0,sP4_iProver_split(X1,X2)) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_74520,c_74631]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_56549,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,X3))),sP1_iProver_split) = sP4_iProver_split(X0,sP4_iProver_split(X1,sP4_iProver_split(X2,X3))) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_56497,c_3026]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_75192,plain,
% 55.01/7.51      ( sP4_iProver_split(X0,sP4_iProver_split(X0,sP4_iProver_split(X1,X2))) = sP4_iProver_split(X0,sP4_iProver_split(X1,X2)) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_75191,c_37461,c_53685,c_56549]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_79097,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sP4_iProver_split(X1,sK3))) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,X1))) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_79096,c_53989,c_69251,c_75192]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_82323,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,k4_xboole_0(X1,sP5_iProver_split)))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X1,sP4_iProver_split(X0,sK3))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_82299,c_79097]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_105361,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sP4_iProver_split(X1,sK3))) = sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X1,X0))) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_105333,c_82323]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_126239,plain,
% 55.01/7.51      ( sP4_iProver_split(X0,sP4_iProver_split(sK3,k2_xboole_0(sP5_iProver_split,X1))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X1,sP4_iProver_split(X0,sK3))) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_126238,c_65380,c_81806,c_105361,c_117418]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_126240,plain,
% 55.01/7.51      ( sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X1,sK3))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X1,sP4_iProver_split(X0,sK3))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_126239,c_105830,c_117418]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_126320,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(X0,sK3),sP5_iProver_split),X1) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sP4_iProver_split(X1,sK3))) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_126240,c_112026]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_70518,plain,
% 55.01/7.51      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sP4_iProver_split(sP5_iProver_split,sK3)),sK2),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_70433,c_2100]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_71203,plain,
% 55.01/7.51      ( k2_xboole_0(k2_xboole_0(sP1_iProver_split,sP5_iProver_split),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,sP4_iProver_split(sK3,sK2)) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_70518,c_59877,c_65380,c_66845]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_71204,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(X0,sK3),sP5_iProver_split) = sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_71203,c_3970,c_35092,c_53685,c_54100,c_61315]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_71205,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(X0,sK3),sP5_iProver_split) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0)) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_71204,c_67465]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_126568,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0)),X1) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sP4_iProver_split(X1,sK3))) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_126320,c_71205]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_127105,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sK3))),sP4_iProver_split(sK4,k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))))) = k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sP4_iProver_split(sK5,sP4_iProver_split(X0,sK3)),sK4))) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_127092,c_105856,c_118259,c_120099,c_126568]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_3636,plain,
% 55.01/7.51      ( k2_xboole_0(sK4,k2_xboole_0(sK2,sK5)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_3452,c_11]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_12521,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sK2,sK5),k4_xboole_0(k2_xboole_0(sK2,sK5),k4_xboole_0(X0,sK4))) = k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_3636,c_616]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_12808,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sK2,sK5),k4_xboole_0(k2_xboole_0(sK2,sK5),k4_xboole_0(X0,sK4))) = k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_12475,c_12521]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_58404,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(sK5,sK2),k4_xboole_0(sP4_iProver_split(sK5,sK2),k4_xboole_0(X0,sK4))) = k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_12808,c_53685]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_17100,plain,
% 55.01/7.51      ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK5,X1))),sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_16936,c_1761]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_58473,plain,
% 55.01/7.51      ( k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))),sK2)) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_58404,c_17100]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_58474,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(sK2,k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)))),sK3) = sP4_iProver_split(sK2,sK3) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_58473,c_1761,c_53685]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_53298,plain,
% 55.01/7.51      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(sK5,X1))) = k2_xboole_0(k4_xboole_0(sK5,X1),X0) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_24125,c_21035]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_54786,plain,
% 55.01/7.51      ( k2_xboole_0(sP1_iProver_split,k2_xboole_0(X0,k4_xboole_0(sK5,X1))) = k2_xboole_0(k4_xboole_0(sK5,X1),X0) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_53298,c_34016]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_54787,plain,
% 55.01/7.51      ( sP4_iProver_split(k4_xboole_0(sK5,X0),X1) = sP4_iProver_split(X1,k4_xboole_0(sK5,X0)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_54786,c_35092,c_53685]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_8692,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK4),X0)),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_8615,c_1862]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_31542,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK4),X0)),k2_xboole_0(k2_xboole_0(k4_xboole_0(k4_xboole_0(sK5,sK4),X1),X0),k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_1955,c_8692]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_16137,plain,
% 55.01/7.51      ( k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(X1,sK5))))) = k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(sK3,sK2)),sK2))) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_1256,c_16088]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_14329,plain,
% 55.01/7.51      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,X1)) = k2_xboole_0(sK4,k2_xboole_0(X1,k2_xboole_0(X0,sK5))) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_1256,c_244]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_14400,plain,
% 55.01/7.51      ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(X1,sK5))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X1,X0))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_14329,c_14397]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_16427,plain,
% 55.01/7.51      ( k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))))) = k2_xboole_0(X1,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK2))) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_16137,c_14400]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_2444,plain,
% 55.01/7.51      ( k2_xboole_0(sK5,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_0,c_2437]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_7789,plain,
% 55.01/7.51      ( k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(X0,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_245,c_3353]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_16428,plain,
% 55.01/7.51      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK5,X1),k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X1,X0))) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_16427,c_1512,c_1525,c_2444,c_7789]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_4139,plain,
% 55.01/7.51      ( k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(k2_xboole_0(sK5,X0),sK4) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_1329,c_1672]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_4208,plain,
% 55.01/7.51      ( k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_4139,c_1259,c_3970]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_1326,plain,
% 55.01/7.51      ( k2_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_1044,c_6]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_14516,plain,
% 55.01/7.51      ( k2_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_1326,c_1703,c_3970]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_14520,plain,
% 55.01/7.51      ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK2)) = k2_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_8,c_14516]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_14588,plain,
% 55.01/7.51      ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK2)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_14520,c_14516]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_14589,plain,
% 55.01/7.51      ( k2_xboole_0(k2_xboole_0(sK5,X0),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_14588,c_1512,c_7789]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_16429,plain,
% 55.01/7.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sK3,sK2)) = k2_xboole_0(X1,k2_xboole_0(sK3,k2_xboole_0(X0,sK2))) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_16428,c_4208,c_14397,c_14589]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_23154,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_11,c_625]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_31696,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK5,sK4)),k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(k4_xboole_0(sK5,sK4),X1),sK2)))) = k1_xboole_0 ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_31542,c_16429,c_23154]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_31697,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK5,sK4)),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_31696,c_9,c_1761]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_53305,plain,
% 55.01/7.51      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(sK5,sK4)))) = k2_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK5,sK4)),X0) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_31697,c_21035]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_54756,plain,
% 55.01/7.51      ( k2_xboole_0(sP1_iProver_split,k2_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(sK5,sK4)))) = k2_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK5,sK4)),X0) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_53305,c_34016]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_54757,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(X0,sK2),k4_xboole_0(sK5,sK4)) = sP4_iProver_split(k2_xboole_0(sK2,k4_xboole_0(sK5,sK4)),X0) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_54756,c_3970,c_35092,c_53685]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_54758,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(X0,sK2),k4_xboole_0(sK5,sK4)) = sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK5,sK4),sK2),X0) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_54757,c_53685]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_54788,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(sK2,k4_xboole_0(sK5,sK4)),X0) = sP4_iProver_split(sP4_iProver_split(X0,sK2),k4_xboole_0(sK5,sK4)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_54787,c_54758]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_54790,plain,
% 55.01/7.51      ( sP4_iProver_split(sK2,sP4_iProver_split(k4_xboole_0(sK5,sK4),X0)) = sP4_iProver_split(sP4_iProver_split(sK2,k4_xboole_0(sK5,sK4)),X0) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_54788,c_54100]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_58475,plain,
% 55.01/7.51      ( sP4_iProver_split(sK2,sP4_iProver_split(k4_xboole_0(sK5,sK4),sK3)) = sP4_iProver_split(sK2,sK3) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_58474,c_10,c_54100,c_54790]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_76096,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(k4_xboole_0(sK5,sK4),sK3)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_58475,c_58475,c_59354,c_65380,c_65760]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_79002,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sK3))) = sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,sK3)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_76096,c_78994]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_79083,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sK5,sK4),sK3))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sK3)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_79002,c_78994]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_74832,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sK5,X0),X1))) = sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X1)),sK5) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_56206,c_68346]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_74839,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sK5,X0),X1))) = sP4_iProver_split(X1,sP4_iProver_split(sP4_iProver_split(sK5,sP5_iProver_split),sK3)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_74832,c_54100]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_74840,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sK5,X0),X1))) = sP4_iProver_split(X1,sP4_iProver_split(sK5,sP4_iProver_split(sK3,sP5_iProver_split))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_74839,c_54923]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_74841,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(k4_xboole_0(sK5,X0),X1))) = sP4_iProver_split(X1,sP4_iProver_split(sP5_iProver_split,sK3)) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_74840,c_62866,c_65760]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_79084,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sK3)) = sP4_iProver_split(sP5_iProver_split,sK3) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_79083,c_53801,c_74841,c_76096]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_2012,plain,
% 55.01/7.51      ( k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),X0))) = k2_xboole_0(sK3,sK2) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_1674,c_505]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_5243,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),X0)),sK5) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK5) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_2012,c_509]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_5267,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),X0)),sK5) = k4_xboole_0(sK4,sK5) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_5243,c_512]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_9791,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sK4,sK3),sK5) = k4_xboole_0(sK4,sK5) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_3755,c_5267]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_113679,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sK4,sK3),sK5) = k4_xboole_0(sK3,sK5) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_9791,c_9791,c_110077]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_113680,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(sK3,sK4),sK5) = k4_xboole_0(sK3,sK5) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_113679,c_9791,c_53685]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_113728,plain,
% 55.01/7.51      ( sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(sK3,sK4))) = sP4_iProver_split(sP4_iProver_split(X0,k4_xboole_0(sK3,sK5)),sK5) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_113680,c_105094]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_68545,plain,
% 55.01/7.51      ( sP4_iProver_split(sK5,sP4_iProver_split(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2)))) = sP4_iProver_split(sP4_iProver_split(k4_xboole_0(k2_xboole_0(sK4,X1),sK5),X0),sK5) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_3006,c_68488]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_69042,plain,
% 55.01/7.51      ( sP4_iProver_split(sK5,sP4_iProver_split(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2)))) = sP4_iProver_split(sK5,sP4_iProver_split(X0,k2_xboole_0(sK4,X1))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_68545,c_68488]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_69043,plain,
% 55.01/7.51      ( sP4_iProver_split(sK5,sP4_iProver_split(X0,k2_xboole_0(X1,sP4_iProver_split(sK3,sK2)))) = sP4_iProver_split(sK5,sP4_iProver_split(X0,k2_xboole_0(sK4,X1))) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_69042,c_59877]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_69044,plain,
% 55.01/7.51      ( sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(sK3,sK2),X1))) = sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(X1,sK4))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_69043,c_53685]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_69045,plain,
% 55.01/7.51      ( sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X1))) = sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(X1,sK4))) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_69044,c_61315]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_69046,plain,
% 55.01/7.51      ( sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(sK3,sP4_iProver_split(X1,sP5_iProver_split)))) = sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(X1,sK4))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_69045,c_54100]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_69047,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,sP4_iProver_split(X0,X1))) = sP4_iProver_split(sK5,sP4_iProver_split(X0,sP4_iProver_split(X1,sK4))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_69046,c_67465,c_68346]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_113776,plain,
% 55.01/7.51      ( sP4_iProver_split(sK5,sP4_iProver_split(X0,sK3)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_113728,c_53801,c_69047,c_105094]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_120019,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(sK4,X0),X0) = k4_xboole_0(sK4,X0) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_118730,c_8]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_120921,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sP4_iProver_split(sK4,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))),sK4))) = k4_xboole_0(sP4_iProver_split(sK4,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))),sP4_iProver_split(k4_xboole_0(sK4,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))),sK4)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_120019,c_76781]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_8699,plain,
% 55.01/7.51      ( k2_xboole_0(k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK4),X0)),k2_xboole_0(X1,sK3)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_8615,c_245]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_58237,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(sK3,X0),sP4_iProver_split(k2_xboole_0(k4_xboole_0(sK5,sK4),X1),sK2)) = sP4_iProver_split(X1,sP4_iProver_split(X0,k2_xboole_0(sK3,sK2))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_8699,c_53685,c_54100]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_58238,plain,
% 55.01/7.51      ( sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(sK2,X1)),sK3)) = sP4_iProver_split(X1,sP4_iProver_split(X0,sP4_iProver_split(sK2,sK3))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_58237,c_53685,c_54100]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_58239,plain,
% 55.01/7.51      ( sP4_iProver_split(X0,sP4_iProver_split(sP4_iProver_split(sK2,X1),sP4_iProver_split(sK3,k4_xboole_0(sK5,sK4)))) = sP4_iProver_split(X1,sP4_iProver_split(X0,sP4_iProver_split(sK2,sK3))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_58238,c_54100]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_53232,plain,
% 55.01/7.51      ( k2_xboole_0(k4_xboole_0(sK5,sK4),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_1279,c_21035]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_1991,plain,
% 55.01/7.51      ( k2_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(sK5,X1)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_1674,c_244]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_18676,plain,
% 55.01/7.51      ( k2_xboole_0(k4_xboole_0(sK5,X0),k2_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k2_xboole_0(sK4,X1),sK5) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_1749,c_1991]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_4141,plain,
% 55.01/7.51      ( k2_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k2_xboole_0(sK4,X0),sK5) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_1674,c_1672]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_4206,plain,
% 55.01/7.51      ( k2_xboole_0(k2_xboole_0(sK4,X0),sK5) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_4141,c_4205]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_18907,plain,
% 55.01/7.51      ( k2_xboole_0(k4_xboole_0(sK5,X0),k2_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X1)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_18676,c_4206]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_54970,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(X0,sK3),sK2) = sP4_iProver_split(sP4_iProver_split(X0,sK2),sK3) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_53232,c_3970,c_18907,c_53685]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_2934,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_1674,c_1862]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_4536,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(k2_xboole_0(sK5,X0),k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_1329,c_2934]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_881,plain,
% 55.01/7.51      ( k2_xboole_0(k2_xboole_0(sK5,X0),k4_xboole_0(sK4,k2_xboole_0(sK5,X0))) = k2_xboole_0(k2_xboole_0(sK5,X0),k2_xboole_0(sK3,sK2)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_717,c_6]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_882,plain,
% 55.01/7.51      ( k2_xboole_0(k2_xboole_0(sK5,X0),k2_xboole_0(sK3,sK2)) = k2_xboole_0(k2_xboole_0(sK5,X0),sK4) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_881,c_6]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_4594,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(k2_xboole_0(sK5,X0),sK4)) = k1_xboole_0 ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_4536,c_882]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_4595,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(X0,k2_xboole_0(sK5,sK4))) = k1_xboole_0 ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_4594,c_3970]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_4596,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_4595,c_1259]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_53252,plain,
% 55.01/7.51      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,X1)))) = k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X1)),X0) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_4596,c_21035]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_28692,plain,
% 55.01/7.51      ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),X1) = k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(X0,sK5),X1)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_2244,c_11]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_16239,plain,
% 55.01/7.51      ( k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(X0,sK2),X1)) = k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(X1,X0))) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_16088,c_245]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_16315,plain,
% 55.01/7.51      ( k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(X0,X1))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X1,X0))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_16239,c_1525,c_3970]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_28751,plain,
% 55.01/7.51      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X1)),X0) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_28692,c_2260,c_3970,c_16315]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_54929,plain,
% 55.01/7.51      ( k2_xboole_0(sP1_iProver_split,k2_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(sK2,X1)))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_53252,c_28751,c_34016]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_54930,plain,
% 55.01/7.51      ( sP4_iProver_split(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),X1) = sP4_iProver_split(sP4_iProver_split(k2_xboole_0(X1,X0),sK2),sK3) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_54929,c_35092,c_53685]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_54931,plain,
% 55.01/7.51      ( sP4_iProver_split(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),X1) = sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(X0,X1),sK2),sK3) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_54930,c_53685]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_54932,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(k2_xboole_0(sK2,X0),sK3),X1) = sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(X0,X1),sK2),sK3) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_54931,c_53685]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_54933,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(X0,sK2),sK3),X1) = sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(X0,X1),sK2),sK3) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_54932,c_53685]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_54971,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(X0,sK3),sK2),X1) = sP4_iProver_split(sP4_iProver_split(sP4_iProver_split(X0,X1),sK2),sK3) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_54970,c_54933]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_54974,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(sK2,X0),sP4_iProver_split(sK3,X1)) = sP4_iProver_split(sK2,sP4_iProver_split(X1,sP4_iProver_split(X0,sK3))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_54971,c_54100,c_54970]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_58240,plain,
% 55.01/7.51      ( sP4_iProver_split(X0,sP4_iProver_split(sK2,sP4_iProver_split(k4_xboole_0(sK5,sK4),sP4_iProver_split(X1,sK3)))) = sP4_iProver_split(X1,sP4_iProver_split(X0,sP4_iProver_split(sK2,sK3))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_58239,c_54974]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_60827,plain,
% 55.01/7.51      ( sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK5,sP4_iProver_split(sK2,sK3)))),sK4) = sK4 ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_58240,c_60822]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_3408,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sK5,sK2),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_0,c_2936]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_56120,plain,
% 55.01/7.51      ( sP4_iProver_split(k1_xboole_0,sP4_iProver_split(k2_xboole_0(sK5,sK2),k2_xboole_0(sK3,sK2))) = sP4_iProver_split(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,sK2)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_3408,c_56078]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_56350,plain,
% 55.01/7.51      ( sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(sK5,k2_xboole_0(sK3,sK2))) = sP4_iProver_split(k2_xboole_0(sK3,sK2),sK5) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_56120,c_34016,c_49910]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_56351,plain,
% 55.01/7.51      ( sP4_iProver_split(sK5,sP4_iProver_split(sK2,sK3)) = sP4_iProver_split(sK3,sP4_iProver_split(sK5,sK2)) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_56350,c_53685,c_53848,c_54100]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_60860,plain,
% 55.01/7.51      ( sP4_iProver_split(k4_xboole_0(sK3,sP4_iProver_split(X0,sP4_iProver_split(sK3,sP4_iProver_split(sK5,sK2)))),sK4) = sK4 ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_60827,c_56351]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_56508,plain,
% 55.01/7.51      ( k4_xboole_0(X0,sP4_iProver_split(X1,sP4_iProver_split(X0,X2))) = sP1_iProver_split ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_56078,c_56497]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_60861,plain,
% 55.01/7.51      ( sP4_iProver_split(sP1_iProver_split,sK4) = sK4 ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_60860,c_56508]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_74349,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sK3,sK2),sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(k2_xboole_0(sK3,sK2),X0))) = sP1_iProver_split ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_34235,c_74313]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_75555,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(sK3,sK2),sP4_iProver_split(sP1_iProver_split,sP4_iProver_split(sP4_iProver_split(sK3,sK2),X0))) = sP1_iProver_split ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_74349,c_59877]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_75556,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sP4_iProver_split(sK3,sK2),X0)) = sP1_iProver_split ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_75555,c_53848,c_56508,c_61315]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_75557,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK3),X0)) = sP1_iProver_split ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_75556,c_61315]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_67345,plain,
% 55.01/7.51      ( k4_xboole_0(sK4,sP4_iProver_split(sK5,sP4_iProver_split(sK3,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,k4_xboole_0(X1,sP4_iProver_split(X2,k4_xboole_0(X1,sK5)))))))) = k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(sK5,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)))) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_67318,c_57991]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_67361,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(sK2,sK3),sP4_iProver_split(sK5,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)))) = k4_xboole_0(sK4,sP4_iProver_split(sK5,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split)))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_67345,c_67318]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_67362,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(sK3,sK2),sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split))) = k4_xboole_0(sK4,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split))) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_67361,c_59354,c_65852]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_67363,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split))) = k4_xboole_0(sK4,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_67362,c_61315]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_40485,plain,
% 55.01/7.51      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK5),X1)),k4_xboole_0(X2,k2_xboole_0(sK3,sK2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK5),X1)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_39565,c_6382]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_71439,plain,
% 55.01/7.51      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK5),X1)),k4_xboole_0(X2,sP4_iProver_split(sK3,sK2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK5),X1)) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_40485,c_40485,c_59877]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_71440,plain,
% 55.01/7.51      ( k4_xboole_0(X0,k2_xboole_0(sP4_iProver_split(X1,k4_xboole_0(X0,sK5)),k4_xboole_0(X2,sP4_iProver_split(sP5_iProver_split,sK3)))) = k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X0,sK5))) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_71439,c_9,c_52508,c_53685,c_61315]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_71441,plain,
% 55.01/7.51      ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X1,sP4_iProver_split(sP5_iProver_split,sK3)),sP4_iProver_split(X2,k4_xboole_0(X0,sK5)))) = k4_xboole_0(X0,sP4_iProver_split(X2,k4_xboole_0(X0,sK5))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_71440,c_53685]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_72719,plain,
% 55.01/7.51      ( k4_xboole_0(X0,sP4_iProver_split(sP4_iProver_split(k4_xboole_0(X0,k4_xboole_0(X0,sK5)),X1),k4_xboole_0(X0,sK5))) = k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X2,sP4_iProver_split(sP5_iProver_split,sK3)),sP4_iProver_split(X0,X1))) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_72427,c_71441]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_72727,plain,
% 55.01/7.51      ( k4_xboole_0(X0,sP4_iProver_split(k4_xboole_0(X1,sP4_iProver_split(sP5_iProver_split,sK3)),sP4_iProver_split(X0,X2))) = k4_xboole_0(X0,sP4_iProver_split(X0,X2)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_72719,c_72427]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_72728,plain,
% 55.01/7.51      ( k4_xboole_0(X0,sP4_iProver_split(X0,X1)) = sP1_iProver_split ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_72727,c_56508]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_75558,plain,
% 55.01/7.51      ( k4_xboole_0(sK4,sP4_iProver_split(sK3,sP4_iProver_split(X0,sP5_iProver_split))) = sP1_iProver_split ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_75557,c_54100,c_67363,c_72728]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_75559,plain,
% 55.01/7.51      ( k4_xboole_0(sK4,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))) = sP1_iProver_split ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_75558,c_67465]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_105159,plain,
% 55.01/7.51      ( sP4_iProver_split(k2_xboole_0(sK3,sK2),sP4_iProver_split(X0,k2_xboole_0(sK2,sK4))) = sP4_iProver_split(sP4_iProver_split(X0,k1_xboole_0),k2_xboole_0(sK3,sK2)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_3349,c_105094]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_105767,plain,
% 55.01/7.51      ( sP4_iProver_split(sP4_iProver_split(sK3,sK2),sP4_iProver_split(X0,k2_xboole_0(sP5_iProver_split,sK4))) = sP4_iProver_split(sP4_iProver_split(X0,sP1_iProver_split),sP4_iProver_split(sK3,sK2)) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_105159,c_34016,c_59877,c_65380]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_105768,plain,
% 55.01/7.51      ( sP4_iProver_split(sK3,sP4_iProver_split(sP4_iProver_split(X0,sP4_iProver_split(sK4,sP5_iProver_split)),sP5_iProver_split)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_105767,c_53685,c_54100,c_61315,c_65380,c_82862]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_43412,plain,
% 55.01/7.51      ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),X0),sK3)) = k2_xboole_0(sK2,sP1_iProver_split) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_43342,c_617]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_43437,plain,
% 55.01/7.51      ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK4),X0),sK3)) = sK2 ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_43412,c_35025]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_43438,plain,
% 55.01/7.51      ( k2_xboole_0(sK2,k4_xboole_0(sK4,k2_xboole_0(X0,sK3))) = sK2 ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_43437,c_9,c_14990]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_43510,plain,
% 55.01/7.51      ( k2_xboole_0(sK2,k4_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(X1,sK3)))) = sK2 ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_11,c_43438]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_69736,plain,
% 55.01/7.51      ( k2_xboole_0(sP5_iProver_split,k4_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(X1,sK3)))) = sP5_iProver_split ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_43510,c_43510,c_65380]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_69737,plain,
% 55.01/7.51      ( sP4_iProver_split(k4_xboole_0(sK4,sP4_iProver_split(k2_xboole_0(X0,sK3),X1)),sP5_iProver_split) = sP5_iProver_split ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_69736,c_53685]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_69738,plain,
% 55.01/7.51      ( sP4_iProver_split(k4_xboole_0(sK4,sP4_iProver_split(X0,sP4_iProver_split(X1,sK3))),sP5_iProver_split) = sP5_iProver_split ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_69737,c_53685,c_54100]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_74660,plain,
% 55.01/7.51      ( sP4_iProver_split(sK4,sP5_iProver_split) = sP4_iProver_split(sP5_iProver_split,sK4) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_69738,c_56206]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_105769,plain,
% 55.01/7.51      ( sP4_iProver_split(sK3,sP4_iProver_split(sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK4)),sP5_iProver_split)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_105768,c_74660]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_105770,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sP4_iProver_split(sP5_iProver_split,sK4),sP4_iProver_split(X0,sK3))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_105769,c_54100,c_67465,c_79097]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_105771,plain,
% 55.01/7.51      ( sP4_iProver_split(sK4,sP4_iProver_split(sP4_iProver_split(X0,sK3),sP5_iProver_split)) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_105770,c_53989,c_54100]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_105772,plain,
% 55.01/7.51      ( sP4_iProver_split(sK4,sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))) = sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_105771,c_71205]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_120937,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sP4_iProver_split(sK5,X0),k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)),sK4))) = k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)),sK4) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_120921,c_60861,c_75559,c_105772]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_127106,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3)),sP4_iProver_split(sK4,k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(sK3,X0))))) = k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)),sK4) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_127105,c_79084,c_113776,c_120937]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_120108,plain,
% 55.01/7.51      ( sP4_iProver_split(sK4,sP1_iProver_split) = sK4 ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_118730,c_35017]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_8589,plain,
% 55.01/7.51      ( k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK5,sK4)))) = k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,sK4)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_1943,c_4236]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_8623,plain,
% 55.01/7.51      ( k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK5,sK4)))) = sK4 ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_8589,c_3765]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_73231,plain,
% 55.01/7.51      ( k4_xboole_0(k4_xboole_0(X0,sK4),sK4) = k4_xboole_0(X0,sK4) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_8623,c_49082]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_124054,plain,
% 55.01/7.51      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,sK5),sK4),sK4) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK4) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_2999,c_73231]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_124238,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK4) = k4_xboole_0(k2_xboole_0(X0,sK5),sK4) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_124054,c_73231]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_3005,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK4) = k4_xboole_0(k2_xboole_0(sK5,X0),sK4) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_1237,c_509]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_115838,plain,
% 55.01/7.51      ( sP4_iProver_split(k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),k4_xboole_0(sK3,sK5)),X0) = k2_xboole_0(X0,sK5) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_110644,c_114564]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_116293,plain,
% 55.01/7.51      ( sP4_iProver_split(sK5,X0) = k2_xboole_0(X0,sK5) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_115838,c_110644]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_124239,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(X0,sP4_iProver_split(sK3,sK2)),sK4) = k4_xboole_0(sP4_iProver_split(sK5,X0),sK4) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_124238,c_3005,c_59877,c_116293]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_124240,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(sK3,sK2)),sK4) = k4_xboole_0(sP4_iProver_split(sK5,X0),sK4) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_124239,c_117418]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_124241,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(X0,sP4_iProver_split(sP5_iProver_split,sK3)),sK4) = k4_xboole_0(sP4_iProver_split(sK5,X0),sK4) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_124240,c_61315]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_127107,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sP4_iProver_split(X0,sK3)),sK4) = k4_xboole_0(sP4_iProver_split(sK5,X0),sK4) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_127106,c_75599,c_120108,c_124241]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_153927,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(sK5,k4_xboole_0(sK3,sK4)),sK4) = sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sK4)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_153888,c_81806,c_127107]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_21180,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),sK5),sK4) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK4) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_1745,c_2999]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_21207,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK3,X0),sK5),sK4) = k4_xboole_0(sK5,sK4) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_21180,c_1279]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_117020,plain,
% 55.01/7.51      ( sP4_iProver_split(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_115896,c_519]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_109627,plain,
% 55.01/7.51      ( sP4_iProver_split(k4_xboole_0(X0,X1),sP4_iProver_split(k4_xboole_0(X0,X1),X2)) = sP4_iProver_split(X2,k4_xboole_0(X0,X1)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_3129,c_56206]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_118614,plain,
% 55.01/7.51      ( sP4_iProver_split(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),X0) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_117020,c_109627,c_114564]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_145827,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(sK5,k4_xboole_0(sK3,X0)),sK4) = k4_xboole_0(sK5,sK4) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_21207,c_118614]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_153928,plain,
% 55.01/7.51      ( sP4_iProver_split(sP5_iProver_split,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK5,sK4) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_153927,c_145827]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_154415,plain,
% 55.01/7.51      ( k2_xboole_0(sK4,k4_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(k4_xboole_0(sK5,sK4),sK3))) = sK3 ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_153873,c_153928]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_6435,plain,
% 55.01/7.51      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X0)),X3)) = k4_xboole_0(X0,X3) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_3133,c_9]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_129406,plain,
% 55.01/7.51      ( k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X2,k2_xboole_0(X3,X0)))) = k4_xboole_0(X0,X1) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_6435,c_118614]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_129407,plain,
% 55.01/7.51      ( k4_xboole_0(X0,sP4_iProver_split(X1,k4_xboole_0(X2,sP4_iProver_split(X3,X0)))) = k4_xboole_0(X0,X1) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_129406,c_117418]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_129451,plain,
% 55.01/7.51      ( k4_xboole_0(k4_xboole_0(sK5,sK4),sP4_iProver_split(X0,sK4)) = k4_xboole_0(k4_xboole_0(sK5,sK4),X0) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_62059,c_129407]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_74725,plain,
% 55.01/7.51      ( sP4_iProver_split(sK4,sP4_iProver_split(sK4,X0)) = sP4_iProver_split(X0,sK4) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_8623,c_56206]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_4349,plain,
% 55.01/7.51      ( k4_xboole_0(k4_xboole_0(sK5,sK4),k2_xboole_0(sK4,X0)) = k4_xboole_0(k4_xboole_0(sK5,sK4),X0) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_4240,c_9]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_4361,plain,
% 55.01/7.51      ( k4_xboole_0(k4_xboole_0(sK5,sK4),k2_xboole_0(sK4,X0)) = k4_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_4349,c_9]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_121190,plain,
% 55.01/7.51      ( k4_xboole_0(k4_xboole_0(sK5,sK4),sP4_iProver_split(sK4,X0)) = k4_xboole_0(sK5,sP4_iProver_split(sK4,X0)) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_4361,c_4361,c_118730]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_124932,plain,
% 55.01/7.51      ( k4_xboole_0(sK5,sP4_iProver_split(sK4,sP4_iProver_split(sK4,X0))) = k4_xboole_0(k4_xboole_0(sK5,sK4),sP4_iProver_split(X0,sK4)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_74725,c_121190]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_124982,plain,
% 55.01/7.51      ( k4_xboole_0(k4_xboole_0(sK5,sK4),sP4_iProver_split(X0,sK4)) = k4_xboole_0(sK5,sP4_iProver_split(X0,sK4)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_124932,c_74725]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_129768,plain,
% 55.01/7.51      ( k4_xboole_0(sK5,sP4_iProver_split(X0,sK4)) = k4_xboole_0(k4_xboole_0(sK5,sK4),X0) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_129451,c_124982]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_154416,plain,
% 55.01/7.51      ( sP4_iProver_split(sK4,k4_xboole_0(sK5,sP4_iProver_split(k4_xboole_0(k4_xboole_0(sK5,sK4),sK3),sK4))) = sK3 ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_154415,c_118730,c_129768]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_148706,plain,
% 55.01/7.51      ( sP4_iProver_split(sK4,k4_xboole_0(sK5,sP4_iProver_split(sK4,X0))) = sP4_iProver_split(sK4,k4_xboole_0(k4_xboole_0(sK5,sK4),X0)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_121190,c_148655]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_149092,plain,
% 55.01/7.51      ( sP4_iProver_split(sK4,k4_xboole_0(k4_xboole_0(sK5,sK4),X0)) = sP4_iProver_split(sK4,k4_xboole_0(sK5,X0)) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_148706,c_148655]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_149093,plain,
% 55.01/7.51      ( sP4_iProver_split(sK4,k4_xboole_0(sK5,sP4_iProver_split(X0,sK4))) = sP4_iProver_split(sK4,k4_xboole_0(sK5,X0)) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_149092,c_129768]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_154417,plain,
% 55.01/7.51      ( sP4_iProver_split(sK4,k4_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK5,sK4),sK3))) = sK3 ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_154416,c_120099,c_148655,c_149093]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_127453,plain,
% 55.01/7.51      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = sP4_iProver_split(k4_xboole_0(X0,X1),X2) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_6242,c_6242,c_114564]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_127454,plain,
% 55.01/7.51      ( sP4_iProver_split(X0,k4_xboole_0(X1,sP4_iProver_split(X2,X0))) = sP4_iProver_split(k4_xboole_0(X1,X2),X0) ),
% 55.01/7.51      inference(demodulation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_127453,c_6242,c_117418,c_118614]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_148765,plain,
% 55.01/7.51      ( sP4_iProver_split(X0,k4_xboole_0(X1,k4_xboole_0(X2,sP4_iProver_split(X3,X0)))) = sP4_iProver_split(X0,k4_xboole_0(X1,sP4_iProver_split(k4_xboole_0(X2,X3),X0))) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_127454,c_148655]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_148994,plain,
% 55.01/7.51      ( sP4_iProver_split(X0,k4_xboole_0(X1,k4_xboole_0(X2,sP4_iProver_split(X3,X0)))) = sP4_iProver_split(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X0) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_148765,c_127454]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_154418,plain,
% 55.01/7.51      ( sP4_iProver_split(k4_xboole_0(sK5,k4_xboole_0(sK5,sK3)),sK4) = sK3 ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_154417,c_129768,c_148994]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_110841,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sK3) = k4_xboole_0(sK5,sK3) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_110644,c_49082]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_77583,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sK3) = k4_xboole_0(sP5_iProver_split,sK3) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_77129,c_509]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_110847,plain,
% 55.01/7.51      ( k4_xboole_0(sP5_iProver_split,sK3) = k4_xboole_0(sK5,sK3) ),
% 55.01/7.51      inference(light_normalisation,[status(thm)],[c_110841,c_77583]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_10722,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))),X2) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_8,c_605]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_10961,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_10722,c_9,c_3133]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_132189,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_10961,c_10961,c_117418]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_132190,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(X0,X1),sP4_iProver_split(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,X2) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_132189,c_118614]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_16961,plain,
% 55.01/7.51      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,k4_xboole_0(sK4,sK5))) = k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK3,sK2),X0))) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_512,c_16936]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_61352,plain,
% 55.01/7.51      ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sP4_iProver_split(sK3,sK2),X0))) = k4_xboole_0(sP4_iProver_split(sK3,sK2),k2_xboole_0(X0,k4_xboole_0(sK4,sK5))) ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_16961,c_16961,c_59877]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_61353,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),sP4_iProver_split(k4_xboole_0(sK4,sK5),X0)) = k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),X0))) ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_61352,c_53685,c_61315]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_132484,plain,
% 55.01/7.51      ( k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),k4_xboole_0(sP5_iProver_split,sK3)))) = k4_xboole_0(sK3,k4_xboole_0(sK4,sK5)) ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_132190,c_61353]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_14,negated_conjecture,
% 55.01/7.51      ( r1_xboole_0(sK5,sK3) ),
% 55.01/7.51      inference(cnf_transformation,[],[f45]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_95,plain,
% 55.01/7.51      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 55.01/7.51      | sK5 != X1
% 55.01/7.51      | sK3 != X2 ),
% 55.01/7.51      inference(resolution_lifted,[status(thm)],[c_3,c_14]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_96,plain,
% 55.01/7.51      ( ~ r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) ),
% 55.01/7.51      inference(unflattening,[status(thm)],[c_95]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_236,plain,
% 55.01/7.51      ( r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) != iProver_top ),
% 55.01/7.51      inference(predicate_to_equality,[status(thm)],[c_96]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_582,plain,
% 55.01/7.51      ( r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) != iProver_top ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_1,c_236]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_15263,plain,
% 55.01/7.51      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k1_xboole_0 ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_238,c_582]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_77582,plain,
% 55.01/7.51      ( k4_xboole_0(sP4_iProver_split(sP5_iProver_split,sK3),k4_xboole_0(sP5_iProver_split,sK3)) = sK3 ),
% 55.01/7.51      inference(superposition,[status(thm)],[c_77129,c_3755]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_132505,plain,
% 55.01/7.51      ( k4_xboole_0(sK5,k4_xboole_0(sP5_iProver_split,sK3)) = k1_xboole_0 ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_132484,c_15263,c_77582,c_110077,c_110847]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_132506,plain,
% 55.01/7.51      ( k4_xboole_0(sK5,k4_xboole_0(sP5_iProver_split,sK3)) = sP1_iProver_split ),
% 55.01/7.51      inference(demodulation,[status(thm)],[c_132505,c_34016]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_154419,plain,
% 55.01/7.51      ( sK4 = sK3 ),
% 55.01/7.51      inference(light_normalisation,
% 55.01/7.51                [status(thm)],
% 55.01/7.51                [c_154418,c_60861,c_110847,c_132506]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_156,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_249,plain,
% 55.01/7.51      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 55.01/7.51      inference(instantiation,[status(thm)],[c_156]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_250,plain,
% 55.01/7.51      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 55.01/7.51      inference(instantiation,[status(thm)],[c_249]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_155,plain,( X0 = X0 ),theory(equality) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_163,plain,
% 55.01/7.51      ( sK3 = sK3 ),
% 55.01/7.51      inference(instantiation,[status(thm)],[c_155]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(c_13,negated_conjecture,
% 55.01/7.51      ( sK3 != sK4 ),
% 55.01/7.51      inference(cnf_transformation,[],[f46]) ).
% 55.01/7.51  
% 55.01/7.51  cnf(contradiction,plain,
% 55.01/7.51      ( $false ),
% 55.01/7.51      inference(minisat,[status(thm)],[c_154419,c_250,c_163,c_13]) ).
% 55.01/7.51  
% 55.01/7.51  
% 55.01/7.51  % SZS output end CNFRefutation for theBenchmark.p
% 55.01/7.51  
% 55.01/7.51  ------                               Statistics
% 55.01/7.51  
% 55.01/7.51  ------ General
% 55.01/7.51  
% 55.01/7.51  abstr_ref_over_cycles:                  0
% 55.01/7.51  abstr_ref_under_cycles:                 0
% 55.01/7.51  gc_basic_clause_elim:                   0
% 55.01/7.51  forced_gc_time:                         0
% 55.01/7.51  parsing_time:                           0.032
% 55.01/7.51  unif_index_cands_time:                  0.
% 55.01/7.51  unif_index_add_time:                    0.
% 55.01/7.51  orderings_time:                         0.
% 55.01/7.51  out_proof_time:                         0.06
% 55.01/7.51  total_time:                             6.816
% 55.01/7.51  num_of_symbols:                         50
% 55.01/7.51  num_of_terms:                           330818
% 55.01/7.51  
% 55.01/7.51  ------ Preprocessing
% 55.01/7.51  
% 55.01/7.51  num_of_splits:                          0
% 55.01/7.51  num_of_split_atoms:                     8
% 55.01/7.51  num_of_reused_defs:                     1
% 55.01/7.51  num_eq_ax_congr_red:                    9
% 55.01/7.51  num_of_sem_filtered_clauses:            1
% 55.01/7.51  num_of_subtypes:                        0
% 55.01/7.51  monotx_restored_types:                  0
% 55.01/7.51  sat_num_of_epr_types:                   0
% 55.01/7.51  sat_num_of_non_cyclic_types:            0
% 55.01/7.51  sat_guarded_non_collapsed_types:        0
% 55.01/7.51  num_pure_diseq_elim:                    0
% 55.01/7.51  simp_replaced_by:                       0
% 55.01/7.51  res_preprocessed:                       76
% 55.01/7.51  prep_upred:                             0
% 55.01/7.51  prep_unflattend:                        6
% 55.01/7.51  smt_new_axioms:                         0
% 55.01/7.51  pred_elim_cands:                        1
% 55.01/7.51  pred_elim:                              1
% 55.01/7.51  pred_elim_cl:                           1
% 55.01/7.51  pred_elim_cycles:                       3
% 55.01/7.51  merged_defs:                            0
% 55.01/7.51  merged_defs_ncl:                        0
% 55.01/7.51  bin_hyper_res:                          0
% 55.01/7.51  prep_cycles:                            4
% 55.01/7.51  pred_elim_time:                         0.001
% 55.01/7.51  splitting_time:                         0.
% 55.01/7.51  sem_filter_time:                        0.
% 55.01/7.51  monotx_time:                            0.
% 55.01/7.51  subtype_inf_time:                       0.
% 55.01/7.51  
% 55.01/7.51  ------ Problem properties
% 55.01/7.51  
% 55.01/7.51  clauses:                                16
% 55.01/7.51  conjectures:                            2
% 55.01/7.51  epr:                                    1
% 55.01/7.51  horn:                                   15
% 55.01/7.51  ground:                                 2
% 55.01/7.51  unary:                                  14
% 55.01/7.51  binary:                                 2
% 55.01/7.51  lits:                                   18
% 55.01/7.51  lits_eq:                                13
% 55.01/7.51  fd_pure:                                0
% 55.01/7.51  fd_pseudo:                              0
% 55.01/7.51  fd_cond:                                1
% 55.01/7.51  fd_pseudo_cond:                         0
% 55.01/7.51  ac_symbols:                             1
% 55.01/7.51  
% 55.01/7.51  ------ Propositional Solver
% 55.01/7.51  
% 55.01/7.51  prop_solver_calls:                      45
% 55.01/7.51  prop_fast_solver_calls:                 1183
% 55.01/7.51  smt_solver_calls:                       0
% 55.01/7.51  smt_fast_solver_calls:                  0
% 55.01/7.51  prop_num_of_clauses:                    44374
% 55.01/7.51  prop_preprocess_simplified:             32424
% 55.01/7.51  prop_fo_subsumed:                       0
% 55.01/7.51  prop_solver_time:                       0.
% 55.01/7.51  smt_solver_time:                        0.
% 55.01/7.51  smt_fast_solver_time:                   0.
% 55.01/7.51  prop_fast_solver_time:                  0.
% 55.01/7.51  prop_unsat_core_time:                   0.006
% 55.01/7.51  
% 55.01/7.51  ------ QBF
% 55.01/7.51  
% 55.01/7.51  qbf_q_res:                              0
% 55.01/7.51  qbf_num_tautologies:                    0
% 55.01/7.51  qbf_prep_cycles:                        0
% 55.01/7.51  
% 55.01/7.51  ------ BMC1
% 55.01/7.51  
% 55.01/7.51  bmc1_current_bound:                     -1
% 55.01/7.51  bmc1_last_solved_bound:                 -1
% 55.01/7.51  bmc1_unsat_core_size:                   -1
% 55.01/7.51  bmc1_unsat_core_parents_size:           -1
% 55.01/7.51  bmc1_merge_next_fun:                    0
% 55.01/7.51  bmc1_unsat_core_clauses_time:           0.
% 55.01/7.51  
% 55.01/7.51  ------ Instantiation
% 55.01/7.51  
% 55.01/7.51  inst_num_of_clauses:                    11206
% 55.01/7.51  inst_num_in_passive:                    4695
% 55.01/7.51  inst_num_in_active:                     1895
% 55.01/7.51  inst_num_in_unprocessed:                4616
% 55.01/7.51  inst_num_of_loops:                      2550
% 55.01/7.51  inst_num_of_learning_restarts:          0
% 55.01/7.51  inst_num_moves_active_passive:          650
% 55.01/7.51  inst_lit_activity:                      0
% 55.01/7.51  inst_lit_activity_moves:                3
% 55.01/7.51  inst_num_tautologies:                   0
% 55.01/7.51  inst_num_prop_implied:                  0
% 55.01/7.51  inst_num_existing_simplified:           0
% 55.01/7.51  inst_num_eq_res_simplified:             0
% 55.01/7.51  inst_num_child_elim:                    0
% 55.01/7.51  inst_num_of_dismatching_blockings:      10513
% 55.01/7.51  inst_num_of_non_proper_insts:           8867
% 55.01/7.51  inst_num_of_duplicates:                 0
% 55.01/7.51  inst_inst_num_from_inst_to_res:         0
% 55.01/7.51  inst_dismatching_checking_time:         0.
% 55.01/7.51  
% 55.01/7.51  ------ Resolution
% 55.01/7.51  
% 55.01/7.51  res_num_of_clauses:                     0
% 55.01/7.51  res_num_in_passive:                     0
% 55.01/7.51  res_num_in_active:                      0
% 55.01/7.51  res_num_of_loops:                       80
% 55.01/7.51  res_forward_subset_subsumed:            1797
% 55.01/7.51  res_backward_subset_subsumed:           0
% 55.01/7.51  res_forward_subsumed:                   0
% 55.01/7.51  res_backward_subsumed:                  0
% 55.01/7.51  res_forward_subsumption_resolution:     0
% 55.01/7.51  res_backward_subsumption_resolution:    0
% 55.01/7.51  res_clause_to_clause_subsumption:       148857
% 55.01/7.51  res_orphan_elimination:                 0
% 55.01/7.51  res_tautology_del:                      693
% 55.01/7.51  res_num_eq_res_simplified:              0
% 55.01/7.51  res_num_sel_changes:                    0
% 55.01/7.51  res_moves_from_active_to_pass:          0
% 55.01/7.51  
% 55.01/7.51  ------ Superposition
% 55.01/7.51  
% 55.01/7.51  sup_time_total:                         0.
% 55.01/7.51  sup_time_generating:                    0.
% 55.01/7.51  sup_time_sim_full:                      0.
% 55.01/7.51  sup_time_sim_immed:                     0.
% 55.01/7.51  
% 55.01/7.51  sup_num_of_clauses:                     14661
% 55.01/7.51  sup_num_in_active:                      330
% 55.01/7.51  sup_num_in_passive:                     14331
% 55.01/7.51  sup_num_of_loops:                       508
% 55.01/7.51  sup_fw_superposition:                   21445
% 55.01/7.51  sup_bw_superposition:                   20872
% 55.01/7.51  sup_immediate_simplified:               30780
% 55.01/7.51  sup_given_eliminated:                   20
% 55.01/7.51  comparisons_done:                       0
% 55.01/7.51  comparisons_avoided:                    0
% 55.01/7.51  
% 55.01/7.51  ------ Simplifications
% 55.01/7.51  
% 55.01/7.51  
% 55.01/7.51  sim_fw_subset_subsumed:                 0
% 55.01/7.51  sim_bw_subset_subsumed:                 0
% 55.01/7.51  sim_fw_subsumed:                        2457
% 55.01/7.51  sim_bw_subsumed:                        459
% 55.01/7.51  sim_fw_subsumption_res:                 0
% 55.01/7.51  sim_bw_subsumption_res:                 0
% 55.01/7.51  sim_tautology_del:                      0
% 55.01/7.51  sim_eq_tautology_del:                   8188
% 55.01/7.51  sim_eq_res_simp:                        0
% 55.01/7.51  sim_fw_demodulated:                     31356
% 55.01/7.51  sim_bw_demodulated:                     1553
% 55.01/7.51  sim_light_normalised:                   16399
% 55.01/7.51  sim_joinable_taut:                      359
% 55.01/7.51  sim_joinable_simp:                      0
% 55.01/7.51  sim_ac_normalised:                      0
% 55.01/7.51  sim_smt_subsumption:                    0
% 55.01/7.51  
%------------------------------------------------------------------------------
