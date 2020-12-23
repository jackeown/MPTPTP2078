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
% DateTime   : Thu Dec  3 11:23:39 EST 2020

% Result     : Theorem 27.29s
% Output     : CNFRefutation 27.29s
% Verified   : 
% Statistics : Number of formulae       :  163 (8798 expanded)
%              Number of clauses        :  122 (3806 expanded)
%              Number of leaves         :   14 (2185 expanded)
%              Depth                    :   29
%              Number of atoms          :  266 (11759 expanded)
%              Number of equality atoms :  168 (8204 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f39,f38])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) )
   => ( ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
        & ( ~ r1_xboole_0(sK1,sK3)
          | ~ r1_xboole_0(sK1,sK2) ) )
      | ( r1_xboole_0(sK1,sK3)
        & r1_xboole_0(sK1,sK2)
        & ~ r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
      & ( ~ r1_xboole_0(sK1,sK3)
        | ~ r1_xboole_0(sK1,sK2) ) )
    | ( r1_xboole_0(sK1,sK3)
      & r1_xboole_0(sK1,sK2)
      & ~ r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f25])).

fof(f47,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f38])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f29,f38])).

fof(f42,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    | ~ r1_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_11,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_589,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7,c_9])).

cnf(c_10,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_914,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_589,c_10])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_920,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_914,c_6])).

cnf(c_1122,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_920])).

cnf(c_8,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1246,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1122,c_8])).

cnf(c_1252,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1246,c_8])).

cnf(c_1404,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1252,c_920])).

cnf(c_1410,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1404,c_589])).

cnf(c_1424,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1410])).

cnf(c_1616,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_1424])).

cnf(c_1750,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1616,c_8])).

cnf(c_1756,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1750,c_6])).

cnf(c_1132,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_920,c_8])).

cnf(c_1138,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1132,c_8])).

cnf(c_1405,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1252,c_1138])).

cnf(c_884,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_589,c_8])).

cnf(c_885,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_884,c_6])).

cnf(c_1407,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1405,c_885])).

cnf(c_2062,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1407])).

cnf(c_2791,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1756,c_2062])).

cnf(c_2823,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2791,c_1756])).

cnf(c_1751,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1616,c_10])).

cnf(c_1753,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1751,c_6])).

cnf(c_4899,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_2823,c_1753])).

cnf(c_5016,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4899,c_1616])).

cnf(c_1624,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1424,c_8])).

cnf(c_1630,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1624,c_6])).

cnf(c_2562,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1630])).

cnf(c_3060,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_8,c_2562])).

cnf(c_3114,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_3060,c_2562])).

cnf(c_3550,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_3114,c_0])).

cnf(c_5092,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5016,c_3550])).

cnf(c_5104,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5092,c_6])).

cnf(c_14,negated_conjecture,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_579,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = iProver_top
    | r1_xboole_0(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_582,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6342,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK3),sK1) = iProver_top
    | r1_xboole_0(sK1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_579,c_582])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_13,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_187,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X3 != X2
    | k2_xboole_0(X3,X4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_13])).

cnf(c_188,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(unflattening,[status(thm)],[c_187])).

cnf(c_576,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_188])).

cnf(c_1650,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(k2_xboole_0(X2,X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_576])).

cnf(c_43909,plain,
    ( r1_xboole_0(sK3,sK1) = iProver_top
    | r1_xboole_0(sK1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6342,c_1650])).

cnf(c_1084,plain,
    ( ~ r1_xboole_0(sK3,sK1)
    | r1_xboole_0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1085,plain,
    ( r1_xboole_0(sK3,sK1) != iProver_top
    | r1_xboole_0(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1084])).

cnf(c_45858,plain,
    ( r1_xboole_0(sK1,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43909,c_1085])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_583,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9377,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) = k1_xboole_0
    | r1_xboole_0(sK1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_579,c_583])).

cnf(c_11310,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) = k1_xboole_0
    | r1_xboole_0(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_9377,c_582])).

cnf(c_11661,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0
    | k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11310,c_583])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_584,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_13034,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0
    | r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11661,c_584])).

cnf(c_19,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | ~ r1_xboole_0(sK1,sK3)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_577,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) != iProver_top
    | r1_xboole_0(sK1,sK3) != iProver_top
    | r1_xboole_0(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_17270,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0
    | r1_xboole_0(sK1,sK3) != iProver_top
    | r1_xboole_0(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_13034,c_577])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_578,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = iProver_top
    | r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6343,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK3),sK1) = iProver_top
    | r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_578,c_582])).

cnf(c_718,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK3),sK1)
    | r1_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_719,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK3),sK1) != iProver_top
    | r1_xboole_0(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_859,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | r1_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_860,plain,
    ( r1_xboole_0(sK2,sK1) != iProver_top
    | r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_859])).

cnf(c_7949,plain,
    ( r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6343,c_719,c_860])).

cnf(c_17495,plain,
    ( r1_xboole_0(sK1,sK3) != iProver_top
    | k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17270,c_719,c_860,c_6343])).

cnf(c_17496,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0
    | r1_xboole_0(sK1,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_17495])).

cnf(c_45865,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_45858,c_17496])).

cnf(c_45920,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) ),
    inference(superposition,[status(thm)],[c_45865,c_8])).

cnf(c_45930,plain,
    ( k4_xboole_0(sK3,sK1) = sK3 ),
    inference(demodulation,[status(thm)],[c_45920,c_6,c_2823])).

cnf(c_7954,plain,
    ( r1_xboole_0(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7949,c_582])).

cnf(c_9381,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7954,c_583])).

cnf(c_12067,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK1),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK2,sK1),sK2) ),
    inference(superposition,[status(thm)],[c_9381,c_8])).

cnf(c_12077,plain,
    ( k4_xboole_0(sK2,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_12067,c_6,c_2823])).

cnf(c_12899,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,X0),sK1) = k2_xboole_0(sK2,k4_xboole_0(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_12077,c_10])).

cnf(c_15190,plain,
    ( k2_xboole_0(k4_xboole_0(X0,sK1),k2_xboole_0(sK2,k4_xboole_0(X1,sK1))) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK2,X1)),sK1) ),
    inference(superposition,[status(thm)],[c_12899,c_10])).

cnf(c_118380,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK2,sK3)),sK1) = k2_xboole_0(k4_xboole_0(X0,sK1),k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_45930,c_15190])).

cnf(c_122955,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1),k2_xboole_0(sK2,sK3)) = k4_xboole_0(k2_xboole_0(sK2,sK3),sK1) ),
    inference(superposition,[status(thm)],[c_5104,c_118380])).

cnf(c_123461,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1),k2_xboole_0(sK2,sK3)) = k2_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_122955,c_12899,c_45930])).

cnf(c_915,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_10,c_0])).

cnf(c_7370,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_9,c_915])).

cnf(c_7536,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_7370,c_9])).

cnf(c_118461,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK2,X1)),sK1),k1_xboole_0) = k2_xboole_0(k2_xboole_0(sK2,k4_xboole_0(X1,sK1)),k4_xboole_0(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_15190,c_7536])).

cnf(c_15178,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,k4_xboole_0(X0,sK1)),k4_xboole_0(X1,sK1)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(sK2,X0),X1),sK1) ),
    inference(superposition,[status(thm)],[c_12899,c_10])).

cnf(c_118815,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK2,X1)),sK1) = k4_xboole_0(k2_xboole_0(k2_xboole_0(sK2,X1),X0),sK1) ),
    inference(demodulation,[status(thm)],[c_118461,c_9,c_15178])).

cnf(c_119463,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,sK2),X1),sK1) = k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(sK2,X0)),sK1) ),
    inference(superposition,[status(thm)],[c_0,c_118815])).

cnf(c_126310,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1)),sK1) = k4_xboole_0(k2_xboole_0(sK2,sK3),sK1) ),
    inference(superposition,[status(thm)],[c_123461,c_119463])).

cnf(c_1239,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_8,c_1122])).

cnf(c_1263,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1239,c_1122])).

cnf(c_1935,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_1263,c_10])).

cnf(c_1938,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_1935,c_10])).

cnf(c_127257,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1)),sK1) = k2_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_126310,c_1938,c_12899,c_45930])).

cnf(c_129002,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1)),k2_xboole_0(sK2,sK3)) != k1_xboole_0
    | r1_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_127257,c_584])).

cnf(c_1619,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1138,c_1424])).

cnf(c_2486,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k2_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1619,c_10])).

cnf(c_878,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_2500,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k4_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_2486,c_878])).

cnf(c_129332,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1),k2_xboole_0(sK2,sK3)) != k1_xboole_0
    | r1_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1)),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_129002,c_2500])).

cnf(c_129489,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),sK1),sK1),sK1),k2_xboole_0(sK2,sK3)) != k1_xboole_0
    | r1_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),sK1),sK1),sK1)),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_129332])).

cnf(c_2886,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2823,c_576])).

cnf(c_129050,plain,
    ( r1_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1)),X2) != iProver_top
    | r1_xboole_0(k2_xboole_0(sK2,sK3),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_127257,c_2886])).

cnf(c_129464,plain,
    ( r1_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),sK1),sK1),sK1)),sK1) != iProver_top
    | r1_xboole_0(k2_xboole_0(sK2,sK3),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_129050])).

cnf(c_5093,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5016,c_8])).

cnf(c_5101,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5093,c_6])).

cnf(c_117338,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK2,sK3),X0),sK1) = k2_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_45930,c_15178])).

cnf(c_120739,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1)) = k4_xboole_0(k2_xboole_0(sK2,sK3),sK1) ),
    inference(superposition,[status(thm)],[c_5101,c_117338])).

cnf(c_121198,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1)) = k2_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_120739,c_12899,c_45930])).

cnf(c_124251,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_121198,c_1424])).

cnf(c_124592,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),sK1),sK1),sK1),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_124251])).

cnf(c_704,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK3),sK1)
    | r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_705,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK3),sK1) != iProver_top
    | r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_20,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) != iProver_top
    | r1_xboole_0(sK1,sK3) != iProver_top
    | r1_xboole_0(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_129489,c_129464,c_124592,c_45858,c_7949,c_705,c_20])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.29/3.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.29/3.99  
% 27.29/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.29/3.99  
% 27.29/3.99  ------  iProver source info
% 27.29/3.99  
% 27.29/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.29/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.29/3.99  git: non_committed_changes: false
% 27.29/3.99  git: last_make_outside_of_git: false
% 27.29/3.99  
% 27.29/3.99  ------ 
% 27.29/3.99  
% 27.29/3.99  ------ Input Options
% 27.29/3.99  
% 27.29/3.99  --out_options                           all
% 27.29/3.99  --tptp_safe_out                         true
% 27.29/3.99  --problem_path                          ""
% 27.29/3.99  --include_path                          ""
% 27.29/3.99  --clausifier                            res/vclausify_rel
% 27.29/3.99  --clausifier_options                    --mode clausify
% 27.29/3.99  --stdin                                 false
% 27.29/3.99  --stats_out                             all
% 27.29/3.99  
% 27.29/3.99  ------ General Options
% 27.29/3.99  
% 27.29/3.99  --fof                                   false
% 27.29/3.99  --time_out_real                         305.
% 27.29/3.99  --time_out_virtual                      -1.
% 27.29/3.99  --symbol_type_check                     false
% 27.29/3.99  --clausify_out                          false
% 27.29/3.99  --sig_cnt_out                           false
% 27.29/3.99  --trig_cnt_out                          false
% 27.29/3.99  --trig_cnt_out_tolerance                1.
% 27.29/3.99  --trig_cnt_out_sk_spl                   false
% 27.29/3.99  --abstr_cl_out                          false
% 27.29/3.99  
% 27.29/3.99  ------ Global Options
% 27.29/3.99  
% 27.29/3.99  --schedule                              default
% 27.29/3.99  --add_important_lit                     false
% 27.29/3.99  --prop_solver_per_cl                    1000
% 27.29/3.99  --min_unsat_core                        false
% 27.29/3.99  --soft_assumptions                      false
% 27.29/3.99  --soft_lemma_size                       3
% 27.29/3.99  --prop_impl_unit_size                   0
% 27.29/3.99  --prop_impl_unit                        []
% 27.29/3.99  --share_sel_clauses                     true
% 27.29/3.99  --reset_solvers                         false
% 27.29/3.99  --bc_imp_inh                            [conj_cone]
% 27.29/3.99  --conj_cone_tolerance                   3.
% 27.29/3.99  --extra_neg_conj                        none
% 27.29/3.99  --large_theory_mode                     true
% 27.29/3.99  --prolific_symb_bound                   200
% 27.29/3.99  --lt_threshold                          2000
% 27.29/3.99  --clause_weak_htbl                      true
% 27.29/3.99  --gc_record_bc_elim                     false
% 27.29/3.99  
% 27.29/3.99  ------ Preprocessing Options
% 27.29/3.99  
% 27.29/3.99  --preprocessing_flag                    true
% 27.29/3.99  --time_out_prep_mult                    0.1
% 27.29/3.99  --splitting_mode                        input
% 27.29/3.99  --splitting_grd                         true
% 27.29/3.99  --splitting_cvd                         false
% 27.29/3.99  --splitting_cvd_svl                     false
% 27.29/3.99  --splitting_nvd                         32
% 27.29/3.99  --sub_typing                            true
% 27.29/3.99  --prep_gs_sim                           true
% 27.29/3.99  --prep_unflatten                        true
% 27.29/3.99  --prep_res_sim                          true
% 27.29/3.99  --prep_upred                            true
% 27.29/3.99  --prep_sem_filter                       exhaustive
% 27.29/3.99  --prep_sem_filter_out                   false
% 27.29/3.99  --pred_elim                             true
% 27.29/3.99  --res_sim_input                         true
% 27.29/3.99  --eq_ax_congr_red                       true
% 27.29/3.99  --pure_diseq_elim                       true
% 27.29/3.99  --brand_transform                       false
% 27.29/3.99  --non_eq_to_eq                          false
% 27.29/3.99  --prep_def_merge                        true
% 27.29/3.99  --prep_def_merge_prop_impl              false
% 27.29/3.99  --prep_def_merge_mbd                    true
% 27.29/3.99  --prep_def_merge_tr_red                 false
% 27.29/3.99  --prep_def_merge_tr_cl                  false
% 27.29/3.99  --smt_preprocessing                     true
% 27.29/3.99  --smt_ac_axioms                         fast
% 27.29/3.99  --preprocessed_out                      false
% 27.29/3.99  --preprocessed_stats                    false
% 27.29/3.99  
% 27.29/3.99  ------ Abstraction refinement Options
% 27.29/3.99  
% 27.29/3.99  --abstr_ref                             []
% 27.29/3.99  --abstr_ref_prep                        false
% 27.29/3.99  --abstr_ref_until_sat                   false
% 27.29/3.99  --abstr_ref_sig_restrict                funpre
% 27.29/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.29/3.99  --abstr_ref_under                       []
% 27.29/3.99  
% 27.29/3.99  ------ SAT Options
% 27.29/3.99  
% 27.29/3.99  --sat_mode                              false
% 27.29/3.99  --sat_fm_restart_options                ""
% 27.29/3.99  --sat_gr_def                            false
% 27.29/3.99  --sat_epr_types                         true
% 27.29/3.99  --sat_non_cyclic_types                  false
% 27.29/3.99  --sat_finite_models                     false
% 27.29/3.99  --sat_fm_lemmas                         false
% 27.29/3.99  --sat_fm_prep                           false
% 27.29/3.99  --sat_fm_uc_incr                        true
% 27.29/3.99  --sat_out_model                         small
% 27.29/3.99  --sat_out_clauses                       false
% 27.29/3.99  
% 27.29/3.99  ------ QBF Options
% 27.29/3.99  
% 27.29/3.99  --qbf_mode                              false
% 27.29/3.99  --qbf_elim_univ                         false
% 27.29/3.99  --qbf_dom_inst                          none
% 27.29/3.99  --qbf_dom_pre_inst                      false
% 27.29/3.99  --qbf_sk_in                             false
% 27.29/3.99  --qbf_pred_elim                         true
% 27.29/3.99  --qbf_split                             512
% 27.29/3.99  
% 27.29/3.99  ------ BMC1 Options
% 27.29/3.99  
% 27.29/3.99  --bmc1_incremental                      false
% 27.29/3.99  --bmc1_axioms                           reachable_all
% 27.29/3.99  --bmc1_min_bound                        0
% 27.29/3.99  --bmc1_max_bound                        -1
% 27.29/3.99  --bmc1_max_bound_default                -1
% 27.29/3.99  --bmc1_symbol_reachability              true
% 27.29/3.99  --bmc1_property_lemmas                  false
% 27.29/3.99  --bmc1_k_induction                      false
% 27.29/3.99  --bmc1_non_equiv_states                 false
% 27.29/3.99  --bmc1_deadlock                         false
% 27.29/3.99  --bmc1_ucm                              false
% 27.29/3.99  --bmc1_add_unsat_core                   none
% 27.29/3.99  --bmc1_unsat_core_children              false
% 27.29/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.29/3.99  --bmc1_out_stat                         full
% 27.29/3.99  --bmc1_ground_init                      false
% 27.29/3.99  --bmc1_pre_inst_next_state              false
% 27.29/3.99  --bmc1_pre_inst_state                   false
% 27.29/3.99  --bmc1_pre_inst_reach_state             false
% 27.29/3.99  --bmc1_out_unsat_core                   false
% 27.29/3.99  --bmc1_aig_witness_out                  false
% 27.29/3.99  --bmc1_verbose                          false
% 27.29/3.99  --bmc1_dump_clauses_tptp                false
% 27.29/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.29/3.99  --bmc1_dump_file                        -
% 27.29/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.29/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.29/3.99  --bmc1_ucm_extend_mode                  1
% 27.29/3.99  --bmc1_ucm_init_mode                    2
% 27.29/3.99  --bmc1_ucm_cone_mode                    none
% 27.29/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.29/3.99  --bmc1_ucm_relax_model                  4
% 27.29/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.29/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.29/3.99  --bmc1_ucm_layered_model                none
% 27.29/3.99  --bmc1_ucm_max_lemma_size               10
% 27.29/3.99  
% 27.29/3.99  ------ AIG Options
% 27.29/3.99  
% 27.29/3.99  --aig_mode                              false
% 27.29/3.99  
% 27.29/3.99  ------ Instantiation Options
% 27.29/3.99  
% 27.29/3.99  --instantiation_flag                    true
% 27.29/3.99  --inst_sos_flag                         false
% 27.29/3.99  --inst_sos_phase                        true
% 27.29/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.29/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.29/3.99  --inst_lit_sel_side                     num_symb
% 27.29/3.99  --inst_solver_per_active                1400
% 27.29/3.99  --inst_solver_calls_frac                1.
% 27.29/3.99  --inst_passive_queue_type               priority_queues
% 27.29/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.29/3.99  --inst_passive_queues_freq              [25;2]
% 27.29/3.99  --inst_dismatching                      true
% 27.29/3.99  --inst_eager_unprocessed_to_passive     true
% 27.29/3.99  --inst_prop_sim_given                   true
% 27.29/3.99  --inst_prop_sim_new                     false
% 27.29/3.99  --inst_subs_new                         false
% 27.29/3.99  --inst_eq_res_simp                      false
% 27.29/3.99  --inst_subs_given                       false
% 27.29/3.99  --inst_orphan_elimination               true
% 27.29/3.99  --inst_learning_loop_flag               true
% 27.29/3.99  --inst_learning_start                   3000
% 27.29/3.99  --inst_learning_factor                  2
% 27.29/3.99  --inst_start_prop_sim_after_learn       3
% 27.29/3.99  --inst_sel_renew                        solver
% 27.29/3.99  --inst_lit_activity_flag                true
% 27.29/3.99  --inst_restr_to_given                   false
% 27.29/3.99  --inst_activity_threshold               500
% 27.29/3.99  --inst_out_proof                        true
% 27.29/3.99  
% 27.29/3.99  ------ Resolution Options
% 27.29/3.99  
% 27.29/3.99  --resolution_flag                       true
% 27.29/3.99  --res_lit_sel                           adaptive
% 27.29/3.99  --res_lit_sel_side                      none
% 27.29/3.99  --res_ordering                          kbo
% 27.29/3.99  --res_to_prop_solver                    active
% 27.29/3.99  --res_prop_simpl_new                    false
% 27.29/3.99  --res_prop_simpl_given                  true
% 27.29/3.99  --res_passive_queue_type                priority_queues
% 27.29/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.29/3.99  --res_passive_queues_freq               [15;5]
% 27.29/3.99  --res_forward_subs                      full
% 27.29/3.99  --res_backward_subs                     full
% 27.29/3.99  --res_forward_subs_resolution           true
% 27.29/3.99  --res_backward_subs_resolution          true
% 27.29/3.99  --res_orphan_elimination                true
% 27.29/3.99  --res_time_limit                        2.
% 27.29/3.99  --res_out_proof                         true
% 27.29/3.99  
% 27.29/3.99  ------ Superposition Options
% 27.29/3.99  
% 27.29/3.99  --superposition_flag                    true
% 27.29/3.99  --sup_passive_queue_type                priority_queues
% 27.29/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.29/3.99  --sup_passive_queues_freq               [8;1;4]
% 27.29/3.99  --demod_completeness_check              fast
% 27.29/3.99  --demod_use_ground                      true
% 27.29/3.99  --sup_to_prop_solver                    passive
% 27.29/3.99  --sup_prop_simpl_new                    true
% 27.29/3.99  --sup_prop_simpl_given                  true
% 27.29/3.99  --sup_fun_splitting                     false
% 27.29/3.99  --sup_smt_interval                      50000
% 27.29/3.99  
% 27.29/3.99  ------ Superposition Simplification Setup
% 27.29/3.99  
% 27.29/3.99  --sup_indices_passive                   []
% 27.29/3.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.29/3.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.29/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.29/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.29/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.29/3.99  --sup_full_bw                           [BwDemod]
% 27.29/3.99  --sup_immed_triv                        [TrivRules]
% 27.29/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.29/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.29/3.99  --sup_immed_bw_main                     []
% 27.29/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.29/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.29/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.29/3.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.29/3.99  
% 27.29/3.99  ------ Combination Options
% 27.29/3.99  
% 27.29/3.99  --comb_res_mult                         3
% 27.29/3.99  --comb_sup_mult                         2
% 27.29/3.99  --comb_inst_mult                        10
% 27.29/3.99  
% 27.29/3.99  ------ Debug Options
% 27.29/3.99  
% 27.29/3.99  --dbg_backtrace                         false
% 27.29/3.99  --dbg_dump_prop_clauses                 false
% 27.29/3.99  --dbg_dump_prop_clauses_file            -
% 27.29/3.99  --dbg_out_stat                          false
% 27.29/3.99  ------ Parsing...
% 27.29/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.29/3.99  
% 27.29/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 27.29/3.99  
% 27.29/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.29/3.99  
% 27.29/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.29/3.99  ------ Proving...
% 27.29/3.99  ------ Problem Properties 
% 27.29/3.99  
% 27.29/3.99  
% 27.29/3.99  clauses                                 16
% 27.29/3.99  conjectures                             3
% 27.29/3.99  EPR                                     1
% 27.29/3.99  Horn                                    13
% 27.29/3.99  unary                                   7
% 27.29/3.99  binary                                  8
% 27.29/3.99  lits                                    26
% 27.29/3.99  lits eq                                 9
% 27.29/3.99  fd_pure                                 0
% 27.29/3.99  fd_pseudo                               0
% 27.29/3.99  fd_cond                                 0
% 27.29/3.99  fd_pseudo_cond                          0
% 27.29/3.99  AC symbols                              0
% 27.29/3.99  
% 27.29/3.99  ------ Schedule dynamic 5 is on 
% 27.29/3.99  
% 27.29/3.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.29/3.99  
% 27.29/3.99  
% 27.29/3.99  ------ 
% 27.29/3.99  Current options:
% 27.29/3.99  ------ 
% 27.29/3.99  
% 27.29/3.99  ------ Input Options
% 27.29/3.99  
% 27.29/3.99  --out_options                           all
% 27.29/3.99  --tptp_safe_out                         true
% 27.29/3.99  --problem_path                          ""
% 27.29/3.99  --include_path                          ""
% 27.29/3.99  --clausifier                            res/vclausify_rel
% 27.29/3.99  --clausifier_options                    --mode clausify
% 27.29/3.99  --stdin                                 false
% 27.29/3.99  --stats_out                             all
% 27.29/3.99  
% 27.29/3.99  ------ General Options
% 27.29/3.99  
% 27.29/3.99  --fof                                   false
% 27.29/3.99  --time_out_real                         305.
% 27.29/3.99  --time_out_virtual                      -1.
% 27.29/3.99  --symbol_type_check                     false
% 27.29/3.99  --clausify_out                          false
% 27.29/3.99  --sig_cnt_out                           false
% 27.29/3.99  --trig_cnt_out                          false
% 27.29/3.99  --trig_cnt_out_tolerance                1.
% 27.29/3.99  --trig_cnt_out_sk_spl                   false
% 27.29/3.99  --abstr_cl_out                          false
% 27.29/3.99  
% 27.29/3.99  ------ Global Options
% 27.29/3.99  
% 27.29/3.99  --schedule                              default
% 27.29/3.99  --add_important_lit                     false
% 27.29/3.99  --prop_solver_per_cl                    1000
% 27.29/3.99  --min_unsat_core                        false
% 27.29/3.99  --soft_assumptions                      false
% 27.29/3.99  --soft_lemma_size                       3
% 27.29/3.99  --prop_impl_unit_size                   0
% 27.29/3.99  --prop_impl_unit                        []
% 27.29/3.99  --share_sel_clauses                     true
% 27.29/3.99  --reset_solvers                         false
% 27.29/3.99  --bc_imp_inh                            [conj_cone]
% 27.29/3.99  --conj_cone_tolerance                   3.
% 27.29/3.99  --extra_neg_conj                        none
% 27.29/3.99  --large_theory_mode                     true
% 27.29/3.99  --prolific_symb_bound                   200
% 27.29/3.99  --lt_threshold                          2000
% 27.29/3.99  --clause_weak_htbl                      true
% 27.29/3.99  --gc_record_bc_elim                     false
% 27.29/3.99  
% 27.29/3.99  ------ Preprocessing Options
% 27.29/3.99  
% 27.29/3.99  --preprocessing_flag                    true
% 27.29/3.99  --time_out_prep_mult                    0.1
% 27.29/3.99  --splitting_mode                        input
% 27.29/3.99  --splitting_grd                         true
% 27.29/3.99  --splitting_cvd                         false
% 27.29/3.99  --splitting_cvd_svl                     false
% 27.29/3.99  --splitting_nvd                         32
% 27.29/3.99  --sub_typing                            true
% 27.29/3.99  --prep_gs_sim                           true
% 27.29/3.99  --prep_unflatten                        true
% 27.29/3.99  --prep_res_sim                          true
% 27.29/3.99  --prep_upred                            true
% 27.29/3.99  --prep_sem_filter                       exhaustive
% 27.29/3.99  --prep_sem_filter_out                   false
% 27.29/3.99  --pred_elim                             true
% 27.29/3.99  --res_sim_input                         true
% 27.29/3.99  --eq_ax_congr_red                       true
% 27.29/3.99  --pure_diseq_elim                       true
% 27.29/3.99  --brand_transform                       false
% 27.29/3.99  --non_eq_to_eq                          false
% 27.29/3.99  --prep_def_merge                        true
% 27.29/3.99  --prep_def_merge_prop_impl              false
% 27.29/3.99  --prep_def_merge_mbd                    true
% 27.29/3.99  --prep_def_merge_tr_red                 false
% 27.29/3.99  --prep_def_merge_tr_cl                  false
% 27.29/3.99  --smt_preprocessing                     true
% 27.29/3.99  --smt_ac_axioms                         fast
% 27.29/3.99  --preprocessed_out                      false
% 27.29/3.99  --preprocessed_stats                    false
% 27.29/3.99  
% 27.29/3.99  ------ Abstraction refinement Options
% 27.29/3.99  
% 27.29/3.99  --abstr_ref                             []
% 27.29/3.99  --abstr_ref_prep                        false
% 27.29/3.99  --abstr_ref_until_sat                   false
% 27.29/3.99  --abstr_ref_sig_restrict                funpre
% 27.29/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.29/3.99  --abstr_ref_under                       []
% 27.29/3.99  
% 27.29/3.99  ------ SAT Options
% 27.29/3.99  
% 27.29/3.99  --sat_mode                              false
% 27.29/3.99  --sat_fm_restart_options                ""
% 27.29/3.99  --sat_gr_def                            false
% 27.29/3.99  --sat_epr_types                         true
% 27.29/3.99  --sat_non_cyclic_types                  false
% 27.29/3.99  --sat_finite_models                     false
% 27.29/3.99  --sat_fm_lemmas                         false
% 27.29/3.99  --sat_fm_prep                           false
% 27.29/3.99  --sat_fm_uc_incr                        true
% 27.29/3.99  --sat_out_model                         small
% 27.29/3.99  --sat_out_clauses                       false
% 27.29/3.99  
% 27.29/3.99  ------ QBF Options
% 27.29/3.99  
% 27.29/3.99  --qbf_mode                              false
% 27.29/3.99  --qbf_elim_univ                         false
% 27.29/3.99  --qbf_dom_inst                          none
% 27.29/3.99  --qbf_dom_pre_inst                      false
% 27.29/3.99  --qbf_sk_in                             false
% 27.29/3.99  --qbf_pred_elim                         true
% 27.29/3.99  --qbf_split                             512
% 27.29/3.99  
% 27.29/3.99  ------ BMC1 Options
% 27.29/3.99  
% 27.29/3.99  --bmc1_incremental                      false
% 27.29/3.99  --bmc1_axioms                           reachable_all
% 27.29/3.99  --bmc1_min_bound                        0
% 27.29/3.99  --bmc1_max_bound                        -1
% 27.29/3.99  --bmc1_max_bound_default                -1
% 27.29/3.99  --bmc1_symbol_reachability              true
% 27.29/3.99  --bmc1_property_lemmas                  false
% 27.29/3.99  --bmc1_k_induction                      false
% 27.29/3.99  --bmc1_non_equiv_states                 false
% 27.29/3.99  --bmc1_deadlock                         false
% 27.29/3.99  --bmc1_ucm                              false
% 27.29/3.99  --bmc1_add_unsat_core                   none
% 27.29/3.99  --bmc1_unsat_core_children              false
% 27.29/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.29/3.99  --bmc1_out_stat                         full
% 27.29/3.99  --bmc1_ground_init                      false
% 27.29/3.99  --bmc1_pre_inst_next_state              false
% 27.29/3.99  --bmc1_pre_inst_state                   false
% 27.29/3.99  --bmc1_pre_inst_reach_state             false
% 27.29/3.99  --bmc1_out_unsat_core                   false
% 27.29/3.99  --bmc1_aig_witness_out                  false
% 27.29/3.99  --bmc1_verbose                          false
% 27.29/3.99  --bmc1_dump_clauses_tptp                false
% 27.29/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.29/3.99  --bmc1_dump_file                        -
% 27.29/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.29/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.29/3.99  --bmc1_ucm_extend_mode                  1
% 27.29/3.99  --bmc1_ucm_init_mode                    2
% 27.29/3.99  --bmc1_ucm_cone_mode                    none
% 27.29/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.29/3.99  --bmc1_ucm_relax_model                  4
% 27.29/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.29/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.29/3.99  --bmc1_ucm_layered_model                none
% 27.29/3.99  --bmc1_ucm_max_lemma_size               10
% 27.29/3.99  
% 27.29/3.99  ------ AIG Options
% 27.29/3.99  
% 27.29/3.99  --aig_mode                              false
% 27.29/3.99  
% 27.29/3.99  ------ Instantiation Options
% 27.29/3.99  
% 27.29/3.99  --instantiation_flag                    true
% 27.29/3.99  --inst_sos_flag                         false
% 27.29/3.99  --inst_sos_phase                        true
% 27.29/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.29/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.29/3.99  --inst_lit_sel_side                     none
% 27.29/3.99  --inst_solver_per_active                1400
% 27.29/3.99  --inst_solver_calls_frac                1.
% 27.29/3.99  --inst_passive_queue_type               priority_queues
% 27.29/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.29/3.99  --inst_passive_queues_freq              [25;2]
% 27.29/3.99  --inst_dismatching                      true
% 27.29/3.99  --inst_eager_unprocessed_to_passive     true
% 27.29/3.99  --inst_prop_sim_given                   true
% 27.29/3.99  --inst_prop_sim_new                     false
% 27.29/3.99  --inst_subs_new                         false
% 27.29/3.99  --inst_eq_res_simp                      false
% 27.29/3.99  --inst_subs_given                       false
% 27.29/3.99  --inst_orphan_elimination               true
% 27.29/3.99  --inst_learning_loop_flag               true
% 27.29/3.99  --inst_learning_start                   3000
% 27.29/3.99  --inst_learning_factor                  2
% 27.29/3.99  --inst_start_prop_sim_after_learn       3
% 27.29/3.99  --inst_sel_renew                        solver
% 27.29/3.99  --inst_lit_activity_flag                true
% 27.29/3.99  --inst_restr_to_given                   false
% 27.29/3.99  --inst_activity_threshold               500
% 27.29/3.99  --inst_out_proof                        true
% 27.29/3.99  
% 27.29/3.99  ------ Resolution Options
% 27.29/3.99  
% 27.29/3.99  --resolution_flag                       false
% 27.29/3.99  --res_lit_sel                           adaptive
% 27.29/3.99  --res_lit_sel_side                      none
% 27.29/3.99  --res_ordering                          kbo
% 27.29/3.99  --res_to_prop_solver                    active
% 27.29/3.99  --res_prop_simpl_new                    false
% 27.29/3.99  --res_prop_simpl_given                  true
% 27.29/3.99  --res_passive_queue_type                priority_queues
% 27.29/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.29/3.99  --res_passive_queues_freq               [15;5]
% 27.29/3.99  --res_forward_subs                      full
% 27.29/3.99  --res_backward_subs                     full
% 27.29/3.99  --res_forward_subs_resolution           true
% 27.29/3.99  --res_backward_subs_resolution          true
% 27.29/3.99  --res_orphan_elimination                true
% 27.29/3.99  --res_time_limit                        2.
% 27.29/3.99  --res_out_proof                         true
% 27.29/3.99  
% 27.29/3.99  ------ Superposition Options
% 27.29/3.99  
% 27.29/3.99  --superposition_flag                    true
% 27.29/3.99  --sup_passive_queue_type                priority_queues
% 27.29/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.29/3.99  --sup_passive_queues_freq               [8;1;4]
% 27.29/3.99  --demod_completeness_check              fast
% 27.29/3.99  --demod_use_ground                      true
% 27.29/3.99  --sup_to_prop_solver                    passive
% 27.29/3.99  --sup_prop_simpl_new                    true
% 27.29/3.99  --sup_prop_simpl_given                  true
% 27.29/3.99  --sup_fun_splitting                     false
% 27.29/3.99  --sup_smt_interval                      50000
% 27.29/3.99  
% 27.29/3.99  ------ Superposition Simplification Setup
% 27.29/3.99  
% 27.29/3.99  --sup_indices_passive                   []
% 27.29/3.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.29/3.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.29/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.29/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.29/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.29/3.99  --sup_full_bw                           [BwDemod]
% 27.29/3.99  --sup_immed_triv                        [TrivRules]
% 27.29/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.29/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.29/3.99  --sup_immed_bw_main                     []
% 27.29/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.29/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.29/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.29/3.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.29/3.99  
% 27.29/3.99  ------ Combination Options
% 27.29/3.99  
% 27.29/3.99  --comb_res_mult                         3
% 27.29/3.99  --comb_sup_mult                         2
% 27.29/3.99  --comb_inst_mult                        10
% 27.29/3.99  
% 27.29/3.99  ------ Debug Options
% 27.29/3.99  
% 27.29/3.99  --dbg_backtrace                         false
% 27.29/3.99  --dbg_dump_prop_clauses                 false
% 27.29/3.99  --dbg_dump_prop_clauses_file            -
% 27.29/3.99  --dbg_out_stat                          false
% 27.29/3.99  
% 27.29/3.99  
% 27.29/3.99  
% 27.29/3.99  
% 27.29/3.99  ------ Proving...
% 27.29/3.99  
% 27.29/3.99  
% 27.29/3.99  % SZS status Theorem for theBenchmark.p
% 27.29/3.99  
% 27.29/3.99  % SZS output start CNFRefutation for theBenchmark.p
% 27.29/3.99  
% 27.29/3.99  fof(f11,axiom,(
% 27.29/3.99    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 27.29/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.29/3.99  
% 27.29/3.99  fof(f39,plain,(
% 27.29/3.99    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 27.29/3.99    inference(cnf_transformation,[],[f11])).
% 27.29/3.99  
% 27.29/3.99  fof(f10,axiom,(
% 27.29/3.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 27.29/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.29/3.99  
% 27.29/3.99  fof(f38,plain,(
% 27.29/3.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 27.29/3.99    inference(cnf_transformation,[],[f10])).
% 27.29/3.99  
% 27.29/3.99  fof(f53,plain,(
% 27.29/3.99    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 27.29/3.99    inference(definition_unfolding,[],[f39,f38])).
% 27.29/3.99  
% 27.29/3.99  fof(f1,axiom,(
% 27.29/3.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 27.29/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.29/3.99  
% 27.29/3.99  fof(f27,plain,(
% 27.29/3.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 27.29/3.99    inference(cnf_transformation,[],[f1])).
% 27.29/3.99  
% 27.29/3.99  fof(f6,axiom,(
% 27.29/3.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 27.29/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.29/3.99  
% 27.29/3.99  fof(f34,plain,(
% 27.29/3.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 27.29/3.99    inference(cnf_transformation,[],[f6])).
% 27.29/3.99  
% 27.29/3.99  fof(f52,plain,(
% 27.29/3.99    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 27.29/3.99    inference(definition_unfolding,[],[f34,f38])).
% 27.29/3.99  
% 27.29/3.99  fof(f8,axiom,(
% 27.29/3.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 27.29/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.29/3.99  
% 27.29/3.99  fof(f36,plain,(
% 27.29/3.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.29/3.99    inference(cnf_transformation,[],[f8])).
% 27.29/3.99  
% 27.29/3.99  fof(f9,axiom,(
% 27.29/3.99    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 27.29/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.29/3.99  
% 27.29/3.99  fof(f37,plain,(
% 27.29/3.99    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 27.29/3.99    inference(cnf_transformation,[],[f9])).
% 27.29/3.99  
% 27.29/3.99  fof(f5,axiom,(
% 27.29/3.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 27.29/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.29/3.99  
% 27.29/3.99  fof(f33,plain,(
% 27.29/3.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.29/3.99    inference(cnf_transformation,[],[f5])).
% 27.29/3.99  
% 27.29/3.99  fof(f7,axiom,(
% 27.29/3.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 27.29/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.29/3.99  
% 27.29/3.99  fof(f35,plain,(
% 27.29/3.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 27.29/3.99    inference(cnf_transformation,[],[f7])).
% 27.29/3.99  
% 27.29/3.99  fof(f14,conjecture,(
% 27.29/3.99    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 27.29/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.29/3.99  
% 27.29/3.99  fof(f15,negated_conjecture,(
% 27.29/3.99    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 27.29/3.99    inference(negated_conjecture,[],[f14])).
% 27.29/3.99  
% 27.29/3.99  fof(f21,plain,(
% 27.29/3.99    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 27.29/3.99    inference(ennf_transformation,[],[f15])).
% 27.29/3.99  
% 27.29/3.99  fof(f25,plain,(
% 27.29/3.99    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) & (~r1_xboole_0(sK1,sK3) | ~r1_xboole_0(sK1,sK2))) | (r1_xboole_0(sK1,sK3) & r1_xboole_0(sK1,sK2) & ~r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))))),
% 27.29/3.99    introduced(choice_axiom,[])).
% 27.29/3.99  
% 27.29/3.99  fof(f26,plain,(
% 27.29/3.99    (r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) & (~r1_xboole_0(sK1,sK3) | ~r1_xboole_0(sK1,sK2))) | (r1_xboole_0(sK1,sK3) & r1_xboole_0(sK1,sK2) & ~r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)))),
% 27.29/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f21,f25])).
% 27.29/3.99  
% 27.29/3.99  fof(f47,plain,(
% 27.29/3.99    r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | r1_xboole_0(sK1,sK3)),
% 27.29/3.99    inference(cnf_transformation,[],[f26])).
% 27.29/3.99  
% 27.29/3.99  fof(f3,axiom,(
% 27.29/3.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 27.29/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.29/3.99  
% 27.29/3.99  fof(f17,plain,(
% 27.29/3.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 27.29/3.99    inference(ennf_transformation,[],[f3])).
% 27.29/3.99  
% 27.29/3.99  fof(f30,plain,(
% 27.29/3.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 27.29/3.99    inference(cnf_transformation,[],[f17])).
% 27.29/3.99  
% 27.29/3.99  fof(f12,axiom,(
% 27.29/3.99    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 27.29/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.29/3.99  
% 27.29/3.99  fof(f19,plain,(
% 27.29/3.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 27.29/3.99    inference(ennf_transformation,[],[f12])).
% 27.29/3.99  
% 27.29/3.99  fof(f20,plain,(
% 27.29/3.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 27.29/3.99    inference(flattening,[],[f19])).
% 27.29/3.99  
% 27.29/3.99  fof(f40,plain,(
% 27.29/3.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 27.29/3.99    inference(cnf_transformation,[],[f20])).
% 27.29/3.99  
% 27.29/3.99  fof(f13,axiom,(
% 27.29/3.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 27.29/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.29/3.99  
% 27.29/3.99  fof(f41,plain,(
% 27.29/3.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 27.29/3.99    inference(cnf_transformation,[],[f13])).
% 27.29/3.99  
% 27.29/3.99  fof(f2,axiom,(
% 27.29/3.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 27.29/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.29/3.99  
% 27.29/3.99  fof(f22,plain,(
% 27.29/3.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 27.29/3.99    inference(nnf_transformation,[],[f2])).
% 27.29/3.99  
% 27.29/3.99  fof(f28,plain,(
% 27.29/3.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 27.29/3.99    inference(cnf_transformation,[],[f22])).
% 27.29/3.99  
% 27.29/3.99  fof(f49,plain,(
% 27.29/3.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 27.29/3.99    inference(definition_unfolding,[],[f28,f38])).
% 27.29/3.99  
% 27.29/3.99  fof(f29,plain,(
% 27.29/3.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 27.29/3.99    inference(cnf_transformation,[],[f22])).
% 27.29/3.99  
% 27.29/3.99  fof(f48,plain,(
% 27.29/3.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 27.29/3.99    inference(definition_unfolding,[],[f29,f38])).
% 27.29/3.99  
% 27.29/3.99  fof(f42,plain,(
% 27.29/3.99    ~r1_xboole_0(sK1,sK3) | ~r1_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))),
% 27.29/3.99    inference(cnf_transformation,[],[f26])).
% 27.29/3.99  
% 27.29/3.99  fof(f46,plain,(
% 27.29/3.99    r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | r1_xboole_0(sK1,sK2)),
% 27.29/3.99    inference(cnf_transformation,[],[f26])).
% 27.29/3.99  
% 27.29/3.99  cnf(c_11,plain,
% 27.29/3.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 27.29/3.99      inference(cnf_transformation,[],[f53]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_0,plain,
% 27.29/3.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 27.29/3.99      inference(cnf_transformation,[],[f27]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_7,plain,
% 27.29/3.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 27.29/3.99      inference(cnf_transformation,[],[f52]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_9,plain,
% 27.29/3.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.29/3.99      inference(cnf_transformation,[],[f36]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_589,plain,
% 27.29/3.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 27.29/3.99      inference(light_normalisation,[status(thm)],[c_7,c_9]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_10,plain,
% 27.29/3.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 27.29/3.99      inference(cnf_transformation,[],[f37]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_914,plain,
% 27.29/3.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 27.29/3.99      inference(superposition,[status(thm)],[c_589,c_10]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_6,plain,
% 27.29/3.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.29/3.99      inference(cnf_transformation,[],[f33]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_920,plain,
% 27.29/3.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 27.29/3.99      inference(demodulation,[status(thm)],[c_914,c_6]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_1122,plain,
% 27.29/3.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 27.29/3.99      inference(superposition,[status(thm)],[c_0,c_920]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_8,plain,
% 27.29/3.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 27.29/3.99      inference(cnf_transformation,[],[f35]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_1246,plain,
% 27.29/3.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 27.29/3.99      inference(superposition,[status(thm)],[c_1122,c_8]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_1252,plain,
% 27.29/3.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 27.29/3.99      inference(light_normalisation,[status(thm)],[c_1246,c_8]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_1404,plain,
% 27.29/3.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 27.29/3.99      inference(superposition,[status(thm)],[c_1252,c_920]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_1410,plain,
% 27.29/3.99      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 27.29/3.99      inference(demodulation,[status(thm)],[c_1404,c_589]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_1424,plain,
% 27.29/3.99      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 27.29/3.99      inference(superposition,[status(thm)],[c_0,c_1410]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_1616,plain,
% 27.29/3.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 27.29/3.99      inference(superposition,[status(thm)],[c_11,c_1424]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_1750,plain,
% 27.29/3.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 27.29/3.99      inference(superposition,[status(thm)],[c_1616,c_8]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_1756,plain,
% 27.29/3.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 27.29/3.99      inference(light_normalisation,[status(thm)],[c_1750,c_6]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_1132,plain,
% 27.29/3.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 27.29/3.99      inference(superposition,[status(thm)],[c_920,c_8]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_1138,plain,
% 27.29/3.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 27.29/3.99      inference(light_normalisation,[status(thm)],[c_1132,c_8]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_1405,plain,
% 27.29/3.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 27.29/3.99      inference(superposition,[status(thm)],[c_1252,c_1138]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_884,plain,
% 27.29/3.99      ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 27.29/3.99      inference(superposition,[status(thm)],[c_589,c_8]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_885,plain,
% 27.29/3.99      ( k2_xboole_0(X0,X0) = X0 ),
% 27.29/3.99      inference(light_normalisation,[status(thm)],[c_884,c_6]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_1407,plain,
% 27.29/3.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 27.29/3.99      inference(demodulation,[status(thm)],[c_1405,c_885]) ).
% 27.29/3.99  
% 27.29/3.99  cnf(c_2062,plain,
% 27.29/3.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 27.29/3.99      inference(superposition,[status(thm)],[c_0,c_1407]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_2791,plain,
% 27.29/4.00      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_1756,c_2062]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_2823,plain,
% 27.29/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 27.29/4.00      inference(light_normalisation,[status(thm)],[c_2791,c_1756]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_1751,plain,
% 27.29/4.00      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_1616,c_10]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_1753,plain,
% 27.29/4.00      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X1) = k4_xboole_0(X0,X1) ),
% 27.29/4.00      inference(demodulation,[status(thm)],[c_1751,c_6]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_4899,plain,
% 27.29/4.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_2823,c_1753]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_5016,plain,
% 27.29/4.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k1_xboole_0 ),
% 27.29/4.00      inference(light_normalisation,[status(thm)],[c_4899,c_1616]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_1624,plain,
% 27.29/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_1424,c_8]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_1630,plain,
% 27.29/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 27.29/4.00      inference(demodulation,[status(thm)],[c_1624,c_6]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_2562,plain,
% 27.29/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_0,c_1630]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_3060,plain,
% 27.29/4.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_8,c_2562]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_3114,plain,
% 27.29/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 27.29/4.00      inference(light_normalisation,[status(thm)],[c_3060,c_2562]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_3550,plain,
% 27.29/4.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_3114,c_0]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_5092,plain,
% 27.29/4.00      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_5016,c_3550]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_5104,plain,
% 27.29/4.00      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = X0 ),
% 27.29/4.00      inference(light_normalisation,[status(thm)],[c_5092,c_6]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_14,negated_conjecture,
% 27.29/4.00      ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | r1_xboole_0(sK1,sK3) ),
% 27.29/4.00      inference(cnf_transformation,[],[f47]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_579,plain,
% 27.29/4.00      ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = iProver_top
% 27.29/4.00      | r1_xboole_0(sK1,sK3) = iProver_top ),
% 27.29/4.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_3,plain,
% 27.29/4.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 27.29/4.00      inference(cnf_transformation,[],[f30]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_582,plain,
% 27.29/4.00      ( r1_xboole_0(X0,X1) != iProver_top
% 27.29/4.00      | r1_xboole_0(X1,X0) = iProver_top ),
% 27.29/4.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_6342,plain,
% 27.29/4.00      ( r1_xboole_0(k2_xboole_0(sK2,sK3),sK1) = iProver_top
% 27.29/4.00      | r1_xboole_0(sK1,sK3) = iProver_top ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_579,c_582]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_12,plain,
% 27.29/4.00      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 27.29/4.00      inference(cnf_transformation,[],[f40]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_13,plain,
% 27.29/4.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 27.29/4.00      inference(cnf_transformation,[],[f41]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_187,plain,
% 27.29/4.00      ( ~ r1_xboole_0(X0,X1)
% 27.29/4.00      | r1_xboole_0(X2,X1)
% 27.29/4.00      | X3 != X2
% 27.29/4.00      | k2_xboole_0(X3,X4) != X0 ),
% 27.29/4.00      inference(resolution_lifted,[status(thm)],[c_12,c_13]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_188,plain,
% 27.29/4.00      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 27.29/4.00      inference(unflattening,[status(thm)],[c_187]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_576,plain,
% 27.29/4.00      ( r1_xboole_0(X0,X1) = iProver_top
% 27.29/4.00      | r1_xboole_0(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 27.29/4.00      inference(predicate_to_equality,[status(thm)],[c_188]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_1650,plain,
% 27.29/4.00      ( r1_xboole_0(X0,X1) = iProver_top
% 27.29/4.00      | r1_xboole_0(k2_xboole_0(X2,X0),X1) != iProver_top ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_0,c_576]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_43909,plain,
% 27.29/4.00      ( r1_xboole_0(sK3,sK1) = iProver_top
% 27.29/4.00      | r1_xboole_0(sK1,sK3) = iProver_top ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_6342,c_1650]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_1084,plain,
% 27.29/4.00      ( ~ r1_xboole_0(sK3,sK1) | r1_xboole_0(sK1,sK3) ),
% 27.29/4.00      inference(instantiation,[status(thm)],[c_3]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_1085,plain,
% 27.29/4.00      ( r1_xboole_0(sK3,sK1) != iProver_top
% 27.29/4.00      | r1_xboole_0(sK1,sK3) = iProver_top ),
% 27.29/4.00      inference(predicate_to_equality,[status(thm)],[c_1084]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_45858,plain,
% 27.29/4.00      ( r1_xboole_0(sK1,sK3) = iProver_top ),
% 27.29/4.00      inference(global_propositional_subsumption,
% 27.29/4.00                [status(thm)],
% 27.29/4.00                [c_43909,c_1085]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_2,plain,
% 27.29/4.00      ( ~ r1_xboole_0(X0,X1)
% 27.29/4.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 27.29/4.00      inference(cnf_transformation,[],[f49]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_583,plain,
% 27.29/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 27.29/4.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 27.29/4.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_9377,plain,
% 27.29/4.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) = k1_xboole_0
% 27.29/4.00      | r1_xboole_0(sK1,sK3) = iProver_top ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_579,c_583]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_11310,plain,
% 27.29/4.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) = k1_xboole_0
% 27.29/4.00      | r1_xboole_0(sK3,sK1) = iProver_top ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_9377,c_582]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_11661,plain,
% 27.29/4.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0
% 27.29/4.00      | k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) = k1_xboole_0 ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_11310,c_583]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_1,plain,
% 27.29/4.00      ( r1_xboole_0(X0,X1)
% 27.29/4.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 27.29/4.00      inference(cnf_transformation,[],[f48]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_584,plain,
% 27.29/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 27.29/4.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 27.29/4.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_13034,plain,
% 27.29/4.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0
% 27.29/4.00      | r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = iProver_top ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_11661,c_584]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_19,negated_conjecture,
% 27.29/4.00      ( ~ r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
% 27.29/4.00      | ~ r1_xboole_0(sK1,sK3)
% 27.29/4.00      | ~ r1_xboole_0(sK1,sK2) ),
% 27.29/4.00      inference(cnf_transformation,[],[f42]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_577,plain,
% 27.29/4.00      ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) != iProver_top
% 27.29/4.00      | r1_xboole_0(sK1,sK3) != iProver_top
% 27.29/4.00      | r1_xboole_0(sK1,sK2) != iProver_top ),
% 27.29/4.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_17270,plain,
% 27.29/4.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0
% 27.29/4.00      | r1_xboole_0(sK1,sK3) != iProver_top
% 27.29/4.00      | r1_xboole_0(sK1,sK2) != iProver_top ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_13034,c_577]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_15,negated_conjecture,
% 27.29/4.00      ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | r1_xboole_0(sK1,sK2) ),
% 27.29/4.00      inference(cnf_transformation,[],[f46]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_578,plain,
% 27.29/4.00      ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = iProver_top
% 27.29/4.00      | r1_xboole_0(sK1,sK2) = iProver_top ),
% 27.29/4.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_6343,plain,
% 27.29/4.00      ( r1_xboole_0(k2_xboole_0(sK2,sK3),sK1) = iProver_top
% 27.29/4.00      | r1_xboole_0(sK1,sK2) = iProver_top ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_578,c_582]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_718,plain,
% 27.29/4.00      ( ~ r1_xboole_0(k2_xboole_0(sK2,sK3),sK1) | r1_xboole_0(sK2,sK1) ),
% 27.29/4.00      inference(instantiation,[status(thm)],[c_188]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_719,plain,
% 27.29/4.00      ( r1_xboole_0(k2_xboole_0(sK2,sK3),sK1) != iProver_top
% 27.29/4.00      | r1_xboole_0(sK2,sK1) = iProver_top ),
% 27.29/4.00      inference(predicate_to_equality,[status(thm)],[c_718]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_859,plain,
% 27.29/4.00      ( ~ r1_xboole_0(sK2,sK1) | r1_xboole_0(sK1,sK2) ),
% 27.29/4.00      inference(instantiation,[status(thm)],[c_3]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_860,plain,
% 27.29/4.00      ( r1_xboole_0(sK2,sK1) != iProver_top
% 27.29/4.00      | r1_xboole_0(sK1,sK2) = iProver_top ),
% 27.29/4.00      inference(predicate_to_equality,[status(thm)],[c_859]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_7949,plain,
% 27.29/4.00      ( r1_xboole_0(sK1,sK2) = iProver_top ),
% 27.29/4.00      inference(global_propositional_subsumption,
% 27.29/4.00                [status(thm)],
% 27.29/4.00                [c_6343,c_719,c_860]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_17495,plain,
% 27.29/4.00      ( r1_xboole_0(sK1,sK3) != iProver_top
% 27.29/4.00      | k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
% 27.29/4.00      inference(global_propositional_subsumption,
% 27.29/4.00                [status(thm)],
% 27.29/4.00                [c_17270,c_719,c_860,c_6343]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_17496,plain,
% 27.29/4.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0
% 27.29/4.00      | r1_xboole_0(sK1,sK3) != iProver_top ),
% 27.29/4.00      inference(renaming,[status(thm)],[c_17495]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_45865,plain,
% 27.29/4.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_45858,c_17496]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_45920,plain,
% 27.29/4.00      ( k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_45865,c_8]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_45930,plain,
% 27.29/4.00      ( k4_xboole_0(sK3,sK1) = sK3 ),
% 27.29/4.00      inference(demodulation,[status(thm)],[c_45920,c_6,c_2823]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_7954,plain,
% 27.29/4.00      ( r1_xboole_0(sK2,sK1) = iProver_top ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_7949,c_582]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_9381,plain,
% 27.29/4.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_7954,c_583]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_12067,plain,
% 27.29/4.00      ( k2_xboole_0(k4_xboole_0(sK2,sK1),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK2,sK1),sK2) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_9381,c_8]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_12077,plain,
% 27.29/4.00      ( k4_xboole_0(sK2,sK1) = sK2 ),
% 27.29/4.00      inference(demodulation,[status(thm)],[c_12067,c_6,c_2823]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_12899,plain,
% 27.29/4.00      ( k4_xboole_0(k2_xboole_0(sK2,X0),sK1) = k2_xboole_0(sK2,k4_xboole_0(X0,sK1)) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_12077,c_10]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_15190,plain,
% 27.29/4.00      ( k2_xboole_0(k4_xboole_0(X0,sK1),k2_xboole_0(sK2,k4_xboole_0(X1,sK1))) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK2,X1)),sK1) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_12899,c_10]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_118380,plain,
% 27.29/4.00      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK2,sK3)),sK1) = k2_xboole_0(k4_xboole_0(X0,sK1),k2_xboole_0(sK2,sK3)) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_45930,c_15190]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_122955,plain,
% 27.29/4.00      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1),k2_xboole_0(sK2,sK3)) = k4_xboole_0(k2_xboole_0(sK2,sK3),sK1) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_5104,c_118380]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_123461,plain,
% 27.29/4.00      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1),k2_xboole_0(sK2,sK3)) = k2_xboole_0(sK2,sK3) ),
% 27.29/4.00      inference(demodulation,[status(thm)],[c_122955,c_12899,c_45930]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_915,plain,
% 27.29/4.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_10,c_0]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_7370,plain,
% 27.29/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0)) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_9,c_915]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_7536,plain,
% 27.29/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 27.29/4.00      inference(light_normalisation,[status(thm)],[c_7370,c_9]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_118461,plain,
% 27.29/4.00      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK2,X1)),sK1),k1_xboole_0) = k2_xboole_0(k2_xboole_0(sK2,k4_xboole_0(X1,sK1)),k4_xboole_0(X0,sK1)) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_15190,c_7536]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_15178,plain,
% 27.29/4.00      ( k2_xboole_0(k2_xboole_0(sK2,k4_xboole_0(X0,sK1)),k4_xboole_0(X1,sK1)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(sK2,X0),X1),sK1) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_12899,c_10]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_118815,plain,
% 27.29/4.00      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK2,X1)),sK1) = k4_xboole_0(k2_xboole_0(k2_xboole_0(sK2,X1),X0),sK1) ),
% 27.29/4.00      inference(demodulation,[status(thm)],[c_118461,c_9,c_15178]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_119463,plain,
% 27.29/4.00      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,sK2),X1),sK1) = k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(sK2,X0)),sK1) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_0,c_118815]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_126310,plain,
% 27.29/4.00      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1)),sK1) = k4_xboole_0(k2_xboole_0(sK2,sK3),sK1) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_123461,c_119463]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_1239,plain,
% 27.29/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_8,c_1122]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_1263,plain,
% 27.29/4.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 27.29/4.00      inference(demodulation,[status(thm)],[c_1239,c_1122]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_1935,plain,
% 27.29/4.00      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_1263,c_10]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_1938,plain,
% 27.29/4.00      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 27.29/4.00      inference(demodulation,[status(thm)],[c_1935,c_10]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_127257,plain,
% 27.29/4.00      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1)),sK1) = k2_xboole_0(sK2,sK3) ),
% 27.29/4.00      inference(demodulation,
% 27.29/4.00                [status(thm)],
% 27.29/4.00                [c_126310,c_1938,c_12899,c_45930]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_129002,plain,
% 27.29/4.00      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1)),k2_xboole_0(sK2,sK3)) != k1_xboole_0
% 27.29/4.00      | r1_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1)),sK1) = iProver_top ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_127257,c_584]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_1619,plain,
% 27.29/4.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_1138,c_1424]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_2486,plain,
% 27.29/4.00      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k2_xboole_0(X1,X0))) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_1619,c_10]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_878,plain,
% 27.29/4.00      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_2500,plain,
% 27.29/4.00      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X1,X0)) = k4_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 27.29/4.00      inference(demodulation,[status(thm)],[c_2486,c_878]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_129332,plain,
% 27.29/4.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1),k2_xboole_0(sK2,sK3)) != k1_xboole_0
% 27.29/4.00      | r1_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1)),sK1) = iProver_top ),
% 27.29/4.00      inference(demodulation,[status(thm)],[c_129002,c_2500]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_129489,plain,
% 27.29/4.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),sK1),sK1),sK1),k2_xboole_0(sK2,sK3)) != k1_xboole_0
% 27.29/4.00      | r1_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),sK1),sK1),sK1)),sK1) = iProver_top ),
% 27.29/4.00      inference(instantiation,[status(thm)],[c_129332]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_2886,plain,
% 27.29/4.00      ( r1_xboole_0(X0,X1) != iProver_top
% 27.29/4.00      | r1_xboole_0(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_2823,c_576]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_129050,plain,
% 27.29/4.00      ( r1_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1)),X2) != iProver_top
% 27.29/4.00      | r1_xboole_0(k2_xboole_0(sK2,sK3),X2) = iProver_top ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_127257,c_2886]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_129464,plain,
% 27.29/4.00      ( r1_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),sK1),sK1),sK1)),sK1) != iProver_top
% 27.29/4.00      | r1_xboole_0(k2_xboole_0(sK2,sK3),sK1) = iProver_top ),
% 27.29/4.00      inference(instantiation,[status(thm)],[c_129050]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_5093,plain,
% 27.29/4.00      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,k1_xboole_0) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_5016,c_8]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_5101,plain,
% 27.29/4.00      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2)) = X0 ),
% 27.29/4.00      inference(light_normalisation,[status(thm)],[c_5093,c_6]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_117338,plain,
% 27.29/4.00      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK2,sK3),X0),sK1) = k2_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(X0,sK1)) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_45930,c_15178]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_120739,plain,
% 27.29/4.00      ( k2_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1)) = k4_xboole_0(k2_xboole_0(sK2,sK3),sK1) ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_5101,c_117338]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_121198,plain,
% 27.29/4.00      ( k2_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1)) = k2_xboole_0(sK2,sK3) ),
% 27.29/4.00      inference(demodulation,[status(thm)],[c_120739,c_12899,c_45930]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_124251,plain,
% 27.29/4.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),X0),X1),sK1),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 27.29/4.00      inference(superposition,[status(thm)],[c_121198,c_1424]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_124592,plain,
% 27.29/4.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),sK1),sK1),sK1),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 27.29/4.00      inference(instantiation,[status(thm)],[c_124251]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_704,plain,
% 27.29/4.00      ( ~ r1_xboole_0(k2_xboole_0(sK2,sK3),sK1)
% 27.29/4.00      | r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
% 27.29/4.00      inference(instantiation,[status(thm)],[c_3]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_705,plain,
% 27.29/4.00      ( r1_xboole_0(k2_xboole_0(sK2,sK3),sK1) != iProver_top
% 27.29/4.00      | r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = iProver_top ),
% 27.29/4.00      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(c_20,plain,
% 27.29/4.00      ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) != iProver_top
% 27.29/4.00      | r1_xboole_0(sK1,sK3) != iProver_top
% 27.29/4.00      | r1_xboole_0(sK1,sK2) != iProver_top ),
% 27.29/4.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 27.29/4.00  
% 27.29/4.00  cnf(contradiction,plain,
% 27.29/4.00      ( $false ),
% 27.29/4.00      inference(minisat,
% 27.29/4.00                [status(thm)],
% 27.29/4.00                [c_129489,c_129464,c_124592,c_45858,c_7949,c_705,c_20]) ).
% 27.29/4.00  
% 27.29/4.00  
% 27.29/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.29/4.00  
% 27.29/4.00  ------                               Statistics
% 27.29/4.00  
% 27.29/4.00  ------ General
% 27.29/4.00  
% 27.29/4.00  abstr_ref_over_cycles:                  0
% 27.29/4.00  abstr_ref_under_cycles:                 0
% 27.29/4.00  gc_basic_clause_elim:                   0
% 27.29/4.00  forced_gc_time:                         0
% 27.29/4.00  parsing_time:                           0.01
% 27.29/4.00  unif_index_cands_time:                  0.
% 27.29/4.00  unif_index_add_time:                    0.
% 27.29/4.00  orderings_time:                         0.
% 27.29/4.00  out_proof_time:                         0.015
% 27.29/4.00  total_time:                             3.054
% 27.29/4.00  num_of_symbols:                         41
% 27.29/4.00  num_of_terms:                           145425
% 27.29/4.00  
% 27.29/4.00  ------ Preprocessing
% 27.29/4.00  
% 27.29/4.00  num_of_splits:                          0
% 27.29/4.00  num_of_split_atoms:                     0
% 27.29/4.00  num_of_reused_defs:                     0
% 27.29/4.00  num_eq_ax_congr_red:                    7
% 27.29/4.00  num_of_sem_filtered_clauses:            1
% 27.29/4.00  num_of_subtypes:                        0
% 27.29/4.00  monotx_restored_types:                  0
% 27.29/4.00  sat_num_of_epr_types:                   0
% 27.29/4.00  sat_num_of_non_cyclic_types:            0
% 27.29/4.00  sat_guarded_non_collapsed_types:        0
% 27.29/4.00  num_pure_diseq_elim:                    0
% 27.29/4.00  simp_replaced_by:                       0
% 27.29/4.00  res_preprocessed:                       78
% 27.29/4.00  prep_upred:                             0
% 27.29/4.00  prep_unflattend:                        4
% 27.29/4.00  smt_new_axioms:                         0
% 27.29/4.00  pred_elim_cands:                        2
% 27.29/4.00  pred_elim:                              1
% 27.29/4.00  pred_elim_cl:                           1
% 27.29/4.00  pred_elim_cycles:                       4
% 27.29/4.00  merged_defs:                            8
% 27.29/4.00  merged_defs_ncl:                        0
% 27.29/4.00  bin_hyper_res:                          8
% 27.29/4.00  prep_cycles:                            4
% 27.29/4.00  pred_elim_time:                         0.001
% 27.29/4.00  splitting_time:                         0.
% 27.29/4.00  sem_filter_time:                        0.
% 27.29/4.00  monotx_time:                            0.
% 27.29/4.00  subtype_inf_time:                       0.
% 27.29/4.00  
% 27.29/4.00  ------ Problem properties
% 27.29/4.00  
% 27.29/4.00  clauses:                                16
% 27.29/4.00  conjectures:                            3
% 27.29/4.00  epr:                                    1
% 27.29/4.00  horn:                                   13
% 27.29/4.00  ground:                                 3
% 27.29/4.00  unary:                                  7
% 27.29/4.00  binary:                                 8
% 27.29/4.00  lits:                                   26
% 27.29/4.00  lits_eq:                                9
% 27.29/4.00  fd_pure:                                0
% 27.29/4.00  fd_pseudo:                              0
% 27.29/4.00  fd_cond:                                0
% 27.29/4.00  fd_pseudo_cond:                         0
% 27.29/4.00  ac_symbols:                             0
% 27.29/4.00  
% 27.29/4.00  ------ Propositional Solver
% 27.29/4.00  
% 27.29/4.00  prop_solver_calls:                      31
% 27.29/4.00  prop_fast_solver_calls:                 1129
% 27.29/4.00  smt_solver_calls:                       0
% 27.29/4.00  smt_fast_solver_calls:                  0
% 27.29/4.00  prop_num_of_clauses:                    30296
% 27.29/4.00  prop_preprocess_simplified:             22425
% 27.29/4.00  prop_fo_subsumed:                       107
% 27.29/4.00  prop_solver_time:                       0.
% 27.29/4.00  smt_solver_time:                        0.
% 27.29/4.00  smt_fast_solver_time:                   0.
% 27.29/4.00  prop_fast_solver_time:                  0.
% 27.29/4.00  prop_unsat_core_time:                   0.002
% 27.29/4.00  
% 27.29/4.00  ------ QBF
% 27.29/4.00  
% 27.29/4.00  qbf_q_res:                              0
% 27.29/4.00  qbf_num_tautologies:                    0
% 27.29/4.00  qbf_prep_cycles:                        0
% 27.29/4.00  
% 27.29/4.00  ------ BMC1
% 27.29/4.00  
% 27.29/4.00  bmc1_current_bound:                     -1
% 27.29/4.00  bmc1_last_solved_bound:                 -1
% 27.29/4.00  bmc1_unsat_core_size:                   -1
% 27.29/4.00  bmc1_unsat_core_parents_size:           -1
% 27.29/4.00  bmc1_merge_next_fun:                    0
% 27.29/4.00  bmc1_unsat_core_clauses_time:           0.
% 27.29/4.00  
% 27.29/4.00  ------ Instantiation
% 27.29/4.00  
% 27.29/4.00  inst_num_of_clauses:                    3472
% 27.29/4.00  inst_num_in_passive:                    760
% 27.29/4.00  inst_num_in_active:                     1318
% 27.29/4.00  inst_num_in_unprocessed:                1394
% 27.29/4.00  inst_num_of_loops:                      1600
% 27.29/4.00  inst_num_of_learning_restarts:          0
% 27.29/4.00  inst_num_moves_active_passive:          280
% 27.29/4.00  inst_lit_activity:                      0
% 27.29/4.00  inst_lit_activity_moves:                1
% 27.29/4.00  inst_num_tautologies:                   0
% 27.29/4.00  inst_num_prop_implied:                  0
% 27.29/4.00  inst_num_existing_simplified:           0
% 27.29/4.00  inst_num_eq_res_simplified:             0
% 27.29/4.00  inst_num_child_elim:                    0
% 27.29/4.00  inst_num_of_dismatching_blockings:      5686
% 27.29/4.00  inst_num_of_non_proper_insts:           4468
% 27.29/4.00  inst_num_of_duplicates:                 0
% 27.29/4.00  inst_inst_num_from_inst_to_res:         0
% 27.29/4.00  inst_dismatching_checking_time:         0.
% 27.29/4.00  
% 27.29/4.00  ------ Resolution
% 27.29/4.00  
% 27.29/4.00  res_num_of_clauses:                     0
% 27.29/4.00  res_num_in_passive:                     0
% 27.29/4.00  res_num_in_active:                      0
% 27.29/4.00  res_num_of_loops:                       82
% 27.29/4.00  res_forward_subset_subsumed:            80
% 27.29/4.00  res_backward_subset_subsumed:           0
% 27.29/4.00  res_forward_subsumed:                   0
% 27.29/4.00  res_backward_subsumed:                  0
% 27.29/4.00  res_forward_subsumption_resolution:     0
% 27.29/4.00  res_backward_subsumption_resolution:    0
% 27.29/4.00  res_clause_to_clause_subsumption:       215793
% 27.29/4.00  res_orphan_elimination:                 0
% 27.29/4.00  res_tautology_del:                      67
% 27.29/4.00  res_num_eq_res_simplified:              0
% 27.29/4.00  res_num_sel_changes:                    0
% 27.29/4.00  res_moves_from_active_to_pass:          0
% 27.29/4.00  
% 27.29/4.00  ------ Superposition
% 27.29/4.00  
% 27.29/4.00  sup_time_total:                         0.
% 27.29/4.00  sup_time_generating:                    0.
% 27.29/4.00  sup_time_sim_full:                      0.
% 27.29/4.00  sup_time_sim_immed:                     0.
% 27.29/4.00  
% 27.29/4.00  sup_num_of_clauses:                     9264
% 27.29/4.00  sup_num_in_active:                      256
% 27.29/4.00  sup_num_in_passive:                     9008
% 27.29/4.00  sup_num_of_loops:                       319
% 27.29/4.00  sup_fw_superposition:                   17238
% 27.29/4.00  sup_bw_superposition:                   16098
% 27.29/4.00  sup_immediate_simplified:               19791
% 27.29/4.00  sup_given_eliminated:                   6
% 27.29/4.00  comparisons_done:                       0
% 27.29/4.00  comparisons_avoided:                    45
% 27.29/4.00  
% 27.29/4.00  ------ Simplifications
% 27.29/4.00  
% 27.29/4.00  
% 27.29/4.00  sim_fw_subset_subsumed:                 104
% 27.29/4.00  sim_bw_subset_subsumed:                 369
% 27.29/4.00  sim_fw_subsumed:                        3485
% 27.29/4.00  sim_bw_subsumed:                        115
% 27.29/4.00  sim_fw_subsumption_res:                 0
% 27.29/4.00  sim_bw_subsumption_res:                 0
% 27.29/4.00  sim_tautology_del:                      143
% 27.29/4.00  sim_eq_tautology_del:                   3497
% 27.29/4.00  sim_eq_res_simp:                        9
% 27.29/4.00  sim_fw_demodulated:                     9693
% 27.29/4.00  sim_bw_demodulated:                     599
% 27.29/4.00  sim_light_normalised:                   8377
% 27.29/4.00  sim_joinable_taut:                      0
% 27.29/4.00  sim_joinable_simp:                      0
% 27.29/4.00  sim_ac_normalised:                      0
% 27.29/4.00  sim_smt_subsumption:                    0
% 27.29/4.00  
%------------------------------------------------------------------------------
