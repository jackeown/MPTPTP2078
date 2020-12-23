%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:48 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :   87 (1568 expanded)
%              Number of clauses        :   63 ( 632 expanded)
%              Number of leaves         :    8 ( 356 expanded)
%              Depth                    :   23
%              Number of atoms          :  118 (2950 expanded)
%              Number of equality atoms :   94 (1983 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f11])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f13])).

fof(f22,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f23,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f21,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f24,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_8,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_53,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK0 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_54,plain,
    ( k3_xboole_0(sK2,sK0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_53])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_5,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_83,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_5])).

cnf(c_140,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) = sK0 ),
    inference(superposition,[status(thm)],[c_54,c_83])).

cnf(c_7,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_48,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_7])).

cnf(c_49,plain,
    ( k3_xboole_0(sK3,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_48])).

cnf(c_85,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) = sK3 ),
    inference(superposition,[status(thm)],[c_49,c_5])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_3,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_77,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_3])).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_94,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_77,c_4])).

cnf(c_98,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_94,c_4])).

cnf(c_1332,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK3) ),
    inference(superposition,[status(thm)],[c_85,c_98])).

cnf(c_1458,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK3) = k4_xboole_0(X0,sK3) ),
    inference(light_normalisation,[status(thm)],[c_1332,c_85])).

cnf(c_1762,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),sK3) = k4_xboole_0(sK0,sK3) ),
    inference(superposition,[status(thm)],[c_140,c_1458])).

cnf(c_2257,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK0,sK3) ),
    inference(superposition,[status(thm)],[c_1762,c_4])).

cnf(c_9,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_72,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_0,c_9])).

cnf(c_82,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK2) = k4_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_72,c_77])).

cnf(c_107,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,X0)) = k4_xboole_0(k4_xboole_0(sK3,sK2),X0) ),
    inference(superposition,[status(thm)],[c_82,c_4])).

cnf(c_109,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,X0)) = k4_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_107,c_4])).

cnf(c_334,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK3,k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_72,c_109])).

cnf(c_340,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_334,c_72])).

cnf(c_1389,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_98,c_340])).

cnf(c_2262,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK0,sK3) ),
    inference(light_normalisation,[status(thm)],[c_2257,c_72,c_1389])).

cnf(c_1329,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(k3_xboole_0(X1,X2),X0),X1) ),
    inference(superposition,[status(thm)],[c_5,c_98])).

cnf(c_1462,plain,
    ( k4_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),X2),X0) = k4_xboole_0(X2,X0) ),
    inference(demodulation,[status(thm)],[c_1329,c_5])).

cnf(c_1543,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_5,c_1462])).

cnf(c_96,plain,
    ( k2_xboole_0(k3_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_5])).

cnf(c_644,plain,
    ( k2_xboole_0(k3_xboole_0(k4_xboole_0(X0,sK2),sK3),k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k4_xboole_0(X0,sK2) ),
    inference(superposition,[status(thm)],[c_72,c_96])).

cnf(c_762,plain,
    ( k2_xboole_0(k3_xboole_0(sK3,k4_xboole_0(X0,sK2)),k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k4_xboole_0(X0,sK2) ),
    inference(superposition,[status(thm)],[c_1,c_644])).

cnf(c_1576,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK0)),sK3) = k4_xboole_0(k4_xboole_0(X0,sK2),sK3) ),
    inference(superposition,[status(thm)],[c_762,c_1462])).

cnf(c_1635,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK0)),sK3) = k4_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_1576,c_4,c_72])).

cnf(c_2156,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_1543,c_1635])).

cnf(c_1767,plain,
    ( k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_1458,c_3])).

cnf(c_1346,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK0) ),
    inference(superposition,[status(thm)],[c_140,c_98])).

cnf(c_1444,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK0) = k4_xboole_0(X0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_1346,c_140])).

cnf(c_1710,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,sK1),sK0) = k4_xboole_0(sK3,sK0) ),
    inference(superposition,[status(thm)],[c_85,c_1444])).

cnf(c_1781,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK3,sK0) ),
    inference(superposition,[status(thm)],[c_1710,c_4])).

cnf(c_2157,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k4_xboole_0(k1_xboole_0,sK3) ),
    inference(light_normalisation,[status(thm)],[c_2156,c_1767,c_1781])).

cnf(c_2263,plain,
    ( k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK0,sK3) ),
    inference(demodulation,[status(thm)],[c_2262,c_2157])).

cnf(c_2271,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK3),k4_xboole_0(k1_xboole_0,sK3)) = sK0 ),
    inference(superposition,[status(thm)],[c_2263,c_5])).

cnf(c_2730,plain,
    ( k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK3,sK0) ),
    inference(light_normalisation,[status(thm)],[c_1781,c_2157])).

cnf(c_2738,plain,
    ( k2_xboole_0(k3_xboole_0(sK0,sK3),k4_xboole_0(k1_xboole_0,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_2730,c_83])).

cnf(c_3299,plain,
    ( sK0 = sK3 ),
    inference(light_normalisation,[status(thm)],[c_2271,c_2738])).

cnf(c_79,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_72,c_3])).

cnf(c_3372,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK3),sK3) = k4_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_3299,c_79])).

cnf(c_3376,plain,
    ( k4_xboole_0(sK1,sK3) = k4_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_3372,c_3])).

cnf(c_86,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) = sK2 ),
    inference(superposition,[status(thm)],[c_54,c_5])).

cnf(c_3373,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_3299,c_86])).

cnf(c_3377,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_3376,c_3373])).

cnf(c_73,plain,
    ( k3_xboole_0(sK1,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_49,c_1])).

cnf(c_87,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) = sK1 ),
    inference(superposition,[status(thm)],[c_73,c_5])).

cnf(c_3378,plain,
    ( sK2 = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3377,c_87])).

cnf(c_6,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_4508,plain,
    ( sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_3378,c_6])).

cnf(c_4509,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_4508])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:49:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.93/1.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.06  
% 1.93/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.93/1.06  
% 1.93/1.06  ------  iProver source info
% 1.93/1.06  
% 1.93/1.06  git: date: 2020-06-30 10:37:57 +0100
% 1.93/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.93/1.06  git: non_committed_changes: false
% 1.93/1.06  git: last_make_outside_of_git: false
% 1.93/1.06  
% 1.93/1.06  ------ 
% 1.93/1.06  
% 1.93/1.06  ------ Input Options
% 1.93/1.06  
% 1.93/1.06  --out_options                           all
% 1.93/1.06  --tptp_safe_out                         true
% 1.93/1.06  --problem_path                          ""
% 1.93/1.06  --include_path                          ""
% 1.93/1.06  --clausifier                            res/vclausify_rel
% 1.93/1.06  --clausifier_options                    --mode clausify
% 1.93/1.06  --stdin                                 false
% 1.93/1.06  --stats_out                             all
% 1.93/1.06  
% 1.93/1.06  ------ General Options
% 1.93/1.06  
% 1.93/1.06  --fof                                   false
% 1.93/1.06  --time_out_real                         305.
% 1.93/1.06  --time_out_virtual                      -1.
% 1.93/1.06  --symbol_type_check                     false
% 1.93/1.06  --clausify_out                          false
% 1.93/1.06  --sig_cnt_out                           false
% 1.93/1.06  --trig_cnt_out                          false
% 1.93/1.06  --trig_cnt_out_tolerance                1.
% 1.93/1.06  --trig_cnt_out_sk_spl                   false
% 1.93/1.06  --abstr_cl_out                          false
% 1.93/1.06  
% 1.93/1.06  ------ Global Options
% 1.93/1.06  
% 1.93/1.06  --schedule                              default
% 1.93/1.06  --add_important_lit                     false
% 1.93/1.06  --prop_solver_per_cl                    1000
% 1.93/1.06  --min_unsat_core                        false
% 1.93/1.06  --soft_assumptions                      false
% 1.93/1.06  --soft_lemma_size                       3
% 1.93/1.06  --prop_impl_unit_size                   0
% 1.93/1.06  --prop_impl_unit                        []
% 1.93/1.06  --share_sel_clauses                     true
% 1.93/1.06  --reset_solvers                         false
% 1.93/1.06  --bc_imp_inh                            [conj_cone]
% 1.93/1.06  --conj_cone_tolerance                   3.
% 1.93/1.06  --extra_neg_conj                        none
% 1.93/1.06  --large_theory_mode                     true
% 1.93/1.06  --prolific_symb_bound                   200
% 1.93/1.06  --lt_threshold                          2000
% 1.93/1.06  --clause_weak_htbl                      true
% 1.93/1.06  --gc_record_bc_elim                     false
% 1.93/1.06  
% 1.93/1.06  ------ Preprocessing Options
% 1.93/1.06  
% 1.93/1.06  --preprocessing_flag                    true
% 1.93/1.06  --time_out_prep_mult                    0.1
% 1.93/1.06  --splitting_mode                        input
% 1.93/1.06  --splitting_grd                         true
% 1.93/1.06  --splitting_cvd                         false
% 1.93/1.06  --splitting_cvd_svl                     false
% 1.93/1.06  --splitting_nvd                         32
% 1.93/1.06  --sub_typing                            true
% 1.93/1.06  --prep_gs_sim                           true
% 1.93/1.06  --prep_unflatten                        true
% 1.93/1.06  --prep_res_sim                          true
% 1.93/1.06  --prep_upred                            true
% 1.93/1.06  --prep_sem_filter                       exhaustive
% 1.93/1.06  --prep_sem_filter_out                   false
% 1.93/1.06  --pred_elim                             true
% 1.93/1.06  --res_sim_input                         true
% 1.93/1.06  --eq_ax_congr_red                       true
% 1.93/1.06  --pure_diseq_elim                       true
% 1.93/1.06  --brand_transform                       false
% 1.93/1.06  --non_eq_to_eq                          false
% 1.93/1.06  --prep_def_merge                        true
% 1.93/1.06  --prep_def_merge_prop_impl              false
% 1.93/1.06  --prep_def_merge_mbd                    true
% 1.93/1.06  --prep_def_merge_tr_red                 false
% 1.93/1.06  --prep_def_merge_tr_cl                  false
% 1.93/1.06  --smt_preprocessing                     true
% 1.93/1.06  --smt_ac_axioms                         fast
% 1.93/1.06  --preprocessed_out                      false
% 1.93/1.06  --preprocessed_stats                    false
% 1.93/1.06  
% 1.93/1.06  ------ Abstraction refinement Options
% 1.93/1.06  
% 1.93/1.06  --abstr_ref                             []
% 1.93/1.06  --abstr_ref_prep                        false
% 1.93/1.06  --abstr_ref_until_sat                   false
% 1.93/1.06  --abstr_ref_sig_restrict                funpre
% 1.93/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 1.93/1.06  --abstr_ref_under                       []
% 1.93/1.06  
% 1.93/1.06  ------ SAT Options
% 1.93/1.06  
% 1.93/1.06  --sat_mode                              false
% 1.93/1.06  --sat_fm_restart_options                ""
% 1.93/1.06  --sat_gr_def                            false
% 1.93/1.06  --sat_epr_types                         true
% 1.93/1.06  --sat_non_cyclic_types                  false
% 1.93/1.06  --sat_finite_models                     false
% 1.93/1.06  --sat_fm_lemmas                         false
% 1.93/1.06  --sat_fm_prep                           false
% 1.93/1.06  --sat_fm_uc_incr                        true
% 1.93/1.06  --sat_out_model                         small
% 1.93/1.06  --sat_out_clauses                       false
% 1.93/1.06  
% 1.93/1.06  ------ QBF Options
% 1.93/1.06  
% 1.93/1.06  --qbf_mode                              false
% 1.93/1.06  --qbf_elim_univ                         false
% 1.93/1.06  --qbf_dom_inst                          none
% 1.93/1.06  --qbf_dom_pre_inst                      false
% 1.93/1.06  --qbf_sk_in                             false
% 1.93/1.06  --qbf_pred_elim                         true
% 1.93/1.06  --qbf_split                             512
% 1.93/1.06  
% 1.93/1.06  ------ BMC1 Options
% 1.93/1.06  
% 1.93/1.06  --bmc1_incremental                      false
% 1.93/1.06  --bmc1_axioms                           reachable_all
% 1.93/1.06  --bmc1_min_bound                        0
% 1.93/1.06  --bmc1_max_bound                        -1
% 1.93/1.06  --bmc1_max_bound_default                -1
% 1.93/1.06  --bmc1_symbol_reachability              true
% 1.93/1.06  --bmc1_property_lemmas                  false
% 1.93/1.06  --bmc1_k_induction                      false
% 1.93/1.06  --bmc1_non_equiv_states                 false
% 1.93/1.06  --bmc1_deadlock                         false
% 1.93/1.06  --bmc1_ucm                              false
% 1.93/1.06  --bmc1_add_unsat_core                   none
% 1.93/1.06  --bmc1_unsat_core_children              false
% 1.93/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 1.93/1.06  --bmc1_out_stat                         full
% 1.93/1.06  --bmc1_ground_init                      false
% 1.93/1.06  --bmc1_pre_inst_next_state              false
% 1.93/1.06  --bmc1_pre_inst_state                   false
% 1.93/1.06  --bmc1_pre_inst_reach_state             false
% 1.93/1.06  --bmc1_out_unsat_core                   false
% 1.93/1.06  --bmc1_aig_witness_out                  false
% 1.93/1.06  --bmc1_verbose                          false
% 1.93/1.06  --bmc1_dump_clauses_tptp                false
% 1.93/1.06  --bmc1_dump_unsat_core_tptp             false
% 1.93/1.06  --bmc1_dump_file                        -
% 1.93/1.06  --bmc1_ucm_expand_uc_limit              128
% 1.93/1.06  --bmc1_ucm_n_expand_iterations          6
% 1.93/1.06  --bmc1_ucm_extend_mode                  1
% 1.93/1.06  --bmc1_ucm_init_mode                    2
% 1.93/1.06  --bmc1_ucm_cone_mode                    none
% 1.93/1.06  --bmc1_ucm_reduced_relation_type        0
% 1.93/1.06  --bmc1_ucm_relax_model                  4
% 1.93/1.06  --bmc1_ucm_full_tr_after_sat            true
% 1.93/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 1.93/1.06  --bmc1_ucm_layered_model                none
% 1.93/1.06  --bmc1_ucm_max_lemma_size               10
% 1.93/1.06  
% 1.93/1.06  ------ AIG Options
% 1.93/1.06  
% 1.93/1.06  --aig_mode                              false
% 1.93/1.06  
% 1.93/1.06  ------ Instantiation Options
% 1.93/1.06  
% 1.93/1.06  --instantiation_flag                    true
% 1.93/1.06  --inst_sos_flag                         false
% 1.93/1.06  --inst_sos_phase                        true
% 1.93/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.93/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.93/1.06  --inst_lit_sel_side                     num_symb
% 1.93/1.06  --inst_solver_per_active                1400
% 1.93/1.06  --inst_solver_calls_frac                1.
% 1.93/1.06  --inst_passive_queue_type               priority_queues
% 1.93/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.93/1.06  --inst_passive_queues_freq              [25;2]
% 1.93/1.06  --inst_dismatching                      true
% 1.93/1.06  --inst_eager_unprocessed_to_passive     true
% 1.93/1.06  --inst_prop_sim_given                   true
% 1.93/1.06  --inst_prop_sim_new                     false
% 1.93/1.06  --inst_subs_new                         false
% 1.93/1.06  --inst_eq_res_simp                      false
% 1.93/1.06  --inst_subs_given                       false
% 1.93/1.06  --inst_orphan_elimination               true
% 1.93/1.06  --inst_learning_loop_flag               true
% 1.93/1.06  --inst_learning_start                   3000
% 1.93/1.06  --inst_learning_factor                  2
% 1.93/1.06  --inst_start_prop_sim_after_learn       3
% 1.93/1.06  --inst_sel_renew                        solver
% 1.93/1.06  --inst_lit_activity_flag                true
% 1.93/1.06  --inst_restr_to_given                   false
% 1.93/1.06  --inst_activity_threshold               500
% 1.93/1.06  --inst_out_proof                        true
% 1.93/1.06  
% 1.93/1.06  ------ Resolution Options
% 1.93/1.06  
% 1.93/1.06  --resolution_flag                       true
% 1.93/1.06  --res_lit_sel                           adaptive
% 1.93/1.06  --res_lit_sel_side                      none
% 1.93/1.06  --res_ordering                          kbo
% 1.93/1.06  --res_to_prop_solver                    active
% 1.93/1.06  --res_prop_simpl_new                    false
% 1.93/1.06  --res_prop_simpl_given                  true
% 1.93/1.06  --res_passive_queue_type                priority_queues
% 1.93/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.93/1.06  --res_passive_queues_freq               [15;5]
% 1.93/1.06  --res_forward_subs                      full
% 1.93/1.06  --res_backward_subs                     full
% 1.93/1.06  --res_forward_subs_resolution           true
% 1.93/1.06  --res_backward_subs_resolution          true
% 1.93/1.06  --res_orphan_elimination                true
% 1.93/1.06  --res_time_limit                        2.
% 1.93/1.06  --res_out_proof                         true
% 1.93/1.06  
% 1.93/1.06  ------ Superposition Options
% 1.93/1.06  
% 1.93/1.06  --superposition_flag                    true
% 1.93/1.06  --sup_passive_queue_type                priority_queues
% 1.93/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.93/1.06  --sup_passive_queues_freq               [8;1;4]
% 1.93/1.06  --demod_completeness_check              fast
% 1.93/1.06  --demod_use_ground                      true
% 1.93/1.06  --sup_to_prop_solver                    passive
% 1.93/1.06  --sup_prop_simpl_new                    true
% 1.93/1.06  --sup_prop_simpl_given                  true
% 1.93/1.06  --sup_fun_splitting                     false
% 1.93/1.06  --sup_smt_interval                      50000
% 3.76/1.06  
% 3.76/1.06  ------ Superposition Simplification Setup
% 3.76/1.06  
% 3.76/1.06  --sup_indices_passive                   []
% 3.76/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 3.76/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/1.06  --sup_full_bw                           [BwDemod]
% 3.76/1.06  --sup_immed_triv                        [TrivRules]
% 3.76/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/1.06  --sup_immed_bw_main                     []
% 3.76/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 3.76/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.76/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.76/1.06  
% 3.76/1.06  ------ Combination Options
% 3.76/1.06  
% 3.76/1.06  --comb_res_mult                         3
% 3.76/1.06  --comb_sup_mult                         2
% 3.76/1.06  --comb_inst_mult                        10
% 3.76/1.06  
% 3.76/1.06  ------ Debug Options
% 3.76/1.06  
% 3.76/1.06  --dbg_backtrace                         false
% 3.76/1.06  --dbg_dump_prop_clauses                 false
% 3.76/1.06  --dbg_dump_prop_clauses_file            -
% 3.76/1.06  --dbg_out_stat                          false
% 3.76/1.06  ------ Parsing...
% 3.76/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.76/1.06  
% 3.76/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.76/1.06  
% 3.76/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.76/1.06  
% 3.76/1.06  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.76/1.06  ------ Proving...
% 3.76/1.06  ------ Problem Properties 
% 3.76/1.06  
% 3.76/1.06  
% 3.76/1.06  clauses                                 9
% 3.76/1.06  conjectures                             2
% 3.76/1.06  EPR                                     1
% 3.76/1.06  Horn                                    9
% 3.76/1.06  unary                                   9
% 3.76/1.06  binary                                  0
% 3.76/1.06  lits                                    9
% 3.76/1.06  lits eq                                 9
% 3.76/1.06  fd_pure                                 0
% 3.76/1.06  fd_pseudo                               0
% 3.76/1.06  fd_cond                                 0
% 3.76/1.06  fd_pseudo_cond                          0
% 3.76/1.06  AC symbols                              0
% 3.76/1.06  
% 3.76/1.06  ------ Schedule UEQ
% 3.76/1.06  
% 3.76/1.06  ------ pure equality problem: resolution off 
% 3.76/1.06  
% 3.76/1.06  ------ Option_UEQ Time Limit: Unbounded
% 3.76/1.06  
% 3.76/1.06  
% 3.76/1.06  ------ 
% 3.76/1.06  Current options:
% 3.76/1.06  ------ 
% 3.76/1.06  
% 3.76/1.06  ------ Input Options
% 3.76/1.06  
% 3.76/1.06  --out_options                           all
% 3.76/1.06  --tptp_safe_out                         true
% 3.76/1.06  --problem_path                          ""
% 3.76/1.06  --include_path                          ""
% 3.76/1.06  --clausifier                            res/vclausify_rel
% 3.76/1.06  --clausifier_options                    --mode clausify
% 3.76/1.06  --stdin                                 false
% 3.76/1.06  --stats_out                             all
% 3.76/1.06  
% 3.76/1.06  ------ General Options
% 3.76/1.06  
% 3.76/1.06  --fof                                   false
% 3.76/1.06  --time_out_real                         305.
% 3.76/1.06  --time_out_virtual                      -1.
% 3.76/1.06  --symbol_type_check                     false
% 3.76/1.06  --clausify_out                          false
% 3.76/1.06  --sig_cnt_out                           false
% 3.76/1.06  --trig_cnt_out                          false
% 3.76/1.06  --trig_cnt_out_tolerance                1.
% 3.76/1.06  --trig_cnt_out_sk_spl                   false
% 3.76/1.06  --abstr_cl_out                          false
% 3.76/1.06  
% 3.76/1.06  ------ Global Options
% 3.76/1.06  
% 3.76/1.06  --schedule                              default
% 3.76/1.06  --add_important_lit                     false
% 3.76/1.06  --prop_solver_per_cl                    1000
% 3.76/1.06  --min_unsat_core                        false
% 3.76/1.06  --soft_assumptions                      false
% 3.76/1.06  --soft_lemma_size                       3
% 3.76/1.06  --prop_impl_unit_size                   0
% 3.76/1.06  --prop_impl_unit                        []
% 3.76/1.06  --share_sel_clauses                     true
% 3.76/1.06  --reset_solvers                         false
% 3.76/1.06  --bc_imp_inh                            [conj_cone]
% 3.76/1.06  --conj_cone_tolerance                   3.
% 3.76/1.06  --extra_neg_conj                        none
% 3.76/1.06  --large_theory_mode                     true
% 3.76/1.06  --prolific_symb_bound                   200
% 3.76/1.06  --lt_threshold                          2000
% 3.76/1.06  --clause_weak_htbl                      true
% 3.76/1.06  --gc_record_bc_elim                     false
% 3.76/1.06  
% 3.76/1.06  ------ Preprocessing Options
% 3.76/1.06  
% 3.76/1.06  --preprocessing_flag                    true
% 3.76/1.06  --time_out_prep_mult                    0.1
% 3.76/1.06  --splitting_mode                        input
% 3.76/1.06  --splitting_grd                         true
% 3.76/1.06  --splitting_cvd                         false
% 3.76/1.06  --splitting_cvd_svl                     false
% 3.76/1.06  --splitting_nvd                         32
% 3.76/1.06  --sub_typing                            true
% 3.76/1.06  --prep_gs_sim                           true
% 3.76/1.06  --prep_unflatten                        true
% 3.76/1.06  --prep_res_sim                          true
% 3.76/1.06  --prep_upred                            true
% 3.76/1.06  --prep_sem_filter                       exhaustive
% 3.76/1.06  --prep_sem_filter_out                   false
% 3.76/1.06  --pred_elim                             true
% 3.76/1.06  --res_sim_input                         true
% 3.76/1.06  --eq_ax_congr_red                       true
% 3.76/1.06  --pure_diseq_elim                       true
% 3.76/1.06  --brand_transform                       false
% 3.76/1.06  --non_eq_to_eq                          false
% 3.76/1.06  --prep_def_merge                        true
% 3.76/1.06  --prep_def_merge_prop_impl              false
% 3.76/1.06  --prep_def_merge_mbd                    true
% 3.76/1.06  --prep_def_merge_tr_red                 false
% 3.76/1.06  --prep_def_merge_tr_cl                  false
% 3.76/1.06  --smt_preprocessing                     true
% 3.76/1.06  --smt_ac_axioms                         fast
% 3.76/1.06  --preprocessed_out                      false
% 3.76/1.06  --preprocessed_stats                    false
% 3.76/1.06  
% 3.76/1.06  ------ Abstraction refinement Options
% 3.76/1.06  
% 3.76/1.06  --abstr_ref                             []
% 3.76/1.06  --abstr_ref_prep                        false
% 3.76/1.06  --abstr_ref_until_sat                   false
% 3.76/1.06  --abstr_ref_sig_restrict                funpre
% 3.76/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 3.76/1.06  --abstr_ref_under                       []
% 3.76/1.06  
% 3.76/1.06  ------ SAT Options
% 3.76/1.06  
% 3.76/1.06  --sat_mode                              false
% 3.76/1.06  --sat_fm_restart_options                ""
% 3.76/1.06  --sat_gr_def                            false
% 3.76/1.06  --sat_epr_types                         true
% 3.76/1.06  --sat_non_cyclic_types                  false
% 3.76/1.06  --sat_finite_models                     false
% 3.76/1.06  --sat_fm_lemmas                         false
% 3.76/1.06  --sat_fm_prep                           false
% 3.76/1.06  --sat_fm_uc_incr                        true
% 3.76/1.06  --sat_out_model                         small
% 3.76/1.06  --sat_out_clauses                       false
% 3.76/1.06  
% 3.76/1.06  ------ QBF Options
% 3.76/1.06  
% 3.76/1.06  --qbf_mode                              false
% 3.76/1.06  --qbf_elim_univ                         false
% 3.76/1.06  --qbf_dom_inst                          none
% 3.76/1.06  --qbf_dom_pre_inst                      false
% 3.76/1.06  --qbf_sk_in                             false
% 3.76/1.06  --qbf_pred_elim                         true
% 3.76/1.06  --qbf_split                             512
% 3.76/1.06  
% 3.76/1.06  ------ BMC1 Options
% 3.76/1.06  
% 3.76/1.06  --bmc1_incremental                      false
% 3.76/1.06  --bmc1_axioms                           reachable_all
% 3.76/1.06  --bmc1_min_bound                        0
% 3.76/1.06  --bmc1_max_bound                        -1
% 3.76/1.06  --bmc1_max_bound_default                -1
% 3.76/1.06  --bmc1_symbol_reachability              true
% 3.76/1.06  --bmc1_property_lemmas                  false
% 3.76/1.06  --bmc1_k_induction                      false
% 3.76/1.06  --bmc1_non_equiv_states                 false
% 3.76/1.06  --bmc1_deadlock                         false
% 3.76/1.06  --bmc1_ucm                              false
% 3.76/1.06  --bmc1_add_unsat_core                   none
% 3.76/1.06  --bmc1_unsat_core_children              false
% 3.76/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 3.76/1.06  --bmc1_out_stat                         full
% 3.76/1.06  --bmc1_ground_init                      false
% 3.76/1.06  --bmc1_pre_inst_next_state              false
% 3.76/1.06  --bmc1_pre_inst_state                   false
% 3.76/1.06  --bmc1_pre_inst_reach_state             false
% 3.76/1.06  --bmc1_out_unsat_core                   false
% 3.76/1.06  --bmc1_aig_witness_out                  false
% 3.76/1.06  --bmc1_verbose                          false
% 3.76/1.06  --bmc1_dump_clauses_tptp                false
% 3.76/1.06  --bmc1_dump_unsat_core_tptp             false
% 3.76/1.06  --bmc1_dump_file                        -
% 3.76/1.06  --bmc1_ucm_expand_uc_limit              128
% 3.76/1.06  --bmc1_ucm_n_expand_iterations          6
% 3.76/1.06  --bmc1_ucm_extend_mode                  1
% 3.76/1.06  --bmc1_ucm_init_mode                    2
% 3.76/1.06  --bmc1_ucm_cone_mode                    none
% 3.76/1.06  --bmc1_ucm_reduced_relation_type        0
% 3.76/1.06  --bmc1_ucm_relax_model                  4
% 3.76/1.06  --bmc1_ucm_full_tr_after_sat            true
% 3.76/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 3.76/1.06  --bmc1_ucm_layered_model                none
% 3.76/1.06  --bmc1_ucm_max_lemma_size               10
% 3.76/1.06  
% 3.76/1.06  ------ AIG Options
% 3.76/1.06  
% 3.76/1.06  --aig_mode                              false
% 3.76/1.06  
% 3.76/1.06  ------ Instantiation Options
% 3.76/1.06  
% 3.76/1.06  --instantiation_flag                    false
% 3.76/1.06  --inst_sos_flag                         false
% 3.76/1.06  --inst_sos_phase                        true
% 3.76/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.76/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.76/1.06  --inst_lit_sel_side                     num_symb
% 3.76/1.06  --inst_solver_per_active                1400
% 3.76/1.06  --inst_solver_calls_frac                1.
% 3.76/1.06  --inst_passive_queue_type               priority_queues
% 3.76/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.76/1.06  --inst_passive_queues_freq              [25;2]
% 3.76/1.06  --inst_dismatching                      true
% 3.76/1.06  --inst_eager_unprocessed_to_passive     true
% 3.76/1.06  --inst_prop_sim_given                   true
% 3.76/1.06  --inst_prop_sim_new                     false
% 3.76/1.06  --inst_subs_new                         false
% 3.76/1.06  --inst_eq_res_simp                      false
% 3.76/1.06  --inst_subs_given                       false
% 3.76/1.06  --inst_orphan_elimination               true
% 3.76/1.06  --inst_learning_loop_flag               true
% 3.76/1.06  --inst_learning_start                   3000
% 3.76/1.06  --inst_learning_factor                  2
% 3.76/1.06  --inst_start_prop_sim_after_learn       3
% 3.76/1.06  --inst_sel_renew                        solver
% 3.76/1.06  --inst_lit_activity_flag                true
% 3.76/1.06  --inst_restr_to_given                   false
% 3.76/1.06  --inst_activity_threshold               500
% 3.76/1.06  --inst_out_proof                        true
% 3.76/1.06  
% 3.76/1.06  ------ Resolution Options
% 3.76/1.06  
% 3.76/1.06  --resolution_flag                       false
% 3.76/1.06  --res_lit_sel                           adaptive
% 3.76/1.06  --res_lit_sel_side                      none
% 3.76/1.06  --res_ordering                          kbo
% 3.76/1.06  --res_to_prop_solver                    active
% 3.76/1.06  --res_prop_simpl_new                    false
% 3.76/1.06  --res_prop_simpl_given                  true
% 3.76/1.06  --res_passive_queue_type                priority_queues
% 3.76/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.76/1.06  --res_passive_queues_freq               [15;5]
% 3.76/1.06  --res_forward_subs                      full
% 3.76/1.06  --res_backward_subs                     full
% 3.76/1.06  --res_forward_subs_resolution           true
% 3.76/1.06  --res_backward_subs_resolution          true
% 3.76/1.06  --res_orphan_elimination                true
% 3.76/1.06  --res_time_limit                        2.
% 3.76/1.06  --res_out_proof                         true
% 3.76/1.06  
% 3.76/1.06  ------ Superposition Options
% 3.76/1.06  
% 3.76/1.06  --superposition_flag                    true
% 3.76/1.06  --sup_passive_queue_type                priority_queues
% 3.76/1.06  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.76/1.06  --sup_passive_queues_freq               [8;1;4]
% 3.76/1.06  --demod_completeness_check              fast
% 3.76/1.06  --demod_use_ground                      true
% 3.76/1.06  --sup_to_prop_solver                    active
% 3.76/1.06  --sup_prop_simpl_new                    false
% 3.76/1.06  --sup_prop_simpl_given                  false
% 3.76/1.06  --sup_fun_splitting                     true
% 3.76/1.06  --sup_smt_interval                      10000
% 3.76/1.06  
% 3.76/1.06  ------ Superposition Simplification Setup
% 3.76/1.06  
% 3.76/1.06  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.76/1.06  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.76/1.06  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.76/1.06  --sup_full_triv                         [TrivRules]
% 3.76/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.76/1.06  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.76/1.06  --sup_immed_triv                        [TrivRules]
% 3.76/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/1.06  --sup_immed_bw_main                     []
% 3.76/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.76/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 3.76/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.76/1.06  --sup_input_bw                          [BwDemod;BwSubsumption]
% 3.76/1.06  
% 3.76/1.06  ------ Combination Options
% 3.76/1.06  
% 3.76/1.06  --comb_res_mult                         1
% 3.76/1.06  --comb_sup_mult                         1
% 3.76/1.06  --comb_inst_mult                        1000000
% 3.76/1.06  
% 3.76/1.06  ------ Debug Options
% 3.76/1.06  
% 3.76/1.06  --dbg_backtrace                         false
% 3.76/1.06  --dbg_dump_prop_clauses                 false
% 3.76/1.06  --dbg_dump_prop_clauses_file            -
% 3.76/1.06  --dbg_out_stat                          false
% 3.76/1.06  
% 3.76/1.06  
% 3.76/1.06  
% 3.76/1.06  
% 3.76/1.06  ------ Proving...
% 3.76/1.06  
% 3.76/1.06  
% 3.76/1.06  % SZS status Theorem for theBenchmark.p
% 3.76/1.06  
% 3.76/1.06   Resolution empty clause
% 3.76/1.06  
% 3.76/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 3.76/1.06  
% 3.76/1.06  fof(f3,axiom,(
% 3.76/1.06    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.76/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.06  
% 3.76/1.06  fof(f9,plain,(
% 3.76/1.06    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.76/1.06    inference(unused_predicate_definition_removal,[],[f3])).
% 3.76/1.06  
% 3.76/1.06  fof(f10,plain,(
% 3.76/1.06    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 3.76/1.06    inference(ennf_transformation,[],[f9])).
% 3.76/1.06  
% 3.76/1.06  fof(f17,plain,(
% 3.76/1.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.76/1.06    inference(cnf_transformation,[],[f10])).
% 3.76/1.06  
% 3.76/1.06  fof(f7,conjecture,(
% 3.76/1.06    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 3.76/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.06  
% 3.76/1.06  fof(f8,negated_conjecture,(
% 3.76/1.06    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 3.76/1.06    inference(negated_conjecture,[],[f7])).
% 3.76/1.06  
% 3.76/1.06  fof(f11,plain,(
% 3.76/1.06    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 3.76/1.06    inference(ennf_transformation,[],[f8])).
% 3.76/1.06  
% 3.76/1.06  fof(f12,plain,(
% 3.76/1.06    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 3.76/1.06    inference(flattening,[],[f11])).
% 3.76/1.06  
% 3.76/1.06  fof(f13,plain,(
% 3.76/1.06    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 3.76/1.06    introduced(choice_axiom,[])).
% 3.76/1.06  
% 3.76/1.06  fof(f14,plain,(
% 3.76/1.06    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 3.76/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f13])).
% 3.76/1.06  
% 3.76/1.06  fof(f22,plain,(
% 3.76/1.06    r1_xboole_0(sK2,sK0)),
% 3.76/1.06    inference(cnf_transformation,[],[f14])).
% 3.76/1.06  
% 3.76/1.06  fof(f2,axiom,(
% 3.76/1.06    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.76/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.06  
% 3.76/1.06  fof(f16,plain,(
% 3.76/1.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.76/1.06    inference(cnf_transformation,[],[f2])).
% 3.76/1.06  
% 3.76/1.06  fof(f6,axiom,(
% 3.76/1.06    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.76/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.06  
% 3.76/1.06  fof(f20,plain,(
% 3.76/1.06    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.76/1.06    inference(cnf_transformation,[],[f6])).
% 3.76/1.06  
% 3.76/1.06  fof(f23,plain,(
% 3.76/1.06    r1_xboole_0(sK3,sK1)),
% 3.76/1.06    inference(cnf_transformation,[],[f14])).
% 3.76/1.06  
% 3.76/1.06  fof(f1,axiom,(
% 3.76/1.06    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.76/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.06  
% 3.76/1.06  fof(f15,plain,(
% 3.76/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.76/1.06    inference(cnf_transformation,[],[f1])).
% 3.76/1.06  
% 3.76/1.06  fof(f4,axiom,(
% 3.76/1.06    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.76/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.06  
% 3.76/1.06  fof(f18,plain,(
% 3.76/1.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.76/1.06    inference(cnf_transformation,[],[f4])).
% 3.76/1.06  
% 3.76/1.06  fof(f5,axiom,(
% 3.76/1.06    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.76/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.76/1.06  
% 3.76/1.06  fof(f19,plain,(
% 3.76/1.06    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.76/1.06    inference(cnf_transformation,[],[f5])).
% 3.76/1.06  
% 3.76/1.06  fof(f21,plain,(
% 3.76/1.06    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 3.76/1.06    inference(cnf_transformation,[],[f14])).
% 3.76/1.06  
% 3.76/1.06  fof(f24,plain,(
% 3.76/1.06    sK1 != sK2),
% 3.76/1.06    inference(cnf_transformation,[],[f14])).
% 3.76/1.06  
% 3.76/1.06  cnf(c_2,plain,
% 3.76/1.06      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.76/1.06      inference(cnf_transformation,[],[f17]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_8,negated_conjecture,
% 3.76/1.06      ( r1_xboole_0(sK2,sK0) ),
% 3.76/1.06      inference(cnf_transformation,[],[f22]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_53,plain,
% 3.76/1.06      ( k3_xboole_0(X0,X1) = k1_xboole_0 | sK0 != X1 | sK2 != X0 ),
% 3.76/1.06      inference(resolution_lifted,[status(thm)],[c_2,c_8]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_54,plain,
% 3.76/1.06      ( k3_xboole_0(sK2,sK0) = k1_xboole_0 ),
% 3.76/1.06      inference(unflattening,[status(thm)],[c_53]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_1,plain,
% 3.76/1.06      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.76/1.06      inference(cnf_transformation,[],[f16]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_5,plain,
% 3.76/1.06      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
% 3.76/1.06      inference(cnf_transformation,[],[f20]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_83,plain,
% 3.76/1.06      ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X1 ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_1,c_5]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_140,plain,
% 3.76/1.06      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) = sK0 ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_54,c_83]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_7,negated_conjecture,
% 3.76/1.06      ( r1_xboole_0(sK3,sK1) ),
% 3.76/1.06      inference(cnf_transformation,[],[f23]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_48,plain,
% 3.76/1.06      ( k3_xboole_0(X0,X1) = k1_xboole_0 | sK3 != X0 | sK1 != X1 ),
% 3.76/1.06      inference(resolution_lifted,[status(thm)],[c_2,c_7]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_49,plain,
% 3.76/1.06      ( k3_xboole_0(sK3,sK1) = k1_xboole_0 ),
% 3.76/1.06      inference(unflattening,[status(thm)],[c_48]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_85,plain,
% 3.76/1.06      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) = sK3 ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_49,c_5]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_0,plain,
% 3.76/1.06      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.76/1.06      inference(cnf_transformation,[],[f15]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_3,plain,
% 3.76/1.06      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 3.76/1.06      inference(cnf_transformation,[],[f18]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_77,plain,
% 3.76/1.06      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_0,c_3]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_4,plain,
% 3.76/1.06      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.76/1.06      inference(cnf_transformation,[],[f19]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_94,plain,
% 3.76/1.06      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_77,c_4]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_98,plain,
% 3.76/1.06      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 3.76/1.06      inference(demodulation,[status(thm)],[c_94,c_4]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_1332,plain,
% 3.76/1.06      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK3) ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_85,c_98]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_1458,plain,
% 3.76/1.06      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK3) = k4_xboole_0(X0,sK3) ),
% 3.76/1.06      inference(light_normalisation,[status(thm)],[c_1332,c_85]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_1762,plain,
% 3.76/1.06      ( k4_xboole_0(k4_xboole_0(sK0,sK2),sK3) = k4_xboole_0(sK0,sK3) ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_140,c_1458]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_2257,plain,
% 3.76/1.06      ( k4_xboole_0(sK0,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK0,sK3) ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_1762,c_4]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_9,negated_conjecture,
% 3.76/1.06      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 3.76/1.06      inference(cnf_transformation,[],[f21]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_72,plain,
% 3.76/1.06      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
% 3.76/1.06      inference(demodulation,[status(thm)],[c_0,c_9]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_82,plain,
% 3.76/1.06      ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK2) = k4_xboole_0(sK3,sK2) ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_72,c_77]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_107,plain,
% 3.76/1.06      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,X0)) = k4_xboole_0(k4_xboole_0(sK3,sK2),X0) ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_82,c_4]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_109,plain,
% 3.76/1.06      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,X0)) = k4_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
% 3.76/1.06      inference(demodulation,[status(thm)],[c_107,c_4]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_334,plain,
% 3.76/1.06      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK3,k2_xboole_0(sK2,sK3)) ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_72,c_109]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_340,plain,
% 3.76/1.06      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) ),
% 3.76/1.06      inference(light_normalisation,[status(thm)],[c_334,c_72]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_1389,plain,
% 3.76/1.06      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_98,c_340]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_2262,plain,
% 3.76/1.06      ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK0,sK3) ),
% 3.76/1.06      inference(light_normalisation,[status(thm)],[c_2257,c_72,c_1389]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_1329,plain,
% 3.76/1.06      ( k4_xboole_0(X0,k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(k3_xboole_0(X1,X2),X0),X1) ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_5,c_98]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_1462,plain,
% 3.76/1.06      ( k4_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),X2),X0) = k4_xboole_0(X2,X0) ),
% 3.76/1.06      inference(demodulation,[status(thm)],[c_1329,c_5]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_1543,plain,
% 3.76/1.06      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_5,c_1462]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_96,plain,
% 3.76/1.06      ( k2_xboole_0(k3_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_4,c_5]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_644,plain,
% 3.76/1.06      ( k2_xboole_0(k3_xboole_0(k4_xboole_0(X0,sK2),sK3),k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k4_xboole_0(X0,sK2) ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_72,c_96]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_762,plain,
% 3.76/1.06      ( k2_xboole_0(k3_xboole_0(sK3,k4_xboole_0(X0,sK2)),k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k4_xboole_0(X0,sK2) ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_1,c_644]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_1576,plain,
% 3.76/1.06      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK0)),sK3) = k4_xboole_0(k4_xboole_0(X0,sK2),sK3) ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_762,c_1462]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_1635,plain,
% 3.76/1.06      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK1,sK0)),sK3) = k4_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 3.76/1.06      inference(demodulation,[status(thm)],[c_1576,c_4,c_72]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_2156,plain,
% 3.76/1.06      ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK3,sK3) ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_1543,c_1635]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_1767,plain,
% 3.76/1.06      ( k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK3,sK3) ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_1458,c_3]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_1346,plain,
% 3.76/1.06      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK0) ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_140,c_98]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_1444,plain,
% 3.76/1.06      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK0) = k4_xboole_0(X0,sK0) ),
% 3.76/1.06      inference(light_normalisation,[status(thm)],[c_1346,c_140]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_1710,plain,
% 3.76/1.06      ( k4_xboole_0(k4_xboole_0(sK3,sK1),sK0) = k4_xboole_0(sK3,sK0) ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_85,c_1444]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_1781,plain,
% 3.76/1.06      ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK3,sK0) ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_1710,c_4]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_2157,plain,
% 3.76/1.06      ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k4_xboole_0(k1_xboole_0,sK3) ),
% 3.76/1.06      inference(light_normalisation,[status(thm)],[c_2156,c_1767,c_1781]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_2263,plain,
% 3.76/1.06      ( k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK0,sK3) ),
% 3.76/1.06      inference(demodulation,[status(thm)],[c_2262,c_2157]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_2271,plain,
% 3.76/1.06      ( k2_xboole_0(k3_xboole_0(sK0,sK3),k4_xboole_0(k1_xboole_0,sK3)) = sK0 ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_2263,c_5]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_2730,plain,
% 3.76/1.06      ( k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK3,sK0) ),
% 3.76/1.06      inference(light_normalisation,[status(thm)],[c_1781,c_2157]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_2738,plain,
% 3.76/1.06      ( k2_xboole_0(k3_xboole_0(sK0,sK3),k4_xboole_0(k1_xboole_0,sK3)) = sK3 ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_2730,c_83]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_3299,plain,
% 3.76/1.06      ( sK0 = sK3 ),
% 3.76/1.06      inference(light_normalisation,[status(thm)],[c_2271,c_2738]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_79,plain,
% 3.76/1.06      ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k4_xboole_0(sK2,sK3) ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_72,c_3]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_3372,plain,
% 3.76/1.06      ( k4_xboole_0(k2_xboole_0(sK1,sK3),sK3) = k4_xboole_0(sK2,sK3) ),
% 3.76/1.06      inference(demodulation,[status(thm)],[c_3299,c_79]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_3376,plain,
% 3.76/1.06      ( k4_xboole_0(sK1,sK3) = k4_xboole_0(sK2,sK3) ),
% 3.76/1.06      inference(demodulation,[status(thm)],[c_3372,c_3]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_86,plain,
% 3.76/1.06      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) = sK2 ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_54,c_5]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_3373,plain,
% 3.76/1.06      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK3)) = sK2 ),
% 3.76/1.06      inference(demodulation,[status(thm)],[c_3299,c_86]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_3377,plain,
% 3.76/1.06      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) = sK2 ),
% 3.76/1.06      inference(demodulation,[status(thm)],[c_3376,c_3373]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_73,plain,
% 3.76/1.06      ( k3_xboole_0(sK1,sK3) = k1_xboole_0 ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_49,c_1]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_87,plain,
% 3.76/1.06      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) = sK1 ),
% 3.76/1.06      inference(superposition,[status(thm)],[c_73,c_5]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_3378,plain,
% 3.76/1.06      ( sK2 = sK1 ),
% 3.76/1.06      inference(light_normalisation,[status(thm)],[c_3377,c_87]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_6,negated_conjecture,
% 3.76/1.06      ( sK1 != sK2 ),
% 3.76/1.06      inference(cnf_transformation,[],[f24]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_4508,plain,
% 3.76/1.06      ( sK1 != sK1 ),
% 3.76/1.06      inference(demodulation,[status(thm)],[c_3378,c_6]) ).
% 3.76/1.06  
% 3.76/1.06  cnf(c_4509,plain,
% 3.76/1.06      ( $false ),
% 3.76/1.06      inference(equality_resolution_simp,[status(thm)],[c_4508]) ).
% 3.76/1.06  
% 3.76/1.06  
% 3.76/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 3.76/1.06  
% 3.76/1.06  ------                               Statistics
% 3.76/1.06  
% 3.76/1.06  ------ General
% 3.76/1.06  
% 3.76/1.06  abstr_ref_over_cycles:                  0
% 3.76/1.06  abstr_ref_under_cycles:                 0
% 3.76/1.06  gc_basic_clause_elim:                   0
% 3.76/1.06  forced_gc_time:                         0
% 3.76/1.06  parsing_time:                           0.008
% 3.76/1.06  unif_index_cands_time:                  0.
% 3.76/1.06  unif_index_add_time:                    0.
% 3.76/1.06  orderings_time:                         0.
% 3.76/1.06  out_proof_time:                         0.007
% 3.76/1.06  total_time:                             0.404
% 3.76/1.06  num_of_symbols:                         40
% 3.76/1.06  num_of_terms:                           11771
% 3.76/1.06  
% 3.76/1.06  ------ Preprocessing
% 3.76/1.06  
% 3.76/1.06  num_of_splits:                          0
% 3.76/1.06  num_of_split_atoms:                     0
% 3.76/1.06  num_of_reused_defs:                     0
% 3.76/1.06  num_eq_ax_congr_red:                    2
% 3.76/1.06  num_of_sem_filtered_clauses:            0
% 3.76/1.06  num_of_subtypes:                        0
% 3.76/1.06  monotx_restored_types:                  0
% 3.76/1.06  sat_num_of_epr_types:                   0
% 3.76/1.06  sat_num_of_non_cyclic_types:            0
% 3.76/1.06  sat_guarded_non_collapsed_types:        0
% 3.76/1.06  num_pure_diseq_elim:                    0
% 3.76/1.06  simp_replaced_by:                       0
% 3.76/1.06  res_preprocessed:                       33
% 3.76/1.06  prep_upred:                             0
% 3.76/1.06  prep_unflattend:                        4
% 3.76/1.06  smt_new_axioms:                         0
% 3.76/1.06  pred_elim_cands:                        0
% 3.76/1.06  pred_elim:                              1
% 3.76/1.06  pred_elim_cl:                           1
% 3.76/1.06  pred_elim_cycles:                       2
% 3.76/1.06  merged_defs:                            0
% 3.76/1.06  merged_defs_ncl:                        0
% 3.76/1.06  bin_hyper_res:                          0
% 3.76/1.06  prep_cycles:                            3
% 3.76/1.06  pred_elim_time:                         0.001
% 3.76/1.06  splitting_time:                         0.
% 3.76/1.06  sem_filter_time:                        0.
% 3.76/1.06  monotx_time:                            0.
% 3.76/1.06  subtype_inf_time:                       0.
% 3.76/1.06  
% 3.76/1.06  ------ Problem properties
% 3.76/1.06  
% 3.76/1.06  clauses:                                9
% 3.76/1.06  conjectures:                            2
% 3.76/1.06  epr:                                    1
% 3.76/1.06  horn:                                   9
% 3.76/1.06  ground:                                 4
% 3.76/1.06  unary:                                  9
% 3.76/1.06  binary:                                 0
% 3.76/1.06  lits:                                   9
% 3.76/1.06  lits_eq:                                9
% 3.76/1.06  fd_pure:                                0
% 3.76/1.06  fd_pseudo:                              0
% 3.76/1.06  fd_cond:                                0
% 3.76/1.06  fd_pseudo_cond:                         0
% 3.76/1.06  ac_symbols:                             0
% 3.76/1.06  
% 3.76/1.06  ------ Propositional Solver
% 3.76/1.06  
% 3.76/1.06  prop_solver_calls:                      17
% 3.76/1.06  prop_fast_solver_calls:                 86
% 3.76/1.06  smt_solver_calls:                       0
% 3.76/1.06  smt_fast_solver_calls:                  0
% 3.76/1.06  prop_num_of_clauses:                    233
% 3.76/1.06  prop_preprocess_simplified:             412
% 3.76/1.06  prop_fo_subsumed:                       0
% 3.76/1.06  prop_solver_time:                       0.
% 3.76/1.06  smt_solver_time:                        0.
% 3.76/1.06  smt_fast_solver_time:                   0.
% 3.76/1.06  prop_fast_solver_time:                  0.
% 3.76/1.06  prop_unsat_core_time:                   0.
% 3.76/1.06  
% 3.76/1.06  ------ QBF
% 3.76/1.06  
% 3.76/1.06  qbf_q_res:                              0
% 3.76/1.06  qbf_num_tautologies:                    0
% 3.76/1.06  qbf_prep_cycles:                        0
% 3.76/1.06  
% 3.76/1.06  ------ BMC1
% 3.76/1.06  
% 3.76/1.06  bmc1_current_bound:                     -1
% 3.76/1.06  bmc1_last_solved_bound:                 -1
% 3.76/1.06  bmc1_unsat_core_size:                   -1
% 3.76/1.06  bmc1_unsat_core_parents_size:           -1
% 3.76/1.06  bmc1_merge_next_fun:                    0
% 3.76/1.06  bmc1_unsat_core_clauses_time:           0.
% 3.76/1.06  
% 3.76/1.06  ------ Instantiation
% 3.76/1.06  
% 3.76/1.06  inst_num_of_clauses:                    0
% 3.76/1.06  inst_num_in_passive:                    0
% 3.76/1.06  inst_num_in_active:                     0
% 3.76/1.06  inst_num_in_unprocessed:                0
% 3.76/1.06  inst_num_of_loops:                      0
% 3.76/1.06  inst_num_of_learning_restarts:          0
% 3.76/1.06  inst_num_moves_active_passive:          0
% 3.76/1.06  inst_lit_activity:                      0
% 3.76/1.06  inst_lit_activity_moves:                0
% 3.76/1.06  inst_num_tautologies:                   0
% 3.76/1.06  inst_num_prop_implied:                  0
% 3.76/1.06  inst_num_existing_simplified:           0
% 3.76/1.06  inst_num_eq_res_simplified:             0
% 3.76/1.06  inst_num_child_elim:                    0
% 3.76/1.06  inst_num_of_dismatching_blockings:      0
% 3.76/1.06  inst_num_of_non_proper_insts:           0
% 3.76/1.06  inst_num_of_duplicates:                 0
% 3.76/1.06  inst_inst_num_from_inst_to_res:         0
% 3.76/1.06  inst_dismatching_checking_time:         0.
% 3.76/1.06  
% 3.76/1.06  ------ Resolution
% 3.76/1.06  
% 3.76/1.06  res_num_of_clauses:                     0
% 3.76/1.06  res_num_in_passive:                     0
% 3.76/1.06  res_num_in_active:                      0
% 3.76/1.06  res_num_of_loops:                       36
% 3.76/1.06  res_forward_subset_subsumed:            0
% 3.76/1.06  res_backward_subset_subsumed:           0
% 3.76/1.06  res_forward_subsumed:                   0
% 3.76/1.06  res_backward_subsumed:                  0
% 3.76/1.06  res_forward_subsumption_resolution:     0
% 3.76/1.06  res_backward_subsumption_resolution:    0
% 3.76/1.06  res_clause_to_clause_subsumption:       12432
% 3.76/1.06  res_orphan_elimination:                 0
% 3.76/1.06  res_tautology_del:                      0
% 3.76/1.06  res_num_eq_res_simplified:              0
% 3.76/1.06  res_num_sel_changes:                    0
% 3.76/1.06  res_moves_from_active_to_pass:          0
% 3.76/1.06  
% 3.76/1.06  ------ Superposition
% 3.76/1.06  
% 3.76/1.06  sup_time_total:                         0.
% 3.76/1.06  sup_time_generating:                    0.
% 3.76/1.06  sup_time_sim_full:                      0.
% 3.76/1.06  sup_time_sim_immed:                     0.
% 3.76/1.06  
% 3.76/1.06  sup_num_of_clauses:                     1519
% 3.76/1.06  sup_num_in_active:                      70
% 3.76/1.06  sup_num_in_passive:                     1449
% 3.76/1.06  sup_num_of_loops:                       159
% 3.76/1.06  sup_fw_superposition:                   1370
% 3.76/1.06  sup_bw_superposition:                   1267
% 3.76/1.06  sup_immediate_simplified:               1635
% 3.76/1.06  sup_given_eliminated:                   1
% 3.76/1.06  comparisons_done:                       0
% 3.76/1.06  comparisons_avoided:                    0
% 3.76/1.06  
% 3.76/1.06  ------ Simplifications
% 3.76/1.06  
% 3.76/1.06  
% 3.76/1.06  sim_fw_subset_subsumed:                 0
% 3.76/1.06  sim_bw_subset_subsumed:                 0
% 3.76/1.06  sim_fw_subsumed:                        238
% 3.76/1.06  sim_bw_subsumed:                        53
% 3.76/1.06  sim_fw_subsumption_res:                 0
% 3.76/1.06  sim_bw_subsumption_res:                 0
% 3.76/1.06  sim_tautology_del:                      0
% 3.76/1.06  sim_eq_tautology_del:                   133
% 3.76/1.06  sim_eq_res_simp:                        0
% 3.76/1.06  sim_fw_demodulated:                     1103
% 3.76/1.06  sim_bw_demodulated:                     152
% 3.76/1.06  sim_light_normalised:                   492
% 3.76/1.06  sim_joinable_taut:                      0
% 3.76/1.06  sim_joinable_simp:                      0
% 3.76/1.06  sim_ac_normalised:                      0
% 3.76/1.06  sim_smt_subsumption:                    0
% 3.76/1.06  
%------------------------------------------------------------------------------
