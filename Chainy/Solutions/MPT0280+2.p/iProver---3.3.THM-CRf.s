%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0280+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:33 EST 2020

% Result     : Theorem 31.15s
% Output     : CNFRefutation 31.15s
% Verified   : 
% Statistics : Number of formulae       :   52 (  94 expanded)
%              Number of clauses        :   19 (  26 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 128 expanded)
%              Number of equality atoms :   11 (  49 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f845,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f96])).

fof(f106,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f443,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f106])).

fof(f856,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f443])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f920,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f860,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1235,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f920,f860])).

fof(f1336,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f856,f1235])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f917,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f709,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f149,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f902,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f149])).

fof(f1370,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f902,f1235])).

fof(f375,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f549,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f375])).

fof(f1230,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f549])).

fof(f161,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f488,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f161])).

fof(f489,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f488])).

fof(f915,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f489])).

fof(f1374,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(X0,k4_xboole_0(X0,X2))),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f915,f1235])).

fof(f377,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f378,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f377])).

fof(f550,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f378])).

fof(f703,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36)),k1_zfmisc_1(k2_xboole_0(sK35,sK36))) ),
    introduced(choice_axiom,[])).

fof(f704,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36)),k1_zfmisc_1(k2_xboole_0(sK35,sK36))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36])],[f550,f703])).

fof(f1232,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36)),k1_zfmisc_1(k2_xboole_0(sK35,sK36))) ),
    inference(cnf_transformation,[],[f704])).

fof(f1584,plain,(
    ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36)),k4_xboole_0(k1_zfmisc_1(sK35),k4_xboole_0(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36)))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK35,sK36),k4_xboole_0(sK35,k4_xboole_0(sK35,sK36))))) ),
    inference(definition_unfolding,[],[f1232,f1235,f1235])).

cnf(c_140,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f845])).

cnf(c_79167,plain,
    ( r1_tarski(k4_xboole_0(sK36,sK35),sK36) ),
    inference(instantiation,[status(thm)],[c_140])).

cnf(c_151,plain,
    ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1336])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f917])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f709])).

cnf(c_8968,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(theory_normalisation,[status(thm)],[c_151,c_211,c_7])).

cnf(c_21931,plain,
    ( ~ r1_tarski(k4_xboole_0(sK36,sK35),sK36)
    | r1_tarski(sK36,k5_xboole_0(sK35,k5_xboole_0(sK36,k4_xboole_0(sK35,k4_xboole_0(sK35,sK36))))) ),
    inference(instantiation,[status(thm)],[c_8968])).

cnf(c_196,plain,
    ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(cnf_transformation,[],[f1370])).

cnf(c_8951,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(theory_normalisation,[status(thm)],[c_196,c_211,c_7])).

cnf(c_20792,plain,
    ( r1_tarski(sK35,k5_xboole_0(sK35,k5_xboole_0(sK36,k4_xboole_0(sK35,k4_xboole_0(sK35,sK36))))) ),
    inference(instantiation,[status(thm)],[c_8951])).

cnf(c_513,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f1230])).

cnf(c_16470,plain,
    ( r1_tarski(k1_zfmisc_1(sK36),k1_zfmisc_1(k5_xboole_0(sK35,k5_xboole_0(sK36,k4_xboole_0(sK35,k4_xboole_0(sK35,sK36))))))
    | ~ r1_tarski(sK36,k5_xboole_0(sK35,k5_xboole_0(sK36,k4_xboole_0(sK35,k4_xboole_0(sK35,sK36))))) ),
    inference(instantiation,[status(thm)],[c_513])).

cnf(c_16361,plain,
    ( r1_tarski(k1_zfmisc_1(sK35),k1_zfmisc_1(k5_xboole_0(sK35,k5_xboole_0(sK36,k4_xboole_0(sK35,k4_xboole_0(sK35,sK36))))))
    | ~ r1_tarski(sK35,k5_xboole_0(sK35,k5_xboole_0(sK36,k4_xboole_0(sK35,k4_xboole_0(sK35,sK36))))) ),
    inference(instantiation,[status(thm)],[c_513])).

cnf(c_209,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k5_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(X0,k4_xboole_0(X0,X2))),X1) ),
    inference(cnf_transformation,[],[f1374])).

cnf(c_8948,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k5_xboole_0(X0,k5_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X2)))),X1) ),
    inference(theory_normalisation,[status(thm)],[c_209,c_211,c_7])).

cnf(c_15747,plain,
    ( r1_tarski(k5_xboole_0(k1_zfmisc_1(sK35),k5_xboole_0(k1_zfmisc_1(sK36),k4_xboole_0(k1_zfmisc_1(sK35),k4_xboole_0(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36))))),k1_zfmisc_1(k5_xboole_0(sK35,k5_xboole_0(sK36,k4_xboole_0(sK35,k4_xboole_0(sK35,sK36))))))
    | ~ r1_tarski(k1_zfmisc_1(sK36),k1_zfmisc_1(k5_xboole_0(sK35,k5_xboole_0(sK36,k4_xboole_0(sK35,k4_xboole_0(sK35,sK36))))))
    | ~ r1_tarski(k1_zfmisc_1(sK35),k1_zfmisc_1(k5_xboole_0(sK35,k5_xboole_0(sK36,k4_xboole_0(sK35,k4_xboole_0(sK35,sK36)))))) ),
    inference(instantiation,[status(thm)],[c_8948])).

cnf(c_515,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36)),k4_xboole_0(k1_zfmisc_1(sK35),k4_xboole_0(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36)))),k1_zfmisc_1(k5_xboole_0(k5_xboole_0(sK35,sK36),k4_xboole_0(sK35,k4_xboole_0(sK35,sK36))))) ),
    inference(cnf_transformation,[],[f1584])).

cnf(c_8795,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK35),k5_xboole_0(k1_zfmisc_1(sK36),k4_xboole_0(k1_zfmisc_1(sK35),k4_xboole_0(k1_zfmisc_1(sK35),k1_zfmisc_1(sK36))))),k1_zfmisc_1(k5_xboole_0(sK35,k5_xboole_0(sK36,k4_xboole_0(sK35,k4_xboole_0(sK35,sK36)))))) ),
    inference(theory_normalisation,[status(thm)],[c_515,c_211,c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_79167,c_21931,c_20792,c_16470,c_16361,c_15747,c_8795])).

%------------------------------------------------------------------------------
