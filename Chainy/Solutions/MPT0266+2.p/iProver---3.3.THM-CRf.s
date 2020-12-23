%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0266+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:31 EST 2020

% Result     : Theorem 42.81s
% Output     : CNFRefutation 42.81s
% Verified   : 
% Statistics : Number of formulae       :  324 (100911 expanded)
%              Number of clauses        :  244 (23999 expanded)
%              Number of leaves         :   27 (31476 expanded)
%              Depth                    :   39
%              Number of atoms          :  339 (104174 expanded)
%              Number of equality atoms :  323 (101374 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :   15 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f676,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f828,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1188,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f676,f828,f828])).

fof(f60,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f773,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f60])).

fof(f1230,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f773,f828,f828,f828])).

fof(f109,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f827,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f109])).

fof(f1278,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f827,f828])).

fof(f48,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f755,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

fof(f1185,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f755,f828])).

fof(f111,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f829,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f111])).

fof(f1279,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f829,f828,f828])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f892,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f888,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f1174,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f888,f828])).

fof(f1318,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f892,f1174])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f885,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f677,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f818,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f680,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1269,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f818,f680])).

fof(f112,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f830,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f112])).

fof(f1280,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f830,f680,f680])).

fof(f124,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f842,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f124])).

fof(f1288,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f842,f680])).

fof(f164,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f886,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f164])).

fof(f1315,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f886,f680])).

fof(f88,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f805,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

fof(f1261,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f805,f828,f680,f680])).

fof(f362,conjecture,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f363,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f362])).

fof(f530,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f363])).

fof(f671,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) )
   => ( ~ r2_hidden(sK35,sK37)
      & k3_xboole_0(k2_tarski(sK35,sK36),sK37) = k2_tarski(sK35,sK36) ) ),
    introduced(choice_axiom,[])).

fof(f672,plain,
    ( ~ r2_hidden(sK35,sK37)
    & k3_xboole_0(k2_tarski(sK35,sK36),sK37) = k2_tarski(sK35,sK36) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK35,sK36,sK37])],[f530,f671])).

fof(f1169,plain,(
    k3_xboole_0(k2_tarski(sK35,sK36),sK37) = k2_tarski(sK35,sK36) ),
    inference(cnf_transformation,[],[f672])).

fof(f226,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f984,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f1175,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f984,f1174])).

fof(f1502,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))) = k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))),sK37)) ),
    inference(definition_unfolding,[],[f1169,f828,f1175,f1175])).

fof(f103,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f821,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f103])).

fof(f1272,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f821,f1174])).

fof(f61,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f774,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f61])).

fof(f1231,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
    inference(definition_unfolding,[],[f774,f828,f828,f828])).

fof(f114,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f832,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f114])).

fof(f1282,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f832,f828,f828,f828])).

fof(f116,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f834,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f116])).

fof(f1284,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f834,f1174,f828])).

fof(f117,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f835,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f117])).

fof(f1285,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f835,f828,f1174])).

fof(f118,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f836,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f118])).

fof(f1286,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f836,f1174,f828])).

fof(f167,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f889,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f167])).

fof(f1317,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f889,f828,f1174])).

fof(f303,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f648,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f303])).

fof(f1074,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f648])).

fof(f1431,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | o_0_0_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(definition_unfolding,[],[f1074,f680])).

fof(f1170,plain,(
    ~ r2_hidden(sK35,sK37) ),
    inference(cnf_transformation,[],[f672])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1188])).

cnf(c_100,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(cnf_transformation,[],[f1230])).

cnf(c_154,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1278])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1185])).

cnf(c_25653,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_154,c_1])).

cnf(c_37024,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(light_normalisation,[status(thm)],[c_100,c_100,c_25653])).

cnf(c_155,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f1279])).

cnf(c_34472,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_155,c_155,c_25653])).

cnf(c_34473,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_34472,c_25653])).

cnf(c_37025,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X2,X1))))) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(demodulation,[status(thm)],[c_37024,c_25653,c_34473])).

cnf(c_25641,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_154])).

cnf(c_26072,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_25641,c_25653])).

cnf(c_37026,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))) ),
    inference(demodulation,[status(thm)],[c_37025,c_26072])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1318])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f885])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f677])).

cnf(c_8570,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_37058,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),X1)))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_37026,c_8570])).

cnf(c_37079,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),X1)))) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X1))) ),
    inference(demodulation,[status(thm)],[c_37058,c_37026])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1269])).

cnf(c_156,plain,
    ( k4_xboole_0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1280])).

cnf(c_168,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1288])).

cnf(c_212,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1315])).

cnf(c_132,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1261])).

cnf(c_14304,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_132,c_145])).

cnf(c_34482,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[status(thm)],[c_6,c_34473])).

cnf(c_25629,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_34524,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_34482,c_25629])).

cnf(c_37080,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_37079,c_145,c_156,c_168,c_212,c_14304,c_34524])).

cnf(c_72907,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_25629,c_25653])).

cnf(c_72961,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_37080,c_72907])).

cnf(c_73063,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_72961,c_168,c_212])).

cnf(c_485,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))) = k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k1_tarski(sK36)),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36)))),sK37)) ),
    inference(cnf_transformation,[],[f1502])).

cnf(c_8432,negated_conjecture,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))),sK37)) = k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k1_tarski(sK36))))) ),
    inference(theory_normalisation,[status(thm)],[c_485,c_211,c_7])).

cnf(c_14421,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),sK37)) = k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))) ),
    inference(demodulation,[status(thm)],[c_8432,c_8570])).

cnf(c_24691,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),sK37) ),
    inference(superposition,[status(thm)],[c_14421,c_1])).

cnf(c_24702,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),sK37) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_24691,c_212])).

cnf(c_34488,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0))) = k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),o_0_0_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_24702,c_34473])).

cnf(c_34518,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0) ),
    inference(demodulation,[status(thm)],[c_34488,c_168])).

cnf(c_73466,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),sK37)) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(X0,sK37)) ),
    inference(superposition,[status(thm)],[c_73063,c_34518])).

cnf(c_73611,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(X0,sK37)) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),o_0_0_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_73466,c_24702])).

cnf(c_73612,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(X0,sK37)) = k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))) ),
    inference(demodulation,[status(thm)],[c_73611,c_168])).

cnf(c_25632,plain,
    ( k4_xboole_0(sK37,k4_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))))) = k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))) ),
    inference(superposition,[status(thm)],[c_6,c_14421])).

cnf(c_148,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1272])).

cnf(c_8596,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(theory_normalisation,[status(thm)],[c_148,c_211,c_7])).

cnf(c_14317,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_8596,c_8570])).

cnf(c_25633,plain,
    ( k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))) = k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))) ),
    inference(demodulation,[status(thm)],[c_25632,c_14317])).

cnf(c_37052,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0)) = k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))) ),
    inference(superposition,[status(thm)],[c_25633,c_37026])).

cnf(c_101,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
    inference(cnf_transformation,[],[f1231])).

cnf(c_39954,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
    inference(light_normalisation,[status(thm)],[c_101,c_101,c_25653])).

cnf(c_39955,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X2,k4_xboole_0(X2,X1))) = k5_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
    inference(demodulation,[status(thm)],[c_39954,c_25653])).

cnf(c_39967,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0),X1)) = k5_xboole_0(k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))),k5_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_37052,c_39955])).

cnf(c_72949,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_6,c_72907])).

cnf(c_73080,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_72949,c_212,c_25653,c_72907])).

cnf(c_158,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f1282])).

cnf(c_36927,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_158,c_158,c_25653])).

cnf(c_36928,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X0,X2))))) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_36927,c_25653,c_34473])).

cnf(c_37672,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X1))),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_37052,c_36928])).

cnf(c_37673,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)))))),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))) = k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))) ),
    inference(demodulation,[status(thm)],[c_37672,c_37052])).

cnf(c_37665,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0) ),
    inference(superposition,[status(thm)],[c_37052,c_1])).

cnf(c_43462,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))))),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0)) ),
    inference(superposition,[status(thm)],[c_6,c_37665])).

cnf(c_43488,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))))) = k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))) ),
    inference(demodulation,[status(thm)],[c_43462,c_25653,c_34473,c_37052])).

cnf(c_35553,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))) ),
    inference(superposition,[status(thm)],[c_25633,c_34518])).

cnf(c_24695,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),sK37)) ),
    inference(superposition,[status(thm)],[c_14421,c_1])).

cnf(c_24696,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))))) = k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))) ),
    inference(light_normalisation,[status(thm)],[c_24695,c_14421])).

cnf(c_24697,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k1_tarski(sK35)),k1_tarski(sK36))) = k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))) ),
    inference(demodulation,[status(thm)],[c_24696,c_14317])).

cnf(c_28711,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,X1),X2))))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X2,k5_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_211,c_8570])).

cnf(c_28718,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X2,k5_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_28711,c_25629])).

cnf(c_35560,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))) = k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))) ),
    inference(demodulation,[status(thm)],[c_35553,c_14317,c_24697,c_28718])).

cnf(c_43489,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k5_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))))))) = k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))) ),
    inference(light_normalisation,[status(thm)],[c_43488,c_35560])).

cnf(c_37670,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(sK37,X0),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0) ),
    inference(superposition,[status(thm)],[c_37052,c_34518])).

cnf(c_39404,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK37)),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_37670])).

cnf(c_39422,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0)) ),
    inference(demodulation,[status(thm)],[c_39404,c_25653,c_34473])).

cnf(c_39423,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k5_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))))))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0)) ),
    inference(light_normalisation,[status(thm)],[c_39422,c_25633])).

cnf(c_39424,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k1_tarski(sK35)),k1_tarski(sK36))))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0)) ),
    inference(demodulation,[status(thm)],[c_39423,c_14317])).

cnf(c_43490,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0)) ),
    inference(demodulation,[status(thm)],[c_43489,c_14317,c_39424])).

cnf(c_52905,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X1))))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_37673,c_43490])).

cnf(c_73475,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),sK37)))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(X1,sK37)))) ),
    inference(superposition,[status(thm)],[c_73063,c_52905])).

cnf(c_73596,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(X1,sK37)))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0)) ),
    inference(light_normalisation,[status(thm)],[c_73475,c_145,c_24702])).

cnf(c_73700,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,sK37)))))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k5_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_34473,c_73596])).

cnf(c_91594,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,sK37),X2))))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k5_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)))) ),
    inference(superposition,[status(thm)],[c_73080,c_73700])).

cnf(c_91712,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,sK37),X2))))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,o_0_0_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_91594,c_145,c_212])).

cnf(c_91713,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,sK37),X2))))) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_91712,c_145,c_24702])).

cnf(c_37664,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0),X1)) = k5_xboole_0(k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))),X1) ),
    inference(superposition,[status(thm)],[c_37052,c_211])).

cnf(c_48897,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0),X1)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_37664,c_37664,c_43490])).

cnf(c_92189,plain,
    ( k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(sK37,k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,sK37),X2)))))),X3) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(o_0_0_xboole_0,X3)) ),
    inference(superposition,[status(thm)],[c_91713,c_48897])).

cnf(c_15005,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_211,c_7])).

cnf(c_26083,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))))) = k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))) ),
    inference(superposition,[status(thm)],[c_25633,c_1])).

cnf(c_26086,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))))) = k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))) ),
    inference(demodulation,[status(thm)],[c_26083,c_25633])).

cnf(c_26087,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))) = k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))) ),
    inference(demodulation,[status(thm)],[c_26086,c_14317])).

cnf(c_28705,plain,
    ( k5_xboole_0(sK37,k5_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),X0)) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0) ),
    inference(superposition,[status(thm)],[c_26087,c_211])).

cnf(c_72673,plain,
    ( k5_xboole_0(sK37,k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),X1))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_15005,c_28705])).

cnf(c_15003,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_211,c_7])).

cnf(c_64529,plain,
    ( k5_xboole_0(sK37,k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),X1))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_15003,c_28705])).

cnf(c_28712,plain,
    ( k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k1_tarski(sK35)),k1_tarski(sK36)))) = k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))) ),
    inference(superposition,[status(thm)],[c_211,c_24697])).

cnf(c_30065,plain,
    ( k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k5_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k1_tarski(sK35)),k1_tarski(sK36))),X0)) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0) ),
    inference(superposition,[status(thm)],[c_28712,c_211])).

cnf(c_64530,plain,
    ( k5_xboole_0(k1_tarski(sK35),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k1_tarski(sK35)),k1_tarski(sK36))),X1))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_15003,c_30065])).

cnf(c_39402,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK36),k4_xboole_0(sK37,k1_tarski(sK35)))))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k1_tarski(sK35)) ),
    inference(superposition,[status(thm)],[c_6,c_37670])).

cnf(c_160,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1284])).

cnf(c_8588,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(theory_normalisation,[status(thm)],[c_160,c_211,c_7])).

cnf(c_161,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(cnf_transformation,[],[f1285])).

cnf(c_8587,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(theory_normalisation,[status(thm)],[c_161,c_211,c_7])).

cnf(c_14356,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_8587,c_8570,c_14317])).

cnf(c_162,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f1286])).

cnf(c_8621,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(theory_normalisation,[status(thm)],[c_162,c_211,c_7])).

cnf(c_14380,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_8621,c_14356])).

cnf(c_14384,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_8588,c_8570,c_14356,c_14380])).

cnf(c_39425,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k1_tarski(sK35)) = k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))) ),
    inference(demodulation,[status(thm)],[c_39402,c_14384])).

cnf(c_64541,plain,
    ( k5_xboole_0(k1_tarski(sK35),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k4_xboole_0(k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),k1_tarski(sK36))),X1))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_64530,c_39425])).

cnf(c_37059,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))),X3) ),
    inference(superposition,[status(thm)],[c_37026,c_34473])).

cnf(c_37078,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X3) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X3),X2))) ),
    inference(demodulation,[status(thm)],[c_37059,c_37026])).

cnf(c_64542,plain,
    ( k5_xboole_0(k1_tarski(sK35),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK36)),k1_tarski(sK35))))),X1))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_64541,c_37078])).

cnf(c_34489,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),X0))) = k4_xboole_0(k5_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),X0) ),
    inference(superposition,[status(thm)],[c_25633,c_34473])).

cnf(c_36944,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),X1)))) = k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),X1)))) ),
    inference(superposition,[status(thm)],[c_34489,c_36928])).

cnf(c_214,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1317])).

cnf(c_8571,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(theory_normalisation,[status(thm)],[c_214,c_211,c_7])).

cnf(c_28206,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X0,X1)))))) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_8571,c_8571,c_25653])).

cnf(c_39929,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),k5_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),k5_xboole_0(sK37,k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),sK37))))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),sK37)) ),
    inference(superposition,[status(thm)],[c_28705,c_28206])).

cnf(c_28698,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(o_0_0_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_212,c_211])).

cnf(c_19853,plain,
    ( k5_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_168,c_7])).

cnf(c_28725,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_28698,c_19853])).

cnf(c_26084,plain,
    ( k5_xboole_0(sK37,k5_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),k4_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))))) = k5_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),sK37)) ),
    inference(superposition,[status(thm)],[c_25633,c_8570])).

cnf(c_26085,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),sK37)) = sK37 ),
    inference(demodulation,[status(thm)],[c_26084,c_168,c_212,c_14317])).

cnf(c_28704,plain,
    ( k5_xboole_0(sK37,k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),sK37),X0)) = k5_xboole_0(sK37,X0) ),
    inference(superposition,[status(thm)],[c_26085,c_211])).

cnf(c_35971,plain,
    ( k5_xboole_0(sK37,k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),sK37))) = k5_xboole_0(sK37,X0) ),
    inference(superposition,[status(thm)],[c_7,c_28704])).

cnf(c_39932,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k1_tarski(sK35)))) = k5_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))) ),
    inference(demodulation,[status(thm)],[c_39929,c_28725,c_35971,c_37026])).

cnf(c_39933,plain,
    ( k5_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))) = k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k1_tarski(sK35)) ),
    inference(demodulation,[status(thm)],[c_39932,c_34524])).

cnf(c_45773,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k1_tarski(sK35)),X1)))) = k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),X1)))) ),
    inference(light_normalisation,[status(thm)],[c_36944,c_36944,c_39933])).

cnf(c_45793,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),X0)))) = k4_xboole_0(k5_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k1_tarski(sK35)),X0)) ),
    inference(superposition,[status(thm)],[c_45773,c_34489])).

cnf(c_45801,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),X0)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k1_tarski(sK35)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k1_tarski(sK35)),X0)) ),
    inference(light_normalisation,[status(thm)],[c_45793,c_39933])).

cnf(c_45802,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k5_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),X0)))) = k5_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k4_xboole_0(X0,k1_tarski(sK35)))) ),
    inference(demodulation,[status(thm)],[c_45801,c_25653,c_34489,c_37026])).

cnf(c_45803,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k5_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k4_xboole_0(X0,k1_tarski(sK36)))))) = k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(X0,k1_tarski(sK35)),k1_tarski(sK36)))) ),
    inference(demodulation,[status(thm)],[c_45802,c_37026])).

cnf(c_25657,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_25653,c_154])).

cnf(c_45804,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(X0,k1_tarski(sK35)),k1_tarski(sK36)))) = k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(X0,k1_tarski(sK36)),k1_tarski(sK35)))) ),
    inference(demodulation,[status(thm)],[c_45803,c_25657,c_37026])).

cnf(c_64543,plain,
    ( k5_xboole_0(k1_tarski(sK35),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k1_tarski(sK36))))),X1))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_64542,c_45804])).

cnf(c_57029,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_37080,c_34473])).

cnf(c_57133,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X1))) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_57029,c_156,c_212,c_37026])).

cnf(c_64544,plain,
    ( k5_xboole_0(k1_tarski(sK35),k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),X1))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_64543,c_168,c_57133])).

cnf(c_64546,plain,
    ( k5_xboole_0(sK37,k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),X1))) = k5_xboole_0(k1_tarski(sK35),k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),X1))) ),
    inference(demodulation,[status(thm)],[c_64529,c_64544])).

cnf(c_72703,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(X0,X1)) = k5_xboole_0(k1_tarski(sK35),k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),X0))) ),
    inference(light_normalisation,[status(thm)],[c_72673,c_64546])).

cnf(c_73706,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,sK37)))))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0)) ),
    inference(superposition,[status(thm)],[c_34473,c_73596])).

cnf(c_85050,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,sK37),X3)))))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0)) ),
    inference(superposition,[status(thm)],[c_37026,c_73706])).

cnf(c_92218,plain,
    ( k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,sK37)),X0) = k5_xboole_0(k1_tarski(sK35),k5_xboole_0(X0,k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))) ),
    inference(demodulation,[status(thm)],[c_92189,c_168,c_72703,c_85050])).

cnf(c_92219,plain,
    ( k5_xboole_0(k1_tarski(sK35),k5_xboole_0(X0,k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0) ),
    inference(demodulation,[status(thm)],[c_92218,c_73612])).

cnf(c_110498,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(X0,k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(X0,k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),X1)) = k5_xboole_0(k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))),k5_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_39967,c_92219])).

cnf(c_39979,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0),sK37)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),o_0_0_xboole_0),k5_xboole_0(X0,k4_xboole_0(X0,sK37))) ),
    inference(superposition,[status(thm)],[c_24702,c_39955])).

cnf(c_40052,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0),sK37)) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(X0,k4_xboole_0(X0,sK37))) ),
    inference(demodulation,[status(thm)],[c_39979,c_168])).

cnf(c_64425,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,o_0_0_xboole_0) ),
    inference(superposition,[status(thm)],[c_212,c_15003])).

cnf(c_64614,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_64425,c_168])).

cnf(c_67214,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_64614,c_211])).

cnf(c_87518,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_7,c_67214])).

cnf(c_94162,plain,
    ( k5_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0),sK37),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(X0,k4_xboole_0(X0,sK37))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0),X1) ),
    inference(superposition,[status(thm)],[c_40052,c_87518])).

cnf(c_28214,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))))) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_6,c_28206])).

cnf(c_28234,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_28214,c_1,c_25629])).

cnf(c_28235,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_28234,c_168,c_212])).

cnf(c_76940,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0),k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(X0,k4_xboole_0(X0,sK37)))) = k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0),sK37) ),
    inference(superposition,[status(thm)],[c_40052,c_28235])).

cnf(c_72633,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_15005,c_64614])).

cnf(c_77093,plain,
    ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0),sK37) = k4_xboole_0(X0,sK37) ),
    inference(demodulation,[status(thm)],[c_76940,c_72633])).

cnf(c_94276,plain,
    ( k5_xboole_0(k4_xboole_0(X0,sK37),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(X0,k4_xboole_0(X0,sK37))))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(X0,k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),X1) ),
    inference(light_normalisation,[status(thm)],[c_94162,c_77093,c_92219])).

cnf(c_15004,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_211,c_7])).

cnf(c_87529,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X0)))) = k5_xboole_0(X3,k5_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_15004,c_67214])).

cnf(c_94277,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_tarski(sK35),k5_xboole_0(X1,k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(X0,k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),X1) ),
    inference(demodulation,[status(thm)],[c_94276,c_87529,c_92219])).

cnf(c_110499,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(X0,k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(X0,k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),X1)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X1)),k5_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_110498,c_43490,c_94277])).

cnf(c_110620,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),k4_xboole_0(X0,sK37))) = k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(X0,sK37))),k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))))) ),
    inference(superposition,[status(thm)],[c_73612,c_110499])).

cnf(c_28703,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k1_tarski(sK35)),k1_tarski(sK36)),X0)) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0) ),
    inference(superposition,[status(thm)],[c_24697,c_211])).

cnf(c_30736,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k1_tarski(sK35)),k1_tarski(sK36)))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0) ),
    inference(superposition,[status(thm)],[c_7,c_28703])).

cnf(c_37063,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k1_tarski(sK35))) ),
    inference(superposition,[status(thm)],[c_37026,c_30736])).

cnf(c_37070,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k1_tarski(sK35))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))) ),
    inference(demodulation,[status(thm)],[c_37063,c_28235])).

cnf(c_37085,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))) = k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))) ),
    inference(demodulation,[status(thm)],[c_37052,c_37070])).

cnf(c_42111,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))) ),
    inference(superposition,[status(thm)],[c_37085,c_1])).

cnf(c_42114,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)))))) = k4_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k4_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))))) ),
    inference(superposition,[status(thm)],[c_37085,c_6])).

cnf(c_42121,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)))))) = k5_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k1_tarski(sK35)),k1_tarski(sK36))) ),
    inference(demodulation,[status(thm)],[c_42114,c_14317,c_25653])).

cnf(c_42122,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)))))) = k5_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK36),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))) ),
    inference(demodulation,[status(thm)],[c_42121,c_37026,c_37080])).

cnf(c_42123,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)))))) = k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)) ),
    inference(demodulation,[status(thm)],[c_42122,c_1])).

cnf(c_42128,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))) ),
    inference(demodulation,[status(thm)],[c_42111,c_37085,c_42123])).

cnf(c_52910,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0)),X0))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,o_0_0_xboole_0)) ),
    inference(superposition,[status(thm)],[c_14304,c_52905])).

cnf(c_52985,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0)),X0))) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_52910,c_145,c_24702])).

cnf(c_53038,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(X0,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X1)),X1))))) = k5_xboole_0(o_0_0_xboole_0,k4_xboole_0(o_0_0_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_52985,c_37026])).

cnf(c_53076,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(X0,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X1)),X1))))) = k5_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_53038,c_156])).

cnf(c_53077,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(X0,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X1)),X1))))) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_53076,c_19853,c_37052])).

cnf(c_53046,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(X0,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X1)),X1))))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),o_0_0_xboole_0)))) ),
    inference(superposition,[status(thm)],[c_52985,c_36928])).

cnf(c_53066,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(X0,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X1)),X1))))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(X0,k1_tarski(sK35)),k1_tarski(sK36)))) ),
    inference(demodulation,[status(thm)],[c_53046,c_168,c_14317,c_37052,c_43490])).

cnf(c_52918,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),o_0_0_xboole_0)))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(X0,sK37))) ),
    inference(superposition,[status(thm)],[c_14304,c_52905])).

cnf(c_52979,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(X0,k1_tarski(sK35)),k1_tarski(sK36)))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(X0,sK37))) ),
    inference(demodulation,[status(thm)],[c_52918,c_145,c_14317])).

cnf(c_53067,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(X0,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X1)),X1))))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(X0,sK37))) ),
    inference(light_normalisation,[status(thm)],[c_53066,c_52979])).

cnf(c_53078,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(X0,sK37))) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_53077,c_53067])).

cnf(c_110981,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)))))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)))))),k4_xboole_0(X0,sK37))) = k5_xboole_0(o_0_0_xboole_0,k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))))) ),
    inference(light_normalisation,[status(thm)],[c_110620,c_42128,c_53078])).

cnf(c_72931,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_37026,c_72907])).

cnf(c_94132,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k1_tarski(sK35)),k1_tarski(sK36)),k5_xboole_0(X0,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),X0) ),
    inference(superposition,[status(thm)],[c_24697,c_87518])).

cnf(c_53023,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X1)))))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_52905,c_52985])).

cnf(c_76696,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X1)))))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),o_0_0_xboole_0)) ),
    inference(superposition,[status(thm)],[c_53023,c_25657])).

cnf(c_76819,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_76696,c_53023])).

cnf(c_76820,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k1_tarski(sK35)),k1_tarski(sK36)) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_76819,c_168,c_14317])).

cnf(c_76821,plain,
    ( k4_xboole_0(k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),k1_tarski(sK36)) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_76820,c_39425])).

cnf(c_94303,plain,
    ( k5_xboole_0(o_0_0_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))))) = k5_xboole_0(k1_tarski(sK35),k5_xboole_0(X0,k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))) ),
    inference(light_normalisation,[status(thm)],[c_94132,c_39425,c_76821,c_92219])).

cnf(c_110982,plain,
    ( k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k4_xboole_0(X0,sK37),k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)))))) = k4_xboole_0(k1_tarski(sK35),k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)))) ),
    inference(demodulation,[status(thm)],[c_110981,c_37026,c_42128,c_72931,c_94303])).

cnf(c_74059,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK37),k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))) = k4_xboole_0(X0,sK37) ),
    inference(superposition,[status(thm)],[c_73612,c_73063])).

cnf(c_75762,plain,
    ( k4_xboole_0(k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))),k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_37085,c_73080])).

cnf(c_73000,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k1_tarski(sK35)),k1_tarski(sK36))),k1_tarski(sK35))) = k4_xboole_0(k1_tarski(sK35),k5_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k1_tarski(sK35)),k1_tarski(sK36)))) ),
    inference(superposition,[status(thm)],[c_72907,c_30065])).

cnf(c_73014,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k4_xboole_0(k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),k1_tarski(sK36))),k1_tarski(sK35))) = k4_xboole_0(k1_tarski(sK35),k5_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k4_xboole_0(k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),k1_tarski(sK36)))) ),
    inference(light_normalisation,[status(thm)],[c_73000,c_39425])).

cnf(c_73015,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK36)),k1_tarski(sK35))))),k1_tarski(sK35))) = k4_xboole_0(k1_tarski(sK35),k5_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK36)),k1_tarski(sK35)))))) ),
    inference(demodulation,[status(thm)],[c_73014,c_37078])).

cnf(c_73016,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k1_tarski(sK36))))),k1_tarski(sK35))) = k4_xboole_0(k1_tarski(sK35),k5_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k1_tarski(sK36)))))) ),
    inference(demodulation,[status(thm)],[c_73015,c_45804])).

cnf(c_37668,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(X0,X1))) = k4_xboole_0(k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))),X1) ),
    inference(superposition,[status(thm)],[c_37052,c_34473])).

cnf(c_37677,plain,
    ( k4_xboole_0(k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))),X1) = k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))) ),
    inference(demodulation,[status(thm)],[c_37668,c_37052])).

cnf(c_36968,plain,
    ( k4_xboole_0(k5_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),k5_xboole_0(sK37,k4_xboole_0(sK37,X0))) = k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),X0))) ),
    inference(superposition,[status(thm)],[c_36928,c_34489])).

cnf(c_36975,plain,
    ( k4_xboole_0(k5_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),k5_xboole_0(sK37,k4_xboole_0(sK37,X0))) = k4_xboole_0(k5_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),X0) ),
    inference(light_normalisation,[status(thm)],[c_36968,c_34489])).

cnf(c_39800,plain,
    ( k4_xboole_0(k5_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),k4_xboole_0(k5_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),X0)) = k4_xboole_0(k5_xboole_0(sK37,k4_xboole_0(sK37,X0)),k4_xboole_0(k5_xboole_0(sK37,k4_xboole_0(sK37,X0)),k5_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))))) ),
    inference(superposition,[status(thm)],[c_36975,c_6])).

cnf(c_39803,plain,
    ( k4_xboole_0(k5_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),k4_xboole_0(k5_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),X0)) = k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k5_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))))))))) ),
    inference(demodulation,[status(thm)],[c_39800,c_25653,c_34473])).

cnf(c_36954,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k5_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))))))) = k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))) ),
    inference(superposition,[status(thm)],[c_25633,c_36928])).

cnf(c_39804,plain,
    ( k4_xboole_0(k5_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),k4_xboole_0(k5_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),X0)) = k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)))))))) ),
    inference(light_normalisation,[status(thm)],[c_39803,c_36954])).

cnf(c_39780,plain,
    ( k4_xboole_0(k5_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),k4_xboole_0(k5_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),X0)) = k4_xboole_0(k5_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)),X0)) ),
    inference(superposition,[status(thm)],[c_34489,c_36975])).

cnf(c_66297,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k1_tarski(sK35)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k1_tarski(sK35)),X0)) ),
    inference(light_normalisation,[status(thm)],[c_39804,c_39780,c_39933,c_43490])).

cnf(c_66298,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0))))) = k5_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k4_xboole_0(X0,k1_tarski(sK35)))) ),
    inference(demodulation,[status(thm)],[c_66297,c_25653,c_37026])).

cnf(c_66299,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0))))) = k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(X0,k1_tarski(sK35)),k1_tarski(sK36)))) ),
    inference(demodulation,[status(thm)],[c_66298,c_37026])).

cnf(c_66306,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)))))))),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))))) = k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))),k1_tarski(sK35)),k1_tarski(sK36)))) ),
    inference(superposition,[status(thm)],[c_37677,c_66299])).

cnf(c_66376,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0))))),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))))) = k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0)),k1_tarski(sK35)),k1_tarski(sK36)))) ),
    inference(light_normalisation,[status(thm)],[c_66306,c_43490])).

cnf(c_66377,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0))))))) = k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0)),k1_tarski(sK35)),k1_tarski(sK36)))) ),
    inference(demodulation,[status(thm)],[c_66376,c_25657,c_43490])).

cnf(c_52937,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X1)))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_52905,c_34518])).

cnf(c_52950,plain,
    ( k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(X0,k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X1)))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_52937,c_34518])).

cnf(c_66378,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0)),k1_tarski(sK35)),k1_tarski(sK36)))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,k4_xboole_0(X0,X0))) ),
    inference(demodulation,[status(thm)],[c_66377,c_52905,c_52950])).

cnf(c_66379,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0)),k1_tarski(sK35)),k1_tarski(sK36)))) = k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,o_0_0_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_66378,c_14304])).

cnf(c_66380,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(sK37,X0)),k1_tarski(sK35)),k1_tarski(sK36)))) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_66379,c_145,c_24702])).

cnf(c_67070,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),k1_tarski(sK35)),k1_tarski(sK36)))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_25633,c_66380])).

cnf(c_57046,plain,
    ( k4_xboole_0(k5_xboole_0(sK37,k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),k1_tarski(sK36)) = k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36)))) ),
    inference(superposition,[status(thm)],[c_37080,c_34489])).

cnf(c_57119,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k1_tarski(sK35)),k1_tarski(sK36)) = k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k1_tarski(sK35)) ),
    inference(light_normalisation,[status(thm)],[c_57046,c_25633,c_39933])).

cnf(c_58294,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k1_tarski(sK35)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k1_tarski(sK35)),k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k1_tarski(sK35)),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k1_tarski(sK35)))))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k1_tarski(sK35)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k1_tarski(sK35)),k4_xboole_0(X0,k1_tarski(sK36)))) ),
    inference(superposition,[status(thm)],[c_57119,c_36928])).

cnf(c_58317,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k1_tarski(sK36)),k1_tarski(sK35)),k1_tarski(sK36)))) = k5_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK36)),k4_xboole_0(X0,k1_tarski(sK35)))) ),
    inference(demodulation,[status(thm)],[c_58294,c_145,c_212,c_37026])).

cnf(c_58318,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,k1_tarski(sK36)),k1_tarski(sK35)),k1_tarski(sK36)))) = k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(X0,k1_tarski(sK35)),k1_tarski(sK36)))) ),
    inference(demodulation,[status(thm)],[c_58317,c_37026])).

cnf(c_67105,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k1_tarski(sK35)),k1_tarski(sK35)),k1_tarski(sK36)))) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_67070,c_14317,c_58318])).

cnf(c_67106,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))),k1_tarski(sK35)),k1_tarski(sK36)))) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_67105,c_39425])).

cnf(c_57014,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X2) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_34473,c_37080])).

cnf(c_57145,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_57014,c_34473])).

cnf(c_67107,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),k1_tarski(sK36)))) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_67106,c_25657,c_37078,c_45804,c_57145])).

cnf(c_73017,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))),k4_xboole_0(k5_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),o_0_0_xboole_0),k1_tarski(sK35))) = k4_xboole_0(k1_tarski(sK35),k5_xboole_0(k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)),o_0_0_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_73016,c_67107])).

cnf(c_73018,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))) = k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35))) ),
    inference(demodulation,[status(thm)],[c_73017,c_168,c_37080,c_42128])).

cnf(c_73065,plain,
    ( k5_xboole_0(sK37,k4_xboole_0(sK37,k4_xboole_0(k1_tarski(sK35),k4_xboole_0(k4_xboole_0(sK37,k1_tarski(sK35)),k1_tarski(sK36))))) = k1_tarski(sK35) ),
    inference(demodulation,[status(thm)],[c_73063,c_73018])).

cnf(c_75923,plain,
    ( k4_xboole_0(k1_tarski(sK35),k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK36),k1_tarski(sK35)))) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_75762,c_73065])).

cnf(c_110983,plain,
    ( k5_xboole_0(k1_tarski(sK35),k4_xboole_0(k1_tarski(sK35),k4_xboole_0(X0,sK37))) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_110982,c_25633,c_74059,c_75923])).

cnf(c_111981,plain,
    ( k5_xboole_0(k1_tarski(sK35),k4_xboole_0(sK37,k4_xboole_0(sK37,k1_tarski(sK35)))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_110983])).

cnf(c_112304,plain,
    ( k4_xboole_0(k1_tarski(sK35),sK37) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_111981,c_25653,c_72907])).

cnf(c_390,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1431])).

cnf(c_15017,plain,
    ( r2_hidden(sK35,sK37)
    | k4_xboole_0(k1_tarski(sK35),sK37) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_390])).

cnf(c_484,negated_conjecture,
    ( ~ r2_hidden(sK35,sK37) ),
    inference(cnf_transformation,[],[f1170])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_112304,c_15017,c_484])).

%------------------------------------------------------------------------------
