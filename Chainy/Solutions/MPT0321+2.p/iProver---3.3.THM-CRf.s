%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0321+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:35 EST 2020

% Result     : Theorem 35.36s
% Output     : CNFRefutation 35.36s
% Verified   : 
% Statistics : Number of formulae       :  329 (25536 expanded)
%              Number of clauses        :  188 (6531 expanded)
%              Number of leaves         :   39 (7352 expanded)
%              Depth                    :   38
%              Number of atoms          :  586 (43908 expanded)
%              Number of equality atoms :  460 (42417 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f344,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f345,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f344])).

fof(f579,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f345])).

fof(f580,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f579])).

fof(f782,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK51 != sK53
        | sK50 != sK52 )
      & k1_xboole_0 != sK51
      & k1_xboole_0 != sK50
      & k2_zfmisc_1(sK50,sK51) = k2_zfmisc_1(sK52,sK53) ) ),
    introduced(choice_axiom,[])).

fof(f783,plain,
    ( ( sK51 != sK53
      | sK50 != sK52 )
    & k1_xboole_0 != sK51
    & k1_xboole_0 != sK50
    & k2_zfmisc_1(sK50,sK51) = k2_zfmisc_1(sK52,sK53) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK50,sK51,sK52,sK53])],[f580,f782])).

fof(f1303,plain,(
    k2_zfmisc_1(sK50,sK51) = k2_zfmisc_1(sK52,sK53) ),
    inference(cnf_transformation,[],[f783])).

fof(f335,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))
      & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1286,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f335])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f818,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f970,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1443,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f818,f970,f970])).

fof(f109,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f969,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f109])).

fof(f1533,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f969,f970])).

fof(f48,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f897,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

fof(f1440,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f897,f970])).

fof(f1285,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f335])).

fof(f111,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f971,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f111])).

fof(f1534,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f971,f970,f970])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f960,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f822,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1524,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f960,f822])).

fof(f124,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f984,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f124])).

fof(f1543,plain,(
    ! [X0] : k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f984,f822])).

fof(f323,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f776,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f323])).

fof(f777,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f776])).

fof(f1269,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f777])).

fof(f1710,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X1 ) ),
    inference(definition_unfolding,[],[f1269,f822,f822])).

fof(f1884,plain,(
    ! [X0] : o_0_0_xboole_0 = k2_zfmisc_1(X0,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f1710])).

fof(f88,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f947,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

fof(f1516,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f947,f970,f822,f822])).

fof(f103,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f963,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f103])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1030,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f1429,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f1030,f970])).

fof(f1527,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f963,f1429])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1027,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f819,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f170,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1034,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f170])).

fof(f1573,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f1034,f1429])).

fof(f92,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f481,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f92])).

fof(f951,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f481])).

fof(f164,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1028,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f164])).

fof(f1570,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f1028,f822])).

fof(f108,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f968,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f108])).

fof(f1532,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f968,f822,f1429])).

fof(f333,axiom,(
    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1283,plain,(
    ! [X2,X0,X3,X1] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    inference(cnf_transformation,[],[f333])).

fof(f1722,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) = k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(definition_unfolding,[],[f1283,f970,f970,f970])).

fof(f336,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1287,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ),
    inference(cnf_transformation,[],[f336])).

fof(f1724,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))))) = k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ),
    inference(definition_unfolding,[],[f1287,f1429])).

fof(f1268,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f777])).

fof(f1711,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)
      | o_0_0_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f1268,f822,f822])).

fof(f1885,plain,(
    ! [X1] : o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1) ),
    inference(equality_resolution,[],[f1711])).

fof(f112,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f972,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f112])).

fof(f1535,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f972,f822,f822])).

fof(f1267,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f777])).

fof(f1712,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0
      | o_0_0_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f1267,f822,f822,f822])).

fof(f1304,plain,(
    k1_xboole_0 != sK50 ),
    inference(cnf_transformation,[],[f783])).

fof(f1731,plain,(
    o_0_0_xboole_0 != sK50 ),
    inference(definition_unfolding,[],[f1304,f822])).

fof(f403,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f801,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f403])).

fof(f802,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(flattening,[],[f801])).

fof(f1393,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | r2_hidden(X1,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f802])).

fof(f226,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1126,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f1430,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f1126,f1429])).

fof(f1793,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | r2_hidden(X1,X2)
      | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2) != k1_tarski(X0) ) ),
    inference(definition_unfolding,[],[f1393,f1430])).

fof(f1395,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f802])).

fof(f1791,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2) = k1_tarski(X0)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f1395,f1430])).

fof(f1900,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X1)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X1)))),X2) = k1_tarski(X1)
      | r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f1791])).

fof(f384,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1367,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f384])).

fof(f1776,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2))) != o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f1367,f1429,f1430,f822])).

fof(f382,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f603,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f382])).

fof(f604,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f603])).

fof(f1365,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f604])).

fof(f1774,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))),X1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))),X1))) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f1365,f1429,f1430])).

fof(f1305,plain,(
    k1_xboole_0 != sK51 ),
    inference(cnf_transformation,[],[f783])).

fof(f1730,plain,(
    o_0_0_xboole_0 != sK51 ),
    inference(definition_unfolding,[],[f1305,f822])).

fof(f153,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f695,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f153])).

fof(f1016,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f695])).

fof(f1017,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f695])).

fof(f132,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f504,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f132])).

fof(f992,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f504])).

fof(f1549,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(definition_unfolding,[],[f992,f822])).

fof(f1830,plain,(
    r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f1549])).

fof(f337,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f576,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f337])).

fof(f1288,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f576])).

fof(f993,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f504])).

fof(f1548,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f993,f822])).

fof(f329,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f572,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f329])).

fof(f573,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f572])).

fof(f1277,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f573])).

fof(f1306,plain,
    ( sK51 != sK53
    | sK50 != sK52 ),
    inference(cnf_transformation,[],[f783])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f681,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f682,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f681])).

fof(f883,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f682])).

fof(f97,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f694,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f97])).

fof(f956,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f694])).

fof(f1521,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | o_0_0_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f956,f822])).

fof(f324,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f566,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f324])).

fof(f567,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f566])).

fof(f1270,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f567])).

fof(f1713,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X1,X0) ) ),
    inference(definition_unfolding,[],[f1270,f822,f822])).

fof(f328,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f571,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f328])).

fof(f1276,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f571])).

fof(f327,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f570,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f327])).

fof(f1273,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f570])).

fof(f1716,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f1273,f822])).

fof(f882,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f682])).

fof(f1827,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f882])).

cnf(c_479,negated_conjecture,
    ( k2_zfmisc_1(sK50,sK51) = k2_zfmisc_1(sK52,sK53) ),
    inference(cnf_transformation,[],[f1303])).

cnf(c_458,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1286])).

cnf(c_45623,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK52,X0),k2_zfmisc_1(sK50,sK51)) = k2_zfmisc_1(sK52,k4_xboole_0(X0,sK53)) ),
    inference(superposition,[status(thm)],[c_479,c_458])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1443])).

cnf(c_46457,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK50,sK51),k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,X0))) = k4_xboole_0(k2_zfmisc_1(sK52,X0),k2_zfmisc_1(sK52,k4_xboole_0(X0,sK53))) ),
    inference(superposition,[status(thm)],[c_45623,c_6])).

cnf(c_45619,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,X0)) = k2_zfmisc_1(sK52,k4_xboole_0(sK53,X0)) ),
    inference(superposition,[status(thm)],[c_479,c_458])).

cnf(c_46463,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK52,X0),k2_zfmisc_1(sK52,k4_xboole_0(X0,sK53))) = k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,k4_xboole_0(sK53,X0))) ),
    inference(light_normalisation,[status(thm)],[c_46457,c_45619])).

cnf(c_154,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1533])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1440])).

cnf(c_32737,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_154,c_1])).

cnf(c_46464,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK52,X0),k2_zfmisc_1(sK52,k4_xboole_0(X0,sK53))) = k2_zfmisc_1(sK52,k5_xboole_0(sK53,k4_xboole_0(sK53,X0))) ),
    inference(demodulation,[status(thm)],[c_46463,c_458,c_32737,c_45619])).

cnf(c_459,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f1285])).

cnf(c_46121,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(X0,sK53)) = k2_zfmisc_1(k4_xboole_0(sK52,X0),sK53) ),
    inference(superposition,[status(thm)],[c_479,c_459])).

cnf(c_155,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f1534])).

cnf(c_49413,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_155,c_155,c_32737])).

cnf(c_49414,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_49413,c_32737])).

cnf(c_49435,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK50,sK51),k4_xboole_0(k2_zfmisc_1(sK50,sK51),k4_xboole_0(k2_zfmisc_1(X0,sK53),X1))) = k4_xboole_0(k5_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(k4_xboole_0(sK52,X0),sK53)),X1) ),
    inference(superposition,[status(thm)],[c_46121,c_49414])).

cnf(c_46125,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,sK53),k2_zfmisc_1(sK50,sK51)) = k2_zfmisc_1(k4_xboole_0(X0,sK52),sK53) ),
    inference(superposition,[status(thm)],[c_479,c_459])).

cnf(c_46811,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK50,sK51),k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(X0,sK53))) = k4_xboole_0(k2_zfmisc_1(X0,sK53),k2_zfmisc_1(k4_xboole_0(X0,sK52),sK53)) ),
    inference(superposition,[status(thm)],[c_46125,c_6])).

cnf(c_46502,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,sK53),k4_xboole_0(k2_zfmisc_1(X0,sK53),k2_zfmisc_1(sK50,sK51))) = k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(k4_xboole_0(sK52,X0),sK53)) ),
    inference(superposition,[status(thm)],[c_46121,c_6])).

cnf(c_46509,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,sK53),k4_xboole_0(k2_zfmisc_1(X0,sK53),k2_zfmisc_1(sK50,sK51))) = k2_zfmisc_1(k4_xboole_0(sK52,k4_xboole_0(sK52,X0)),sK53) ),
    inference(demodulation,[status(thm)],[c_46502,c_46121])).

cnf(c_46510,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,sK53),k2_zfmisc_1(k4_xboole_0(X0,sK52),sK53)) = k2_zfmisc_1(k4_xboole_0(sK52,k4_xboole_0(sK52,X0)),sK53) ),
    inference(light_normalisation,[status(thm)],[c_46509,c_46125])).

cnf(c_46511,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,sK53),k2_zfmisc_1(k4_xboole_0(X0,sK52),sK53)) = k2_zfmisc_1(k5_xboole_0(sK52,k4_xboole_0(sK52,X0)),sK53) ),
    inference(demodulation,[status(thm)],[c_46510,c_459,c_32737])).

cnf(c_46818,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(k4_xboole_0(sK52,X0),sK53)) = k2_zfmisc_1(k5_xboole_0(sK52,k4_xboole_0(sK52,X0)),sK53) ),
    inference(light_normalisation,[status(thm)],[c_46811,c_46121,c_46511])).

cnf(c_72350,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK50,sK51),k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(k5_xboole_0(sK52,k4_xboole_0(sK52,X0)),sK53))) = k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(k4_xboole_0(sK52,X0),sK53)) ),
    inference(superposition,[status(thm)],[c_46818,c_1])).

cnf(c_72367,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK50,sK51),k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(k5_xboole_0(sK52,k4_xboole_0(sK52,X0)),sK53))) = k2_zfmisc_1(k5_xboole_0(sK52,k4_xboole_0(sK52,X0)),sK53) ),
    inference(demodulation,[status(thm)],[c_72350,c_46818])).

cnf(c_72368,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(k4_xboole_0(sK52,k5_xboole_0(sK52,k4_xboole_0(sK52,X0))),sK53)) = k2_zfmisc_1(k5_xboole_0(sK52,k4_xboole_0(sK52,X0)),sK53) ),
    inference(demodulation,[status(thm)],[c_72367,c_46121])).

cnf(c_32742,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_32737,c_154])).

cnf(c_72369,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(k4_xboole_0(sK52,X0),sK53)) = k2_zfmisc_1(k5_xboole_0(sK52,k4_xboole_0(sK52,X0)),sK53) ),
    inference(demodulation,[status(thm)],[c_72368,c_32742])).

cnf(c_100061,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK50,sK51),k4_xboole_0(k2_zfmisc_1(sK50,sK51),k4_xboole_0(k2_zfmisc_1(X0,sK53),X1))) = k4_xboole_0(k2_zfmisc_1(k5_xboole_0(sK52,k4_xboole_0(sK52,X0)),sK53),X1) ),
    inference(light_normalisation,[status(thm)],[c_49435,c_49435,c_72369])).

cnf(c_100076,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK50,sK51),k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,k5_xboole_0(sK53,k4_xboole_0(sK53,sK53))))) = k4_xboole_0(k2_zfmisc_1(k5_xboole_0(sK52,k4_xboole_0(sK52,sK52)),sK53),k2_zfmisc_1(sK52,k4_xboole_0(sK53,sK53))) ),
    inference(superposition,[status(thm)],[c_46464,c_100061])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1524])).

cnf(c_168,plain,
    ( k5_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1543])).

cnf(c_440,plain,
    ( k2_zfmisc_1(X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1884])).

cnf(c_132,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1516])).

cnf(c_17171,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_132,c_145])).

cnf(c_148,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1527])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1027])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f819])).

cnf(c_10178,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(theory_normalisation,[status(thm)],[c_148,c_211,c_7])).

cnf(c_217,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1573])).

cnf(c_10152,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(theory_normalisation,[status(thm)],[c_217,c_211,c_7])).

cnf(c_17185,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_10178,c_10152])).

cnf(c_136,plain,
    ( X0 = X1
    | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f951])).

cnf(c_46455,plain,
    ( k2_zfmisc_1(sK52,X0) = k2_zfmisc_1(sK50,sK51)
    | k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,X0)) != k2_zfmisc_1(sK52,k4_xboole_0(X0,sK53)) ),
    inference(superposition,[status(thm)],[c_45623,c_136])).

cnf(c_46465,plain,
    ( k2_zfmisc_1(sK52,X0) = k2_zfmisc_1(sK50,sK51)
    | k2_zfmisc_1(sK52,k4_xboole_0(X0,sK53)) != k2_zfmisc_1(sK52,k4_xboole_0(sK53,X0)) ),
    inference(light_normalisation,[status(thm)],[c_46455,c_45619])).

cnf(c_73213,plain,
    ( k2_zfmisc_1(sK52,sK53) = k2_zfmisc_1(sK50,sK51) ),
    inference(equality_resolution,[status(thm)],[c_46465])).

cnf(c_46505,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK52,sK50),sK53) = k2_zfmisc_1(sK50,k4_xboole_0(sK51,sK53)) ),
    inference(superposition,[status(thm)],[c_46121,c_458])).

cnf(c_92615,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,sK53),k4_xboole_0(k2_zfmisc_1(X0,sK53),k2_zfmisc_1(sK50,sK51))) = k4_xboole_0(k2_zfmisc_1(X0,sK53),k2_zfmisc_1(k4_xboole_0(X0,sK52),sK53)) ),
    inference(superposition,[status(thm)],[c_46125,c_32737])).

cnf(c_92719,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,sK53),k2_zfmisc_1(k4_xboole_0(X0,sK52),sK53)) = k2_zfmisc_1(k5_xboole_0(sK52,k4_xboole_0(sK52,X0)),sK53) ),
    inference(light_normalisation,[status(thm)],[c_92615,c_46125,c_46511])).

cnf(c_93632,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK50,k4_xboole_0(sK51,sK53)),k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK52,sK50),sK52),sK53)) = k2_zfmisc_1(k5_xboole_0(sK52,k4_xboole_0(sK52,k4_xboole_0(sK52,sK50))),sK53) ),
    inference(superposition,[status(thm)],[c_46505,c_92719])).

cnf(c_52659,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK50,k4_xboole_0(sK51,sK53)),k2_zfmisc_1(sK50,sK51)) = k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK52,sK50),sK52),sK53) ),
    inference(superposition,[status(thm)],[c_46505,c_46125])).

cnf(c_52664,plain,
    ( k2_zfmisc_1(sK50,k4_xboole_0(k4_xboole_0(sK51,sK53),sK51)) = k2_zfmisc_1(k4_xboole_0(k4_xboole_0(sK52,sK50),sK52),sK53) ),
    inference(demodulation,[status(thm)],[c_52659,c_458])).

cnf(c_93676,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK50,k4_xboole_0(sK51,sK53)),k2_zfmisc_1(sK50,k4_xboole_0(k4_xboole_0(sK51,sK53),sK51))) = k2_zfmisc_1(k5_xboole_0(sK52,k4_xboole_0(sK52,k4_xboole_0(sK52,sK50))),sK53) ),
    inference(light_normalisation,[status(thm)],[c_93632,c_52664])).

cnf(c_212,plain,
    ( k5_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1570])).

cnf(c_34245,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(o_0_0_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_212,c_211])).

cnf(c_26260,plain,
    ( k5_xboole_0(o_0_0_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_168,c_7])).

cnf(c_34259,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_34245,c_26260])).

cnf(c_153,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1532])).

cnf(c_10173,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = o_0_0_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_153,c_211,c_7])).

cnf(c_32690,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10173,c_10152,c_10173])).

cnf(c_456,plain,
    ( k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(cnf_transformation,[],[f1722])).

cnf(c_61131,plain,
    ( k2_zfmisc_1(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(light_normalisation,[status(thm)],[c_456,c_456,c_32737])).

cnf(c_61132,plain,
    ( k2_zfmisc_1(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X2,k4_xboole_0(X2,X3))) = k5_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(demodulation,[status(thm)],[c_61131,c_32737])).

cnf(c_61147,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X3))) = k2_zfmisc_1(k5_xboole_0(X0,o_0_0_xboole_0),k5_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(superposition,[status(thm)],[c_32690,c_61132])).

cnf(c_460,plain,
    ( k5_xboole_0(k5_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X1),X2),k2_zfmisc_1(X0,k4_xboole_0(X2,X3))),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X1),X2),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X1),X2),k2_zfmisc_1(X0,k4_xboole_0(X2,X3))))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f1724])).

cnf(c_10039,plain,
    ( k5_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X1),X2),k5_xboole_0(k2_zfmisc_1(X0,k4_xboole_0(X2,X3)),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X1),X2),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X1),X2),k2_zfmisc_1(X0,k4_xboole_0(X2,X3)))))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(theory_normalisation,[status(thm)],[c_460,c_211,c_7])).

cnf(c_32700,plain,
    ( k5_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,X0),k5_xboole_0(k2_zfmisc_1(X1,k4_xboole_0(X0,X2)),k4_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,X0),k4_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,X0),k2_zfmisc_1(X1,k4_xboole_0(X0,X2)))))) = k4_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(k5_xboole_0(X1,k4_xboole_0(X3,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_32690,c_10039])).

cnf(c_441,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1885])).

cnf(c_32710,plain,
    ( k5_xboole_0(o_0_0_xboole_0,k5_xboole_0(k2_zfmisc_1(X0,k4_xboole_0(X1,X2)),k4_xboole_0(o_0_0_xboole_0,k4_xboole_0(o_0_0_xboole_0,k2_zfmisc_1(X0,k4_xboole_0(X1,X2)))))) = k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k5_xboole_0(X0,k4_xboole_0(X3,X0)),X2)) ),
    inference(light_normalisation,[status(thm)],[c_32700,c_441])).

cnf(c_27378,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_32711,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X3)) = k4_xboole_0(k2_zfmisc_1(X0,k4_xboole_0(X1,X3)),o_0_0_xboole_0) ),
    inference(demodulation,[status(thm)],[c_32710,c_26260,c_27378])).

cnf(c_32712,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X3)) = k2_zfmisc_1(X0,k4_xboole_0(X1,X3)) ),
    inference(demodulation,[status(thm)],[c_32711,c_145])).

cnf(c_61208,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X2))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_61147,c_168,c_32712])).

cnf(c_52655,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK50,k4_xboole_0(sK51,sK53)),k5_xboole_0(k2_zfmisc_1(sK52,k4_xboole_0(sK53,X0)),k4_xboole_0(k2_zfmisc_1(sK50,k4_xboole_0(sK51,sK53)),k4_xboole_0(k2_zfmisc_1(sK50,k4_xboole_0(sK51,sK53)),k2_zfmisc_1(sK52,k4_xboole_0(sK53,X0)))))) = k4_xboole_0(k2_zfmisc_1(sK52,sK53),k2_zfmisc_1(sK50,X0)) ),
    inference(superposition,[status(thm)],[c_46505,c_10039])).

cnf(c_52666,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK50,k4_xboole_0(sK51,sK53)),k5_xboole_0(k2_zfmisc_1(sK52,k4_xboole_0(sK53,X0)),k4_xboole_0(k2_zfmisc_1(sK50,k4_xboole_0(sK51,sK53)),k4_xboole_0(k2_zfmisc_1(sK50,k4_xboole_0(sK51,sK53)),k2_zfmisc_1(sK52,k4_xboole_0(sK53,X0)))))) = k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK50,X0)) ),
    inference(light_normalisation,[status(thm)],[c_52655,c_479])).

cnf(c_52667,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK50,k4_xboole_0(sK51,sK53)),k4_xboole_0(k2_zfmisc_1(sK52,k4_xboole_0(sK53,X0)),k2_zfmisc_1(sK50,k4_xboole_0(sK51,sK53)))) = k2_zfmisc_1(sK50,k4_xboole_0(sK51,X0)) ),
    inference(demodulation,[status(thm)],[c_52666,c_458,c_10152,c_27378])).

cnf(c_78183,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK50,k4_xboole_0(sK51,sK53)),k4_xboole_0(k2_zfmisc_1(sK52,o_0_0_xboole_0),k2_zfmisc_1(sK50,k4_xboole_0(sK51,sK53)))) = k2_zfmisc_1(sK50,k4_xboole_0(sK51,k5_xboole_0(sK53,k4_xboole_0(X0,sK53)))) ),
    inference(superposition,[status(thm)],[c_32690,c_52667])).

cnf(c_156,plain,
    ( k4_xboole_0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1535])).

cnf(c_78253,plain,
    ( k2_zfmisc_1(sK50,k4_xboole_0(k4_xboole_0(sK51,sK53),X0)) = k2_zfmisc_1(sK50,k4_xboole_0(sK51,sK53)) ),
    inference(demodulation,[status(thm)],[c_78183,c_156,c_168,c_440,c_17185])).

cnf(c_93677,plain,
    ( k2_zfmisc_1(sK50,k4_xboole_0(sK51,sK53)) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_93676,c_212,c_32737,c_34259,c_46505,c_61208,c_78253])).

cnf(c_442,plain,
    ( k2_zfmisc_1(X0,X1) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f1712])).

cnf(c_94236,plain,
    ( k4_xboole_0(sK51,sK53) = o_0_0_xboole_0
    | sK50 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_93677,c_442])).

cnf(c_478,negated_conjecture,
    ( o_0_0_xboole_0 != sK50 ),
    inference(cnf_transformation,[],[f1731])).

cnf(c_567,plain,
    ( r2_hidden(X0,X1)
    | X0 = X2
    | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X0)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X0)))),X1) != k1_tarski(X2) ),
    inference(cnf_transformation,[],[f1793])).

cnf(c_675,plain,
    ( r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0)
    | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),o_0_0_xboole_0) != k1_tarski(o_0_0_xboole_0)
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_567])).

cnf(c_565,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X0)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0)))),X1) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1900])).

cnf(c_679,plain,
    ( r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0)
    | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),o_0_0_xboole_0) = k1_tarski(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_565])).

cnf(c_540,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2))) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1776])).

cnf(c_747,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),o_0_0_xboole_0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),o_0_0_xboole_0))) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_540])).

cnf(c_538,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))),X1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))),X1))) = X1 ),
    inference(cnf_transformation,[],[f1774])).

cnf(c_750,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0)
    | k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),o_0_0_xboole_0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),o_0_0_xboole_0))) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_10220,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_18701,plain,
    ( sK50 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK50 ),
    inference(instantiation,[status(thm)],[c_10220])).

cnf(c_18712,plain,
    ( sK50 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK50
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18701])).

cnf(c_94862,plain,
    ( k4_xboole_0(sK51,sK53) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_94236,c_478,c_675,c_679,c_747,c_750,c_18712])).

cnf(c_46460,plain,
    ( k2_zfmisc_1(sK52,k4_xboole_0(sK51,sK53)) = k2_zfmisc_1(k4_xboole_0(sK52,sK50),sK51) ),
    inference(superposition,[status(thm)],[c_45623,c_459])).

cnf(c_94866,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK52,sK50),sK51) = k2_zfmisc_1(sK52,o_0_0_xboole_0) ),
    inference(demodulation,[status(thm)],[c_94862,c_46460])).

cnf(c_94867,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK52,sK50),sK51) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_94866,c_440])).

cnf(c_94948,plain,
    ( k4_xboole_0(sK52,sK50) = o_0_0_xboole_0
    | sK51 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_94867,c_442])).

cnf(c_477,negated_conjecture,
    ( o_0_0_xboole_0 != sK51 ),
    inference(cnf_transformation,[],[f1730])).

cnf(c_18394,plain,
    ( sK51 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK51 ),
    inference(instantiation,[status(thm)],[c_10220])).

cnf(c_18405,plain,
    ( sK51 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK51
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18394])).

cnf(c_99308,plain,
    ( k4_xboole_0(sK52,sK50) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_94948,c_477,c_675,c_679,c_747,c_750,c_18405])).

cnf(c_90675,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_27378,c_32737])).

cnf(c_99328,plain,
    ( k5_xboole_0(sK50,k5_xboole_0(sK52,o_0_0_xboole_0)) = k4_xboole_0(sK50,sK52) ),
    inference(superposition,[status(thm)],[c_99308,c_90675])).

cnf(c_99367,plain,
    ( k4_xboole_0(sK50,sK52) = k5_xboole_0(sK50,sK52) ),
    inference(demodulation,[status(thm)],[c_99328,c_168])).

cnf(c_99483,plain,
    ( k2_zfmisc_1(k5_xboole_0(sK50,k5_xboole_0(sK50,sK52)),k5_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(sK50,X0),k4_xboole_0(k2_zfmisc_1(sK50,X0),k2_zfmisc_1(sK52,X1))) ),
    inference(superposition,[status(thm)],[c_99367,c_61132])).

cnf(c_99517,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK50,X0),k4_xboole_0(k2_zfmisc_1(sK50,X0),k2_zfmisc_1(sK52,X1))) = k2_zfmisc_1(sK52,k5_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_99483,c_34259])).

cnf(c_100130,plain,
    ( k2_zfmisc_1(sK52,k5_xboole_0(sK51,k4_xboole_0(k4_xboole_0(sK51,sK53),sK53))) = k2_zfmisc_1(sK50,sK51) ),
    inference(demodulation,[status(thm)],[c_100076,c_145,c_168,c_440,c_17171,c_17185,c_73213,c_99517])).

cnf(c_100131,plain,
    ( k2_zfmisc_1(sK52,k5_xboole_0(sK51,k4_xboole_0(o_0_0_xboole_0,sK53))) = k2_zfmisc_1(sK50,sK51) ),
    inference(light_normalisation,[status(thm)],[c_100130,c_94862])).

cnf(c_100132,plain,
    ( k2_zfmisc_1(sK52,sK51) = k2_zfmisc_1(sK50,sK51) ),
    inference(demodulation,[status(thm)],[c_100131,c_156,c_168])).

cnf(c_94883,plain,
    ( k5_xboole_0(sK53,k5_xboole_0(sK51,o_0_0_xboole_0)) = k4_xboole_0(sK53,sK51) ),
    inference(superposition,[status(thm)],[c_94862,c_90675])).

cnf(c_94921,plain,
    ( k4_xboole_0(sK53,sK51) = k5_xboole_0(sK53,sK51) ),
    inference(demodulation,[status(thm)],[c_94883,c_168])).

cnf(c_92612,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK50,sK51),k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,X0))) = k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,k4_xboole_0(sK53,X0))) ),
    inference(superposition,[status(thm)],[c_45619,c_32737])).

cnf(c_90699,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK52,X0),k5_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,k4_xboole_0(sK53,X0)))) = k4_xboole_0(k2_zfmisc_1(sK52,X0),k2_zfmisc_1(sK50,sK51)) ),
    inference(superposition,[status(thm)],[c_45619,c_90675])).

cnf(c_90759,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK52,X0),k5_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,k4_xboole_0(sK53,X0)))) = k2_zfmisc_1(sK52,k4_xboole_0(X0,sK53)) ),
    inference(light_normalisation,[status(thm)],[c_90699,c_45623])).

cnf(c_91274,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK52,X0),k2_zfmisc_1(sK52,k4_xboole_0(X0,sK53))) = k5_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,k4_xboole_0(sK53,X0))) ),
    inference(superposition,[status(thm)],[c_90759,c_34259])).

cnf(c_46450,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK52,X0),k4_xboole_0(k2_zfmisc_1(sK52,X0),k2_zfmisc_1(sK52,k4_xboole_0(X0,sK53)))) = k4_xboole_0(k2_zfmisc_1(sK52,X0),k2_zfmisc_1(sK50,sK51)) ),
    inference(superposition,[status(thm)],[c_45623,c_1])).

cnf(c_46469,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK52,X0),k2_zfmisc_1(sK52,k5_xboole_0(sK53,k4_xboole_0(sK53,X0)))) = k2_zfmisc_1(sK52,k4_xboole_0(X0,sK53)) ),
    inference(demodulation,[status(thm)],[c_46450,c_45623,c_46464])).

cnf(c_68884,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK52,X0),k2_zfmisc_1(sK52,k4_xboole_0(X0,sK53))) = k2_zfmisc_1(sK52,k5_xboole_0(sK53,k4_xboole_0(sK53,X0))) ),
    inference(superposition,[status(thm)],[c_46469,c_34259])).

cnf(c_91292,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,k4_xboole_0(sK53,X0))) = k2_zfmisc_1(sK52,k5_xboole_0(sK53,k4_xboole_0(sK53,X0))) ),
    inference(light_normalisation,[status(thm)],[c_91274,c_68884])).

cnf(c_92722,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,k4_xboole_0(sK53,X0))) = k2_zfmisc_1(sK52,k5_xboole_0(sK53,k4_xboole_0(sK53,X0))) ),
    inference(light_normalisation,[status(thm)],[c_92612,c_45619,c_91292])).

cnf(c_95547,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,k5_xboole_0(sK53,sK51))) = k2_zfmisc_1(sK52,k5_xboole_0(sK53,k4_xboole_0(sK53,sK51))) ),
    inference(superposition,[status(thm)],[c_94921,c_92722])).

cnf(c_95569,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,k5_xboole_0(sK53,sK51))) = k2_zfmisc_1(sK52,k5_xboole_0(sK53,k5_xboole_0(sK53,sK51))) ),
    inference(demodulation,[status(thm)],[c_95547,c_94921])).

cnf(c_95570,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,k5_xboole_0(sK53,sK51))) = k2_zfmisc_1(sK52,sK51) ),
    inference(demodulation,[status(thm)],[c_95569,c_34259,c_45619])).

cnf(c_96563,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK50,sK51),k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,k5_xboole_0(sK53,sK51)))) = k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,sK51)) ),
    inference(superposition,[status(thm)],[c_95570,c_32737])).

cnf(c_96594,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,sK51)) = k5_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,sK51)) ),
    inference(demodulation,[status(thm)],[c_96563,c_95570])).

cnf(c_96595,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,sK51)) = k2_zfmisc_1(sK52,k5_xboole_0(sK53,sK51)) ),
    inference(demodulation,[status(thm)],[c_96594,c_45619,c_94921])).

cnf(c_102730,plain,
    ( k5_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK50,sK51)) = k2_zfmisc_1(sK52,k5_xboole_0(sK53,sK51)) ),
    inference(demodulation,[status(thm)],[c_100132,c_96595])).

cnf(c_102732,plain,
    ( k2_zfmisc_1(sK52,k5_xboole_0(sK53,sK51)) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_102730,c_212])).

cnf(c_102846,plain,
    ( k5_xboole_0(sK53,sK51) = o_0_0_xboole_0
    | sK52 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_102732,c_442])).

cnf(c_95543,plain,
    ( k4_xboole_0(sK53,k5_xboole_0(sK53,sK51)) = k4_xboole_0(sK51,k4_xboole_0(sK51,sK53)) ),
    inference(superposition,[status(thm)],[c_94921,c_6])).

cnf(c_95576,plain,
    ( k4_xboole_0(sK53,k5_xboole_0(sK53,sK51)) = k4_xboole_0(sK51,o_0_0_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_95543,c_94862])).

cnf(c_95577,plain,
    ( k4_xboole_0(sK53,k5_xboole_0(sK53,sK51)) = sK51 ),
    inference(demodulation,[status(thm)],[c_95576,c_145])).

cnf(c_104030,plain,
    ( k4_xboole_0(sK53,o_0_0_xboole_0) = sK51
    | sK52 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_102846,c_95577])).

cnf(c_104031,plain,
    ( sK52 = o_0_0_xboole_0
    | sK53 = sK51 ),
    inference(demodulation,[status(thm)],[c_104030,c_145])).

cnf(c_104395,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,sK53) = k2_zfmisc_1(sK50,sK51)
    | sK53 = sK51 ),
    inference(superposition,[status(thm)],[c_104031,c_479])).

cnf(c_104396,plain,
    ( k2_zfmisc_1(sK50,sK51) = o_0_0_xboole_0
    | sK53 = sK51 ),
    inference(demodulation,[status(thm)],[c_104395,c_441])).

cnf(c_201,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f1016])).

cnf(c_1249,plain,
    ( ~ r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)
    | k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_200,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f1017])).

cnf(c_1251,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_200])).

cnf(c_1253,plain,
    ( k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) != o_0_0_xboole_0
    | r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1251])).

cnf(c_177,plain,
    ( r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1830])).

cnf(c_462,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f1288])).

cnf(c_16883,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_79002,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(X0,X1)) = iProver_top
    | r1_xboole_0(sK52,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_479,c_16883])).

cnf(c_81467,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK50,sK51)) = iProver_top
    | r1_xboole_0(sK52,sK52) != iProver_top ),
    inference(superposition,[status(thm)],[c_479,c_79002])).

cnf(c_176,plain,
    ( ~ r1_xboole_0(X0,X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f1548])).

cnf(c_17053,plain,
    ( o_0_0_xboole_0 = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_176])).

cnf(c_81947,plain,
    ( k2_zfmisc_1(sK50,sK51) = o_0_0_xboole_0
    | r1_xboole_0(sK52,sK52) != iProver_top ),
    inference(superposition,[status(thm)],[c_81467,c_17053])).

cnf(c_18633,plain,
    ( k2_zfmisc_1(sK50,X0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = sK50 ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_34652,plain,
    ( k2_zfmisc_1(sK50,sK51) != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK50
    | o_0_0_xboole_0 = sK51 ),
    inference(instantiation,[status(thm)],[c_18633])).

cnf(c_82956,plain,
    ( r1_xboole_0(sK52,sK52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_81947,c_478,c_477,c_34652])).

cnf(c_104336,plain,
    ( sK53 = sK51
    | r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_104031,c_82956])).

cnf(c_111315,plain,
    ( sK53 = sK51 ),
    inference(global_propositional_subsumption,[status(thm)],[c_104396,c_1249,c_1253,c_177,c_104336])).

cnf(c_46200,plain,
    ( k2_zfmisc_1(sK52,k4_xboole_0(sK53,sK51)) = k2_zfmisc_1(k4_xboole_0(sK50,sK52),sK51) ),
    inference(superposition,[status(thm)],[c_45619,c_459])).

cnf(c_450,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f1277])).

cnf(c_16886,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_89363,plain,
    ( r1_tarski(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(X0,X1)) = iProver_top
    | r1_tarski(sK52,X0) != iProver_top
    | r1_tarski(sK53,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_479,c_16886])).

cnf(c_90958,plain,
    ( r1_tarski(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,k4_xboole_0(sK53,sK51))) = iProver_top
    | r1_tarski(sK52,k4_xboole_0(sK50,sK52)) != iProver_top
    | r1_tarski(sK53,sK51) != iProver_top ),
    inference(superposition,[status(thm)],[c_46200,c_89363])).

cnf(c_476,negated_conjecture,
    ( sK50 != sK52
    | sK51 != sK53 ),
    inference(cnf_transformation,[],[f1306])).

cnf(c_67,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f883])).

cnf(c_18031,plain,
    ( ~ r1_tarski(sK52,sK50)
    | ~ r1_tarski(sK50,sK52)
    | sK50 = sK52 ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_18044,plain,
    ( sK50 = sK52
    | r1_tarski(sK52,sK50) != iProver_top
    | r1_tarski(sK50,sK52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18031])).

cnf(c_142,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1521])).

cnf(c_24864,plain,
    ( r1_tarski(sK52,sK50)
    | k4_xboole_0(sK52,sK50) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_142])).

cnf(c_24882,plain,
    ( k4_xboole_0(sK52,sK50) != o_0_0_xboole_0
    | r1_tarski(sK52,sK50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24864])).

cnf(c_443,plain,
    ( X0 = X1
    | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X1,X0)
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f1713])).

cnf(c_18451,plain,
    ( X0 = sK51
    | k2_zfmisc_1(X0,sK51) != k2_zfmisc_1(sK51,X0)
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = sK51 ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_38982,plain,
    ( k2_zfmisc_1(sK51,sK51) != k2_zfmisc_1(sK51,sK51)
    | sK51 = sK51
    | o_0_0_xboole_0 = sK51 ),
    inference(instantiation,[status(thm)],[c_18451])).

cnf(c_10219,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_42152,plain,
    ( k2_zfmisc_1(sK51,sK51) = k2_zfmisc_1(sK51,sK51) ),
    inference(instantiation,[status(thm)],[c_10219])).

cnf(c_18892,plain,
    ( sK53 != X0
    | sK51 != X0
    | sK51 = sK53 ),
    inference(instantiation,[status(thm)],[c_10220])).

cnf(c_73673,plain,
    ( sK53 != sK51
    | sK51 = sK53
    | sK51 != sK51 ),
    inference(instantiation,[status(thm)],[c_18892])).

cnf(c_448,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f1276])).

cnf(c_16888,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_94164,plain,
    ( r1_tarski(k2_zfmisc_1(sK50,sK51),k2_zfmisc_1(sK52,X0)) = iProver_top
    | r1_tarski(sK53,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_479,c_16888])).

cnf(c_447,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f1716])).

cnf(c_16889,plain,
    ( o_0_0_xboole_0 = X0
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_447])).

cnf(c_97781,plain,
    ( sK51 = o_0_0_xboole_0
    | r1_tarski(sK50,sK52) = iProver_top
    | r1_tarski(sK53,sK51) != iProver_top ),
    inference(superposition,[status(thm)],[c_94164,c_16889])).

cnf(c_111253,plain,
    ( r1_tarski(sK53,sK51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_90958,c_477,c_476,c_675,c_679,c_747,c_750,c_1249,c_1253,c_177,c_18044,c_18405,c_24882,c_38982,c_42152,c_73673,c_94948,c_97781,c_104336])).

cnf(c_111317,plain,
    ( r1_tarski(sK51,sK51) != iProver_top ),
    inference(demodulation,[status(thm)],[c_111315,c_111253])).

cnf(c_68,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f1827])).

cnf(c_58530,plain,
    ( r1_tarski(sK51,sK51) ),
    inference(instantiation,[status(thm)],[c_68])).

cnf(c_58531,plain,
    ( r1_tarski(sK51,sK51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58530])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_111317,c_58531])).

%------------------------------------------------------------------------------
