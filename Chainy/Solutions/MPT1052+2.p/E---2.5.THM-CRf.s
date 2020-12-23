%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1052+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:01 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 201 expanded)
%              Number of clauses        :   25 (  90 expanded)
%              Number of leaves         :    6 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  130 ( 626 expanded)
%              Number of equality atoms :   50 ( 203 expanded)
%              Maximal formula depth    :   25 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k1_funct_2(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( v1_relat_1(X5)
              & v1_funct_1(X5)
              & X4 = X5
              & k1_relat_1(X5) = X1
              & r1_tarski(k2_relat_1(X5),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(t160_funct_2,axiom,(
    ! [X1,X2] : k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)) = k1_funct_2(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_funct_2)).

fof(t169_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( k1_relat_1(X3) = X1
          & r1_tarski(k2_relat_1(X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

fof(t87_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k3_partfun1(X3,X1,X2) = X3 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_partfun1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',t4_subset_1)).

fof(t45_ordinal1,axiom,(
    ! [X1] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X1)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT009+2.ax',t45_ordinal1)).

fof(c_0_6,plain,(
    ! [X1312,X1313,X1314,X1315,X1317,X1318,X1319,X1320,X1321,X1323] :
      ( ( v1_relat_1(esk154_4(X1312,X1313,X1314,X1315))
        | ~ r2_hidden(X1315,X1314)
        | X1314 != k1_funct_2(X1312,X1313) )
      & ( v1_funct_1(esk154_4(X1312,X1313,X1314,X1315))
        | ~ r2_hidden(X1315,X1314)
        | X1314 != k1_funct_2(X1312,X1313) )
      & ( X1315 = esk154_4(X1312,X1313,X1314,X1315)
        | ~ r2_hidden(X1315,X1314)
        | X1314 != k1_funct_2(X1312,X1313) )
      & ( k1_relat_1(esk154_4(X1312,X1313,X1314,X1315)) = X1312
        | ~ r2_hidden(X1315,X1314)
        | X1314 != k1_funct_2(X1312,X1313) )
      & ( r1_tarski(k2_relat_1(esk154_4(X1312,X1313,X1314,X1315)),X1313)
        | ~ r2_hidden(X1315,X1314)
        | X1314 != k1_funct_2(X1312,X1313) )
      & ( ~ v1_relat_1(X1318)
        | ~ v1_funct_1(X1318)
        | X1317 != X1318
        | k1_relat_1(X1318) != X1312
        | ~ r1_tarski(k2_relat_1(X1318),X1313)
        | r2_hidden(X1317,X1314)
        | X1314 != k1_funct_2(X1312,X1313) )
      & ( ~ r2_hidden(esk155_3(X1319,X1320,X1321),X1321)
        | ~ v1_relat_1(X1323)
        | ~ v1_funct_1(X1323)
        | esk155_3(X1319,X1320,X1321) != X1323
        | k1_relat_1(X1323) != X1319
        | ~ r1_tarski(k2_relat_1(X1323),X1320)
        | X1321 = k1_funct_2(X1319,X1320) )
      & ( v1_relat_1(esk156_3(X1319,X1320,X1321))
        | r2_hidden(esk155_3(X1319,X1320,X1321),X1321)
        | X1321 = k1_funct_2(X1319,X1320) )
      & ( v1_funct_1(esk156_3(X1319,X1320,X1321))
        | r2_hidden(esk155_3(X1319,X1320,X1321),X1321)
        | X1321 = k1_funct_2(X1319,X1320) )
      & ( esk155_3(X1319,X1320,X1321) = esk156_3(X1319,X1320,X1321)
        | r2_hidden(esk155_3(X1319,X1320,X1321),X1321)
        | X1321 = k1_funct_2(X1319,X1320) )
      & ( k1_relat_1(esk156_3(X1319,X1320,X1321)) = X1319
        | r2_hidden(esk155_3(X1319,X1320,X1321),X1321)
        | X1321 = k1_funct_2(X1319,X1320) )
      & ( r1_tarski(k2_relat_1(esk156_3(X1319,X1320,X1321)),X1320)
        | r2_hidden(esk155_3(X1319,X1320,X1321),X1321)
        | X1321 = k1_funct_2(X1319,X1320) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

fof(c_0_7,plain,(
    ! [X1343,X1344] : k5_partfun1(X1343,X1344,k3_partfun1(k1_xboole_0,X1343,X1344)) = k1_funct_2(X1343,X1344) ),
    inference(variable_rename,[status(thm)],[t160_funct_2])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X3,k1_funct_2(X1,X2))
         => ( k1_relat_1(X3) = X1
            & r1_tarski(k2_relat_1(X3),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t169_funct_2])).

cnf(c_0_9,plain,
    ( X1 = esk154_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)) = k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X3307,X3308,X3309] :
      ( ~ v1_funct_1(X3309)
      | ~ m1_subset_1(X3309,k1_zfmisc_1(k2_zfmisc_1(X3307,X3308)))
      | k3_partfun1(X3309,X3307,X3308) = X3309 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_partfun1])])).

fof(c_0_12,plain,(
    ! [X1478] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1478)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_13,plain,(
    ! [X3026] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X3026)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[t45_ordinal1])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r2_hidden(esk3_0,k1_funct_2(esk1_0,esk2_0))
    & ( k1_relat_1(esk3_0) != esk1_0
      | ~ r1_tarski(k2_relat_1(esk3_0),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_15,plain,
    ( k1_relat_1(esk154_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( X1 = esk154_4(X2,X3,X4,X1)
    | X4 != k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3))
    | ~ r2_hidden(X1,X4) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_17,plain,
    ( k3_partfun1(X1,X2,X3) = X1
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk3_0,k1_funct_2(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k1_relat_1(esk154_4(X1,X2,X3,X4)) = X1
    | X3 != k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))
    | ~ r2_hidden(X4,X3) ),
    inference(rw,[status(thm)],[c_0_15,c_0_10])).

cnf(c_0_22,plain,
    ( esk154_4(X1,X2,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)),X3) = X3
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k3_partfun1(k1_xboole_0,X1,X2) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk3_0,k5_partfun1(esk1_0,esk2_0,k3_partfun1(k1_xboole_0,esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_10])).

cnf(c_0_25,plain,
    ( r1_tarski(k2_relat_1(esk154_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,plain,
    ( k1_relat_1(esk154_4(X1,X2,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)),X3)) = X1
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( esk154_4(X1,X2,k5_partfun1(X1,X2,k1_xboole_0),X3) = X3
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk3_0,k5_partfun1(esk1_0,esk2_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_relat_1(esk154_4(X1,X2,X3,X4)),X2)
    | X3 != k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))
    | ~ r2_hidden(X4,X3) ),
    inference(rw,[status(thm)],[c_0_25,c_0_10])).

cnf(c_0_30,plain,
    ( k1_relat_1(esk154_4(X1,X2,k5_partfun1(X1,X2,k1_xboole_0),X3)) = X1
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_23]),c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( esk154_4(esk1_0,esk2_0,k5_partfun1(esk1_0,esk2_0,k1_xboole_0),esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( r1_tarski(k2_relat_1(esk154_4(X1,X2,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)),X3)),X2)
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(esk3_0) != esk1_0
    | ~ r1_tarski(k2_relat_1(esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_28]),c_0_31])).

cnf(c_0_35,plain,
    ( r1_tarski(k2_relat_1(esk154_4(X1,X2,k5_partfun1(X1,X2,k1_xboole_0),X3)),X2)
    | ~ r2_hidden(X3,k5_partfun1(X1,X2,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_23]),c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_28]),c_0_31]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
