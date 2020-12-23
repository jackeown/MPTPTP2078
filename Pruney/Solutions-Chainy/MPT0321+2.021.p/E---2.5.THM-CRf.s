%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:01 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  107 (2630 expanded)
%              Number of clauses        :   68 (1119 expanded)
%              Number of leaves         :   19 ( 717 expanded)
%              Depth                    :   16
%              Number of atoms          :  179 (4419 expanded)
%              Number of equality atoms :  127 (4056 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t134_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(t125_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k4_xboole_0(X1,X2)) = k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | ( X1 = X3
            & X2 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t134_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X65,X66,X67] :
      ( k2_zfmisc_1(k4_xboole_0(X65,X66),X67) = k4_xboole_0(k2_zfmisc_1(X65,X67),k2_zfmisc_1(X66,X67))
      & k2_zfmisc_1(X67,k4_xboole_0(X65,X66)) = k4_xboole_0(k2_zfmisc_1(X67,X65),k2_zfmisc_1(X67,X66)) ) ),
    inference(variable_rename,[status(thm)],[t125_zfmisc_1])).

fof(c_0_21,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k2_zfmisc_1(esk7_0,esk8_0)
    & esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & ( esk5_0 != esk7_0
      | esk6_0 != esk8_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_22,plain,(
    ! [X54,X55] : k3_tarski(k2_tarski(X54,X55)) = k2_xboole_0(X54,X55) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X49,X50] : k1_enumset1(X49,X49,X50) = k2_tarski(X49,X50) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_24,plain,(
    ! [X61,X62,X63,X64] : k2_zfmisc_1(k3_xboole_0(X61,X62),k3_xboole_0(X63,X64)) = k3_xboole_0(k2_zfmisc_1(X61,X63),k2_zfmisc_1(X62,X64)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_25,plain,(
    ! [X44,X45] : k4_xboole_0(X44,k4_xboole_0(X44,X45)) = k3_xboole_0(X44,X45) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k2_zfmisc_1(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_29,plain,(
    ! [X41,X42,X43] : k4_xboole_0(k4_xboole_0(X41,X42),X43) = k4_xboole_0(X41,k2_xboole_0(X42,X43)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_30,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X51,X52,X53] : k2_enumset1(X51,X51,X52,X53) = k1_enumset1(X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_33,plain,(
    ! [X16] : k2_xboole_0(X16,X16) = X16 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_34,plain,(
    ! [X35] : k3_xboole_0(X35,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_38,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk7_0,X1),k2_zfmisc_1(esk5_0,esk6_0)) = k2_zfmisc_1(esk7_0,k4_xboole_0(X1,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_40,plain,(
    ! [X33,X34] :
      ( ( k4_xboole_0(X33,X34) != k1_xboole_0
        | r1_tarski(X33,X34) )
      & ( ~ r1_tarski(X33,X34)
        | k4_xboole_0(X33,X34) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_41,plain,(
    ! [X38,X39] : r1_tarski(k4_xboole_0(X38,X39),X38) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_44,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_47,plain,(
    ! [X40] : k4_xboole_0(X40,k1_xboole_0) = X40 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_48,plain,(
    ! [X56,X57] :
      ( ( k2_zfmisc_1(X56,X57) != k1_xboole_0
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0 )
      & ( X56 != k1_xboole_0
        | k2_zfmisc_1(X56,X57) = k1_xboole_0 )
      & ( X57 != k1_xboole_0
        | k2_zfmisc_1(X56,X57) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_49,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_36]),c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(esk7_0,esk5_0),esk6_0) = k2_zfmisc_1(esk7_0,k4_xboole_0(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(X1,esk8_0),k2_zfmisc_1(esk5_0,esk6_0)) = k2_zfmisc_1(k4_xboole_0(X1,esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_27])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_36]),c_0_36])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(X1,esk8_0)) = k2_zfmisc_1(k4_xboole_0(esk7_0,X1),esk8_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_27])).

cnf(c_0_56,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_57,plain,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_43]),c_0_44])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_46,c_0_36])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_60,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_62,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_63,plain,(
    ! [X31] :
      ( X31 = k1_xboole_0
      | r2_hidden(esk4_1(X31),X31) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_64,plain,(
    ! [X47,X48] :
      ( ( ~ r1_xboole_0(X47,X48)
        | k4_xboole_0(X47,X48) = X47 )
      & ( k4_xboole_0(X47,X48) != X47
        | r1_xboole_0(X47,X48) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_65,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(k4_xboole_0(esk7_0,esk5_0),k4_xboole_0(k4_xboole_0(esk7_0,esk5_0),X1)),k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X2))) = k2_zfmisc_1(k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,X1)),k4_xboole_0(k4_xboole_0(esk6_0,esk8_0),k4_xboole_0(k4_xboole_0(esk6_0,esk8_0),X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_49])).

cnf(c_0_66,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)),k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk8_0))) = k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,esk7_0)),esk8_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_51]),c_0_37]),c_0_52])).

cnf(c_0_67,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_68,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(esk7_0,esk5_0),esk8_0) = k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_55])).

cnf(c_0_69,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_71,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_72,negated_conjecture,
    ( k4_xboole_0(esk7_0,esk5_0) = k1_xboole_0
    | k2_zfmisc_1(esk7_0,k4_xboole_0(esk6_0,esk8_0)) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_50]),c_0_62])).

cnf(c_0_73,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_74,plain,(
    ! [X19,X20,X22,X23,X24] :
      ( ( r2_hidden(esk2_2(X19,X20),X19)
        | r1_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_2(X19,X20),X20)
        | r1_xboole_0(X19,X20) )
      & ( ~ r2_hidden(X24,X22)
        | ~ r2_hidden(X24,X23)
        | ~ r1_xboole_0(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_75,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,esk8_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_59]),c_0_68]),c_0_52]),c_0_69]),c_0_70]),c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_78,negated_conjecture,
    ( k4_xboole_0(esk7_0,esk5_0) = k1_xboole_0
    | r2_hidden(esk4_1(k4_xboole_0(esk6_0,esk8_0)),k4_xboole_0(esk6_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_71])])).

cnf(c_0_79,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_80,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_70])])).

cnf(c_0_81,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_82,plain,(
    ! [X58,X59,X60] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X59,X58),k2_zfmisc_1(X60,X58))
        | X58 = k1_xboole_0
        | r1_tarski(X59,X60) )
      & ( ~ r1_tarski(k2_zfmisc_1(X58,X59),k2_zfmisc_1(X58,X60))
        | X58 = k1_xboole_0
        | r1_tarski(X59,X60) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(esk6_0,esk8_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_76]),c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0)) = esk7_0
    | r2_hidden(esk4_1(k4_xboole_0(esk6_0,esk8_0)),k4_xboole_0(esk6_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_78]),c_0_59])).

cnf(c_0_85,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_86,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_87,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,esk7_0)),esk8_0) = k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)),esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_83]),c_0_59])).

cnf(c_0_89,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0)) = esk7_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_83]),c_0_83]),c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k1_xboole_0
    | r2_hidden(esk4_1(esk7_0),esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_73]),c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r1_tarski(esk8_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_27])).

cnf(c_0_92,negated_conjecture,
    ( k2_zfmisc_1(esk7_0,esk6_0) = k2_zfmisc_1(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_70]),c_0_59]),c_0_27]),c_0_52]),c_0_89])).

cnf(c_0_93,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_59])).

cnf(c_0_94,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk7_0,X1)) = k2_zfmisc_1(esk7_0,k4_xboole_0(esk8_0,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk4_1(esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_90]),c_0_62]),c_0_77])).

cnf(c_0_96,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r1_tarski(esk8_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])])).

cnf(c_0_97,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(esk5_0,esk7_0),esk6_0) = k2_zfmisc_1(esk7_0,k4_xboole_0(esk8_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(esk8_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_85])).

cnf(c_0_99,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk7_0) = k1_xboole_0
    | k2_zfmisc_1(esk7_0,k4_xboole_0(esk8_0,esk6_0)) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_97]),c_0_62])).

cnf(c_0_100,negated_conjecture,
    ( k4_xboole_0(esk8_0,esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_98])).

cnf(c_0_101,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk7_0) = k1_xboole_0
    | r2_hidden(esk4_1(k2_zfmisc_1(esk7_0,k4_xboole_0(esk8_0,esk6_0))),k2_zfmisc_1(esk7_0,k4_xboole_0(esk8_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_73])).

cnf(c_0_102,negated_conjecture,
    ( esk5_0 != esk7_0
    | esk6_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_103,negated_conjecture,
    ( esk8_0 = esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_100]),c_0_59]),c_0_83]),c_0_59])).

cnf(c_0_104,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk7_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_100]),c_0_71]),c_0_100]),c_0_71]),c_0_85])).

cnf(c_0_105,negated_conjecture,
    ( esk7_0 != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103])])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_104]),c_0_59]),c_0_105]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.60/0.77  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.60/0.77  # and selection function SelectNegativeLiterals.
% 0.60/0.77  #
% 0.60/0.77  # Preprocessing time       : 0.052 s
% 0.60/0.77  # Presaturation interreduction done
% 0.60/0.77  
% 0.60/0.77  # Proof found!
% 0.60/0.77  # SZS status Theorem
% 0.60/0.77  # SZS output start CNFRefutation
% 0.60/0.77  fof(t134_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.60/0.77  fof(t125_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k4_xboole_0(X1,X2))=k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 0.60/0.77  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.60/0.77  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.60/0.77  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.60/0.77  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.60/0.77  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.60/0.77  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.60/0.77  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.60/0.77  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.60/0.77  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.60/0.77  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.60/0.77  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.60/0.77  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.60/0.77  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.60/0.77  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.60/0.77  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.60/0.77  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.60/0.77  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 0.60/0.77  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4)))), inference(assume_negation,[status(cth)],[t134_zfmisc_1])).
% 0.60/0.77  fof(c_0_20, plain, ![X65, X66, X67]:(k2_zfmisc_1(k4_xboole_0(X65,X66),X67)=k4_xboole_0(k2_zfmisc_1(X65,X67),k2_zfmisc_1(X66,X67))&k2_zfmisc_1(X67,k4_xboole_0(X65,X66))=k4_xboole_0(k2_zfmisc_1(X67,X65),k2_zfmisc_1(X67,X66))), inference(variable_rename,[status(thm)],[t125_zfmisc_1])).
% 0.60/0.77  fof(c_0_21, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k2_zfmisc_1(esk7_0,esk8_0)&((esk5_0!=k1_xboole_0&esk6_0!=k1_xboole_0)&(esk5_0!=esk7_0|esk6_0!=esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.60/0.77  fof(c_0_22, plain, ![X54, X55]:k3_tarski(k2_tarski(X54,X55))=k2_xboole_0(X54,X55), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.60/0.77  fof(c_0_23, plain, ![X49, X50]:k1_enumset1(X49,X49,X50)=k2_tarski(X49,X50), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.60/0.77  fof(c_0_24, plain, ![X61, X62, X63, X64]:k2_zfmisc_1(k3_xboole_0(X61,X62),k3_xboole_0(X63,X64))=k3_xboole_0(k2_zfmisc_1(X61,X63),k2_zfmisc_1(X62,X64)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.60/0.77  fof(c_0_25, plain, ![X44, X45]:k4_xboole_0(X44,k4_xboole_0(X44,X45))=k3_xboole_0(X44,X45), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.60/0.77  cnf(c_0_26, plain, (k2_zfmisc_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.60/0.77  cnf(c_0_27, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k2_zfmisc_1(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.77  fof(c_0_28, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.60/0.77  fof(c_0_29, plain, ![X41, X42, X43]:k4_xboole_0(k4_xboole_0(X41,X42),X43)=k4_xboole_0(X41,k2_xboole_0(X42,X43)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.60/0.77  cnf(c_0_30, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.60/0.77  cnf(c_0_31, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.60/0.77  fof(c_0_32, plain, ![X51, X52, X53]:k2_enumset1(X51,X51,X52,X53)=k1_enumset1(X51,X52,X53), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.60/0.77  fof(c_0_33, plain, ![X16]:k2_xboole_0(X16,X16)=X16, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.60/0.77  fof(c_0_34, plain, ![X35]:k3_xboole_0(X35,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.60/0.77  cnf(c_0_35, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.60/0.77  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.60/0.77  cnf(c_0_37, plain, (k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.60/0.77  cnf(c_0_38, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(esk7_0,X1),k2_zfmisc_1(esk5_0,esk6_0))=k2_zfmisc_1(esk7_0,k4_xboole_0(X1,esk8_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.60/0.77  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.60/0.77  fof(c_0_40, plain, ![X33, X34]:((k4_xboole_0(X33,X34)!=k1_xboole_0|r1_tarski(X33,X34))&(~r1_tarski(X33,X34)|k4_xboole_0(X33,X34)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.60/0.77  fof(c_0_41, plain, ![X38, X39]:r1_tarski(k4_xboole_0(X38,X39),X38), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.60/0.77  cnf(c_0_42, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.60/0.77  cnf(c_0_43, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.60/0.77  cnf(c_0_44, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.60/0.77  cnf(c_0_45, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.60/0.77  cnf(c_0_46, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.60/0.77  fof(c_0_47, plain, ![X40]:k4_xboole_0(X40,k1_xboole_0)=X40, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.60/0.77  fof(c_0_48, plain, ![X56, X57]:((k2_zfmisc_1(X56,X57)!=k1_xboole_0|(X56=k1_xboole_0|X57=k1_xboole_0))&((X56!=k1_xboole_0|k2_zfmisc_1(X56,X57)=k1_xboole_0)&(X57!=k1_xboole_0|k2_zfmisc_1(X56,X57)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.60/0.77  cnf(c_0_49, plain, (k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4)))=k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_36]), c_0_36])).
% 0.60/0.77  cnf(c_0_50, negated_conjecture, (k2_zfmisc_1(k4_xboole_0(esk7_0,esk5_0),esk6_0)=k2_zfmisc_1(esk7_0,k4_xboole_0(esk6_0,esk8_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.60/0.77  cnf(c_0_51, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(X1,esk8_0),k2_zfmisc_1(esk5_0,esk6_0))=k2_zfmisc_1(k4_xboole_0(X1,esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_37, c_0_27])).
% 0.60/0.77  cnf(c_0_52, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_36]), c_0_36])).
% 0.60/0.77  cnf(c_0_53, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.60/0.77  cnf(c_0_54, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.60/0.77  cnf(c_0_55, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(X1,esk8_0))=k2_zfmisc_1(k4_xboole_0(esk7_0,X1),esk8_0)), inference(spm,[status(thm)],[c_0_37, c_0_27])).
% 0.60/0.77  cnf(c_0_56, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k3_tarski(k2_enumset1(X2,X2,X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.60/0.77  cnf(c_0_57, plain, (k3_tarski(k2_enumset1(X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_43]), c_0_44])).
% 0.60/0.77  cnf(c_0_58, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_46, c_0_36])).
% 0.60/0.77  cnf(c_0_59, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.60/0.77  cnf(c_0_60, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.60/0.77  cnf(c_0_61, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.60/0.77  cnf(c_0_62, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.77  fof(c_0_63, plain, ![X31]:(X31=k1_xboole_0|r2_hidden(esk4_1(X31),X31)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.60/0.77  fof(c_0_64, plain, ![X47, X48]:((~r1_xboole_0(X47,X48)|k4_xboole_0(X47,X48)=X47)&(k4_xboole_0(X47,X48)!=X47|r1_xboole_0(X47,X48))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.60/0.77  cnf(c_0_65, negated_conjecture, (k2_zfmisc_1(k4_xboole_0(k4_xboole_0(esk7_0,esk5_0),k4_xboole_0(k4_xboole_0(esk7_0,esk5_0),X1)),k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X2)))=k2_zfmisc_1(k4_xboole_0(esk7_0,k4_xboole_0(esk7_0,X1)),k4_xboole_0(k4_xboole_0(esk6_0,esk8_0),k4_xboole_0(k4_xboole_0(esk6_0,esk8_0),X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_49])).
% 0.60/0.77  cnf(c_0_66, negated_conjecture, (k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)),k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,esk8_0)))=k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,esk7_0)),esk8_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_51]), c_0_37]), c_0_52])).
% 0.60/0.77  cnf(c_0_67, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.60/0.77  cnf(c_0_68, negated_conjecture, (k2_zfmisc_1(k4_xboole_0(esk7_0,esk5_0),esk8_0)=k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,esk8_0))), inference(spm,[status(thm)],[c_0_26, c_0_55])).
% 0.60/0.77  cnf(c_0_69, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.60/0.77  cnf(c_0_70, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.60/0.77  cnf(c_0_71, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_60])).
% 0.60/0.77  cnf(c_0_72, negated_conjecture, (k4_xboole_0(esk7_0,esk5_0)=k1_xboole_0|k2_zfmisc_1(esk7_0,k4_xboole_0(esk6_0,esk8_0))!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_50]), c_0_62])).
% 0.60/0.77  cnf(c_0_73, plain, (X1=k1_xboole_0|r2_hidden(esk4_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.60/0.77  fof(c_0_74, plain, ![X19, X20, X22, X23, X24]:(((r2_hidden(esk2_2(X19,X20),X19)|r1_xboole_0(X19,X20))&(r2_hidden(esk2_2(X19,X20),X20)|r1_xboole_0(X19,X20)))&(~r2_hidden(X24,X22)|~r2_hidden(X24,X23)|~r1_xboole_0(X22,X23))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.60/0.77  cnf(c_0_75, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.60/0.77  cnf(c_0_76, negated_conjecture, (k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,esk8_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_59]), c_0_68]), c_0_52]), c_0_69]), c_0_70]), c_0_71])).
% 0.60/0.77  cnf(c_0_77, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.77  cnf(c_0_78, negated_conjecture, (k4_xboole_0(esk7_0,esk5_0)=k1_xboole_0|r2_hidden(esk4_1(k4_xboole_0(esk6_0,esk8_0)),k4_xboole_0(esk6_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_71])])).
% 0.60/0.77  cnf(c_0_79, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.60/0.77  cnf(c_0_80, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_70])])).
% 0.60/0.77  cnf(c_0_81, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.60/0.77  fof(c_0_82, plain, ![X58, X59, X60]:((~r1_tarski(k2_zfmisc_1(X59,X58),k2_zfmisc_1(X60,X58))|X58=k1_xboole_0|r1_tarski(X59,X60))&(~r1_tarski(k2_zfmisc_1(X58,X59),k2_zfmisc_1(X58,X60))|X58=k1_xboole_0|r1_tarski(X59,X60))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 0.60/0.77  cnf(c_0_83, negated_conjecture, (k4_xboole_0(esk6_0,esk8_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_76]), c_0_77])).
% 0.60/0.77  cnf(c_0_84, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0))=esk7_0|r2_hidden(esk4_1(k4_xboole_0(esk6_0,esk8_0)),k4_xboole_0(esk6_0,esk8_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_78]), c_0_59])).
% 0.60/0.77  cnf(c_0_85, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.60/0.77  cnf(c_0_86, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_81])).
% 0.60/0.77  cnf(c_0_87, plain, (X1=k1_xboole_0|r1_tarski(X2,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.60/0.77  cnf(c_0_88, negated_conjecture, (k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,esk7_0)),esk8_0)=k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,esk5_0)),esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_83]), c_0_59])).
% 0.60/0.77  cnf(c_0_89, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk7_0))=esk7_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_83]), c_0_83]), c_0_85])).
% 0.60/0.77  cnf(c_0_90, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k1_xboole_0|r2_hidden(esk4_1(esk7_0),esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_73]), c_0_86])).
% 0.60/0.77  cnf(c_0_91, negated_conjecture, (esk7_0=k1_xboole_0|r1_tarski(esk8_0,X1)|~r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk7_0,X1))), inference(spm,[status(thm)],[c_0_87, c_0_27])).
% 0.60/0.77  cnf(c_0_92, negated_conjecture, (k2_zfmisc_1(esk7_0,esk6_0)=k2_zfmisc_1(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_70]), c_0_59]), c_0_27]), c_0_52]), c_0_89])).
% 0.60/0.77  cnf(c_0_93, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_54, c_0_59])).
% 0.60/0.77  cnf(c_0_94, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(esk7_0,X1))=k2_zfmisc_1(esk7_0,k4_xboole_0(esk8_0,X1))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.60/0.77  cnf(c_0_95, negated_conjecture, (r2_hidden(esk4_1(esk7_0),esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_90]), c_0_62]), c_0_77])).
% 0.60/0.77  cnf(c_0_96, negated_conjecture, (esk7_0=k1_xboole_0|r1_tarski(esk8_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])])).
% 0.60/0.77  cnf(c_0_97, negated_conjecture, (k2_zfmisc_1(k4_xboole_0(esk5_0,esk7_0),esk6_0)=k2_zfmisc_1(esk7_0,k4_xboole_0(esk8_0,esk6_0))), inference(spm,[status(thm)],[c_0_37, c_0_94])).
% 0.60/0.77  cnf(c_0_98, negated_conjecture, (r1_tarski(esk8_0,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_85])).
% 0.60/0.77  cnf(c_0_99, negated_conjecture, (k4_xboole_0(esk5_0,esk7_0)=k1_xboole_0|k2_zfmisc_1(esk7_0,k4_xboole_0(esk8_0,esk6_0))!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_97]), c_0_62])).
% 0.60/0.77  cnf(c_0_100, negated_conjecture, (k4_xboole_0(esk8_0,esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_98])).
% 0.60/0.77  cnf(c_0_101, negated_conjecture, (k4_xboole_0(esk5_0,esk7_0)=k1_xboole_0|r2_hidden(esk4_1(k2_zfmisc_1(esk7_0,k4_xboole_0(esk8_0,esk6_0))),k2_zfmisc_1(esk7_0,k4_xboole_0(esk8_0,esk6_0)))), inference(spm,[status(thm)],[c_0_99, c_0_73])).
% 0.60/0.77  cnf(c_0_102, negated_conjecture, (esk5_0!=esk7_0|esk6_0!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.60/0.77  cnf(c_0_103, negated_conjecture, (esk8_0=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_100]), c_0_59]), c_0_83]), c_0_59])).
% 0.60/0.77  cnf(c_0_104, negated_conjecture, (k4_xboole_0(esk5_0,esk7_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_100]), c_0_71]), c_0_100]), c_0_71]), c_0_85])).
% 0.60/0.77  cnf(c_0_105, negated_conjecture, (esk7_0!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_103])])).
% 0.60/0.77  cnf(c_0_106, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_104]), c_0_59]), c_0_105]), ['proof']).
% 0.60/0.77  # SZS output end CNFRefutation
% 0.60/0.77  # Proof object total steps             : 107
% 0.60/0.77  # Proof object clause steps            : 68
% 0.60/0.77  # Proof object formula steps           : 39
% 0.60/0.77  # Proof object conjectures             : 36
% 0.60/0.77  # Proof object clause conjectures      : 33
% 0.60/0.77  # Proof object formula conjectures     : 3
% 0.60/0.77  # Proof object initial clauses used    : 25
% 0.60/0.77  # Proof object initial formulas used   : 19
% 0.60/0.77  # Proof object generating inferences   : 29
% 0.60/0.77  # Proof object simplifying inferences  : 59
% 0.60/0.77  # Training examples: 0 positive, 0 negative
% 0.60/0.77  # Parsed axioms                        : 24
% 0.60/0.77  # Removed by relevancy pruning/SinE    : 0
% 0.60/0.77  # Initial clauses                      : 41
% 0.60/0.77  # Removed in clause preprocessing      : 4
% 0.60/0.77  # Initial clauses in saturation        : 37
% 0.60/0.77  # Processed clauses                    : 2537
% 0.60/0.77  # ...of these trivial                  : 378
% 0.60/0.77  # ...subsumed                          : 1536
% 0.60/0.77  # ...remaining for further processing  : 623
% 0.60/0.77  # Other redundant clauses eliminated   : 421
% 0.60/0.77  # Clauses deleted for lack of memory   : 0
% 0.60/0.77  # Backward-subsumed                    : 37
% 0.60/0.77  # Backward-rewritten                   : 278
% 0.60/0.77  # Generated clauses                    : 56925
% 0.60/0.77  # ...of the previous two non-trivial   : 35875
% 0.60/0.77  # Contextual simplify-reflections      : 0
% 0.60/0.77  # Paramodulations                      : 56490
% 0.60/0.77  # Factorizations                       : 8
% 0.60/0.77  # Equation resolutions                 : 426
% 0.60/0.77  # Propositional unsat checks           : 0
% 0.60/0.77  #    Propositional check models        : 0
% 0.60/0.77  #    Propositional check unsatisfiable : 0
% 0.60/0.77  #    Propositional clauses             : 0
% 0.60/0.77  #    Propositional clauses after purity: 0
% 0.60/0.77  #    Propositional unsat core size     : 0
% 0.60/0.77  #    Propositional preprocessing time  : 0.000
% 0.60/0.77  #    Propositional encoding time       : 0.000
% 0.60/0.77  #    Propositional solver time         : 0.000
% 0.60/0.77  #    Success case prop preproc time    : 0.000
% 0.60/0.77  #    Success case prop encoding time   : 0.000
% 0.60/0.77  #    Success case prop solver time     : 0.000
% 0.60/0.77  # Current number of processed clauses  : 265
% 0.60/0.77  #    Positive orientable unit clauses  : 86
% 0.60/0.77  #    Positive unorientable unit clauses: 3
% 0.60/0.77  #    Negative unit clauses             : 4
% 0.60/0.77  #    Non-unit-clauses                  : 172
% 0.60/0.77  # Current number of unprocessed clauses: 32702
% 0.60/0.77  # ...number of literals in the above   : 80019
% 0.60/0.77  # Current number of archived formulas  : 0
% 0.60/0.77  # Current number of archived clauses   : 357
% 0.60/0.77  # Clause-clause subsumption calls (NU) : 20268
% 0.60/0.77  # Rec. Clause-clause subsumption calls : 18400
% 0.60/0.77  # Non-unit clause-clause subsumptions  : 1038
% 0.60/0.77  # Unit Clause-clause subsumption calls : 1495
% 0.60/0.77  # Rewrite failures with RHS unbound    : 0
% 0.60/0.77  # BW rewrite match attempts            : 756
% 0.60/0.77  # BW rewrite match successes           : 89
% 0.60/0.77  # Condensation attempts                : 0
% 0.60/0.77  # Condensation successes               : 0
% 0.60/0.77  # Termbank termtop insertions          : 856979
% 0.60/0.77  
% 0.60/0.77  # -------------------------------------------------
% 0.60/0.77  # User time                : 0.408 s
% 0.60/0.77  # System time              : 0.021 s
% 0.60/0.77  # Total time               : 0.429 s
% 0.60/0.77  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
