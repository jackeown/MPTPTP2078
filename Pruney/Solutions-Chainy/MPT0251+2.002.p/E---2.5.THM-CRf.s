%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:22 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 448 expanded)
%              Number of clauses        :   38 ( 181 expanded)
%              Number of leaves         :   15 ( 132 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 500 expanded)
%              Number of equality atoms :   58 ( 437 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t46_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(c_0_15,plain,(
    ! [X54,X55] : k3_tarski(k2_tarski(X54,X55)) = k2_xboole_0(X54,X55) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X45,X46] : k1_enumset1(X45,X45,X46) = k2_tarski(X45,X46) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,plain,(
    ! [X29,X30] :
      ( ( r1_tarski(X29,X30)
        | X29 != X30 )
      & ( r1_tarski(X30,X29)
        | X29 != X30 )
      & ( ~ r1_tarski(X29,X30)
        | ~ r1_tarski(X30,X29)
        | X29 = X30 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_18,plain,(
    ! [X56,X57,X58] :
      ( ( r2_hidden(X56,X58)
        | ~ r1_tarski(k2_tarski(X56,X57),X58) )
      & ( r2_hidden(X57,X58)
        | ~ r1_tarski(k2_tarski(X56,X57),X58) )
      & ( ~ r2_hidden(X56,X58)
        | ~ r2_hidden(X57,X58)
        | r1_tarski(k2_tarski(X56,X57),X58) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_19,plain,(
    ! [X47,X48,X49] : k2_enumset1(X47,X47,X48,X49) = k1_enumset1(X47,X48,X49) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X50,X51,X52,X53] : k3_enumset1(X50,X50,X51,X52,X53) = k2_enumset1(X50,X51,X52,X53) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    inference(assume_negation,[status(cth)],[t46_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X40,X41] : r1_tarski(X40,k2_xboole_0(X40,X41)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_23,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,plain,(
    ! [X33] : k2_xboole_0(X33,k1_xboole_0) = X33 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_26,plain,(
    ! [X42,X43] : k2_tarski(X42,X43) = k2_tarski(X43,X42) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_27,plain,(
    ! [X36,X37] : k2_xboole_0(X36,k4_xboole_0(X37,X36)) = k2_xboole_0(X36,X37) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_28,plain,(
    ! [X31,X32] : k4_xboole_0(X31,X32) = k5_xboole_0(X31,k3_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_29,plain,(
    ! [X34,X35] :
      ( ~ r1_tarski(X34,X35)
      | k3_xboole_0(X34,X35) = X34 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_34,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    & k2_xboole_0(k1_tarski(esk5_0),esk6_0) != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_35,plain,(
    ! [X38,X39] : k4_xboole_0(k2_xboole_0(X38,X39),X39) = k4_xboole_0(X38,X39) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_24]),c_0_32]),c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_32]),c_0_33])).

cnf(c_0_48,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_37]),c_0_32]),c_0_33])).

cnf(c_0_49,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_24]),c_0_24]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_50,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_37]),c_0_37]),c_0_41]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_52,plain,(
    ! [X44] : k2_tarski(X44,X44) = k1_tarski(X44) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X1),esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X2)) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_37]),c_0_41]),c_0_41]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = X1 ),
    inference(spm,[status(thm)],[c_0_42,c_0_47])).

cnf(c_0_56,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X1,X1))) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk5_0),esk6_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_59,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_45])).

cnf(c_0_61,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X1)) = k5_xboole_0(X2,k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_49])).

cnf(c_0_62,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_56]),c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)) != esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_24]),c_0_37]),c_0_32]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_33]),c_0_33])).

cnf(c_0_65,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0) = k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_60])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_48]),c_0_51]),c_0_62]),c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) != esk6_0 ),
    inference(rw,[status(thm)],[c_0_64,c_0_49])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_65]),c_0_66]),c_0_49]),c_0_56]),c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.47  # and selection function SelectNegativeLiterals.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.028 s
% 0.19/0.47  # Presaturation interreduction done
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.47  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.47  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.47  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.19/0.47  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.47  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.47  fof(t46_zfmisc_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 0.19/0.47  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.47  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.19/0.47  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.19/0.47  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.19/0.47  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.47  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.47  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.19/0.47  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.47  fof(c_0_15, plain, ![X54, X55]:k3_tarski(k2_tarski(X54,X55))=k2_xboole_0(X54,X55), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.47  fof(c_0_16, plain, ![X45, X46]:k1_enumset1(X45,X45,X46)=k2_tarski(X45,X46), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.47  fof(c_0_17, plain, ![X29, X30]:(((r1_tarski(X29,X30)|X29!=X30)&(r1_tarski(X30,X29)|X29!=X30))&(~r1_tarski(X29,X30)|~r1_tarski(X30,X29)|X29=X30)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.47  fof(c_0_18, plain, ![X56, X57, X58]:(((r2_hidden(X56,X58)|~r1_tarski(k2_tarski(X56,X57),X58))&(r2_hidden(X57,X58)|~r1_tarski(k2_tarski(X56,X57),X58)))&(~r2_hidden(X56,X58)|~r2_hidden(X57,X58)|r1_tarski(k2_tarski(X56,X57),X58))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.19/0.47  fof(c_0_19, plain, ![X47, X48, X49]:k2_enumset1(X47,X47,X48,X49)=k1_enumset1(X47,X48,X49), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.47  fof(c_0_20, plain, ![X50, X51, X52, X53]:k3_enumset1(X50,X50,X51,X52,X53)=k2_enumset1(X50,X51,X52,X53), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.47  fof(c_0_21, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2)), inference(assume_negation,[status(cth)],[t46_zfmisc_1])).
% 0.19/0.47  fof(c_0_22, plain, ![X40, X41]:r1_tarski(X40,k2_xboole_0(X40,X41)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.47  cnf(c_0_23, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.47  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.47  fof(c_0_25, plain, ![X33]:k2_xboole_0(X33,k1_xboole_0)=X33, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.19/0.47  fof(c_0_26, plain, ![X42, X43]:k2_tarski(X42,X43)=k2_tarski(X43,X42), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.19/0.47  fof(c_0_27, plain, ![X36, X37]:k2_xboole_0(X36,k4_xboole_0(X37,X36))=k2_xboole_0(X36,X37), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.19/0.47  fof(c_0_28, plain, ![X31, X32]:k4_xboole_0(X31,X32)=k5_xboole_0(X31,k3_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.47  fof(c_0_29, plain, ![X34, X35]:(~r1_tarski(X34,X35)|k3_xboole_0(X34,X35)=X34), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.47  cnf(c_0_30, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.47  cnf(c_0_31, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.47  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.47  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.47  fof(c_0_34, negated_conjecture, (r2_hidden(esk5_0,esk6_0)&k2_xboole_0(k1_tarski(esk5_0),esk6_0)!=esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.19/0.47  fof(c_0_35, plain, ![X38, X39]:k4_xboole_0(k2_xboole_0(X38,X39),X39)=k4_xboole_0(X38,X39), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.19/0.47  cnf(c_0_36, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.47  cnf(c_0_37, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.47  cnf(c_0_38, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.47  cnf(c_0_39, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.47  cnf(c_0_40, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.47  cnf(c_0_41, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.47  cnf(c_0_42, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.47  cnf(c_0_43, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_30])).
% 0.19/0.47  cnf(c_0_44, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_24]), c_0_32]), c_0_33])).
% 0.19/0.47  cnf(c_0_45, negated_conjecture, (r2_hidden(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.47  cnf(c_0_46, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.47  cnf(c_0_47, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_32]), c_0_33])).
% 0.19/0.47  cnf(c_0_48, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_37]), c_0_32]), c_0_33])).
% 0.19/0.47  cnf(c_0_49, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_24]), c_0_24]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.19/0.47  cnf(c_0_50, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_37]), c_0_37]), c_0_41]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.19/0.47  cnf(c_0_51, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.47  fof(c_0_52, plain, ![X44]:k2_tarski(X44,X44)=k1_tarski(X44), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.47  cnf(c_0_53, negated_conjecture, (r1_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X1),esk6_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.47  cnf(c_0_54, plain, (k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X2))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_37]), c_0_41]), c_0_41]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.19/0.47  cnf(c_0_55, plain, (k3_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))=X1), inference(spm,[status(thm)],[c_0_42, c_0_47])).
% 0.19/0.47  cnf(c_0_56, plain, (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.47  cnf(c_0_57, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X1,X1)))=k3_tarski(k3_enumset1(X1,X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.47  cnf(c_0_58, negated_conjecture, (k2_xboole_0(k1_tarski(esk5_0),esk6_0)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.47  cnf(c_0_59, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.47  cnf(c_0_60, negated_conjecture, (r1_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_53, c_0_45])).
% 0.19/0.47  cnf(c_0_61, plain, (k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k3_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X1))=k5_xboole_0(X2,k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_54, c_0_49])).
% 0.19/0.47  cnf(c_0_62, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.47  cnf(c_0_63, plain, (k5_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_56]), c_0_56])).
% 0.19/0.47  cnf(c_0_64, negated_conjecture, (k3_tarski(k3_enumset1(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0))!=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_24]), c_0_37]), c_0_32]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_33]), c_0_33])).
% 0.19/0.47  cnf(c_0_65, negated_conjecture, (k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_42, c_0_60])).
% 0.19/0.47  cnf(c_0_66, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_48]), c_0_51]), c_0_62]), c_0_63])).
% 0.19/0.47  cnf(c_0_67, negated_conjecture, (k3_tarski(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))!=esk6_0), inference(rw,[status(thm)],[c_0_64, c_0_49])).
% 0.19/0.47  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_65]), c_0_66]), c_0_49]), c_0_56]), c_0_67]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 69
% 0.19/0.47  # Proof object clause steps            : 38
% 0.19/0.47  # Proof object formula steps           : 31
% 0.19/0.47  # Proof object conjectures             : 11
% 0.19/0.47  # Proof object clause conjectures      : 8
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 16
% 0.19/0.47  # Proof object initial formulas used   : 15
% 0.19/0.47  # Proof object generating inferences   : 12
% 0.19/0.47  # Proof object simplifying inferences  : 50
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 20
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 31
% 0.19/0.47  # Removed in clause preprocessing      : 6
% 0.19/0.47  # Initial clauses in saturation        : 25
% 0.19/0.47  # Processed clauses                    : 871
% 0.19/0.47  # ...of these trivial                  : 66
% 0.19/0.47  # ...subsumed                          : 429
% 0.19/0.47  # ...remaining for further processing  : 375
% 0.19/0.47  # Other redundant clauses eliminated   : 2
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 1
% 0.19/0.47  # Backward-rewritten                   : 16
% 0.19/0.47  # Generated clauses                    : 6217
% 0.19/0.47  # ...of the previous two non-trivial   : 4972
% 0.19/0.47  # Contextual simplify-reflections      : 0
% 0.19/0.47  # Paramodulations                      : 6213
% 0.19/0.47  # Factorizations                       : 2
% 0.19/0.47  # Equation resolutions                 : 2
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 332
% 0.19/0.47  #    Positive orientable unit clauses  : 63
% 0.19/0.47  #    Positive unorientable unit clauses: 1
% 0.19/0.47  #    Negative unit clauses             : 37
% 0.19/0.47  #    Non-unit-clauses                  : 231
% 0.19/0.47  # Current number of unprocessed clauses: 4100
% 0.19/0.47  # ...number of literals in the above   : 9630
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 47
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 6475
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 5882
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 254
% 0.19/0.47  # Unit Clause-clause subsumption calls : 158
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 148
% 0.19/0.47  # BW rewrite match successes           : 36
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 113674
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.116 s
% 0.19/0.47  # System time              : 0.012 s
% 0.19/0.47  # Total time               : 0.128 s
% 0.19/0.47  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
