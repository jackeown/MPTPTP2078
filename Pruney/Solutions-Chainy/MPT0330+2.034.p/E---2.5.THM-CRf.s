%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:30 EST 2020

% Result     : Theorem 11.73s
% Output     : CNFRefutation 11.73s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 234 expanded)
%              Number of clauses        :   40 ( 110 expanded)
%              Number of leaves         :    7 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :   89 ( 357 expanded)
%              Number of equality atoms :   11 ( 126 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t143_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
        & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
     => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(c_0_7,plain,(
    ! [X13,X14] : r1_tarski(X13,k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_8,plain,(
    ! [X18,X19] : k3_tarski(k2_tarski(X18,X19)) = k2_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X23,X24,X25] :
      ( k2_zfmisc_1(k2_xboole_0(X23,X24),X25) = k2_xboole_0(k2_zfmisc_1(X23,X25),k2_zfmisc_1(X24,X25))
      & k2_zfmisc_1(X25,k2_xboole_0(X23,X24)) = k2_xboole_0(k2_zfmisc_1(X25,X23),k2_zfmisc_1(X25,X24)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_tarski(X11,X12)
      | r1_tarski(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | r1_tarski(X7,k2_xboole_0(X9,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_15,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_18,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X3))) = k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_12]),c_0_12])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,X16)
      | ~ r1_tarski(X17,X16)
      | r1_tarski(k2_xboole_0(X15,X17),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_27,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk1_0,k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(k3_tarski(k2_tarski(X1,X2)),X3) = k3_tarski(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_12]),c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk2_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(esk5_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k2_tarski(X3,X4))))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,X1)),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_35,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,X1)),k3_tarski(k2_tarski(esk4_0,X2)))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk2_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X2,esk6_0)))))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(X1,esk1_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,X2)),k3_tarski(k2_tarski(esk4_0,X3))))
    | ~ r1_tarski(X1,k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,X2)),k3_tarski(k2_tarski(esk4_0,X3)))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k2_tarski(X1,esk5_0)),k3_tarski(k2_tarski(X2,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_29])).

cnf(c_0_40,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,k2_zfmisc_1(X2,X3))),k2_zfmisc_1(X2,k3_tarski(k2_tarski(X3,X4))))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k2_tarski(X3,X4)))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk2_0,esk1_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(k3_tarski(k2_tarski(esk2_0,esk1_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),esk4_0))),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_43,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_17])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk1_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,X2)),esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0))))
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(k3_tarski(k2_tarski(esk2_0,esk1_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk1_0,X1)),k3_tarski(k2_tarski(X1,k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,X2)),esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,X3))))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk1_0,k3_tarski(k2_tarski(esk2_0,esk1_0)))),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X2,X4)))))
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X2,X4))))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0))))
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(esk1_0,k3_tarski(k2_tarski(esk2_0,esk1_0))))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_48])).

cnf(c_0_52,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X2,X3))))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_17])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_12]),c_0_12]),c_0_12])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.35  % CPULimit   : 60
% 0.19/0.35  % WCLimit    : 600
% 0.19/0.35  % DateTime   : Tue Dec  1 16:28:21 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  # Version: 2.5pre002
% 0.19/0.35  # No SInE strategy applied
% 0.19/0.35  # Trying AutoSched0 for 299 seconds
% 11.73/11.95  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 11.73/11.95  # and selection function SelectDiffNegLit.
% 11.73/11.95  #
% 11.73/11.95  # Preprocessing time       : 0.027 s
% 11.73/11.95  # Presaturation interreduction done
% 11.73/11.95  
% 11.73/11.95  # Proof found!
% 11.73/11.95  # SZS status Theorem
% 11.73/11.95  # SZS output start CNFRefutation
% 11.73/11.95  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 11.73/11.95  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 11.73/11.95  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 11.73/11.95  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 11.73/11.95  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 11.73/11.95  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 11.73/11.95  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 11.73/11.95  fof(c_0_7, plain, ![X13, X14]:r1_tarski(X13,k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 11.73/11.95  fof(c_0_8, plain, ![X18, X19]:k3_tarski(k2_tarski(X18,X19))=k2_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 11.73/11.95  fof(c_0_9, plain, ![X23, X24, X25]:(k2_zfmisc_1(k2_xboole_0(X23,X24),X25)=k2_xboole_0(k2_zfmisc_1(X23,X25),k2_zfmisc_1(X24,X25))&k2_zfmisc_1(X25,k2_xboole_0(X23,X24))=k2_xboole_0(k2_zfmisc_1(X25,X23),k2_zfmisc_1(X25,X24))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 11.73/11.95  fof(c_0_10, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|~r1_tarski(X11,X12)|r1_tarski(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 11.73/11.95  cnf(c_0_11, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 11.73/11.95  cnf(c_0_12, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 11.73/11.95  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 11.73/11.95  fof(c_0_14, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|r1_tarski(X7,k2_xboole_0(X9,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 11.73/11.95  cnf(c_0_15, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 11.73/11.95  cnf(c_0_16, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 11.73/11.95  cnf(c_0_17, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 11.73/11.95  fof(c_0_18, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 11.73/11.95  cnf(c_0_19, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 11.73/11.95  cnf(c_0_20, plain, (k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X3)))=k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_12]), c_0_12])).
% 11.73/11.95  cnf(c_0_21, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 11.73/11.95  cnf(c_0_22, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 11.73/11.95  cnf(c_0_23, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 11.73/11.95  cnf(c_0_24, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_12])).
% 11.73/11.95  cnf(c_0_25, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 11.73/11.95  fof(c_0_26, plain, ![X15, X16, X17]:(~r1_tarski(X15,X16)|~r1_tarski(X17,X16)|r1_tarski(k2_xboole_0(X15,X17),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 11.73/11.95  cnf(c_0_27, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X3))))), inference(spm,[status(thm)],[c_0_17, c_0_20])).
% 11.73/11.95  cnf(c_0_28, negated_conjecture, (r1_tarski(esk1_0,k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1)))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 11.73/11.95  cnf(c_0_29, plain, (k2_zfmisc_1(k3_tarski(k2_tarski(X1,X2)),X3)=k3_tarski(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_12]), c_0_12])).
% 11.73/11.95  cnf(c_0_30, negated_conjecture, (r1_tarski(esk2_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(esk5_0,esk6_0))))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 11.73/11.95  cnf(c_0_31, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 11.73/11.95  cnf(c_0_32, plain, (r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k2_tarski(X3,X4))))|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_16, c_0_27])).
% 11.73/11.95  cnf(c_0_33, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,X1)),esk4_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 11.73/11.95  cnf(c_0_34, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X1,esk6_0))))), inference(spm,[status(thm)],[c_0_30, c_0_20])).
% 11.73/11.95  cnf(c_0_35, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_12])).
% 11.73/11.95  cnf(c_0_36, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,X1)),k3_tarski(k2_tarski(esk4_0,X2))))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 11.73/11.95  cnf(c_0_37, negated_conjecture, (r1_tarski(esk2_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(X2,esk6_0))))))), inference(spm,[status(thm)],[c_0_24, c_0_34])).
% 11.73/11.95  cnf(c_0_38, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(X1,esk1_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,X2)),k3_tarski(k2_tarski(esk4_0,X3))))|~r1_tarski(X1,k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,X2)),k3_tarski(k2_tarski(esk4_0,X3))))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 11.73/11.95  cnf(c_0_39, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k2_tarski(X1,esk5_0)),k3_tarski(k2_tarski(X2,esk6_0))))), inference(spm,[status(thm)],[c_0_37, c_0_29])).
% 11.73/11.95  cnf(c_0_40, plain, (r1_tarski(k3_tarski(k2_tarski(X1,k2_zfmisc_1(X2,X3))),k2_zfmisc_1(X2,k3_tarski(k2_tarski(X3,X4))))|~r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k2_tarski(X3,X4))))), inference(spm,[status(thm)],[c_0_35, c_0_27])).
% 11.73/11.95  cnf(c_0_41, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk2_0,esk1_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0))))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 11.73/11.95  cnf(c_0_42, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(k3_tarski(k2_tarski(esk2_0,esk1_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),esk4_0))),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0))))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 11.73/11.95  cnf(c_0_43, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))), inference(spm,[status(thm)],[c_0_35, c_0_17])).
% 11.73/11.96  cnf(c_0_44, negated_conjecture, (r1_tarski(esk1_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,X2)),esk4_0))))), inference(spm,[status(thm)],[c_0_24, c_0_33])).
% 11.73/11.96  cnf(c_0_45, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0))))|~r1_tarski(X1,k3_tarski(k2_tarski(k3_tarski(k2_tarski(esk2_0,esk1_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),esk4_0))))), inference(spm,[status(thm)],[c_0_16, c_0_42])).
% 11.73/11.96  cnf(c_0_46, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk1_0,X1)),k3_tarski(k2_tarski(X1,k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,X2)),esk4_0))))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 11.73/11.96  cnf(c_0_47, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,k3_tarski(k2_tarski(X1,X3)))))), inference(spm,[status(thm)],[c_0_24, c_0_17])).
% 11.73/11.96  cnf(c_0_48, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk1_0,k3_tarski(k2_tarski(esk2_0,esk1_0)))),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0))))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 11.73/11.96  cnf(c_0_49, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X2,X4)))))|~r1_tarski(X1,k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X2,X4)))))), inference(spm,[status(thm)],[c_0_35, c_0_47])).
% 11.73/11.96  cnf(c_0_50, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 11.73/11.96  cnf(c_0_51, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0))))|~r1_tarski(X1,k3_tarski(k2_tarski(esk1_0,k3_tarski(k2_tarski(esk2_0,esk1_0)))))), inference(spm,[status(thm)],[c_0_16, c_0_48])).
% 11.73/11.96  cnf(c_0_52, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X2,X3)))))), inference(spm,[status(thm)],[c_0_49, c_0_17])).
% 11.73/11.96  cnf(c_0_53, negated_conjecture, (~r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_12]), c_0_12]), c_0_12])).
% 11.73/11.96  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), ['proof']).
% 11.73/11.96  # SZS output end CNFRefutation
% 11.73/11.96  # Proof object total steps             : 55
% 11.73/11.96  # Proof object clause steps            : 40
% 11.73/11.96  # Proof object formula steps           : 15
% 11.73/11.96  # Proof object conjectures             : 23
% 11.73/11.96  # Proof object clause conjectures      : 20
% 11.73/11.96  # Proof object formula conjectures     : 3
% 11.73/11.96  # Proof object initial clauses used    : 10
% 11.73/11.96  # Proof object initial formulas used   : 7
% 11.73/11.96  # Proof object generating inferences   : 24
% 11.73/11.96  # Proof object simplifying inferences  : 11
% 11.73/11.96  # Training examples: 0 positive, 0 negative
% 11.73/11.96  # Parsed axioms                        : 8
% 11.73/11.96  # Removed by relevancy pruning/SinE    : 0
% 11.73/11.96  # Initial clauses                      : 12
% 11.73/11.96  # Removed in clause preprocessing      : 1
% 11.73/11.96  # Initial clauses in saturation        : 11
% 11.73/11.96  # Processed clauses                    : 21777
% 11.73/11.96  # ...of these trivial                  : 5090
% 11.73/11.96  # ...subsumed                          : 946
% 11.73/11.96  # ...remaining for further processing  : 15741
% 11.73/11.96  # Other redundant clauses eliminated   : 0
% 11.73/11.96  # Clauses deleted for lack of memory   : 0
% 11.73/11.96  # Backward-subsumed                    : 493
% 11.73/11.96  # Backward-rewritten                   : 572
% 11.73/11.96  # Generated clauses                    : 1107678
% 11.73/11.96  # ...of the previous two non-trivial   : 980839
% 11.73/11.96  # Contextual simplify-reflections      : 0
% 11.73/11.96  # Paramodulations                      : 1107678
% 11.73/11.96  # Factorizations                       : 0
% 11.73/11.96  # Equation resolutions                 : 0
% 11.73/11.96  # Propositional unsat checks           : 0
% 11.73/11.96  #    Propositional check models        : 0
% 11.73/11.96  #    Propositional check unsatisfiable : 0
% 11.73/11.96  #    Propositional clauses             : 0
% 11.73/11.96  #    Propositional clauses after purity: 0
% 11.73/11.96  #    Propositional unsat core size     : 0
% 11.73/11.96  #    Propositional preprocessing time  : 0.000
% 11.73/11.96  #    Propositional encoding time       : 0.000
% 11.73/11.96  #    Propositional solver time         : 0.000
% 11.73/11.96  #    Success case prop preproc time    : 0.000
% 11.73/11.96  #    Success case prop encoding time   : 0.000
% 11.73/11.96  #    Success case prop solver time     : 0.000
% 11.73/11.96  # Current number of processed clauses  : 14665
% 11.73/11.96  #    Positive orientable unit clauses  : 7937
% 11.73/11.96  #    Positive unorientable unit clauses: 10
% 11.73/11.96  #    Negative unit clauses             : 1
% 11.73/11.96  #    Non-unit-clauses                  : 6717
% 11.73/11.96  # Current number of unprocessed clauses: 957785
% 11.73/11.96  # ...number of literals in the above   : 978620
% 11.73/11.96  # Current number of archived formulas  : 0
% 11.73/11.96  # Current number of archived clauses   : 1077
% 11.73/11.96  # Clause-clause subsumption calls (NU) : 4809912
% 11.73/11.96  # Rec. Clause-clause subsumption calls : 4605849
% 11.73/11.96  # Non-unit clause-clause subsumptions  : 1438
% 11.73/11.96  # Unit Clause-clause subsumption calls : 30376
% 11.73/11.96  # Rewrite failures with RHS unbound    : 0
% 11.73/11.96  # BW rewrite match attempts            : 3664565
% 11.73/11.96  # BW rewrite match successes           : 749
% 11.73/11.96  # Condensation attempts                : 0
% 11.73/11.96  # Condensation successes               : 0
% 11.73/11.96  # Termbank termtop insertions          : 30270495
% 11.83/11.99  
% 11.83/11.99  # -------------------------------------------------
% 11.83/11.99  # User time                : 11.202 s
% 11.83/11.99  # System time              : 0.442 s
% 11.83/11.99  # Total time               : 11.644 s
% 11.83/11.99  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
