%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:29 EST 2020

% Result     : Theorem 18.62s
% Output     : CNFRefutation 18.62s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 185 expanded)
%              Number of clauses        :   35 (  82 expanded)
%              Number of leaves         :   11 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 290 expanded)
%              Number of equality atoms :   18 ( 114 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t143_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
        & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
     => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(c_0_11,plain,(
    ! [X29,X30] : k3_tarski(k2_tarski(X29,X30)) = k2_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X20,X21] : k1_enumset1(X20,X20,X21) = k2_tarski(X20,X21) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | r1_tarski(X9,k2_xboole_0(X11,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_14,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X22,X23,X24] : k2_enumset1(X22,X22,X23,X24) = k1_enumset1(X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X25,X26,X27,X28] : k3_enumset1(X25,X25,X26,X27,X28) = k2_enumset1(X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_18,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X31,X32,X33] :
      ( ( r1_tarski(k2_zfmisc_1(X31,X33),k2_zfmisc_1(X32,X33))
        | ~ r1_tarski(X31,X32) )
      & ( r1_tarski(k2_zfmisc_1(X33,X31),k2_zfmisc_1(X33,X32))
        | ~ r1_tarski(X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X15,X16] : r1_tarski(X15,k2_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_28,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X13,X14)
      | r1_tarski(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_36,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_20]),c_0_21]),c_0_22])).

fof(c_0_38,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,X18)
      | ~ r1_tarski(X19,X18)
      | r1_tarski(k2_xboole_0(X17,X19),X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_39,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_tarski(k3_enumset1(X3,X3,X3,X3,X1)),X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_30])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k3_enumset1(X3,X3,X3,X3,X4))))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_37])).

cnf(c_0_43,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)),X4))
    | ~ r1_tarski(X1,k2_zfmisc_1(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k3_enumset1(X1,X1,X1,X1,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_tarski(k3_enumset1(X1,X1,X1,X1,X3)),X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_37])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k3_enumset1(X3,X3,X3,X3,X4))))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k3_enumset1(X1,X1,X1,X1,esk5_0)),k3_tarski(k3_enumset1(X2,X2,X2,X2,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)),X4))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,esk2_0)),k2_zfmisc_1(k3_tarski(k3_enumset1(X2,X2,X2,X2,esk5_0)),k3_tarski(k3_enumset1(X3,X3,X3,X3,esk6_0))))
    | ~ r1_tarski(X1,k2_zfmisc_1(k3_tarski(k3_enumset1(X2,X2,X2,X2,esk5_0)),k3_tarski(k3_enumset1(X3,X3,X3,X3,esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)),k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,X2)))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_20]),c_0_20]),c_0_20]),c_0_21]),c_0_21]),c_0_21]),c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 18.62/18.84  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S081N
% 18.62/18.84  # and selection function SelectCQArNTNp.
% 18.62/18.84  #
% 18.62/18.84  # Preprocessing time       : 0.027 s
% 18.62/18.84  # Presaturation interreduction done
% 18.62/18.84  
% 18.62/18.84  # Proof found!
% 18.62/18.84  # SZS status Theorem
% 18.62/18.84  # SZS output start CNFRefutation
% 18.62/18.84  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 18.62/18.84  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 18.62/18.84  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 18.62/18.84  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 18.62/18.84  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 18.62/18.85  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.62/18.85  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 18.62/18.85  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 18.62/18.85  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 18.62/18.85  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 18.62/18.85  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 18.62/18.85  fof(c_0_11, plain, ![X29, X30]:k3_tarski(k2_tarski(X29,X30))=k2_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 18.62/18.85  fof(c_0_12, plain, ![X20, X21]:k1_enumset1(X20,X20,X21)=k2_tarski(X20,X21), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 18.62/18.85  fof(c_0_13, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|r1_tarski(X9,k2_xboole_0(X11,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 18.62/18.85  cnf(c_0_14, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 18.62/18.85  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 18.62/18.85  fof(c_0_16, plain, ![X22, X23, X24]:k2_enumset1(X22,X22,X23,X24)=k1_enumset1(X22,X23,X24), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 18.62/18.85  fof(c_0_17, plain, ![X25, X26, X27, X28]:k3_enumset1(X25,X25,X26,X27,X28)=k2_enumset1(X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 18.62/18.85  fof(c_0_18, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 18.62/18.85  cnf(c_0_19, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 18.62/18.85  cnf(c_0_20, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 18.62/18.85  cnf(c_0_21, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 18.62/18.85  cnf(c_0_22, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 18.62/18.85  cnf(c_0_23, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 18.62/18.85  fof(c_0_24, plain, ![X31, X32, X33]:((r1_tarski(k2_zfmisc_1(X31,X33),k2_zfmisc_1(X32,X33))|~r1_tarski(X31,X32))&(r1_tarski(k2_zfmisc_1(X33,X31),k2_zfmisc_1(X33,X32))|~r1_tarski(X31,X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 18.62/18.85  cnf(c_0_25, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])).
% 18.62/18.85  cnf(c_0_26, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_23])).
% 18.62/18.85  fof(c_0_27, plain, ![X15, X16]:r1_tarski(X15,k2_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 18.62/18.85  fof(c_0_28, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_tarski(X13,X14)|r1_tarski(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 18.62/18.85  cnf(c_0_29, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 18.62/18.85  cnf(c_0_30, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 18.62/18.85  fof(c_0_31, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 18.62/18.85  cnf(c_0_32, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 18.62/18.85  cnf(c_0_33, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 18.62/18.85  cnf(c_0_34, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 18.62/18.85  cnf(c_0_35, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2))))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 18.62/18.85  fof(c_0_36, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 18.62/18.85  cnf(c_0_37, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_20]), c_0_21]), c_0_22])).
% 18.62/18.85  fof(c_0_38, plain, ![X17, X18, X19]:(~r1_tarski(X17,X18)|~r1_tarski(X19,X18)|r1_tarski(k2_xboole_0(X17,X19),X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 18.62/18.85  cnf(c_0_39, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_tarski(k3_enumset1(X3,X3,X3,X3,X1)),X2))), inference(spm,[status(thm)],[c_0_33, c_0_30])).
% 18.62/18.85  cnf(c_0_40, plain, (r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k3_enumset1(X3,X3,X3,X3,X4))))|~r1_tarski(X1,k2_zfmisc_1(X2,X4))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 18.62/18.85  cnf(c_0_41, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 18.62/18.85  cnf(c_0_42, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))))), inference(spm,[status(thm)],[c_0_29, c_0_37])).
% 18.62/18.85  cnf(c_0_43, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 18.62/18.85  cnf(c_0_44, plain, (r1_tarski(X1,k2_zfmisc_1(k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)),X4))|~r1_tarski(X1,k2_zfmisc_1(X3,X4))), inference(spm,[status(thm)],[c_0_34, c_0_39])).
% 18.62/18.85  cnf(c_0_45, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k3_enumset1(X1,X1,X1,X1,esk6_0))))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 18.62/18.85  cnf(c_0_46, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_tarski(k3_enumset1(X1,X1,X1,X1,X3)),X2))), inference(spm,[status(thm)],[c_0_33, c_0_37])).
% 18.62/18.85  cnf(c_0_47, plain, (r1_tarski(X1,k2_zfmisc_1(X2,k3_tarski(k3_enumset1(X3,X3,X3,X3,X4))))|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_34, c_0_42])).
% 18.62/18.85  cnf(c_0_48, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 18.62/18.85  cnf(c_0_49, plain, (r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_20]), c_0_21]), c_0_22])).
% 18.62/18.85  cnf(c_0_50, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k3_tarski(k3_enumset1(X1,X1,X1,X1,esk5_0)),k3_tarski(k3_enumset1(X2,X2,X2,X2,esk6_0))))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 18.62/18.85  cnf(c_0_51, plain, (r1_tarski(X1,k2_zfmisc_1(k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)),X4))|~r1_tarski(X1,k2_zfmisc_1(X2,X4))), inference(spm,[status(thm)],[c_0_34, c_0_46])).
% 18.62/18.85  cnf(c_0_52, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,X1))))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 18.62/18.85  cnf(c_0_53, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 18.62/18.85  cnf(c_0_54, negated_conjecture, (r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,esk2_0)),k2_zfmisc_1(k3_tarski(k3_enumset1(X2,X2,X2,X2,esk5_0)),k3_tarski(k3_enumset1(X3,X3,X3,X3,esk6_0))))|~r1_tarski(X1,k2_zfmisc_1(k3_tarski(k3_enumset1(X2,X2,X2,X2,esk5_0)),k3_tarski(k3_enumset1(X3,X3,X3,X3,esk6_0))))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 18.62/18.85  cnf(c_0_55, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,X1)),k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,X2))))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 18.62/18.85  cnf(c_0_56, negated_conjecture, (~r1_tarski(k3_tarski(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk5_0)),k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_20]), c_0_20]), c_0_20]), c_0_21]), c_0_21]), c_0_21]), c_0_22]), c_0_22]), c_0_22])).
% 18.62/18.85  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), ['proof']).
% 18.62/18.85  # SZS output end CNFRefutation
% 18.62/18.85  # Proof object total steps             : 58
% 18.62/18.85  # Proof object clause steps            : 35
% 18.62/18.85  # Proof object formula steps           : 23
% 18.62/18.85  # Proof object conjectures             : 13
% 18.62/18.85  # Proof object clause conjectures      : 10
% 18.62/18.85  # Proof object formula conjectures     : 3
% 18.62/18.85  # Proof object initial clauses used    : 14
% 18.62/18.85  # Proof object initial formulas used   : 11
% 18.62/18.85  # Proof object generating inferences   : 15
% 18.62/18.85  # Proof object simplifying inferences  : 21
% 18.62/18.85  # Training examples: 0 positive, 0 negative
% 18.62/18.85  # Parsed axioms                        : 11
% 18.62/18.85  # Removed by relevancy pruning/SinE    : 0
% 18.62/18.85  # Initial clauses                      : 16
% 18.62/18.85  # Removed in clause preprocessing      : 4
% 18.62/18.85  # Initial clauses in saturation        : 12
% 18.62/18.85  # Processed clauses                    : 26288
% 18.62/18.85  # ...of these trivial                  : 9014
% 18.62/18.85  # ...subsumed                          : 4606
% 18.62/18.85  # ...remaining for further processing  : 12668
% 18.62/18.85  # Other redundant clauses eliminated   : 2
% 18.62/18.85  # Clauses deleted for lack of memory   : 0
% 18.62/18.85  # Backward-subsumed                    : 154
% 18.62/18.85  # Backward-rewritten                   : 392
% 18.62/18.85  # Generated clauses                    : 1102201
% 18.62/18.85  # ...of the previous two non-trivial   : 1024286
% 18.62/18.85  # Contextual simplify-reflections      : 0
% 18.62/18.85  # Paramodulations                      : 1102199
% 18.62/18.85  # Factorizations                       : 0
% 18.62/18.85  # Equation resolutions                 : 2
% 18.62/18.85  # Propositional unsat checks           : 0
% 18.62/18.85  #    Propositional check models        : 0
% 18.62/18.85  #    Propositional check unsatisfiable : 0
% 18.62/18.85  #    Propositional clauses             : 0
% 18.62/18.85  #    Propositional clauses after purity: 0
% 18.62/18.85  #    Propositional unsat core size     : 0
% 18.62/18.85  #    Propositional preprocessing time  : 0.000
% 18.62/18.85  #    Propositional encoding time       : 0.000
% 18.62/18.85  #    Propositional solver time         : 0.000
% 18.62/18.85  #    Success case prop preproc time    : 0.000
% 18.62/18.85  #    Success case prop encoding time   : 0.000
% 18.62/18.85  #    Success case prop solver time     : 0.000
% 18.62/18.85  # Current number of processed clauses  : 12109
% 18.62/18.85  #    Positive orientable unit clauses  : 5879
% 18.62/18.85  #    Positive unorientable unit clauses: 1
% 18.62/18.85  #    Negative unit clauses             : 1
% 18.62/18.85  #    Non-unit-clauses                  : 6228
% 18.62/18.85  # Current number of unprocessed clauses: 997033
% 18.62/18.85  # ...number of literals in the above   : 1016880
% 18.62/18.85  # Current number of archived formulas  : 0
% 18.62/18.85  # Current number of archived clauses   : 561
% 18.62/18.85  # Clause-clause subsumption calls (NU) : 4505144
% 18.62/18.85  # Rec. Clause-clause subsumption calls : 4418409
% 18.62/18.85  # Non-unit clause-clause subsumptions  : 4747
% 18.62/18.85  # Unit Clause-clause subsumption calls : 27800
% 18.62/18.85  # Rewrite failures with RHS unbound    : 0
% 18.62/18.85  # BW rewrite match attempts            : 1997739
% 18.62/18.85  # BW rewrite match successes           : 444
% 18.62/18.85  # Condensation attempts                : 0
% 18.62/18.85  # Condensation successes               : 0
% 18.62/18.85  # Termbank termtop insertions          : 54413802
% 18.67/18.90  
% 18.67/18.90  # -------------------------------------------------
% 18.67/18.90  # User time                : 17.966 s
% 18.67/18.90  # System time              : 0.554 s
% 18.67/18.90  # Total time               : 18.520 s
% 18.67/18.90  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
