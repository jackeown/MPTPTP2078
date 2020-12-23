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
% DateTime   : Thu Dec  3 10:44:29 EST 2020

% Result     : Theorem 5.05s
% Output     : CNFRefutation 5.05s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 224 expanded)
%              Number of clauses        :   41 ( 107 expanded)
%              Number of leaves         :   10 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 386 expanded)
%              Number of equality atoms :   25 ( 150 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t143_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
        & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
     => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t13_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(c_0_10,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k2_xboole_0(X15,X16) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_11,plain,(
    ! [X32,X33] : k3_tarski(k2_tarski(X32,X33)) = k2_xboole_0(X32,X33) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(k2_xboole_0(X12,X13),X14)
      | r1_tarski(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_17,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X27,X28] : r1_tarski(X27,k2_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_22,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_tarski(k4_xboole_0(X24,X25),X26)
      | r1_tarski(X24,k2_xboole_0(X25,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

fof(c_0_23,plain,(
    ! [X9,X10,X11] :
      ( ( r1_tarski(X9,X10)
        | ~ r1_tarski(X9,k4_xboole_0(X10,X11)) )
      & ( r1_xboole_0(X9,X11)
        | ~ r1_tarski(X9,k4_xboole_0(X10,X11)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X17,X18,X19,X20] :
      ( ~ r1_tarski(X17,X18)
      | ~ r1_tarski(X19,X20)
      | r1_tarski(k2_xboole_0(X17,X19),k2_xboole_0(X18,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3) ),
    inference(rw,[status(thm)],[c_0_18,c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( k3_tarski(k2_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))) = k2_zfmisc_1(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X34,X35,X36] :
      ( k2_zfmisc_1(k2_xboole_0(X34,X35),X36) = k2_xboole_0(k2_zfmisc_1(X34,X36),k2_zfmisc_1(X35,X36))
      & k2_zfmisc_1(X36,k2_xboole_0(X34,X35)) = k2_xboole_0(k2_zfmisc_1(X36,X34),k2_zfmisc_1(X36,X35)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_15])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( k3_tarski(k2_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))) = k2_zfmisc_1(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_30])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_31,c_0_15])).

cnf(c_0_40,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X3)),k3_tarski(k2_tarski(X2,X4)))
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_15]),c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk2_0,k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X3))) = k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_15]),c_0_15])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_38])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X2,X4)))))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_41,c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X1)))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(esk1_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(esk3_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X3,X1)),k3_tarski(k2_tarski(X2,X4))))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_45])).

cnf(c_0_50,plain,
    ( k3_tarski(k2_tarski(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_19,c_0_33])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(X1,esk2_0)),k3_tarski(k2_tarski(X2,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X3))))))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_43])).

cnf(c_0_53,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_54,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_55,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0))),k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X2)))))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( k2_zfmisc_1(k3_tarski(k2_tarski(X1,X2)),X3) = k3_tarski(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_15]),c_0_15])).

cnf(c_0_59,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_55])])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_15]),c_0_15]),c_0_15])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.36  % Computer   : n010.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 11:26:59 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  # Version: 2.5pre002
% 0.15/0.36  # No SInE strategy applied
% 0.15/0.36  # Trying AutoSched0 for 299 seconds
% 5.05/5.24  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 5.05/5.24  # and selection function SelectDiffNegLit.
% 5.05/5.24  #
% 5.05/5.24  # Preprocessing time       : 0.027 s
% 5.05/5.24  # Presaturation interreduction done
% 5.05/5.24  
% 5.05/5.24  # Proof found!
% 5.05/5.24  # SZS status Theorem
% 5.05/5.24  # SZS output start CNFRefutation
% 5.05/5.24  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.05/5.24  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.05/5.24  fof(t143_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 5.05/5.24  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.05/5.24  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.05/5.24  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.05/5.24  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 5.05/5.24  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 5.05/5.24  fof(t13_xboole_1, axiom, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 5.05/5.24  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 5.05/5.24  fof(c_0_10, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k2_xboole_0(X15,X16)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 5.05/5.24  fof(c_0_11, plain, ![X32, X33]:k3_tarski(k2_tarski(X32,X33))=k2_xboole_0(X32,X33), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 5.05/5.24  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:((r1_tarski(X1,k2_zfmisc_1(X3,X4))&r1_tarski(X2,k2_zfmisc_1(X5,X6)))=>r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))))), inference(assume_negation,[status(cth)],[t143_zfmisc_1])).
% 5.05/5.24  fof(c_0_13, plain, ![X12, X13, X14]:(~r1_tarski(k2_xboole_0(X12,X13),X14)|r1_tarski(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 5.05/5.24  cnf(c_0_14, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 5.05/5.24  cnf(c_0_15, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 5.05/5.24  fof(c_0_16, negated_conjecture, ((r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))&r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))&~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 5.05/5.24  fof(c_0_17, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 5.05/5.24  cnf(c_0_18, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 5.05/5.24  cnf(c_0_19, plain, (k3_tarski(k2_tarski(X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 5.05/5.24  cnf(c_0_20, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.05/5.24  fof(c_0_21, plain, ![X27, X28]:r1_tarski(X27,k2_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 5.05/5.24  fof(c_0_22, plain, ![X24, X25, X26]:(~r1_tarski(k4_xboole_0(X24,X25),X26)|r1_tarski(X24,k2_xboole_0(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 5.05/5.24  fof(c_0_23, plain, ![X9, X10, X11]:((r1_tarski(X9,X10)|~r1_tarski(X9,k4_xboole_0(X10,X11)))&(r1_xboole_0(X9,X11)|~r1_tarski(X9,k4_xboole_0(X10,X11)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 5.05/5.24  cnf(c_0_24, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 5.05/5.24  fof(c_0_25, plain, ![X17, X18, X19, X20]:(~r1_tarski(X17,X18)|~r1_tarski(X19,X20)|r1_tarski(k2_xboole_0(X17,X19),k2_xboole_0(X18,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).
% 5.05/5.24  cnf(c_0_26, plain, (r1_tarski(X1,X3)|~r1_tarski(k3_tarski(k2_tarski(X1,X2)),X3)), inference(rw,[status(thm)],[c_0_18, c_0_15])).
% 5.05/5.24  cnf(c_0_27, negated_conjecture, (k3_tarski(k2_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)))=k2_zfmisc_1(esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 5.05/5.24  cnf(c_0_28, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 5.05/5.24  fof(c_0_29, plain, ![X34, X35, X36]:(k2_zfmisc_1(k2_xboole_0(X34,X35),X36)=k2_xboole_0(k2_zfmisc_1(X34,X36),k2_zfmisc_1(X35,X36))&k2_zfmisc_1(X36,k2_xboole_0(X34,X35))=k2_xboole_0(k2_zfmisc_1(X36,X34),k2_zfmisc_1(X36,X35))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 5.05/5.24  cnf(c_0_30, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.05/5.24  cnf(c_0_31, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 5.05/5.24  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 5.05/5.24  cnf(c_0_33, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_24])).
% 5.05/5.24  cnf(c_0_34, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 5.05/5.24  cnf(c_0_35, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 5.05/5.24  cnf(c_0_36, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_28, c_0_15])).
% 5.05/5.24  cnf(c_0_37, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 5.05/5.24  cnf(c_0_38, negated_conjecture, (k3_tarski(k2_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)))=k2_zfmisc_1(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_19, c_0_30])).
% 5.05/5.24  cnf(c_0_39, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_31, c_0_15])).
% 5.05/5.24  cnf(c_0_40, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 5.05/5.24  cnf(c_0_41, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X3)),k3_tarski(k2_tarski(X2,X4)))|~r1_tarski(X3,X4)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_15]), c_0_15])).
% 5.05/5.24  cnf(c_0_42, negated_conjecture, (r1_tarski(esk2_0,k3_tarski(k2_tarski(k2_zfmisc_1(esk5_0,esk6_0),X1)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 5.05/5.24  cnf(c_0_43, plain, (k2_zfmisc_1(X1,k3_tarski(k2_tarski(X2,X3)))=k3_tarski(k2_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_15]), c_0_15])).
% 5.05/5.24  cnf(c_0_44, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_26, c_0_38])).
% 5.05/5.24  cnf(c_0_45, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 5.05/5.24  cnf(c_0_46, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X2,X4)))))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_41, c_0_36])).
% 5.05/5.24  cnf(c_0_47, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X1))))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 5.05/5.24  cnf(c_0_48, negated_conjecture, (r1_tarski(esk1_0,k3_tarski(k2_tarski(X1,k2_zfmisc_1(esk3_0,esk4_0))))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 5.05/5.24  cnf(c_0_49, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X3,X1)),k3_tarski(k2_tarski(X2,X4)))))), inference(spm,[status(thm)],[c_0_46, c_0_45])).
% 5.05/5.24  cnf(c_0_50, plain, (k3_tarski(k2_tarski(X1,X1))=X1), inference(spm,[status(thm)],[c_0_19, c_0_33])).
% 5.05/5.24  cnf(c_0_51, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(X1,esk2_0)),k3_tarski(k2_tarski(X2,k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X3))))))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_47])).
% 5.05/5.24  cnf(c_0_52, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0))))), inference(spm,[status(thm)],[c_0_48, c_0_43])).
% 5.05/5.24  cnf(c_0_53, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 5.05/5.24  cnf(c_0_54, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 5.05/5.24  cnf(c_0_55, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X2)),k3_tarski(k2_tarski(X2,X1)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 5.05/5.24  cnf(c_0_56, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.05/5.24  cnf(c_0_57, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k3_tarski(k2_tarski(k2_zfmisc_1(esk3_0,k3_tarski(k2_tarski(X1,esk4_0))),k2_zfmisc_1(esk5_0,k3_tarski(k2_tarski(esk6_0,X2))))))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 5.05/5.24  cnf(c_0_58, plain, (k2_zfmisc_1(k3_tarski(k2_tarski(X1,X2)),X3)=k3_tarski(k2_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_15]), c_0_15])).
% 5.05/5.24  cnf(c_0_59, plain, (k3_tarski(k2_tarski(X1,X2))=k3_tarski(k2_tarski(X2,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_55])])).
% 5.05/5.24  cnf(c_0_60, negated_conjecture, (~r1_tarski(k3_tarski(k2_tarski(esk1_0,esk2_0)),k2_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk5_0)),k3_tarski(k2_tarski(esk4_0,esk6_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_15]), c_0_15]), c_0_15])).
% 5.05/5.24  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_60]), ['proof']).
% 5.05/5.24  # SZS output end CNFRefutation
% 5.05/5.24  # Proof object total steps             : 62
% 5.05/5.24  # Proof object clause steps            : 41
% 5.05/5.24  # Proof object formula steps           : 21
% 5.05/5.24  # Proof object conjectures             : 18
% 5.05/5.24  # Proof object clause conjectures      : 15
% 5.05/5.24  # Proof object formula conjectures     : 3
% 5.05/5.24  # Proof object initial clauses used    : 14
% 5.05/5.24  # Proof object initial formulas used   : 10
% 5.05/5.24  # Proof object generating inferences   : 18
% 5.05/5.24  # Proof object simplifying inferences  : 18
% 5.05/5.24  # Training examples: 0 positive, 0 negative
% 5.05/5.24  # Parsed axioms                        : 12
% 5.05/5.24  # Removed by relevancy pruning/SinE    : 0
% 5.05/5.24  # Initial clauses                      : 18
% 5.05/5.24  # Removed in clause preprocessing      : 1
% 5.05/5.24  # Initial clauses in saturation        : 17
% 5.05/5.24  # Processed clauses                    : 14692
% 5.05/5.24  # ...of these trivial                  : 2305
% 5.05/5.24  # ...subsumed                          : 6807
% 5.05/5.24  # ...remaining for further processing  : 5579
% 5.05/5.24  # Other redundant clauses eliminated   : 2
% 5.05/5.24  # Clauses deleted for lack of memory   : 0
% 5.05/5.24  # Backward-subsumed                    : 26
% 5.05/5.24  # Backward-rewritten                   : 1289
% 5.05/5.24  # Generated clauses                    : 574735
% 5.05/5.24  # ...of the previous two non-trivial   : 493247
% 5.05/5.24  # Contextual simplify-reflections      : 0
% 5.05/5.24  # Paramodulations                      : 574733
% 5.05/5.24  # Factorizations                       : 0
% 5.05/5.24  # Equation resolutions                 : 2
% 5.05/5.24  # Propositional unsat checks           : 0
% 5.05/5.24  #    Propositional check models        : 0
% 5.05/5.24  #    Propositional check unsatisfiable : 0
% 5.05/5.24  #    Propositional clauses             : 0
% 5.05/5.24  #    Propositional clauses after purity: 0
% 5.05/5.24  #    Propositional unsat core size     : 0
% 5.05/5.24  #    Propositional preprocessing time  : 0.000
% 5.05/5.24  #    Propositional encoding time       : 0.000
% 5.05/5.24  #    Propositional solver time         : 0.000
% 5.05/5.24  #    Success case prop preproc time    : 0.000
% 5.05/5.24  #    Success case prop encoding time   : 0.000
% 5.05/5.24  #    Success case prop solver time     : 0.000
% 5.05/5.24  # Current number of processed clauses  : 4246
% 5.05/5.24  #    Positive orientable unit clauses  : 2696
% 5.05/5.24  #    Positive unorientable unit clauses: 1
% 5.05/5.24  #    Negative unit clauses             : 1
% 5.05/5.24  #    Non-unit-clauses                  : 1548
% 5.05/5.24  # Current number of unprocessed clauses: 477015
% 5.05/5.24  # ...number of literals in the above   : 507369
% 5.05/5.24  # Current number of archived formulas  : 0
% 5.05/5.24  # Current number of archived clauses   : 1332
% 5.05/5.24  # Clause-clause subsumption calls (NU) : 220295
% 5.05/5.24  # Rec. Clause-clause subsumption calls : 211665
% 5.05/5.24  # Non-unit clause-clause subsumptions  : 6833
% 5.05/5.24  # Unit Clause-clause subsumption calls : 4882
% 5.05/5.24  # Rewrite failures with RHS unbound    : 0
% 5.05/5.24  # BW rewrite match attempts            : 410411
% 5.05/5.24  # BW rewrite match successes           : 2740
% 5.05/5.24  # Condensation attempts                : 0
% 5.05/5.24  # Condensation successes               : 0
% 5.05/5.24  # Termbank termtop insertions          : 14380174
% 5.05/5.27  
% 5.05/5.27  # -------------------------------------------------
% 5.05/5.27  # User time                : 4.634 s
% 5.05/5.27  # System time              : 0.270 s
% 5.05/5.27  # Total time               : 4.903 s
% 5.05/5.27  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
