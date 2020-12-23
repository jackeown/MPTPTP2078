%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:12 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 206 expanded)
%              Number of clauses        :   45 ( 105 expanded)
%              Number of leaves         :    6 (  47 expanded)
%              Depth                    :   19
%              Number of atoms          :  168 ( 655 expanded)
%              Number of equality atoms :   45 ( 233 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t82_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) = k1_zfmisc_1(k2_xboole_0(X1,X2))
     => r3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_zfmisc_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d9_xboole_0,axiom,(
    ! [X1,X2] :
      ( r3_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        | r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(X8,X5)
        | r2_hidden(X8,X6)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_7,plain,(
    ! [X25,X26] : k3_tarski(k2_tarski(X25,X26)) = k2_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) = k1_zfmisc_1(k2_xboole_0(X1,X2))
       => r3_xboole_0(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t82_zfmisc_1])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,negated_conjecture,
    ( k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)) = k1_zfmisc_1(k2_xboole_0(esk3_0,esk4_0))
    & ~ r3_xboole_0(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X4)
    | r2_hidden(X1,X3)
    | X2 != k3_tarski(k2_tarski(X3,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)) = k1_zfmisc_1(k2_xboole_0(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X18,X19,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X20,X19)
        | r1_tarski(X20,X18)
        | X19 != k1_zfmisc_1(X18) )
      & ( ~ r1_tarski(X21,X18)
        | r2_hidden(X21,X19)
        | X19 != k1_zfmisc_1(X18) )
      & ( ~ r2_hidden(esk2_2(X22,X23),X23)
        | ~ r1_tarski(esk2_2(X22,X23),X22)
        | X23 = k1_zfmisc_1(X22) )
      & ( r2_hidden(esk2_2(X22,X23),X23)
        | r1_tarski(esk2_2(X22,X23),X22)
        | X23 = k1_zfmisc_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k3_tarski(k2_tarski(X3,X2))) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( k3_tarski(k2_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0))) = k1_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_10]),c_0_10])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k2_tarski(X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk4_0))
    | r2_hidden(X1,k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(X1,k1_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk3_0))
    | r2_hidden(X1,k1_zfmisc_1(esk4_0))
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k2_tarski(X2,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_10])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk4_0))))
    | ~ r2_hidden(X1,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k3_tarski(k2_tarski(esk3_0,esk4_0)),k1_zfmisc_1(esk4_0))
    | r2_hidden(k3_tarski(k2_tarski(esk3_0,esk4_0)),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(X1,k3_tarski(k2_tarski(esk3_0,esk4_0)))
    | ~ r2_hidden(X1,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk3_0,esk4_0)),esk4_0)
    | r2_hidden(k3_tarski(k2_tarski(esk3_0,esk4_0)),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk4_0))))
    | ~ r2_hidden(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( k3_tarski(k2_tarski(esk3_0,esk4_0)) = X1
    | ~ r1_tarski(k3_tarski(k2_tarski(esk3_0,esk4_0)),X1)
    | ~ r2_hidden(X1,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(esk3_0,esk4_0)),esk4_0)
    | r1_tarski(k3_tarski(k2_tarski(esk3_0,esk4_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(X1,k3_tarski(k2_tarski(esk3_0,esk4_0)))
    | ~ r2_hidden(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( k3_tarski(k2_tarski(esk3_0,esk4_0)) = esk4_0
    | r1_tarski(k3_tarski(k2_tarski(esk3_0,esk4_0)),esk3_0)
    | ~ r2_hidden(esk4_0,k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( k3_tarski(k2_tarski(esk3_0,esk4_0)) = X1
    | ~ r1_tarski(k3_tarski(k2_tarski(esk3_0,esk4_0)),X1)
    | ~ r2_hidden(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( k3_tarski(k2_tarski(esk3_0,esk4_0)) = esk4_0
    | r1_tarski(k3_tarski(k2_tarski(esk3_0,esk4_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_22]),c_0_28])])).

cnf(c_0_44,negated_conjecture,
    ( k3_tarski(k2_tarski(esk3_0,esk4_0)) = esk4_0
    | k3_tarski(k2_tarski(esk3_0,esk4_0)) = esk3_0
    | ~ r2_hidden(esk3_0,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_45,negated_conjecture,
    ( k3_tarski(k2_tarski(esk3_0,esk4_0)) = esk3_0
    | k3_tarski(k2_tarski(esk3_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_22]),c_0_28])])).

fof(c_0_46,plain,(
    ! [X16,X17] :
      ( ( ~ r3_xboole_0(X16,X17)
        | r1_tarski(X16,X17)
        | r1_tarski(X17,X16) )
      & ( ~ r1_tarski(X16,X17)
        | r3_xboole_0(X16,X17) )
      & ( ~ r1_tarski(X17,X16)
        | r3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).

cnf(c_0_47,negated_conjecture,
    ( k3_tarski(k2_tarski(esk3_0,esk4_0)) = esk3_0
    | r1_tarski(X1,esk4_0)
    | ~ r2_hidden(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( ~ r3_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_49,plain,
    ( r3_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( k3_tarski(k2_tarski(esk3_0,esk4_0)) = esk3_0
    | r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( k3_tarski(k2_tarski(esk3_0,esk4_0)) = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_28]),c_0_51])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r2_hidden(X1,k1_zfmisc_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_52])).

cnf(c_0_54,plain,
    ( r3_xboole_0(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_22])).

cnf(c_0_56,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_28]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:59:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.030 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.19/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.38  fof(t82_zfmisc_1, conjecture, ![X1, X2]:(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2))=k1_zfmisc_1(k2_xboole_0(X1,X2))=>r3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_zfmisc_1)).
% 0.19/0.38  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.38  fof(d9_xboole_0, axiom, ![X1, X2]:(r3_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)|r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_xboole_0)).
% 0.19/0.38  fof(c_0_6, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(r2_hidden(X8,X5)|r2_hidden(X8,X6))|X7!=k2_xboole_0(X5,X6))&((~r2_hidden(X9,X5)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))&(~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))))&(((~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k2_xboole_0(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.19/0.38  fof(c_0_7, plain, ![X25, X26]:k3_tarski(k2_tarski(X25,X26))=k2_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.38  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2))=k1_zfmisc_1(k2_xboole_0(X1,X2))=>r3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t82_zfmisc_1])).
% 0.19/0.38  cnf(c_0_9, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_10, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  fof(c_0_11, negated_conjecture, (k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0))=k1_zfmisc_1(k2_xboole_0(esk3_0,esk4_0))&~r3_xboole_0(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.19/0.38  cnf(c_0_12, plain, (r2_hidden(X1,X4)|r2_hidden(X1,X3)|X2!=k3_tarski(k2_tarski(X3,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.19/0.38  cnf(c_0_13, negated_conjecture, (k2_xboole_0(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0))=k1_zfmisc_1(k2_xboole_0(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  fof(c_0_14, plain, ![X18, X19, X20, X21, X22, X23]:(((~r2_hidden(X20,X19)|r1_tarski(X20,X18)|X19!=k1_zfmisc_1(X18))&(~r1_tarski(X21,X18)|r2_hidden(X21,X19)|X19!=k1_zfmisc_1(X18)))&((~r2_hidden(esk2_2(X22,X23),X23)|~r1_tarski(esk2_2(X22,X23),X22)|X23=k1_zfmisc_1(X22))&(r2_hidden(esk2_2(X22,X23),X23)|r1_tarski(esk2_2(X22,X23),X22)|X23=k1_zfmisc_1(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.38  cnf(c_0_15, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_16, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k3_tarski(k2_tarski(X3,X2)))), inference(er,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (k3_tarski(k2_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)))=k1_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_10]), c_0_10])).
% 0.19/0.38  cnf(c_0_18, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  fof(c_0_19, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.38  cnf(c_0_20, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k2_tarski(X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_10])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(esk4_0))|r2_hidden(X1,k1_zfmisc_1(esk3_0))|~r2_hidden(X1,k1_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk4_0))))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.38  cnf(c_0_22, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_23, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_24, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_25, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_26, plain, (r2_hidden(X1,k3_tarski(k2_tarski(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(esk3_0))|r2_hidden(X1,k1_zfmisc_1(esk4_0))|~r1_tarski(X1,k3_tarski(k2_tarski(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.38  cnf(c_0_28, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_29, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k2_tarski(X2,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_10])).
% 0.19/0.38  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk4_0))))|~r2_hidden(X1,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_26, c_0_17])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (r2_hidden(k3_tarski(k2_tarski(esk3_0,esk4_0)),k1_zfmisc_1(esk4_0))|r2_hidden(k3_tarski(k2_tarski(esk3_0,esk4_0)),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.38  cnf(c_0_33, plain, (r2_hidden(X1,k3_tarski(k2_tarski(X2,X3)))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_34, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (r1_tarski(X1,k3_tarski(k2_tarski(esk3_0,esk4_0)))|~r2_hidden(X1,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk3_0,esk4_0)),esk4_0)|r2_hidden(k3_tarski(k2_tarski(esk3_0,esk4_0)),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_30, c_0_32])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(k3_tarski(k2_tarski(esk3_0,esk4_0))))|~r2_hidden(X1,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_33, c_0_17])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (k3_tarski(k2_tarski(esk3_0,esk4_0))=X1|~r1_tarski(k3_tarski(k2_tarski(esk3_0,esk4_0)),X1)|~r2_hidden(X1,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (r1_tarski(k3_tarski(k2_tarski(esk3_0,esk4_0)),esk4_0)|r1_tarski(k3_tarski(k2_tarski(esk3_0,esk4_0)),esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_36])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (r1_tarski(X1,k3_tarski(k2_tarski(esk3_0,esk4_0)))|~r2_hidden(X1,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_30, c_0_37])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (k3_tarski(k2_tarski(esk3_0,esk4_0))=esk4_0|r1_tarski(k3_tarski(k2_tarski(esk3_0,esk4_0)),esk3_0)|~r2_hidden(esk4_0,k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (k3_tarski(k2_tarski(esk3_0,esk4_0))=X1|~r1_tarski(k3_tarski(k2_tarski(esk3_0,esk4_0)),X1)|~r2_hidden(X1,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_34, c_0_40])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (k3_tarski(k2_tarski(esk3_0,esk4_0))=esk4_0|r1_tarski(k3_tarski(k2_tarski(esk3_0,esk4_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_22]), c_0_28])])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (k3_tarski(k2_tarski(esk3_0,esk4_0))=esk4_0|k3_tarski(k2_tarski(esk3_0,esk4_0))=esk3_0|~r2_hidden(esk3_0,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (k3_tarski(k2_tarski(esk3_0,esk4_0))=esk3_0|k3_tarski(k2_tarski(esk3_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_22]), c_0_28])])).
% 0.19/0.38  fof(c_0_46, plain, ![X16, X17]:((~r3_xboole_0(X16,X17)|(r1_tarski(X16,X17)|r1_tarski(X17,X16)))&((~r1_tarski(X16,X17)|r3_xboole_0(X16,X17))&(~r1_tarski(X17,X16)|r3_xboole_0(X16,X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (k3_tarski(k2_tarski(esk3_0,esk4_0))=esk3_0|r1_tarski(X1,esk4_0)|~r2_hidden(X1,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_40, c_0_45])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (~r3_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_49, plain, (r3_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (k3_tarski(k2_tarski(esk3_0,esk4_0))=esk3_0|r1_tarski(X1,esk4_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_47, c_0_22])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (k3_tarski(k2_tarski(esk3_0,esk4_0))=esk3_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_28]), c_0_51])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (r1_tarski(X1,esk3_0)|~r2_hidden(X1,k1_zfmisc_1(esk4_0))), inference(rw,[status(thm)],[c_0_35, c_0_52])).
% 0.19/0.38  cnf(c_0_54, plain, (r3_xboole_0(X2,X1)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_53, c_0_22])).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, (~r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_48, c_0_54])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_28]), c_0_56]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 58
% 0.19/0.38  # Proof object clause steps            : 45
% 0.19/0.38  # Proof object formula steps           : 13
% 0.19/0.38  # Proof object conjectures             : 29
% 0.19/0.38  # Proof object clause conjectures      : 26
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 12
% 0.19/0.38  # Proof object initial formulas used   : 6
% 0.19/0.38  # Proof object generating inferences   : 22
% 0.19/0.38  # Proof object simplifying inferences  : 18
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 6
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 19
% 0.19/0.38  # Removed in clause preprocessing      : 1
% 0.19/0.38  # Initial clauses in saturation        : 18
% 0.19/0.38  # Processed clauses                    : 110
% 0.19/0.38  # ...of these trivial                  : 3
% 0.19/0.38  # ...subsumed                          : 21
% 0.19/0.38  # ...remaining for further processing  : 86
% 0.19/0.38  # Other redundant clauses eliminated   : 7
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 6
% 0.19/0.38  # Backward-rewritten                   : 22
% 0.19/0.38  # Generated clauses                    : 254
% 0.19/0.38  # ...of the previous two non-trivial   : 226
% 0.19/0.38  # Contextual simplify-reflections      : 1
% 0.19/0.38  # Paramodulations                      : 240
% 0.19/0.38  # Factorizations                       : 7
% 0.19/0.38  # Equation resolutions                 : 7
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 34
% 0.19/0.38  #    Positive orientable unit clauses  : 2
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 3
% 0.19/0.38  #    Non-unit-clauses                  : 29
% 0.19/0.38  # Current number of unprocessed clauses: 150
% 0.19/0.38  # ...number of literals in the above   : 617
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 46
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 361
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 337
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 25
% 0.19/0.38  # Unit Clause-clause subsumption calls : 7
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 3
% 0.19/0.38  # BW rewrite match successes           : 1
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 5232
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.038 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.042 s
% 0.19/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
