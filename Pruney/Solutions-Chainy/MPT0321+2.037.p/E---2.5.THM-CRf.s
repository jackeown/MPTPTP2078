%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:03 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 452 expanded)
%              Number of clauses        :   45 ( 207 expanded)
%              Number of leaves         :    8 ( 108 expanded)
%              Depth                    :   16
%              Number of atoms          :  168 (1581 expanded)
%              Number of equality atoms :   50 ( 630 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(t134_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(c_0_8,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_9,plain,(
    ! [X16] : r1_tarski(k1_xboole_0,X16) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_10,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X11,X12] :
      ( ( ~ r2_hidden(esk2_2(X11,X12),X11)
        | ~ r2_hidden(esk2_2(X11,X12),X12)
        | X11 = X12 )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r2_hidden(esk2_2(X11,X12),X12)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | ( X1 = X3
            & X2 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t134_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X17,X18,X19,X20] :
      ( ( r2_hidden(X17,X19)
        | ~ r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,X20)) )
      & ( r2_hidden(X18,X20)
        | ~ r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,X20)) )
      & ( ~ r2_hidden(X17,X19)
        | ~ r2_hidden(X18,X20)
        | r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,X20)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk5_0,esk6_0)
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & ( esk3_0 != esk5_0
      | esk4_0 != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk2_2(k1_xboole_0,X1),X1)
    | r2_hidden(esk2_2(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X1,esk1_2(X2,X3)),k2_zfmisc_1(X4,X2))
    | r1_tarski(X2,X3)
    | ~ r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk2_2(k1_xboole_0,X1),X1) ),
    inference(ef,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(k4_tarski(esk2_2(k1_xboole_0,X1),esk1_2(X2,X3)),k2_zfmisc_1(X1,X2))
    | r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_29,plain,(
    ! [X24,X25,X26] :
      ( ( r1_tarski(k2_zfmisc_1(X24,X26),k2_zfmisc_1(X25,X26))
        | ~ r1_tarski(X24,X25) )
      & ( r1_tarski(k2_zfmisc_1(X26,X24),k2_zfmisc_1(X26,X25))
        | ~ r1_tarski(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),esk6_0)
    | r1_tarski(esk4_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_22])).

cnf(c_0_33,plain,
    ( X1 = X2
    | r2_hidden(k4_tarski(esk2_2(X1,X2),esk1_2(X3,X4)),k2_zfmisc_1(X1,X3))
    | r2_hidden(esk2_2(X1,X2),X2)
    | r1_tarski(X3,X4) ),
    inference(spm,[status(thm)],[c_0_23,c_0_16])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_36,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_37,negated_conjecture,
    ( esk3_0 = X1
    | r2_hidden(esk2_2(esk3_0,X1),esk5_0)
    | r2_hidden(esk2_2(esk3_0,X1),X1)
    | r1_tarski(esk4_0,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_38,plain,(
    ! [X21,X22,X23] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X22,X21),k2_zfmisc_1(X23,X21))
        | X21 = k1_xboole_0
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(k2_zfmisc_1(X21,X22),k2_zfmisc_1(X21,X23))
        | X21 = k1_xboole_0
        | r1_tarski(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,esk4_0),k2_zfmisc_1(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( esk5_0 = esk3_0
    | r2_hidden(esk2_2(esk3_0,esk5_0),esk5_0)
    | r1_tarski(esk4_0,X1) ),
    inference(ef,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk5_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_22])).

cnf(c_0_44,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_45,negated_conjecture,
    ( esk5_0 = esk3_0
    | X1 = esk4_0
    | r2_hidden(esk2_2(esk3_0,esk5_0),esk5_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk5_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_47,plain,
    ( X1 = X2
    | ~ r2_hidden(esk2_2(X1,X2),X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_48,negated_conjecture,
    ( esk5_0 = esk3_0
    | r2_hidden(esk2_2(esk3_0,esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_11]),c_0_44])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( esk5_0 = esk3_0
    | ~ r2_hidden(esk2_2(esk3_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(esk6_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_22])).

cnf(c_0_53,negated_conjecture,
    ( esk5_0 = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_48]),c_0_51])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,X1)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_53]),c_0_27])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( esk3_0 != esk5_0
    | esk4_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_58,negated_conjecture,
    ( esk6_0 = esk4_0
    | ~ r1_tarski(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( esk6_0 != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_53])])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:12:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 3.15/3.32  # AutoSched0-Mode selected heuristic G_E___008_C45_F1_PI_S5PRR_SE_Q4_CS_SP_S4S
% 3.15/3.32  # and selection function SelectNewComplexAHPNS.
% 3.15/3.32  #
% 3.15/3.32  # Preprocessing time       : 0.027 s
% 3.15/3.32  
% 3.15/3.32  # Proof found!
% 3.15/3.32  # SZS status Theorem
% 3.15/3.32  # SZS output start CNFRefutation
% 3.15/3.32  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.15/3.32  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.15/3.32  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 3.15/3.32  fof(t134_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 3.15/3.32  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.15/3.32  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 3.15/3.32  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.15/3.32  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 3.15/3.32  fof(c_0_8, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 3.15/3.32  fof(c_0_9, plain, ![X16]:r1_tarski(k1_xboole_0,X16), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 3.15/3.32  cnf(c_0_10, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 3.15/3.32  cnf(c_0_11, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 3.15/3.32  fof(c_0_12, plain, ![X11, X12]:((~r2_hidden(esk2_2(X11,X12),X11)|~r2_hidden(esk2_2(X11,X12),X12)|X11=X12)&(r2_hidden(esk2_2(X11,X12),X11)|r2_hidden(esk2_2(X11,X12),X12)|X11=X12)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 3.15/3.32  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4)))), inference(assume_negation,[status(cth)],[t134_zfmisc_1])).
% 3.15/3.32  fof(c_0_14, plain, ![X17, X18, X19, X20]:(((r2_hidden(X17,X19)|~r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,X20)))&(r2_hidden(X18,X20)|~r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,X20))))&(~r2_hidden(X17,X19)|~r2_hidden(X18,X20)|r2_hidden(k4_tarski(X17,X18),k2_zfmisc_1(X19,X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 3.15/3.32  cnf(c_0_15, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 3.15/3.32  cnf(c_0_16, plain, (r2_hidden(esk2_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_12])).
% 3.15/3.32  fof(c_0_17, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk5_0,esk6_0)&((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&(esk3_0!=esk5_0|esk4_0!=esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 3.15/3.32  cnf(c_0_18, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.15/3.32  cnf(c_0_19, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 3.15/3.32  cnf(c_0_20, plain, (k1_xboole_0=X1|r2_hidden(esk2_2(k1_xboole_0,X1),X1)|r2_hidden(esk2_2(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 3.15/3.32  cnf(c_0_21, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.15/3.32  cnf(c_0_22, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.15/3.32  cnf(c_0_23, plain, (r2_hidden(k4_tarski(X1,esk1_2(X2,X3)),k2_zfmisc_1(X4,X2))|r1_tarski(X2,X3)|~r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 3.15/3.32  cnf(c_0_24, plain, (k1_xboole_0=X1|r2_hidden(esk2_2(k1_xboole_0,X1),X1)), inference(ef,[status(thm)],[c_0_20])).
% 3.15/3.32  cnf(c_0_25, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 3.15/3.32  cnf(c_0_26, plain, (k1_xboole_0=X1|r2_hidden(k4_tarski(esk2_2(k1_xboole_0,X1),esk1_2(X2,X3)),k2_zfmisc_1(X1,X2))|r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 3.15/3.32  cnf(c_0_27, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.15/3.32  cnf(c_0_28, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.15/3.32  fof(c_0_29, plain, ![X24, X25, X26]:((r1_tarski(k2_zfmisc_1(X24,X26),k2_zfmisc_1(X25,X26))|~r1_tarski(X24,X25))&(r1_tarski(k2_zfmisc_1(X26,X24),k2_zfmisc_1(X26,X25))|~r1_tarski(X24,X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 3.15/3.32  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 3.15/3.32  cnf(c_0_31, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),esk6_0)|r1_tarski(esk4_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 3.15/3.32  cnf(c_0_32, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_28, c_0_22])).
% 3.15/3.32  cnf(c_0_33, plain, (X1=X2|r2_hidden(k4_tarski(esk2_2(X1,X2),esk1_2(X3,X4)),k2_zfmisc_1(X1,X3))|r2_hidden(esk2_2(X1,X2),X2)|r1_tarski(X3,X4)), inference(spm,[status(thm)],[c_0_23, c_0_16])).
% 3.15/3.32  cnf(c_0_34, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 3.15/3.32  cnf(c_0_35, negated_conjecture, (r1_tarski(esk4_0,esk6_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 3.15/3.32  fof(c_0_36, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 3.15/3.32  cnf(c_0_37, negated_conjecture, (esk3_0=X1|r2_hidden(esk2_2(esk3_0,X1),esk5_0)|r2_hidden(esk2_2(esk3_0,X1),X1)|r1_tarski(esk4_0,X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 3.15/3.32  fof(c_0_38, plain, ![X21, X22, X23]:((~r1_tarski(k2_zfmisc_1(X22,X21),k2_zfmisc_1(X23,X21))|X21=k1_xboole_0|r1_tarski(X22,X23))&(~r1_tarski(k2_zfmisc_1(X21,X22),k2_zfmisc_1(X21,X23))|X21=k1_xboole_0|r1_tarski(X22,X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 3.15/3.32  cnf(c_0_39, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,esk4_0),k2_zfmisc_1(X1,esk6_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 3.15/3.32  cnf(c_0_40, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.15/3.32  cnf(c_0_41, negated_conjecture, (esk5_0=esk3_0|r2_hidden(esk2_2(esk3_0,esk5_0),esk5_0)|r1_tarski(esk4_0,X1)), inference(ef,[status(thm)],[c_0_37])).
% 3.15/3.32  cnf(c_0_42, plain, (X2=k1_xboole_0|r1_tarski(X1,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 3.15/3.32  cnf(c_0_43, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk5_0,esk4_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_39, c_0_22])).
% 3.15/3.32  cnf(c_0_44, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.15/3.32  cnf(c_0_45, negated_conjecture, (esk5_0=esk3_0|X1=esk4_0|r2_hidden(esk2_2(esk3_0,esk5_0),esk5_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 3.15/3.32  cnf(c_0_46, negated_conjecture, (r1_tarski(esk5_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 3.15/3.32  cnf(c_0_47, plain, (X1=X2|~r2_hidden(esk2_2(X1,X2),X1)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 3.15/3.32  cnf(c_0_48, negated_conjecture, (esk5_0=esk3_0|r2_hidden(esk2_2(esk3_0,esk5_0),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_11]), c_0_44])).
% 3.15/3.32  cnf(c_0_49, plain, (X1=k1_xboole_0|r1_tarski(X2,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 3.15/3.32  cnf(c_0_50, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_10, c_0_46])).
% 3.15/3.32  cnf(c_0_51, negated_conjecture, (esk5_0=esk3_0|~r2_hidden(esk2_2(esk3_0,esk5_0),esk3_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 3.15/3.32  cnf(c_0_52, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(esk6_0,X1)|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,X1))), inference(spm,[status(thm)],[c_0_49, c_0_22])).
% 3.15/3.32  cnf(c_0_53, negated_conjecture, (esk5_0=esk3_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_48]), c_0_51])).
% 3.15/3.32  cnf(c_0_54, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.15/3.32  cnf(c_0_55, negated_conjecture, (r1_tarski(esk6_0,X1)|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk3_0,X1))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_53]), c_0_27])).
% 3.15/3.32  cnf(c_0_56, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_54])).
% 3.15/3.32  cnf(c_0_57, negated_conjecture, (esk3_0!=esk5_0|esk4_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.15/3.32  cnf(c_0_58, negated_conjecture, (esk6_0=esk4_0|~r1_tarski(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_35])).
% 3.15/3.32  cnf(c_0_59, negated_conjecture, (r1_tarski(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 3.15/3.32  cnf(c_0_60, negated_conjecture, (esk6_0!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_53])])).
% 3.15/3.32  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])]), c_0_60]), ['proof']).
% 3.15/3.32  # SZS output end CNFRefutation
% 3.15/3.32  # Proof object total steps             : 62
% 3.15/3.32  # Proof object clause steps            : 45
% 3.15/3.32  # Proof object formula steps           : 17
% 3.15/3.32  # Proof object conjectures             : 27
% 3.15/3.32  # Proof object clause conjectures      : 24
% 3.15/3.32  # Proof object formula conjectures     : 3
% 3.15/3.32  # Proof object initial clauses used    : 18
% 3.15/3.32  # Proof object initial formulas used   : 8
% 3.15/3.32  # Proof object generating inferences   : 23
% 3.15/3.32  # Proof object simplifying inferences  : 13
% 3.15/3.32  # Training examples: 0 positive, 0 negative
% 3.15/3.32  # Parsed axioms                        : 8
% 3.15/3.32  # Removed by relevancy pruning/SinE    : 0
% 3.15/3.32  # Initial clauses                      : 20
% 3.15/3.32  # Removed in clause preprocessing      : 0
% 3.15/3.32  # Initial clauses in saturation        : 20
% 3.15/3.32  # Processed clauses                    : 8429
% 3.15/3.32  # ...of these trivial                  : 14
% 3.15/3.32  # ...subsumed                          : 5459
% 3.15/3.32  # ...remaining for further processing  : 2956
% 3.15/3.32  # Other redundant clauses eliminated   : 2
% 3.15/3.32  # Clauses deleted for lack of memory   : 0
% 3.15/3.32  # Backward-subsumed                    : 70
% 3.15/3.32  # Backward-rewritten                   : 2013
% 3.15/3.32  # Generated clauses                    : 305096
% 3.15/3.32  # ...of the previous two non-trivial   : 305310
% 3.15/3.32  # Contextual simplify-reflections      : 1
% 3.15/3.32  # Paramodulations                      : 304780
% 3.15/3.32  # Factorizations                       : 314
% 3.15/3.32  # Equation resolutions                 : 2
% 3.15/3.32  # Propositional unsat checks           : 0
% 3.15/3.32  #    Propositional check models        : 0
% 3.15/3.32  #    Propositional check unsatisfiable : 0
% 3.15/3.32  #    Propositional clauses             : 0
% 3.15/3.32  #    Propositional clauses after purity: 0
% 3.15/3.32  #    Propositional unsat core size     : 0
% 3.15/3.32  #    Propositional preprocessing time  : 0.000
% 3.15/3.32  #    Propositional encoding time       : 0.000
% 3.15/3.32  #    Propositional solver time         : 0.000
% 3.15/3.32  #    Success case prop preproc time    : 0.000
% 3.15/3.32  #    Success case prop encoding time   : 0.000
% 3.15/3.32  #    Success case prop solver time     : 0.000
% 3.15/3.32  # Current number of processed clauses  : 871
% 3.15/3.32  #    Positive orientable unit clauses  : 107
% 3.15/3.32  #    Positive unorientable unit clauses: 0
% 3.15/3.32  #    Negative unit clauses             : 5
% 3.15/3.32  #    Non-unit-clauses                  : 759
% 3.15/3.32  # Current number of unprocessed clauses: 296712
% 3.15/3.32  # ...number of literals in the above   : 1119800
% 3.15/3.32  # Current number of archived formulas  : 0
% 3.15/3.32  # Current number of archived clauses   : 2083
% 3.15/3.32  # Clause-clause subsumption calls (NU) : 2627386
% 3.15/3.32  # Rec. Clause-clause subsumption calls : 2147768
% 3.15/3.32  # Non-unit clause-clause subsumptions  : 5527
% 3.15/3.32  # Unit Clause-clause subsumption calls : 34692
% 3.15/3.32  # Rewrite failures with RHS unbound    : 0
% 3.15/3.32  # BW rewrite match attempts            : 3295
% 3.15/3.32  # BW rewrite match successes           : 12
% 3.15/3.32  # Condensation attempts                : 0
% 3.15/3.32  # Condensation successes               : 0
% 3.15/3.32  # Termbank termtop insertions          : 10730474
% 3.15/3.34  
% 3.15/3.34  # -------------------------------------------------
% 3.15/3.34  # User time                : 2.864 s
% 3.15/3.34  # System time              : 0.140 s
% 3.15/3.34  # Total time               : 3.004 s
% 3.15/3.34  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
