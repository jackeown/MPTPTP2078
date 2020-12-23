%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:01 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   34 (  53 expanded)
%              Number of clauses        :   21 (  23 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :   92 ( 158 expanded)
%              Number of equality atoms :   32 (  53 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(t128_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))
    <=> ( X1 = X3
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(t11_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) )
     => ( ! [X4,X5] : X1 != k4_tarski(X4,X5)
        | r2_hidden(X1,k2_zfmisc_1(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_mcart_1)).

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_6,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X9,X8)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X8 != k2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | r2_hidden(X10,X8)
        | X8 != k2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X13)
        | r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k2_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_8,plain,(
    ! [X17,X18,X19] :
      ( k2_zfmisc_1(k2_xboole_0(X17,X18),X19) = k2_xboole_0(k2_zfmisc_1(X17,X19),k2_zfmisc_1(X18,X19))
      & k2_zfmisc_1(X19,k2_xboole_0(X17,X18)) = k2_xboole_0(k2_zfmisc_1(X19,X17),k2_zfmisc_1(X19,X18)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X20,X21,X22,X23] :
      ( ( X20 = X22
        | ~ r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(k1_tarski(X22),X23)) )
      & ( r2_hidden(X21,X23)
        | ~ r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(k1_tarski(X22),X23)) )
      & ( X20 != X22
        | ~ r2_hidden(X21,X23)
        | r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(k1_tarski(X22),X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t128_zfmisc_1])])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r2_hidden(k1_mcart_1(X1),X2)
          & r2_hidden(k2_mcart_1(X1),X3) )
       => ( ! [X4,X5] : X1 != k4_tarski(X4,X5)
          | r2_hidden(X1,k2_zfmisc_1(X2,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t11_mcart_1])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X15,X16)
      | k2_xboole_0(k1_tarski(X15),X16) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4))
    | X1 != X2
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk2_0),esk3_0)
    & r2_hidden(k2_mcart_1(esk2_0),esk4_0)
    & esk2_0 = k4_tarski(esk5_0,esk6_0)
    & ~ r2_hidden(esk2_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_16,plain,(
    ! [X24,X25] :
      ( k1_mcart_1(k4_tarski(X24,X25)) = X24
      & k2_mcart_1(k4_tarski(X24,X25)) = X25 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k2_zfmisc_1(k2_xboole_0(X2,X3),X4))
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X4)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X1),X3))
    | ~ r2_hidden(X2,X3) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( esk2_0 = k4_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(X1,k2_zfmisc_1(k1_tarski(X4),X3))
    | ~ r2_hidden(X4,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k1_tarski(esk5_0),X1))
    | ~ r2_hidden(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( k1_mcart_1(esk2_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( k2_mcart_1(esk2_0) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(esk5_0,X1)
    | ~ r2_hidden(esk6_0,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk6_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:29:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.027 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.12/0.38  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 0.12/0.38  fof(t128_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))<=>(X1=X3&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 0.12/0.38  fof(t11_mcart_1, conjecture, ![X1, X2, X3]:((r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))=>(![X4, X5]:X1!=k4_tarski(X4,X5)|r2_hidden(X1,k2_zfmisc_1(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_mcart_1)).
% 0.12/0.38  fof(l22_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 0.12/0.38  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.12/0.38  fof(c_0_6, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X9,X8)|(r2_hidden(X9,X6)|r2_hidden(X9,X7))|X8!=k2_xboole_0(X6,X7))&((~r2_hidden(X10,X6)|r2_hidden(X10,X8)|X8!=k2_xboole_0(X6,X7))&(~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k2_xboole_0(X6,X7))))&(((~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_xboole_0(X11,X12)))&(r2_hidden(esk1_3(X11,X12,X13),X13)|(r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k2_xboole_0(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.12/0.38  cnf(c_0_7, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.38  fof(c_0_8, plain, ![X17, X18, X19]:(k2_zfmisc_1(k2_xboole_0(X17,X18),X19)=k2_xboole_0(k2_zfmisc_1(X17,X19),k2_zfmisc_1(X18,X19))&k2_zfmisc_1(X19,k2_xboole_0(X17,X18))=k2_xboole_0(k2_zfmisc_1(X19,X17),k2_zfmisc_1(X19,X18))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 0.12/0.38  fof(c_0_9, plain, ![X20, X21, X22, X23]:(((X20=X22|~r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(k1_tarski(X22),X23)))&(r2_hidden(X21,X23)|~r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(k1_tarski(X22),X23))))&(X20!=X22|~r2_hidden(X21,X23)|r2_hidden(k4_tarski(X20,X21),k2_zfmisc_1(k1_tarski(X22),X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t128_zfmisc_1])])])).
% 0.12/0.38  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:((r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))=>(![X4, X5]:X1!=k4_tarski(X4,X5)|r2_hidden(X1,k2_zfmisc_1(X2,X3))))), inference(assume_negation,[status(cth)],[t11_mcart_1])).
% 0.12/0.38  cnf(c_0_11, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_7])).
% 0.12/0.38  cnf(c_0_12, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  fof(c_0_13, plain, ![X15, X16]:(~r2_hidden(X15,X16)|k2_xboole_0(k1_tarski(X15),X16)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).
% 0.12/0.38  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4))|X1!=X2|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  fof(c_0_15, negated_conjecture, ((r2_hidden(k1_mcart_1(esk2_0),esk3_0)&r2_hidden(k2_mcart_1(esk2_0),esk4_0))&(esk2_0=k4_tarski(esk5_0,esk6_0)&~r2_hidden(esk2_0,k2_zfmisc_1(esk3_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.12/0.38  fof(c_0_16, plain, ![X24, X25]:(k1_mcart_1(k4_tarski(X24,X25))=X24&k2_mcart_1(k4_tarski(X24,X25))=X25), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.12/0.38  cnf(c_0_17, plain, (r2_hidden(X1,k2_zfmisc_1(k2_xboole_0(X2,X3),X4))|~r2_hidden(X1,k2_zfmisc_1(X2,X4))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.12/0.38  cnf(c_0_18, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_19, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X1),X3))|~r2_hidden(X2,X3)), inference(er,[status(thm)],[c_0_14])).
% 0.12/0.38  cnf(c_0_20, negated_conjecture, (esk2_0=k4_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_21, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_22, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_23, plain, (r2_hidden(X1,k2_zfmisc_1(X2,X3))|~r2_hidden(X1,k2_zfmisc_1(k1_tarski(X4),X3))|~r2_hidden(X4,X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(k1_tarski(esk5_0),X1))|~r2_hidden(esk6_0,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (r2_hidden(k1_mcart_1(esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (k1_mcart_1(esk2_0)=esk5_0), inference(spm,[status(thm)],[c_0_21, c_0_20])).
% 0.12/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(k2_mcart_1(esk2_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_28, negated_conjecture, (k2_mcart_1(esk2_0)=esk6_0), inference(spm,[status(thm)],[c_0_22, c_0_20])).
% 0.12/0.38  cnf(c_0_29, negated_conjecture, (~r2_hidden(esk2_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(esk2_0,k2_zfmisc_1(X1,X2))|~r2_hidden(esk5_0,X1)|~r2_hidden(esk6_0,X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(esk5_0,esk3_0)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (r2_hidden(esk6_0,esk4_0)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.38  cnf(c_0_33, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 34
% 0.12/0.38  # Proof object clause steps            : 21
% 0.12/0.38  # Proof object formula steps           : 13
% 0.12/0.38  # Proof object conjectures             : 14
% 0.12/0.38  # Proof object clause conjectures      : 11
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 10
% 0.12/0.38  # Proof object initial formulas used   : 6
% 0.12/0.38  # Proof object generating inferences   : 7
% 0.12/0.38  # Proof object simplifying inferences  : 7
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 6
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 18
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 18
% 0.12/0.38  # Processed clauses                    : 142
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 56
% 0.12/0.38  # ...remaining for further processing  : 86
% 0.12/0.38  # Other redundant clauses eliminated   : 4
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 0
% 0.12/0.38  # Backward-rewritten                   : 2
% 0.12/0.38  # Generated clauses                    : 381
% 0.12/0.38  # ...of the previous two non-trivial   : 355
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 371
% 0.12/0.38  # Factorizations                       : 6
% 0.12/0.38  # Equation resolutions                 : 4
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 62
% 0.12/0.38  #    Positive orientable unit clauses  : 9
% 0.12/0.38  #    Positive unorientable unit clauses: 1
% 0.12/0.38  #    Negative unit clauses             : 1
% 0.12/0.38  #    Non-unit-clauses                  : 51
% 0.12/0.38  # Current number of unprocessed clauses: 240
% 0.12/0.38  # ...number of literals in the above   : 642
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 20
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 405
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 391
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 56
% 0.12/0.38  # Unit Clause-clause subsumption calls : 8
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 7
% 0.12/0.38  # BW rewrite match successes           : 2
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 6047
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.036 s
% 0.12/0.38  # System time              : 0.004 s
% 0.12/0.38  # Total time               : 0.040 s
% 0.12/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
