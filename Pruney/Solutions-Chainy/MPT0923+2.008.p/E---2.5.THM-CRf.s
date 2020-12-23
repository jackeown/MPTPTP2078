%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:32 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 388 expanded)
%              Number of clauses        :   41 ( 183 expanded)
%              Number of leaves         :    8 (  94 expanded)
%              Depth                    :   13
%              Number of atoms          :  107 ( 845 expanded)
%              Number of equality atoms :   47 ( 289 expanded)
%              Maximal formula depth    :   18 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t83_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ~ ( r2_hidden(X1,k4_zfmisc_1(X2,X3,X4,X5))
        & ! [X6,X7,X8,X9] :
            ~ ( r2_hidden(X6,X2)
              & r2_hidden(X7,X3)
              & r2_hidden(X8,X4)
              & r2_hidden(X9,X5)
              & X1 = k4_mcart_1(X6,X7,X8,X9) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(t31_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

fof(l139_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] : k4_tarski(X4,X5) != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ~ ( r2_hidden(X1,k4_zfmisc_1(X2,X3,X4,X5))
          & ! [X6,X7,X8,X9] :
              ~ ( r2_hidden(X6,X2)
                & r2_hidden(X7,X3)
                & r2_hidden(X8,X4)
                & r2_hidden(X9,X5)
                & X1 = k4_mcart_1(X6,X7,X8,X9) ) ) ),
    inference(assume_negation,[status(cth)],[t83_mcart_1])).

fof(c_0_9,plain,(
    ! [X22,X23,X24,X25] : k4_zfmisc_1(X22,X23,X24,X25) = k2_zfmisc_1(k3_zfmisc_1(X22,X23,X24),X25) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X15,X16,X17] : k3_zfmisc_1(X15,X16,X17) = k2_zfmisc_1(k2_zfmisc_1(X15,X16),X17) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_11,negated_conjecture,(
    ! [X40,X41,X42,X43] :
      ( r2_hidden(esk3_0,k4_zfmisc_1(esk4_0,esk5_0,esk6_0,esk7_0))
      & ( ~ r2_hidden(X40,esk4_0)
        | ~ r2_hidden(X41,esk5_0)
        | ~ r2_hidden(X42,esk6_0)
        | ~ r2_hidden(X43,esk7_0)
        | esk3_0 != k4_mcart_1(X40,X41,X42,X43) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

cnf(c_0_12,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X26,X27,X28] :
      ( ( r2_hidden(k1_mcart_1(X26),X27)
        | ~ r2_hidden(X26,k2_zfmisc_1(X27,X28)) )
      & ( r2_hidden(k2_mcart_1(X26),X28)
        | ~ r2_hidden(X26,k2_zfmisc_1(X27,X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk3_0,k4_zfmisc_1(esk4_0,esk5_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk3_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_19,plain,(
    ! [X18,X19,X20,X21] : k4_mcart_1(X18,X19,X20,X21) = k4_tarski(k3_mcart_1(X18,X19,X20),X21) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_20,plain,(
    ! [X29,X30,X31,X32] : k4_mcart_1(X29,X30,X31,X32) = k4_tarski(k4_tarski(k4_tarski(X29,X30),X31),X32) ),
    inference(variable_rename,[status(thm)],[t31_mcart_1])).

fof(c_0_21,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,k2_zfmisc_1(X11,X12))
      | k4_tarski(esk1_1(X10),esk2_1(X10)) = X10 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X2,esk5_0)
    | ~ r2_hidden(X3,esk6_0)
    | ~ r2_hidden(X4,esk7_0)
    | esk3_0 != k4_mcart_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X33,X34] :
      ( k1_mcart_1(k4_tarski(X33,X34)) = X33
      & k2_mcart_1(k4_tarski(X33,X34)) = X34 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_27,plain,
    ( k4_tarski(esk1_1(X1),esk2_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(esk3_0)),k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( esk3_0 != k4_tarski(k3_mcart_1(X1,X2,X3),X4)
    | ~ r2_hidden(X4,esk7_0)
    | ~ r2_hidden(X3,esk6_0)
    | ~ r2_hidden(X2,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( k4_tarski(k3_mcart_1(X1,X2,X3),X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_31,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( k4_tarski(esk1_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk2_1(k1_mcart_1(k1_mcart_1(esk3_0)))) = k1_mcart_1(k1_mcart_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k4_tarski(esk1_1(k1_mcart_1(esk3_0)),esk2_1(k1_mcart_1(esk3_0))) = k1_mcart_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) != esk3_0
    | ~ r2_hidden(X4,esk7_0)
    | ~ r2_hidden(X3,esk6_0)
    | ~ r2_hidden(X2,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( esk1_1(k1_mcart_1(k1_mcart_1(esk3_0))) = k1_mcart_1(k1_mcart_1(k1_mcart_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( esk1_1(k1_mcart_1(esk3_0)) = k1_mcart_1(k1_mcart_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( k4_tarski(esk1_1(esk3_0),esk2_1(esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_18])).

cnf(c_0_38,negated_conjecture,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk3_0)),X1),X2) != esk3_0
    | ~ r2_hidden(esk2_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk5_0)
    | ~ r2_hidden(esk1_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk4_0)
    | ~ r2_hidden(X2,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_28])).

cnf(c_0_40,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk2_1(k1_mcart_1(k1_mcart_1(esk3_0)))) = k1_mcart_1(k1_mcart_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_35])).

cnf(c_0_42,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_43,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk3_0)),esk2_1(k1_mcart_1(esk3_0))) = k1_mcart_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( esk1_1(esk3_0) = k1_mcart_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk3_0)),X1),X2) != esk3_0
    | ~ r2_hidden(esk2_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk5_0)
    | ~ r2_hidden(X2,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_35]),c_0_39])])).

cnf(c_0_46,negated_conjecture,
    ( esk2_1(k1_mcart_1(k1_mcart_1(esk3_0))) = k2_mcart_1(k1_mcart_1(k1_mcart_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_28])).

cnf(c_0_48,negated_conjecture,
    ( esk2_1(k1_mcart_1(esk3_0)) = k2_mcart_1(k1_mcart_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk3_0),esk2_1(esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_37,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk3_0)),X1),X2) != esk3_0
    | ~ r2_hidden(X2,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_51,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk3_0)),k2_mcart_1(k1_mcart_1(esk3_0))) = k1_mcart_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_43,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(esk3_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_22])).

cnf(c_0_53,negated_conjecture,
    ( esk2_1(esk3_0) = k2_mcart_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk3_0),X1) != esk3_0
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_55,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk3_0),k2_mcart_1(esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_49,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk3_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_18])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:11:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.027 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(t83_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:~((r2_hidden(X1,k4_zfmisc_1(X2,X3,X4,X5))&![X6, X7, X8, X9]:~(((((r2_hidden(X6,X2)&r2_hidden(X7,X3))&r2_hidden(X8,X4))&r2_hidden(X9,X5))&X1=k4_mcart_1(X6,X7,X8,X9))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_mcart_1)).
% 0.21/0.38  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.21/0.38  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.21/0.38  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.21/0.38  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.21/0.38  fof(t31_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_mcart_1)).
% 0.21/0.38  fof(l139_zfmisc_1, axiom, ![X1, X2, X3]:~((r2_hidden(X1,k2_zfmisc_1(X2,X3))&![X4, X5]:k4_tarski(X4,X5)!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 0.21/0.38  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.21/0.38  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4, X5]:~((r2_hidden(X1,k4_zfmisc_1(X2,X3,X4,X5))&![X6, X7, X8, X9]:~(((((r2_hidden(X6,X2)&r2_hidden(X7,X3))&r2_hidden(X8,X4))&r2_hidden(X9,X5))&X1=k4_mcart_1(X6,X7,X8,X9)))))), inference(assume_negation,[status(cth)],[t83_mcart_1])).
% 0.21/0.38  fof(c_0_9, plain, ![X22, X23, X24, X25]:k4_zfmisc_1(X22,X23,X24,X25)=k2_zfmisc_1(k3_zfmisc_1(X22,X23,X24),X25), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.21/0.38  fof(c_0_10, plain, ![X15, X16, X17]:k3_zfmisc_1(X15,X16,X17)=k2_zfmisc_1(k2_zfmisc_1(X15,X16),X17), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.21/0.38  fof(c_0_11, negated_conjecture, ![X40, X41, X42, X43]:(r2_hidden(esk3_0,k4_zfmisc_1(esk4_0,esk5_0,esk6_0,esk7_0))&(~r2_hidden(X40,esk4_0)|~r2_hidden(X41,esk5_0)|~r2_hidden(X42,esk6_0)|~r2_hidden(X43,esk7_0)|esk3_0!=k4_mcart_1(X40,X41,X42,X43))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.21/0.38  cnf(c_0_12, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  cnf(c_0_13, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.38  fof(c_0_14, plain, ![X26, X27, X28]:((r2_hidden(k1_mcart_1(X26),X27)|~r2_hidden(X26,k2_zfmisc_1(X27,X28)))&(r2_hidden(k2_mcart_1(X26),X28)|~r2_hidden(X26,k2_zfmisc_1(X27,X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.21/0.38  cnf(c_0_15, negated_conjecture, (r2_hidden(esk3_0,k4_zfmisc_1(esk4_0,esk5_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.38  cnf(c_0_16, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.21/0.38  cnf(c_0_17, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  cnf(c_0_18, negated_conjecture, (r2_hidden(esk3_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.38  fof(c_0_19, plain, ![X18, X19, X20, X21]:k4_mcart_1(X18,X19,X20,X21)=k4_tarski(k3_mcart_1(X18,X19,X20),X21), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.21/0.38  fof(c_0_20, plain, ![X29, X30, X31, X32]:k4_mcart_1(X29,X30,X31,X32)=k4_tarski(k4_tarski(k4_tarski(X29,X30),X31),X32), inference(variable_rename,[status(thm)],[t31_mcart_1])).
% 0.21/0.38  fof(c_0_21, plain, ![X10, X11, X12]:(~r2_hidden(X10,k2_zfmisc_1(X11,X12))|k4_tarski(esk1_1(X10),esk2_1(X10))=X10), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).
% 0.21/0.38  cnf(c_0_22, negated_conjecture, (r2_hidden(k1_mcart_1(esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.21/0.38  cnf(c_0_23, negated_conjecture, (~r2_hidden(X1,esk4_0)|~r2_hidden(X2,esk5_0)|~r2_hidden(X3,esk6_0)|~r2_hidden(X4,esk7_0)|esk3_0!=k4_mcart_1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.38  cnf(c_0_24, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_25, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.38  fof(c_0_26, plain, ![X33, X34]:(k1_mcart_1(k4_tarski(X33,X34))=X33&k2_mcart_1(k4_tarski(X33,X34))=X34), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.21/0.38  cnf(c_0_27, plain, (k4_tarski(esk1_1(X1),esk2_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(esk3_0)),k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_17, c_0_22])).
% 0.21/0.38  cnf(c_0_29, negated_conjecture, (esk3_0!=k4_tarski(k3_mcart_1(X1,X2,X3),X4)|~r2_hidden(X4,esk7_0)|~r2_hidden(X3,esk6_0)|~r2_hidden(X2,esk5_0)|~r2_hidden(X1,esk4_0)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.38  cnf(c_0_30, plain, (k4_tarski(k3_mcart_1(X1,X2,X3),X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_25, c_0_24])).
% 0.21/0.38  cnf(c_0_31, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.38  cnf(c_0_32, negated_conjecture, (k4_tarski(esk1_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk2_1(k1_mcart_1(k1_mcart_1(esk3_0))))=k1_mcart_1(k1_mcart_1(esk3_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.38  cnf(c_0_33, negated_conjecture, (k4_tarski(esk1_1(k1_mcart_1(esk3_0)),esk2_1(k1_mcart_1(esk3_0)))=k1_mcart_1(esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_22])).
% 0.21/0.38  cnf(c_0_34, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)!=esk3_0|~r2_hidden(X4,esk7_0)|~r2_hidden(X3,esk6_0)|~r2_hidden(X2,esk5_0)|~r2_hidden(X1,esk4_0)), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.38  cnf(c_0_35, negated_conjecture, (esk1_1(k1_mcart_1(k1_mcart_1(esk3_0)))=k1_mcart_1(k1_mcart_1(k1_mcart_1(esk3_0)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.38  cnf(c_0_36, negated_conjecture, (esk1_1(k1_mcart_1(esk3_0))=k1_mcart_1(k1_mcart_1(esk3_0))), inference(spm,[status(thm)],[c_0_31, c_0_33])).
% 0.21/0.38  cnf(c_0_37, negated_conjecture, (k4_tarski(esk1_1(esk3_0),esk2_1(esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_27, c_0_18])).
% 0.21/0.38  cnf(c_0_38, negated_conjecture, (k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk3_0)),X1),X2)!=esk3_0|~r2_hidden(esk2_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk5_0)|~r2_hidden(esk1_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk4_0)|~r2_hidden(X2,esk7_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_34, c_0_32])).
% 0.21/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk4_0)), inference(spm,[status(thm)],[c_0_17, c_0_28])).
% 0.21/0.38  cnf(c_0_40, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.38  cnf(c_0_41, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk2_1(k1_mcart_1(k1_mcart_1(esk3_0))))=k1_mcart_1(k1_mcart_1(esk3_0))), inference(rw,[status(thm)],[c_0_32, c_0_35])).
% 0.21/0.38  cnf(c_0_42, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  cnf(c_0_43, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk3_0)),esk2_1(k1_mcart_1(esk3_0)))=k1_mcart_1(esk3_0)), inference(rw,[status(thm)],[c_0_33, c_0_36])).
% 0.21/0.38  cnf(c_0_44, negated_conjecture, (esk1_1(esk3_0)=k1_mcart_1(esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_37])).
% 0.21/0.38  cnf(c_0_45, negated_conjecture, (k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk3_0)),X1),X2)!=esk3_0|~r2_hidden(esk2_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk5_0)|~r2_hidden(X2,esk7_0)|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_35]), c_0_39])])).
% 0.21/0.38  cnf(c_0_46, negated_conjecture, (esk2_1(k1_mcart_1(k1_mcart_1(esk3_0)))=k2_mcart_1(k1_mcart_1(k1_mcart_1(esk3_0)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.21/0.38  cnf(c_0_47, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk5_0)), inference(spm,[status(thm)],[c_0_42, c_0_28])).
% 0.21/0.38  cnf(c_0_48, negated_conjecture, (esk2_1(k1_mcart_1(esk3_0))=k2_mcart_1(k1_mcart_1(esk3_0))), inference(spm,[status(thm)],[c_0_40, c_0_43])).
% 0.21/0.38  cnf(c_0_49, negated_conjecture, (k4_tarski(k1_mcart_1(esk3_0),esk2_1(esk3_0))=esk3_0), inference(rw,[status(thm)],[c_0_37, c_0_44])).
% 0.21/0.38  cnf(c_0_50, negated_conjecture, (k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk3_0)),X1),X2)!=esk3_0|~r2_hidden(X2,esk7_0)|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.21/0.38  cnf(c_0_51, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk3_0)),k2_mcart_1(k1_mcart_1(esk3_0)))=k1_mcart_1(esk3_0)), inference(rw,[status(thm)],[c_0_43, c_0_48])).
% 0.21/0.38  cnf(c_0_52, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(esk3_0)),esk6_0)), inference(spm,[status(thm)],[c_0_42, c_0_22])).
% 0.21/0.38  cnf(c_0_53, negated_conjecture, (esk2_1(esk3_0)=k2_mcart_1(esk3_0)), inference(spm,[status(thm)],[c_0_40, c_0_49])).
% 0.21/0.38  cnf(c_0_54, negated_conjecture, (k4_tarski(k1_mcart_1(esk3_0),X1)!=esk3_0|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 0.21/0.38  cnf(c_0_55, negated_conjecture, (k4_tarski(k1_mcart_1(esk3_0),k2_mcart_1(esk3_0))=esk3_0), inference(rw,[status(thm)],[c_0_49, c_0_53])).
% 0.21/0.38  cnf(c_0_56, negated_conjecture, (r2_hidden(k2_mcart_1(esk3_0),esk7_0)), inference(spm,[status(thm)],[c_0_42, c_0_18])).
% 0.21/0.38  cnf(c_0_57, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 58
% 0.21/0.38  # Proof object clause steps            : 41
% 0.21/0.38  # Proof object formula steps           : 17
% 0.21/0.38  # Proof object conjectures             : 33
% 0.21/0.38  # Proof object clause conjectures      : 30
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 11
% 0.21/0.38  # Proof object initial formulas used   : 8
% 0.21/0.38  # Proof object generating inferences   : 18
% 0.21/0.38  # Proof object simplifying inferences  : 20
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 8
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 11
% 0.21/0.38  # Removed in clause preprocessing      : 3
% 0.21/0.38  # Initial clauses in saturation        : 8
% 0.21/0.38  # Processed clauses                    : 60
% 0.21/0.38  # ...of these trivial                  : 0
% 0.21/0.38  # ...subsumed                          : 8
% 0.21/0.38  # ...remaining for further processing  : 52
% 0.21/0.38  # Other redundant clauses eliminated   : 0
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 18
% 0.21/0.38  # Generated clauses                    : 61
% 0.21/0.38  # ...of the previous two non-trivial   : 76
% 0.21/0.38  # Contextual simplify-reflections      : 0
% 0.21/0.38  # Paramodulations                      : 61
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 0
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 26
% 0.21/0.38  #    Positive orientable unit clauses  : 18
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 0
% 0.21/0.38  #    Non-unit-clauses                  : 8
% 0.21/0.38  # Current number of unprocessed clauses: 2
% 0.21/0.38  # ...number of literals in the above   : 5
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 29
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 124
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 44
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 8
% 0.21/0.38  # Unit Clause-clause subsumption calls : 0
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 15
% 0.21/0.38  # BW rewrite match successes           : 15
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 2941
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.029 s
% 0.21/0.38  # System time              : 0.005 s
% 0.21/0.38  # Total time               : 0.034 s
% 0.21/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
