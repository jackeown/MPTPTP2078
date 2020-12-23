%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:32 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 384 expanded)
%              Number of clauses        :   39 ( 181 expanded)
%              Number of leaves         :    8 (  93 expanded)
%              Depth                    :   13
%              Number of atoms          :   97 ( 833 expanded)
%              Number of equality atoms :   45 ( 285 expanded)
%              Maximal formula depth    :   18 (   3 average)
%              Maximal clause size      :    6 (   1 average)
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

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

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
    ! [X25,X26,X27,X28] : k4_zfmisc_1(X25,X26,X27,X28) = k2_zfmisc_1(k3_zfmisc_1(X25,X26,X27),X28) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X18,X19,X20] : k3_zfmisc_1(X18,X19,X20) = k2_zfmisc_1(k2_zfmisc_1(X18,X19),X20) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_11,negated_conjecture,(
    ! [X39,X40,X41,X42] :
      ( r2_hidden(esk3_0,k4_zfmisc_1(esk4_0,esk5_0,esk6_0,esk7_0))
      & ( ~ r2_hidden(X39,esk4_0)
        | ~ r2_hidden(X40,esk5_0)
        | ~ r2_hidden(X41,esk6_0)
        | ~ r2_hidden(X42,esk7_0)
        | esk3_0 != k4_mcart_1(X39,X40,X41,X42) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

cnf(c_0_12,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X29,X30,X31] :
      ( ( r2_hidden(k1_mcart_1(X29),X30)
        | ~ r2_hidden(X29,k2_zfmisc_1(X30,X31)) )
      & ( r2_hidden(k2_mcart_1(X29),X31)
        | ~ r2_hidden(X29,k2_zfmisc_1(X30,X31)) ) ) ),
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
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,k2_zfmisc_1(X11,X12))
      | k4_tarski(esk1_1(X10),esk2_1(X10)) = X10 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_21,plain,(
    ! [X32,X33] :
      ( k1_mcart_1(k4_tarski(X32,X33)) = X32
      & k2_mcart_1(k4_tarski(X32,X33)) = X33 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_22,plain,
    ( k4_tarski(esk1_1(X1),esk2_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X21,X22,X23,X24] : k4_mcart_1(X21,X22,X23,X24) = k4_tarski(k3_mcart_1(X21,X22,X23),X24) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_24,plain,(
    ! [X15,X16,X17] : k3_mcart_1(X15,X16,X17) = k4_tarski(k4_tarski(X15,X16),X17) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(esk3_0)),k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_20])).

cnf(c_0_26,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k4_tarski(esk1_1(k1_mcart_1(esk3_0)),esk2_1(k1_mcart_1(esk3_0))) = k1_mcart_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_28,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k4_tarski(esk1_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk2_1(k1_mcart_1(k1_mcart_1(esk3_0)))) = k1_mcart_1(k1_mcart_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( esk1_1(k1_mcart_1(esk3_0)) = k1_mcart_1(k1_mcart_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X2,esk5_0)
    | ~ r2_hidden(X3,esk6_0)
    | ~ r2_hidden(X4,esk7_0)
    | esk3_0 != k4_mcart_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( esk1_1(k1_mcart_1(k1_mcart_1(esk3_0))) = k1_mcart_1(k1_mcart_1(k1_mcart_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_30])).

cnf(c_0_35,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk3_0)),esk2_1(k1_mcart_1(esk3_0))) = k1_mcart_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k4_tarski(esk1_1(esk3_0),esk2_1(esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_38,negated_conjecture,
    ( esk3_0 != k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)
    | ~ r2_hidden(X4,esk7_0)
    | ~ r2_hidden(X3,esk6_0)
    | ~ r2_hidden(X2,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk2_1(k1_mcart_1(k1_mcart_1(esk3_0)))) = k1_mcart_1(k1_mcart_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( esk2_1(k1_mcart_1(esk3_0)) = k2_mcart_1(k1_mcart_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_43,negated_conjecture,
    ( esk1_1(esk3_0) = k1_mcart_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk3_0)),X1),X2) != esk3_0
    | ~ r2_hidden(esk2_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk5_0)
    | ~ r2_hidden(X2,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_45,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk3_0)),k2_mcart_1(k1_mcart_1(esk3_0))) = k1_mcart_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(esk3_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk3_0),esk2_1(esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_37,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk3_0),X1) != esk3_0
    | ~ r2_hidden(esk2_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk5_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

cnf(c_0_49,negated_conjecture,
    ( esk2_1(k1_mcart_1(k1_mcart_1(esk3_0))) = k2_mcart_1(k1_mcart_1(k1_mcart_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_25])).

cnf(c_0_51,negated_conjecture,
    ( esk2_1(esk3_0) = k2_mcart_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk3_0),X1) != esk3_0
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_50])])).

cnf(c_0_53,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk3_0),k2_mcart_1(esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_47,c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk3_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_18])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t83_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:~((r2_hidden(X1,k4_zfmisc_1(X2,X3,X4,X5))&![X6, X7, X8, X9]:~(((((r2_hidden(X6,X2)&r2_hidden(X7,X3))&r2_hidden(X8,X4))&r2_hidden(X9,X5))&X1=k4_mcart_1(X6,X7,X8,X9))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_mcart_1)).
% 0.13/0.37  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.13/0.37  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.13/0.37  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.13/0.37  fof(l139_zfmisc_1, axiom, ![X1, X2, X3]:~((r2_hidden(X1,k2_zfmisc_1(X2,X3))&![X4, X5]:k4_tarski(X4,X5)!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 0.13/0.37  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.13/0.37  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.13/0.37  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.13/0.37  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4, X5]:~((r2_hidden(X1,k4_zfmisc_1(X2,X3,X4,X5))&![X6, X7, X8, X9]:~(((((r2_hidden(X6,X2)&r2_hidden(X7,X3))&r2_hidden(X8,X4))&r2_hidden(X9,X5))&X1=k4_mcart_1(X6,X7,X8,X9)))))), inference(assume_negation,[status(cth)],[t83_mcart_1])).
% 0.13/0.37  fof(c_0_9, plain, ![X25, X26, X27, X28]:k4_zfmisc_1(X25,X26,X27,X28)=k2_zfmisc_1(k3_zfmisc_1(X25,X26,X27),X28), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.13/0.37  fof(c_0_10, plain, ![X18, X19, X20]:k3_zfmisc_1(X18,X19,X20)=k2_zfmisc_1(k2_zfmisc_1(X18,X19),X20), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.13/0.37  fof(c_0_11, negated_conjecture, ![X39, X40, X41, X42]:(r2_hidden(esk3_0,k4_zfmisc_1(esk4_0,esk5_0,esk6_0,esk7_0))&(~r2_hidden(X39,esk4_0)|~r2_hidden(X40,esk5_0)|~r2_hidden(X41,esk6_0)|~r2_hidden(X42,esk7_0)|esk3_0!=k4_mcart_1(X39,X40,X41,X42))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.13/0.37  cnf(c_0_12, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_13, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  fof(c_0_14, plain, ![X29, X30, X31]:((r2_hidden(k1_mcart_1(X29),X30)|~r2_hidden(X29,k2_zfmisc_1(X30,X31)))&(r2_hidden(k2_mcart_1(X29),X31)|~r2_hidden(X29,k2_zfmisc_1(X30,X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (r2_hidden(esk3_0,k4_zfmisc_1(esk4_0,esk5_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_16, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.37  cnf(c_0_17, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (r2_hidden(esk3_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0),esk7_0))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.37  fof(c_0_19, plain, ![X10, X11, X12]:(~r2_hidden(X10,k2_zfmisc_1(X11,X12))|k4_tarski(esk1_1(X10),esk2_1(X10))=X10), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (r2_hidden(k1_mcart_1(esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.37  fof(c_0_21, plain, ![X32, X33]:(k1_mcart_1(k4_tarski(X32,X33))=X32&k2_mcart_1(k4_tarski(X32,X33))=X33), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.13/0.37  cnf(c_0_22, plain, (k4_tarski(esk1_1(X1),esk2_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  fof(c_0_23, plain, ![X21, X22, X23, X24]:k4_mcart_1(X21,X22,X23,X24)=k4_tarski(k3_mcart_1(X21,X22,X23),X24), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.13/0.37  fof(c_0_24, plain, ![X15, X16, X17]:k3_mcart_1(X15,X16,X17)=k4_tarski(k4_tarski(X15,X16),X17), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(esk3_0)),k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_17, c_0_20])).
% 0.13/0.37  cnf(c_0_26, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (k4_tarski(esk1_1(k1_mcart_1(esk3_0)),esk2_1(k1_mcart_1(esk3_0)))=k1_mcart_1(esk3_0)), inference(spm,[status(thm)],[c_0_22, c_0_20])).
% 0.13/0.37  cnf(c_0_28, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.37  cnf(c_0_29, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (k4_tarski(esk1_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk2_1(k1_mcart_1(k1_mcart_1(esk3_0))))=k1_mcart_1(k1_mcart_1(esk3_0))), inference(spm,[status(thm)],[c_0_22, c_0_25])).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, (esk1_1(k1_mcart_1(esk3_0))=k1_mcart_1(k1_mcart_1(esk3_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (~r2_hidden(X1,esk4_0)|~r2_hidden(X2,esk5_0)|~r2_hidden(X3,esk6_0)|~r2_hidden(X4,esk7_0)|esk3_0!=k4_mcart_1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_33, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (esk1_1(k1_mcart_1(k1_mcart_1(esk3_0)))=k1_mcart_1(k1_mcart_1(k1_mcart_1(esk3_0)))), inference(spm,[status(thm)],[c_0_26, c_0_30])).
% 0.13/0.37  cnf(c_0_35, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk3_0)),esk2_1(k1_mcart_1(esk3_0)))=k1_mcart_1(esk3_0)), inference(rw,[status(thm)],[c_0_27, c_0_31])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (k4_tarski(esk1_1(esk3_0),esk2_1(esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_22, c_0_18])).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, (esk3_0!=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)|~r2_hidden(X4,esk7_0)|~r2_hidden(X3,esk6_0)|~r2_hidden(X2,esk5_0)|~r2_hidden(X1,esk4_0)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk2_1(k1_mcart_1(k1_mcart_1(esk3_0))))=k1_mcart_1(k1_mcart_1(esk3_0))), inference(rw,[status(thm)],[c_0_30, c_0_34])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk4_0)), inference(spm,[status(thm)],[c_0_17, c_0_25])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, (esk2_1(k1_mcart_1(esk3_0))=k2_mcart_1(k1_mcart_1(esk3_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.37  cnf(c_0_42, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_43, negated_conjecture, (esk1_1(esk3_0)=k1_mcart_1(esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_37])).
% 0.13/0.37  cnf(c_0_44, negated_conjecture, (k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk3_0)),X1),X2)!=esk3_0|~r2_hidden(esk2_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk5_0)|~r2_hidden(X2,esk7_0)|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.13/0.37  cnf(c_0_45, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk3_0)),k2_mcart_1(k1_mcart_1(esk3_0)))=k1_mcart_1(esk3_0)), inference(rw,[status(thm)],[c_0_36, c_0_41])).
% 0.13/0.37  cnf(c_0_46, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(esk3_0)),esk6_0)), inference(spm,[status(thm)],[c_0_42, c_0_20])).
% 0.13/0.37  cnf(c_0_47, negated_conjecture, (k4_tarski(k1_mcart_1(esk3_0),esk2_1(esk3_0))=esk3_0), inference(rw,[status(thm)],[c_0_37, c_0_43])).
% 0.13/0.37  cnf(c_0_48, negated_conjecture, (k4_tarski(k1_mcart_1(esk3_0),X1)!=esk3_0|~r2_hidden(esk2_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk5_0)|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])])).
% 0.13/0.37  cnf(c_0_49, negated_conjecture, (esk2_1(k1_mcart_1(k1_mcart_1(esk3_0)))=k2_mcart_1(k1_mcart_1(k1_mcart_1(esk3_0)))), inference(spm,[status(thm)],[c_0_35, c_0_39])).
% 0.13/0.37  cnf(c_0_50, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(esk3_0))),esk5_0)), inference(spm,[status(thm)],[c_0_42, c_0_25])).
% 0.13/0.37  cnf(c_0_51, negated_conjecture, (esk2_1(esk3_0)=k2_mcart_1(esk3_0)), inference(spm,[status(thm)],[c_0_35, c_0_47])).
% 0.13/0.37  cnf(c_0_52, negated_conjecture, (k4_tarski(k1_mcart_1(esk3_0),X1)!=esk3_0|~r2_hidden(X1,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_50])])).
% 0.13/0.37  cnf(c_0_53, negated_conjecture, (k4_tarski(k1_mcart_1(esk3_0),k2_mcart_1(esk3_0))=esk3_0), inference(rw,[status(thm)],[c_0_47, c_0_51])).
% 0.13/0.37  cnf(c_0_54, negated_conjecture, (r2_hidden(k2_mcart_1(esk3_0),esk7_0)), inference(spm,[status(thm)],[c_0_42, c_0_18])).
% 0.13/0.37  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 56
% 0.13/0.37  # Proof object clause steps            : 39
% 0.13/0.37  # Proof object formula steps           : 17
% 0.13/0.37  # Proof object conjectures             : 31
% 0.13/0.37  # Proof object clause conjectures      : 28
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 11
% 0.13/0.37  # Proof object initial formulas used   : 8
% 0.13/0.37  # Proof object generating inferences   : 18
% 0.13/0.37  # Proof object simplifying inferences  : 18
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 8
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 11
% 0.13/0.37  # Removed in clause preprocessing      : 4
% 0.13/0.37  # Initial clauses in saturation        : 7
% 0.13/0.37  # Processed clauses                    : 46
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 3
% 0.13/0.37  # ...remaining for further processing  : 43
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 11
% 0.13/0.37  # Generated clauses                    : 30
% 0.13/0.37  # ...of the previous two non-trivial   : 40
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 30
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 25
% 0.13/0.37  #    Positive orientable unit clauses  : 17
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 0
% 0.13/0.37  #    Non-unit-clauses                  : 8
% 0.13/0.37  # Current number of unprocessed clauses: 2
% 0.13/0.37  # ...number of literals in the above   : 4
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 22
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 30
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 3
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.13/0.37  # Unit Clause-clause subsumption calls : 0
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 6
% 0.13/0.37  # BW rewrite match successes           : 6
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1511
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.027 s
% 0.13/0.37  # System time              : 0.005 s
% 0.13/0.37  # Total time               : 0.032 s
% 0.13/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
