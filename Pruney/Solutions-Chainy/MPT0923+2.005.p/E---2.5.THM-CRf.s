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
% DateTime   : Thu Dec  3 11:00:32 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 168 expanded)
%              Number of clauses        :   26 (  76 expanded)
%              Number of leaves         :    8 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   82 ( 389 expanded)
%              Number of equality atoms :   27 (  96 expanded)
%              Maximal formula depth    :   18 (   4 average)
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

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

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
    ! [X36,X37,X38,X39] :
      ( r2_hidden(esk1_0,k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0))
      & ( ~ r2_hidden(X36,esk2_0)
        | ~ r2_hidden(X37,esk3_0)
        | ~ r2_hidden(X38,esk4_0)
        | ~ r2_hidden(X39,esk5_0)
        | esk1_0 != k4_mcart_1(X36,X37,X38,X39) ) ) ),
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
    ( r2_hidden(esk1_0,k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_17,plain,(
    ! [X18,X19,X20,X21] : k4_mcart_1(X18,X19,X20,X21) = k4_tarski(k3_mcart_1(X18,X19,X20),X21) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_18,plain,(
    ! [X12,X13,X14] : k3_mcart_1(X12,X13,X14) = k4_tarski(k4_tarski(X12,X13),X14) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_19,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk1_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X30)
      | ~ r2_hidden(X29,X30)
      | X29 = k4_tarski(k1_mcart_1(X29),k2_mcart_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk1_0),k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_25,plain,(
    ! [X10,X11] : v1_relat_1(k2_zfmisc_1(X10,X11)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X2,esk3_0)
    | ~ r2_hidden(X3,esk4_0)
    | ~ r2_hidden(X4,esk5_0)
    | esk1_0 != k4_mcart_1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(esk1_0)),k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_24])).

cnf(c_0_30,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,negated_conjecture,
    ( esk1_0 != k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)
    | ~ r2_hidden(X4,esk5_0)
    | ~ r2_hidden(X3,esk4_0)
    | ~ r2_hidden(X2,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk1_0))),k2_mcart_1(k1_mcart_1(k1_mcart_1(esk1_0)))) = k1_mcart_1(k1_mcart_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(esk1_0))),esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk1_0))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk1_0)),X1),X2) != esk1_0
    | ~ r2_hidden(X2,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_37,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk1_0)),k2_mcart_1(k1_mcart_1(esk1_0))) = k1_mcart_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_24]),c_0_30])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(esk1_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk1_0),X1) != esk1_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_40,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk1_0),k2_mcart_1(esk1_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_20]),c_0_30])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk1_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_20])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:56:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.027 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t83_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:~((r2_hidden(X1,k4_zfmisc_1(X2,X3,X4,X5))&![X6, X7, X8, X9]:~(((((r2_hidden(X6,X2)&r2_hidden(X7,X3))&r2_hidden(X8,X4))&r2_hidden(X9,X5))&X1=k4_mcart_1(X6,X7,X8,X9))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_mcart_1)).
% 0.12/0.36  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.12/0.36  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.12/0.36  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.12/0.36  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.12/0.36  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.12/0.36  fof(t23_mcart_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,X2)=>X1=k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 0.12/0.36  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.12/0.36  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4, X5]:~((r2_hidden(X1,k4_zfmisc_1(X2,X3,X4,X5))&![X6, X7, X8, X9]:~(((((r2_hidden(X6,X2)&r2_hidden(X7,X3))&r2_hidden(X8,X4))&r2_hidden(X9,X5))&X1=k4_mcart_1(X6,X7,X8,X9)))))), inference(assume_negation,[status(cth)],[t83_mcart_1])).
% 0.12/0.36  fof(c_0_9, plain, ![X22, X23, X24, X25]:k4_zfmisc_1(X22,X23,X24,X25)=k2_zfmisc_1(k3_zfmisc_1(X22,X23,X24),X25), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.12/0.36  fof(c_0_10, plain, ![X15, X16, X17]:k3_zfmisc_1(X15,X16,X17)=k2_zfmisc_1(k2_zfmisc_1(X15,X16),X17), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.12/0.36  fof(c_0_11, negated_conjecture, ![X36, X37, X38, X39]:(r2_hidden(esk1_0,k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0))&(~r2_hidden(X36,esk2_0)|~r2_hidden(X37,esk3_0)|~r2_hidden(X38,esk4_0)|~r2_hidden(X39,esk5_0)|esk1_0!=k4_mcart_1(X36,X37,X38,X39))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.12/0.36  cnf(c_0_12, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.36  cnf(c_0_13, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.36  fof(c_0_14, plain, ![X26, X27, X28]:((r2_hidden(k1_mcart_1(X26),X27)|~r2_hidden(X26,k2_zfmisc_1(X27,X28)))&(r2_hidden(k2_mcart_1(X26),X28)|~r2_hidden(X26,k2_zfmisc_1(X27,X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.12/0.36  cnf(c_0_15, negated_conjecture, (r2_hidden(esk1_0,k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.36  cnf(c_0_16, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.12/0.36  fof(c_0_17, plain, ![X18, X19, X20, X21]:k4_mcart_1(X18,X19,X20,X21)=k4_tarski(k3_mcart_1(X18,X19,X20),X21), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.12/0.36  fof(c_0_18, plain, ![X12, X13, X14]:k3_mcart_1(X12,X13,X14)=k4_tarski(k4_tarski(X12,X13),X14), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.12/0.36  cnf(c_0_19, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.36  cnf(c_0_20, negated_conjecture, (r2_hidden(esk1_0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0),esk5_0))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.12/0.36  cnf(c_0_21, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_22, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.36  fof(c_0_23, plain, ![X29, X30]:(~v1_relat_1(X30)|(~r2_hidden(X29,X30)|X29=k4_tarski(k1_mcart_1(X29),k2_mcart_1(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).
% 0.12/0.36  cnf(c_0_24, negated_conjecture, (r2_hidden(k1_mcart_1(esk1_0),k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.36  fof(c_0_25, plain, ![X10, X11]:v1_relat_1(k2_zfmisc_1(X10,X11)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.12/0.36  cnf(c_0_26, negated_conjecture, (~r2_hidden(X1,esk2_0)|~r2_hidden(X2,esk3_0)|~r2_hidden(X3,esk4_0)|~r2_hidden(X4,esk5_0)|esk1_0!=k4_mcart_1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.36  cnf(c_0_27, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.36  cnf(c_0_28, plain, (X2=k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.36  cnf(c_0_29, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(esk1_0)),k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_19, c_0_24])).
% 0.12/0.36  cnf(c_0_30, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.36  cnf(c_0_31, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.36  cnf(c_0_32, negated_conjecture, (esk1_0!=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)|~r2_hidden(X4,esk5_0)|~r2_hidden(X3,esk4_0)|~r2_hidden(X2,esk3_0)|~r2_hidden(X1,esk2_0)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.36  cnf(c_0_33, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk1_0))),k2_mcart_1(k1_mcart_1(k1_mcart_1(esk1_0))))=k1_mcart_1(k1_mcart_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.12/0.36  cnf(c_0_34, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(esk1_0))),esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_29])).
% 0.12/0.36  cnf(c_0_35, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(esk1_0))),esk2_0)), inference(spm,[status(thm)],[c_0_19, c_0_29])).
% 0.12/0.36  cnf(c_0_36, negated_conjecture, (k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk1_0)),X1),X2)!=esk1_0|~r2_hidden(X2,esk5_0)|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])])).
% 0.12/0.36  cnf(c_0_37, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk1_0)),k2_mcart_1(k1_mcart_1(esk1_0)))=k1_mcart_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_24]), c_0_30])])).
% 0.12/0.36  cnf(c_0_38, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(esk1_0)),esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_24])).
% 0.12/0.36  cnf(c_0_39, negated_conjecture, (k4_tarski(k1_mcart_1(esk1_0),X1)!=esk1_0|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.12/0.36  cnf(c_0_40, negated_conjecture, (k4_tarski(k1_mcart_1(esk1_0),k2_mcart_1(esk1_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_20]), c_0_30])])).
% 0.12/0.36  cnf(c_0_41, negated_conjecture, (r2_hidden(k2_mcart_1(esk1_0),esk5_0)), inference(spm,[status(thm)],[c_0_31, c_0_20])).
% 0.12/0.36  cnf(c_0_42, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 43
% 0.12/0.36  # Proof object clause steps            : 26
% 0.12/0.36  # Proof object formula steps           : 17
% 0.12/0.36  # Proof object conjectures             : 19
% 0.12/0.36  # Proof object clause conjectures      : 16
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 10
% 0.12/0.36  # Proof object initial formulas used   : 8
% 0.12/0.36  # Proof object generating inferences   : 12
% 0.12/0.36  # Proof object simplifying inferences  : 17
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 8
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 10
% 0.12/0.36  # Removed in clause preprocessing      : 4
% 0.12/0.36  # Initial clauses in saturation        : 6
% 0.12/0.36  # Processed clauses                    : 30
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 0
% 0.12/0.36  # ...remaining for further processing  : 30
% 0.12/0.36  # Other redundant clauses eliminated   : 0
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 0
% 0.12/0.36  # Generated clauses                    : 22
% 0.12/0.36  # ...of the previous two non-trivial   : 21
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 22
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 0
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 24
% 0.12/0.36  #    Positive orientable unit clauses  : 11
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 0
% 0.12/0.36  #    Non-unit-clauses                  : 13
% 0.12/0.36  # Current number of unprocessed clauses: 3
% 0.12/0.36  # ...number of literals in the above   : 14
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 10
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 22
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 1
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.36  # Unit Clause-clause subsumption calls : 0
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 1
% 0.12/0.36  # BW rewrite match successes           : 0
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 1307
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.028 s
% 0.12/0.36  # System time              : 0.004 s
% 0.12/0.36  # Total time               : 0.032 s
% 0.12/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
