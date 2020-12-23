%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:02 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 177 expanded)
%              Number of clauses        :   21 (  86 expanded)
%              Number of leaves         :    5 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  125 ( 632 expanded)
%              Number of equality atoms :   26 ( 110 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t62_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_5,plain,(
    ! [X11] :
      ( ~ v1_xboole_0(X11)
      | v1_relat_1(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_6,plain,(
    ! [X12,X13,X14,X15,X16,X18,X19,X20,X23] :
      ( ( r2_hidden(k4_tarski(X15,esk2_5(X12,X13,X14,X15,X16)),X12)
        | ~ r2_hidden(k4_tarski(X15,X16),X14)
        | X14 != k5_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(esk2_5(X12,X13,X14,X15,X16),X16),X13)
        | ~ r2_hidden(k4_tarski(X15,X16),X14)
        | X14 != k5_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(X18,X20),X12)
        | ~ r2_hidden(k4_tarski(X20,X19),X13)
        | r2_hidden(k4_tarski(X18,X19),X14)
        | X14 != k5_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(esk3_3(X12,X13,X14),esk4_3(X12,X13,X14)),X14)
        | ~ r2_hidden(k4_tarski(esk3_3(X12,X13,X14),X23),X12)
        | ~ r2_hidden(k4_tarski(X23,esk4_3(X12,X13,X14)),X13)
        | X14 = k5_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(esk3_3(X12,X13,X14),esk5_3(X12,X13,X14)),X12)
        | r2_hidden(k4_tarski(esk3_3(X12,X13,X14),esk4_3(X12,X13,X14)),X14)
        | X14 = k5_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(esk5_3(X12,X13,X14),esk4_3(X12,X13,X14)),X13)
        | r2_hidden(k4_tarski(esk3_3(X12,X13,X14),esk4_3(X12,X13,X14)),X14)
        | X14 = k5_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

cnf(c_0_7,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
          & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t62_relat_1])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),esk5_3(X1,X2,X3)),X1)
    | r2_hidden(k4_tarski(esk3_3(X1,X2,X3),esk4_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & ( k5_relat_1(k1_xboole_0,esk6_0) != k1_xboole_0
      | k5_relat_1(esk6_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_13,plain,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(esk3_3(X1,X2,k1_xboole_0),esk4_3(X1,X2,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(esk3_3(X1,X2,k1_xboole_0),esk5_3(X1,X2,k1_xboole_0)),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_16,negated_conjecture,
    ( k5_relat_1(X1,esk6_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk3_3(X1,esk6_0,k1_xboole_0),esk4_3(X1,esk6_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(esk3_3(X1,esk6_0,k1_xboole_0),esk5_3(X1,esk6_0,k1_xboole_0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X1,esk2_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk6_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk3_3(k1_xboole_0,esk6_0,k1_xboole_0),esk5_3(k1_xboole_0,esk6_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(esk3_3(k1_xboole_0,esk6_0,k1_xboole_0),esk4_3(k1_xboole_0,esk6_0,k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_11])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,esk2_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk6_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk3_3(k1_xboole_0,esk6_0,k1_xboole_0),esk4_3(k1_xboole_0,esk6_0,k1_xboole_0)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_8])])).

cnf(c_0_22,plain,
    ( ~ v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_20]),c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk6_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_21]),c_0_8])])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,X2,X3),esk4_3(X1,X2,X3)),X2)
    | r2_hidden(k4_tarski(esk3_3(X1,X2,X3),esk4_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,X2),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_11]),c_0_14]),c_0_8])])).

cnf(c_0_26,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk6_0) != k1_xboole_0
    | k5_relat_1(esk6_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,plain,
    ( k5_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(esk5_3(X1,X2,k1_xboole_0),esk4_3(X1,X2,k1_xboole_0)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_11]),c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( k5_relat_1(esk6_0,k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_23])])).

cnf(c_0_29,plain,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_11]),c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_14])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:04:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.049 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.19/0.41  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 0.19/0.41  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.41  fof(t62_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 0.19/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.41  fof(c_0_5, plain, ![X11]:(~v1_xboole_0(X11)|v1_relat_1(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.19/0.41  fof(c_0_6, plain, ![X12, X13, X14, X15, X16, X18, X19, X20, X23]:((((r2_hidden(k4_tarski(X15,esk2_5(X12,X13,X14,X15,X16)),X12)|~r2_hidden(k4_tarski(X15,X16),X14)|X14!=k5_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X13)|~v1_relat_1(X12))&(r2_hidden(k4_tarski(esk2_5(X12,X13,X14,X15,X16),X16),X13)|~r2_hidden(k4_tarski(X15,X16),X14)|X14!=k5_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X13)|~v1_relat_1(X12)))&(~r2_hidden(k4_tarski(X18,X20),X12)|~r2_hidden(k4_tarski(X20,X19),X13)|r2_hidden(k4_tarski(X18,X19),X14)|X14!=k5_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X13)|~v1_relat_1(X12)))&((~r2_hidden(k4_tarski(esk3_3(X12,X13,X14),esk4_3(X12,X13,X14)),X14)|(~r2_hidden(k4_tarski(esk3_3(X12,X13,X14),X23),X12)|~r2_hidden(k4_tarski(X23,esk4_3(X12,X13,X14)),X13))|X14=k5_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X13)|~v1_relat_1(X12))&((r2_hidden(k4_tarski(esk3_3(X12,X13,X14),esk5_3(X12,X13,X14)),X12)|r2_hidden(k4_tarski(esk3_3(X12,X13,X14),esk4_3(X12,X13,X14)),X14)|X14=k5_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X13)|~v1_relat_1(X12))&(r2_hidden(k4_tarski(esk5_3(X12,X13,X14),esk4_3(X12,X13,X14)),X13)|r2_hidden(k4_tarski(esk3_3(X12,X13,X14),esk4_3(X12,X13,X14)),X14)|X14=k5_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X13)|~v1_relat_1(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.19/0.41  cnf(c_0_7, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.41  cnf(c_0_8, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.41  fof(c_0_9, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t62_relat_1])).
% 0.19/0.41  cnf(c_0_10, plain, (r2_hidden(k4_tarski(esk3_3(X1,X2,X3),esk5_3(X1,X2,X3)),X1)|r2_hidden(k4_tarski(esk3_3(X1,X2,X3),esk4_3(X1,X2,X3)),X3)|X3=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.41  cnf(c_0_11, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.19/0.41  fof(c_0_12, negated_conjecture, (v1_relat_1(esk6_0)&(k5_relat_1(k1_xboole_0,esk6_0)!=k1_xboole_0|k5_relat_1(esk6_0,k1_xboole_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.19/0.41  cnf(c_0_13, plain, (k5_relat_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(esk3_3(X1,X2,k1_xboole_0),esk4_3(X1,X2,k1_xboole_0)),k1_xboole_0)|r2_hidden(k4_tarski(esk3_3(X1,X2,k1_xboole_0),esk5_3(X1,X2,k1_xboole_0)),X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.41  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  fof(c_0_15, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.41  cnf(c_0_16, negated_conjecture, (k5_relat_1(X1,esk6_0)=k1_xboole_0|r2_hidden(k4_tarski(esk3_3(X1,esk6_0,k1_xboole_0),esk4_3(X1,esk6_0,k1_xboole_0)),k1_xboole_0)|r2_hidden(k4_tarski(esk3_3(X1,esk6_0,k1_xboole_0),esk5_3(X1,esk6_0,k1_xboole_0)),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.41  cnf(c_0_17, plain, (r2_hidden(k4_tarski(X1,esk2_5(X2,X3,X4,X1,X5)),X2)|~r2_hidden(k4_tarski(X1,X5),X4)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.41  cnf(c_0_18, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.41  cnf(c_0_19, negated_conjecture, (k5_relat_1(k1_xboole_0,esk6_0)=k1_xboole_0|r2_hidden(k4_tarski(esk3_3(k1_xboole_0,esk6_0,k1_xboole_0),esk5_3(k1_xboole_0,esk6_0,k1_xboole_0)),k1_xboole_0)|r2_hidden(k4_tarski(esk3_3(k1_xboole_0,esk6_0,k1_xboole_0),esk4_3(k1_xboole_0,esk6_0,k1_xboole_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_16, c_0_11])).
% 0.19/0.41  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X1,esk2_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)|~v1_relat_1(k5_relat_1(X2,X3))|~v1_relat_1(X3)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))), inference(er,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_21, negated_conjecture, (k5_relat_1(k1_xboole_0,esk6_0)=k1_xboole_0|r2_hidden(k4_tarski(esk3_3(k1_xboole_0,esk6_0,k1_xboole_0),esk4_3(k1_xboole_0,esk6_0,k1_xboole_0)),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_8])])).
% 0.19/0.41  cnf(c_0_22, plain, (~v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))|~v1_xboole_0(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_20]), c_0_7])).
% 0.19/0.41  cnf(c_0_23, negated_conjecture, (k5_relat_1(k1_xboole_0,esk6_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_21]), c_0_8])])).
% 0.19/0.41  cnf(c_0_24, plain, (r2_hidden(k4_tarski(esk5_3(X1,X2,X3),esk4_3(X1,X2,X3)),X2)|r2_hidden(k4_tarski(esk3_3(X1,X2,X3),esk4_3(X1,X2,X3)),X3)|X3=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.41  cnf(c_0_25, negated_conjecture, (~r2_hidden(k4_tarski(X1,X2),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_11]), c_0_14]), c_0_8])])).
% 0.19/0.41  cnf(c_0_26, negated_conjecture, (k5_relat_1(k1_xboole_0,esk6_0)!=k1_xboole_0|k5_relat_1(esk6_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_27, plain, (k5_relat_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(esk5_3(X1,X2,k1_xboole_0),esk4_3(X1,X2,k1_xboole_0)),X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_11]), c_0_25])).
% 0.19/0.41  cnf(c_0_28, negated_conjecture, (k5_relat_1(esk6_0,k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_23])])).
% 0.19/0.41  cnf(c_0_29, plain, (k5_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_11]), c_0_25])).
% 0.19/0.41  cnf(c_0_30, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_14])]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 31
% 0.19/0.41  # Proof object clause steps            : 21
% 0.19/0.41  # Proof object formula steps           : 10
% 0.19/0.41  # Proof object conjectures             : 12
% 0.19/0.41  # Proof object clause conjectures      : 9
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 8
% 0.19/0.41  # Proof object initial formulas used   : 5
% 0.19/0.41  # Proof object generating inferences   : 11
% 0.19/0.41  # Proof object simplifying inferences  : 16
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 5
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 12
% 0.19/0.41  # Removed in clause preprocessing      : 0
% 0.19/0.41  # Initial clauses in saturation        : 12
% 0.19/0.41  # Processed clauses                    : 117
% 0.19/0.41  # ...of these trivial                  : 0
% 0.19/0.41  # ...subsumed                          : 24
% 0.19/0.41  # ...remaining for further processing  : 93
% 0.19/0.41  # Other redundant clauses eliminated   : 3
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 5
% 0.19/0.41  # Backward-rewritten                   : 9
% 0.19/0.41  # Generated clauses                    : 216
% 0.19/0.41  # ...of the previous two non-trivial   : 174
% 0.19/0.41  # Contextual simplify-reflections      : 5
% 0.19/0.41  # Paramodulations                      : 212
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 3
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 63
% 0.19/0.41  #    Positive orientable unit clauses  : 4
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 2
% 0.19/0.41  #    Non-unit-clauses                  : 57
% 0.19/0.41  # Current number of unprocessed clauses: 80
% 0.19/0.41  # ...number of literals in the above   : 659
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 27
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 2083
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 894
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 23
% 0.19/0.41  # Unit Clause-clause subsumption calls : 34
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 1
% 0.19/0.41  # BW rewrite match successes           : 1
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 8319
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.070 s
% 0.19/0.41  # System time              : 0.004 s
% 0.19/0.41  # Total time               : 0.075 s
% 0.19/0.41  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
