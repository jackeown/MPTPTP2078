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
% DateTime   : Thu Dec  3 10:31:44 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 243 expanded)
%              Number of clauses        :   37 ( 123 expanded)
%              Number of leaves         :    5 (  60 expanded)
%              Depth                    :   17
%              Number of atoms          :  151 (1192 expanded)
%              Number of equality atoms :   31 ( 234 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t3_xboole_0,conjecture,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(c_0_5,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X12,X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | ~ r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | ~ r2_hidden(esk2_3(X14,X15,X16),X14)
        | ~ r2_hidden(esk2_3(X14,X15,X16),X15)
        | X16 = k3_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X14)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k3_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X15)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k3_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_6,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ~ ( ~ r1_xboole_0(X1,X2)
            & ! [X3] :
                ~ ( r2_hidden(X3,X1)
                  & r2_hidden(X3,X2) ) )
        & ~ ( ? [X3] :
                ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) )
            & r1_xboole_0(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t3_xboole_0])).

cnf(c_0_9,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_7])).

fof(c_0_11,negated_conjecture,(
    ! [X22] :
      ( ( r2_hidden(esk5_0,esk3_0)
        | ~ r1_xboole_0(esk3_0,esk4_0) )
      & ( r2_hidden(esk5_0,esk4_0)
        | ~ r1_xboole_0(esk3_0,esk4_0) )
      & ( r1_xboole_0(esk3_0,esk4_0)
        | ~ r1_xboole_0(esk3_0,esk4_0) )
      & ( r2_hidden(esk5_0,esk3_0)
        | ~ r2_hidden(X22,esk3_0)
        | ~ r2_hidden(X22,esk4_0) )
      & ( r2_hidden(esk5_0,esk4_0)
        | ~ r2_hidden(X22,esk3_0)
        | ~ r2_hidden(X22,esk4_0) )
      & ( r1_xboole_0(esk3_0,esk4_0)
        | ~ r2_hidden(X22,esk3_0)
        | ~ r2_hidden(X22,esk4_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( X1 = k3_xboole_0(esk3_0,X2)
    | r2_hidden(esk2_3(esk3_0,X2,X1),X1)
    | r2_hidden(esk5_0,esk3_0)
    | ~ r2_hidden(esk2_3(esk3_0,X2,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( X1 = k3_xboole_0(esk3_0,esk4_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,X1),X1)
    | r2_hidden(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( X1 = k3_xboole_0(esk3_0,X2)
    | r2_hidden(esk2_3(esk3_0,X2,X1),X1)
    | r2_hidden(esk5_0,esk4_0)
    | ~ r2_hidden(esk2_3(esk3_0,X2,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk2_3(esk3_0,esk4_0,k1_xboole_0),X1)
    | r2_hidden(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( X1 = k3_xboole_0(esk3_0,esk4_0)
    | r2_hidden(esk2_3(esk3_0,esk4_0,X1),X1)
    | r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_7])).

fof(c_0_26,plain,(
    ! [X18,X19] :
      ( ( ~ r1_xboole_0(X18,X19)
        | k3_xboole_0(X18,X19) = k1_xboole_0 )
      & ( k3_xboole_0(X18,X19) != k1_xboole_0
        | r1_xboole_0(X18,X19) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_27,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk5_0,esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk2_3(esk3_0,esk4_0,k1_xboole_0),X1)
    | r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_25])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0)
    | ~ r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk5_0,esk4_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_14])).

cnf(c_0_36,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0)
    | ~ r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_35]),c_0_36])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_40,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k1_xboole_0
    | ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0)
    | ~ r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_38])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk5_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_34])])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_45]),c_0_14])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:52:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.19/0.39  # and selection function SelectNewComplexAHP.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.027 s
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.19/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.39  fof(t3_xboole_0, conjecture, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.39  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.39  fof(c_0_5, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X12,X9)|~r2_hidden(X12,X11)|X11!=k3_xboole_0(X9,X10))&(r2_hidden(X12,X10)|~r2_hidden(X12,X11)|X11!=k3_xboole_0(X9,X10)))&(~r2_hidden(X13,X9)|~r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k3_xboole_0(X9,X10)))&((~r2_hidden(esk2_3(X14,X15,X16),X16)|(~r2_hidden(esk2_3(X14,X15,X16),X14)|~r2_hidden(esk2_3(X14,X15,X16),X15))|X16=k3_xboole_0(X14,X15))&((r2_hidden(esk2_3(X14,X15,X16),X14)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k3_xboole_0(X14,X15))&(r2_hidden(esk2_3(X14,X15,X16),X15)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k3_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.19/0.39  fof(c_0_6, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.39  cnf(c_0_7, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2))))), inference(assume_negation,[status(cth)],[t3_xboole_0])).
% 0.19/0.39  cnf(c_0_9, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.39  cnf(c_0_10, plain, (k3_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_7])).
% 0.19/0.39  fof(c_0_11, negated_conjecture, ![X22]:((((r2_hidden(esk5_0,esk3_0)|~r1_xboole_0(esk3_0,esk4_0))&(r2_hidden(esk5_0,esk4_0)|~r1_xboole_0(esk3_0,esk4_0)))&(r1_xboole_0(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,esk4_0)))&(((r2_hidden(esk5_0,esk3_0)|(~r2_hidden(X22,esk3_0)|~r2_hidden(X22,esk4_0)))&(r2_hidden(esk5_0,esk4_0)|(~r2_hidden(X22,esk3_0)|~r2_hidden(X22,esk4_0))))&(r1_xboole_0(esk3_0,esk4_0)|(~r2_hidden(X22,esk3_0)|~r2_hidden(X22,esk4_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).
% 0.19/0.39  cnf(c_0_12, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  cnf(c_0_13, plain, (k3_xboole_0(X1,X2)=X2|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.19/0.39  cnf(c_0_14, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.39  cnf(c_0_15, negated_conjecture, (r2_hidden(esk5_0,esk3_0)|~r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_16, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_18, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.39  cnf(c_0_19, negated_conjecture, (X1=k3_xboole_0(esk3_0,X2)|r2_hidden(esk2_3(esk3_0,X2,X1),X1)|r2_hidden(esk5_0,esk3_0)|~r2_hidden(esk2_3(esk3_0,X2,X1),esk4_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.39  cnf(c_0_20, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|~r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_21, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.39  cnf(c_0_22, negated_conjecture, (X1=k3_xboole_0(esk3_0,esk4_0)|r2_hidden(esk2_3(esk3_0,esk4_0,X1),X1)|r2_hidden(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_7])).
% 0.19/0.39  cnf(c_0_23, negated_conjecture, (X1=k3_xboole_0(esk3_0,X2)|r2_hidden(esk2_3(esk3_0,X2,X1),X1)|r2_hidden(esk5_0,esk4_0)|~r2_hidden(esk2_3(esk3_0,X2,X1),esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_16])).
% 0.19/0.39  cnf(c_0_24, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=k1_xboole_0|r2_hidden(esk2_3(esk3_0,esk4_0,k1_xboole_0),X1)|r2_hidden(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.39  cnf(c_0_25, negated_conjecture, (X1=k3_xboole_0(esk3_0,esk4_0)|r2_hidden(esk2_3(esk3_0,esk4_0,X1),X1)|r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_7])).
% 0.19/0.39  fof(c_0_26, plain, ![X18, X19]:((~r1_xboole_0(X18,X19)|k3_xboole_0(X18,X19)=k1_xboole_0)&(k3_xboole_0(X18,X19)!=k1_xboole_0|r1_xboole_0(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.39  cnf(c_0_27, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=k1_xboole_0|r2_hidden(esk5_0,esk3_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_9, c_0_24])).
% 0.19/0.39  cnf(c_0_28, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=k1_xboole_0|r2_hidden(esk2_3(esk3_0,esk4_0,k1_xboole_0),X1)|r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_25])).
% 0.19/0.39  cnf(c_0_29, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.39  cnf(c_0_30, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=k1_xboole_0|r2_hidden(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_14])).
% 0.19/0.39  cnf(c_0_31, negated_conjecture, (r2_hidden(esk5_0,esk3_0)|~r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_32, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=k1_xboole_0|r2_hidden(esk5_0,esk4_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_9, c_0_28])).
% 0.19/0.39  cnf(c_0_33, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)|~r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_34, negated_conjecture, (r2_hidden(esk5_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.19/0.39  cnf(c_0_35, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=k1_xboole_0|r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_32, c_0_14])).
% 0.19/0.39  cnf(c_0_36, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)|~r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.39  cnf(c_0_37, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.39  cnf(c_0_38, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_35]), c_0_36])).
% 0.19/0.39  cnf(c_0_39, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  cnf(c_0_40, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (r2_hidden(X1,X2)|X2!=k1_xboole_0|~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.39  cnf(c_0_42, negated_conjecture, (r2_hidden(esk5_0,esk4_0)|~r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_43, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(er,[status(thm)],[c_0_41])).
% 0.19/0.39  cnf(c_0_44, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_38])])).
% 0.19/0.39  cnf(c_0_45, negated_conjecture, (r2_hidden(esk5_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_34])])).
% 0.19/0.39  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_45]), c_0_14])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 47
% 0.19/0.39  # Proof object clause steps            : 37
% 0.19/0.39  # Proof object formula steps           : 10
% 0.19/0.39  # Proof object conjectures             : 27
% 0.19/0.39  # Proof object clause conjectures      : 24
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 13
% 0.19/0.39  # Proof object initial formulas used   : 5
% 0.19/0.39  # Proof object generating inferences   : 23
% 0.19/0.39  # Proof object simplifying inferences  : 8
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 5
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 17
% 0.19/0.39  # Removed in clause preprocessing      : 1
% 0.19/0.39  # Initial clauses in saturation        : 16
% 0.19/0.39  # Processed clauses                    : 440
% 0.19/0.39  # ...of these trivial                  : 5
% 0.19/0.39  # ...subsumed                          : 300
% 0.19/0.39  # ...remaining for further processing  : 135
% 0.19/0.39  # Other redundant clauses eliminated   : 20
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 10
% 0.19/0.39  # Backward-rewritten                   : 34
% 0.19/0.39  # Generated clauses                    : 1810
% 0.19/0.39  # ...of the previous two non-trivial   : 1240
% 0.19/0.39  # Contextual simplify-reflections      : 4
% 0.19/0.39  # Paramodulations                      : 1775
% 0.19/0.39  # Factorizations                       : 6
% 0.19/0.39  # Equation resolutions                 : 29
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 91
% 0.19/0.39  #    Positive orientable unit clauses  : 16
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 8
% 0.19/0.39  #    Non-unit-clauses                  : 67
% 0.19/0.39  # Current number of unprocessed clauses: 787
% 0.19/0.39  # ...number of literals in the above   : 2736
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 44
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 2322
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 1827
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 270
% 0.19/0.39  # Unit Clause-clause subsumption calls : 11
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 10
% 0.19/0.39  # BW rewrite match successes           : 4
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 17273
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.052 s
% 0.19/0.39  # System time              : 0.003 s
% 0.19/0.39  # Total time               : 0.055 s
% 0.19/0.39  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
