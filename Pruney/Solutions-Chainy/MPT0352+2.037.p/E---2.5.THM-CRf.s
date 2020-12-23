%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:41 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 188 expanded)
%              Number of clauses        :   26 (  83 expanded)
%              Number of leaves         :    8 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  100 ( 523 expanded)
%              Number of equality atoms :   19 (  84 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t31_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t34_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(c_0_8,plain,(
    ! [X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X11,X10)
        | r1_tarski(X11,X9)
        | X10 != k1_zfmisc_1(X9) )
      & ( ~ r1_tarski(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k1_zfmisc_1(X9) )
      & ( ~ r2_hidden(esk1_2(X13,X14),X14)
        | ~ r1_tarski(esk1_2(X13,X14),X13)
        | X14 = k1_zfmisc_1(X13) )
      & ( r2_hidden(esk1_2(X13,X14),X14)
        | r1_tarski(esk1_2(X13,X14),X13)
        | X14 = k1_zfmisc_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_10,plain,(
    ! [X7,X8] : r1_tarski(k4_xboole_0(X7,X8),X7) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_11,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X17,X16)
        | r2_hidden(X17,X16)
        | v1_xboole_0(X16) )
      & ( ~ r2_hidden(X17,X16)
        | m1_subset_1(X17,X16)
        | v1_xboole_0(X16) )
      & ( ~ m1_subset_1(X17,X16)
        | v1_xboole_0(X17)
        | ~ v1_xboole_0(X16) )
      & ( ~ v1_xboole_0(X17)
        | m1_subset_1(X17,X16)
        | ~ v1_xboole_0(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X20] : ~ v1_xboole_0(k1_zfmisc_1(X20)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,X3)
            <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_subset_1])).

fof(c_0_16,plain,(
    ! [X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | k3_subset_1(X18,X19) = k4_xboole_0(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ( ~ r1_tarski(esk3_0,esk4_0)
      | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) )
    & ( r1_tarski(esk3_0,esk4_0)
      | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_21,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | k3_subset_1(X21,k3_subset_1(X21,X22)) = X22 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_22,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | r1_tarski(k4_xboole_0(X6,X5),k4_xboole_0(X6,X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).

cnf(c_0_23,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_subset_1(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk4_0) = k3_subset_1(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( k4_xboole_0(esk2_0,esk3_0) = k3_subset_1(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k3_subset_1(esk2_0,esk3_0)),k4_xboole_0(X1,k3_subset_1(esk2_0,esk4_0)))
    | r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( k4_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_33]),c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0)
    | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk4_0),k4_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_38])])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_33]),c_0_31]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.19/0.40  # and selection function SelectNewComplexAHP.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.046 s
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.19/0.40  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.40  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.40  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.19/0.40  fof(t31_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 0.19/0.40  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.19/0.40  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.19/0.40  fof(t34_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 0.19/0.40  fof(c_0_8, plain, ![X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X11,X10)|r1_tarski(X11,X9)|X10!=k1_zfmisc_1(X9))&(~r1_tarski(X12,X9)|r2_hidden(X12,X10)|X10!=k1_zfmisc_1(X9)))&((~r2_hidden(esk1_2(X13,X14),X14)|~r1_tarski(esk1_2(X13,X14),X13)|X14=k1_zfmisc_1(X13))&(r2_hidden(esk1_2(X13,X14),X14)|r1_tarski(esk1_2(X13,X14),X13)|X14=k1_zfmisc_1(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.19/0.40  cnf(c_0_9, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  fof(c_0_10, plain, ![X7, X8]:r1_tarski(k4_xboole_0(X7,X8),X7), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.40  fof(c_0_11, plain, ![X16, X17]:(((~m1_subset_1(X17,X16)|r2_hidden(X17,X16)|v1_xboole_0(X16))&(~r2_hidden(X17,X16)|m1_subset_1(X17,X16)|v1_xboole_0(X16)))&((~m1_subset_1(X17,X16)|v1_xboole_0(X17)|~v1_xboole_0(X16))&(~v1_xboole_0(X17)|m1_subset_1(X17,X16)|~v1_xboole_0(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.40  cnf(c_0_12, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_13, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  fof(c_0_14, plain, ![X20]:~v1_xboole_0(k1_zfmisc_1(X20)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.19/0.40  fof(c_0_15, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t31_subset_1])).
% 0.19/0.40  fof(c_0_16, plain, ![X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(X18))|k3_subset_1(X18,X19)=k4_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.19/0.40  cnf(c_0_17, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.40  cnf(c_0_18, plain, (r2_hidden(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.40  cnf(c_0_19, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  fof(c_0_20, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&((~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))&(r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.19/0.40  fof(c_0_21, plain, ![X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|k3_subset_1(X21,k3_subset_1(X21,X22))=X22), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.19/0.40  fof(c_0_22, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|r1_tarski(k4_xboole_0(X6,X5),k4_xboole_0(X6,X4))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_xboole_1])])).
% 0.19/0.40  cnf(c_0_23, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_24, plain, (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.19/0.40  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_26, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.40  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_28, plain, (r1_tarski(k4_xboole_0(X3,X2),k4_xboole_0(X3,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  cnf(c_0_29, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_subset_1(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.40  cnf(c_0_31, negated_conjecture, (k4_xboole_0(esk2_0,esk4_0)=k3_subset_1(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_25])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk4_0))=esk4_0), inference(spm,[status(thm)],[c_0_26, c_0_25])).
% 0.19/0.40  cnf(c_0_33, negated_conjecture, (k4_xboole_0(esk2_0,esk3_0)=k3_subset_1(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_27])).
% 0.19/0.40  cnf(c_0_34, negated_conjecture, (k3_subset_1(esk2_0,k3_subset_1(esk2_0,esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.40  cnf(c_0_35, negated_conjecture, (r1_tarski(k4_xboole_0(X1,k3_subset_1(esk2_0,esk3_0)),k4_xboole_0(X1,k3_subset_1(esk2_0,esk4_0)))|r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (k4_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.19/0.40  cnf(c_0_37, negated_conjecture, (k4_xboole_0(esk2_0,k3_subset_1(esk2_0,esk3_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_33]), c_0_34])).
% 0.19/0.40  cnf(c_0_38, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.19/0.40  cnf(c_0_39, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_40, negated_conjecture, (r1_tarski(k4_xboole_0(X1,esk4_0),k4_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_28, c_0_38])).
% 0.19/0.40  cnf(c_0_41, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_38])])).
% 0.19/0.40  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_33]), c_0_31]), c_0_41]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 43
% 0.19/0.40  # Proof object clause steps            : 26
% 0.19/0.40  # Proof object formula steps           : 17
% 0.19/0.40  # Proof object conjectures             : 18
% 0.19/0.40  # Proof object clause conjectures      : 15
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 11
% 0.19/0.40  # Proof object initial formulas used   : 8
% 0.19/0.40  # Proof object generating inferences   : 14
% 0.19/0.40  # Proof object simplifying inferences  : 9
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 8
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 17
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 17
% 0.19/0.40  # Processed clauses                    : 117
% 0.19/0.40  # ...of these trivial                  : 8
% 0.19/0.40  # ...subsumed                          : 19
% 0.19/0.40  # ...remaining for further processing  : 90
% 0.19/0.40  # Other redundant clauses eliminated   : 0
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 0
% 0.19/0.40  # Backward-rewritten                   : 3
% 0.19/0.40  # Generated clauses                    : 427
% 0.19/0.40  # ...of the previous two non-trivial   : 308
% 0.19/0.40  # Contextual simplify-reflections      : 0
% 0.19/0.40  # Paramodulations                      : 425
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 2
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 87
% 0.19/0.40  #    Positive orientable unit clauses  : 70
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 2
% 0.19/0.40  #    Non-unit-clauses                  : 15
% 0.19/0.40  # Current number of unprocessed clauses: 204
% 0.19/0.40  # ...number of literals in the above   : 259
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 3
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 45
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 24
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.40  # Unit Clause-clause subsumption calls : 46
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 11
% 0.19/0.40  # BW rewrite match successes           : 1
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 5759
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.056 s
% 0.19/0.41  # System time              : 0.005 s
% 0.19/0.41  # Total time               : 0.061 s
% 0.19/0.41  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
