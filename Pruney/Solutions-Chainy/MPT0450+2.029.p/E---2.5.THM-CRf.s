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
% DateTime   : Thu Dec  3 10:48:34 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 102 expanded)
%              Number of clauses        :   28 (  49 expanded)
%              Number of leaves         :    9 (  25 expanded)
%              Depth                    :   13
%              Number of atoms          :   92 ( 233 expanded)
%              Number of equality atoms :   14 (  53 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t31_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(t34_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

fof(t31_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(c_0_9,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_10,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k2_xboole_0(X9,X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X16,X17,X18] : r1_tarski(k2_xboole_0(k3_xboole_0(X16,X17),k3_xboole_0(X16,X18)),k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t31_xboole_1])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_16])).

fof(c_0_19,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X13,X15)
      | r1_tarski(X13,k3_xboole_0(X14,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_22,plain,(
    ! [X19,X20] : r1_tarski(X19,k2_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_23,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | v1_relat_1(k3_xboole_0(X22,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_14])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t34_relat_1])).

fof(c_0_27,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | ~ v1_relat_1(X26)
      | ~ r1_tarski(X25,X26)
      | r1_tarski(k3_relat_1(X25),k3_relat_1(X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).

fof(c_0_28,plain,(
    ! [X11,X12] : r1_tarski(k3_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_29,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_31,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & ~ r1_tarski(k3_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k3_relat_1(esk1_0),k3_relat_1(esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

cnf(c_0_32,plain,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k3_relat_1(esk1_0),k3_relat_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(k2_xboole_0(X1,X2)))
    | ~ v1_relat_1(k2_xboole_0(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_25]),c_0_34])).

cnf(c_0_39,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),X2) = X2 ),
    inference(spm,[status(thm)],[c_0_13,c_0_18])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_relat_1(esk2_0))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k3_relat_1(k3_xboole_0(esk1_0,X1)),k3_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k3_relat_1(k3_xboole_0(X1,esk2_0)),k3_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:26:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.36  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S070I
% 0.19/0.36  # and selection function SelectVGNonCR.
% 0.19/0.36  #
% 0.19/0.36  # Preprocessing time       : 0.026 s
% 0.19/0.36  # Presaturation interreduction done
% 0.19/0.36  
% 0.19/0.36  # Proof found!
% 0.19/0.36  # SZS status Theorem
% 0.19/0.36  # SZS output start CNFRefutation
% 0.19/0.36  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.36  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.36  fof(t31_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 0.19/0.36  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.19/0.36  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.36  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.19/0.36  fof(t34_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relat_1)).
% 0.19/0.36  fof(t31_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 0.19/0.36  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.36  fof(c_0_9, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.36  fof(c_0_10, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k2_xboole_0(X9,X10)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.36  cnf(c_0_11, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.36  fof(c_0_12, plain, ![X16, X17, X18]:r1_tarski(k2_xboole_0(k3_xboole_0(X16,X17),k3_xboole_0(X16,X18)),k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t31_xboole_1])).
% 0.19/0.36  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.36  cnf(c_0_14, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_11])).
% 0.19/0.36  cnf(c_0_15, plain, (r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.36  cnf(c_0_16, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.36  cnf(c_0_17, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.36  cnf(c_0_18, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_16])).
% 0.19/0.36  fof(c_0_19, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X13,X15)|r1_tarski(X13,k3_xboole_0(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.19/0.36  cnf(c_0_20, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.36  cnf(c_0_21, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.36  fof(c_0_22, plain, ![X19, X20]:r1_tarski(X19,k2_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.36  fof(c_0_23, plain, ![X22, X23]:(~v1_relat_1(X22)|v1_relat_1(k3_xboole_0(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.19/0.36  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_14])])).
% 0.19/0.36  cnf(c_0_25, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.36  fof(c_0_26, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t34_relat_1])).
% 0.19/0.36  fof(c_0_27, plain, ![X25, X26]:(~v1_relat_1(X25)|(~v1_relat_1(X26)|(~r1_tarski(X25,X26)|r1_tarski(k3_relat_1(X25),k3_relat_1(X26))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).
% 0.19/0.36  fof(c_0_28, plain, ![X11, X12]:r1_tarski(k3_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.36  cnf(c_0_29, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.36  cnf(c_0_30, plain, (k3_xboole_0(k2_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.36  fof(c_0_31, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&~r1_tarski(k3_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k3_relat_1(esk1_0),k3_relat_1(esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.19/0.36  cnf(c_0_32, plain, (r1_tarski(k3_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.36  cnf(c_0_33, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.36  cnf(c_0_34, plain, (v1_relat_1(X1)|~v1_relat_1(k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.36  cnf(c_0_35, negated_conjecture, (~r1_tarski(k3_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(k3_relat_1(esk1_0),k3_relat_1(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.36  cnf(c_0_36, plain, (r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_relat_1(X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_29])).
% 0.19/0.36  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.36  cnf(c_0_38, plain, (r1_tarski(k3_relat_1(X1),k3_relat_1(k2_xboole_0(X1,X2)))|~v1_relat_1(k2_xboole_0(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_25]), c_0_34])).
% 0.19/0.36  cnf(c_0_39, plain, (k2_xboole_0(k3_xboole_0(X1,X2),X2)=X2), inference(spm,[status(thm)],[c_0_13, c_0_18])).
% 0.19/0.36  cnf(c_0_40, negated_conjecture, (~r1_tarski(k3_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_relat_1(esk2_0))|~r1_tarski(k3_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_35, c_0_21])).
% 0.19/0.36  cnf(c_0_41, negated_conjecture, (r1_tarski(k3_relat_1(k3_xboole_0(esk1_0,X1)),k3_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.36  cnf(c_0_42, plain, (r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_relat_1(X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.36  cnf(c_0_43, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.36  cnf(c_0_44, negated_conjecture, (~r1_tarski(k3_relat_1(k3_xboole_0(esk1_0,esk2_0)),k3_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41])])).
% 0.19/0.36  cnf(c_0_45, negated_conjecture, (r1_tarski(k3_relat_1(k3_xboole_0(X1,esk2_0)),k3_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.36  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45])]), ['proof']).
% 0.19/0.36  # SZS output end CNFRefutation
% 0.19/0.36  # Proof object total steps             : 47
% 0.19/0.36  # Proof object clause steps            : 28
% 0.19/0.36  # Proof object formula steps           : 19
% 0.19/0.36  # Proof object conjectures             : 11
% 0.19/0.36  # Proof object clause conjectures      : 8
% 0.19/0.36  # Proof object formula conjectures     : 3
% 0.19/0.36  # Proof object initial clauses used    : 12
% 0.19/0.36  # Proof object initial formulas used   : 9
% 0.19/0.36  # Proof object generating inferences   : 13
% 0.19/0.36  # Proof object simplifying inferences  : 10
% 0.19/0.36  # Training examples: 0 positive, 0 negative
% 0.19/0.36  # Parsed axioms                        : 12
% 0.19/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.36  # Initial clauses                      : 16
% 0.19/0.36  # Removed in clause preprocessing      : 0
% 0.19/0.36  # Initial clauses in saturation        : 16
% 0.19/0.36  # Processed clauses                    : 158
% 0.19/0.36  # ...of these trivial                  : 8
% 0.19/0.36  # ...subsumed                          : 46
% 0.19/0.36  # ...remaining for further processing  : 104
% 0.19/0.36  # Other redundant clauses eliminated   : 2
% 0.19/0.36  # Clauses deleted for lack of memory   : 0
% 0.19/0.36  # Backward-subsumed                    : 2
% 0.19/0.36  # Backward-rewritten                   : 2
% 0.19/0.36  # Generated clauses                    : 528
% 0.19/0.36  # ...of the previous two non-trivial   : 346
% 0.19/0.36  # Contextual simplify-reflections      : 2
% 0.19/0.36  # Paramodulations                      : 526
% 0.19/0.36  # Factorizations                       : 0
% 0.19/0.36  # Equation resolutions                 : 2
% 0.19/0.36  # Propositional unsat checks           : 0
% 0.19/0.36  #    Propositional check models        : 0
% 0.19/0.36  #    Propositional check unsatisfiable : 0
% 0.19/0.36  #    Propositional clauses             : 0
% 0.19/0.36  #    Propositional clauses after purity: 0
% 0.19/0.36  #    Propositional unsat core size     : 0
% 0.19/0.36  #    Propositional preprocessing time  : 0.000
% 0.19/0.36  #    Propositional encoding time       : 0.000
% 0.19/0.36  #    Propositional solver time         : 0.000
% 0.19/0.36  #    Success case prop preproc time    : 0.000
% 0.19/0.36  #    Success case prop encoding time   : 0.000
% 0.19/0.36  #    Success case prop solver time     : 0.000
% 0.19/0.36  # Current number of processed clauses  : 83
% 0.19/0.36  #    Positive orientable unit clauses  : 39
% 0.19/0.36  #    Positive unorientable unit clauses: 0
% 0.19/0.36  #    Negative unit clauses             : 1
% 0.19/0.36  #    Non-unit-clauses                  : 43
% 0.19/0.36  # Current number of unprocessed clauses: 219
% 0.19/0.36  # ...number of literals in the above   : 380
% 0.19/0.36  # Current number of archived formulas  : 0
% 0.19/0.36  # Current number of archived clauses   : 19
% 0.19/0.36  # Clause-clause subsumption calls (NU) : 200
% 0.19/0.36  # Rec. Clause-clause subsumption calls : 191
% 0.19/0.36  # Non-unit clause-clause subsumptions  : 50
% 0.19/0.36  # Unit Clause-clause subsumption calls : 53
% 0.19/0.36  # Rewrite failures with RHS unbound    : 0
% 0.19/0.36  # BW rewrite match attempts            : 23
% 0.19/0.36  # BW rewrite match successes           : 2
% 0.19/0.36  # Condensation attempts                : 0
% 0.19/0.36  # Condensation successes               : 0
% 0.19/0.36  # Termbank termtop insertions          : 5807
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.036 s
% 0.19/0.37  # System time              : 0.002 s
% 0.19/0.37  # Total time               : 0.038 s
% 0.19/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
