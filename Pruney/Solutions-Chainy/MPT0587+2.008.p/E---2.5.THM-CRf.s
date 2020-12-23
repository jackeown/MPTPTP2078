%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:01 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 104 expanded)
%              Number of clauses        :   25 (  49 expanded)
%              Number of leaves         :    8 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  109 ( 256 expanded)
%              Number of equality atoms :   39 (  91 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t191_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,k6_subset_1(k1_relat_1(X2),X1))) = k6_subset_1(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k1_relat_1(k7_relat_1(X2,k6_subset_1(k1_relat_1(X2),X1))) = k6_subset_1(k1_relat_1(X2),X1) ) ),
    inference(assume_negation,[status(cth)],[t191_relat_1])).

fof(c_0_9,plain,(
    ! [X25,X26,X27] :
      ( ( r2_hidden(X25,X26)
        | ~ r2_hidden(X25,k1_relat_1(k7_relat_1(X27,X26)))
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(X25,k1_relat_1(X27))
        | ~ r2_hidden(X25,k1_relat_1(k7_relat_1(X27,X26)))
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(X25,X26)
        | ~ r2_hidden(X25,k1_relat_1(X27))
        | r2_hidden(X25,k1_relat_1(k7_relat_1(X27,X26)))
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & k1_relat_1(k7_relat_1(esk4_0,k6_subset_1(k1_relat_1(esk4_0),esk3_0))) != k6_subset_1(k1_relat_1(esk4_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X23,X24] : k1_setfam_1(k2_tarski(X23,X24)) = k3_xboole_0(X23,X24) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_12,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X14,X15] :
      ( ( ~ r2_hidden(esk2_2(X14,X15),X14)
        | ~ r2_hidden(esk2_2(X14,X15),X15)
        | X14 = X15 )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r2_hidden(esk2_2(X14,X15),X15)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

fof(c_0_16,plain,(
    ! [X17,X18] : k4_xboole_0(X17,X18) = k5_xboole_0(X17,k3_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_17,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(esk4_0,X2))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,X1)) = X2
    | r2_hidden(esk2_2(k1_relat_1(k7_relat_1(esk4_0,X1)),X2),X2)
    | r2_hidden(esk2_2(k1_relat_1(k7_relat_1(esk4_0,X1)),X2),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( X1 = X2
    | ~ r2_hidden(esk2_2(X1,X2),X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,X1)) = X1
    | r2_hidden(esk2_2(k1_relat_1(k7_relat_1(esk4_0,X1)),X1),X1) ),
    inference(ef,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X4)))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_31,plain,(
    ! [X21,X22] : k6_subset_1(X21,X22) = k4_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_32,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,X1)) = X1
    | ~ r2_hidden(esk2_2(k1_relat_1(k7_relat_1(esk4_0,X1)),X1),k1_relat_1(k7_relat_1(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(esk4_0,X2)))
    | ~ r2_hidden(X1,k1_relat_1(esk4_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_14])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X3)))) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,k6_subset_1(k1_relat_1(esk4_0),esk3_0))) != k6_subset_1(k1_relat_1(esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,X1)) = X1
    | ~ r2_hidden(esk2_2(k1_relat_1(k7_relat_1(esk4_0,X1)),X1),k1_relat_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))))) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))
    | r2_hidden(esk2_2(k1_relat_1(k7_relat_1(esk4_0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))))),k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,k5_xboole_0(k1_relat_1(esk4_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),esk3_0))))) != k5_xboole_0(k1_relat_1(esk4_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_36]),c_0_26]),c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,k5_xboole_0(k1_relat_1(esk4_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),X1))))) = k5_xboole_0(k1_relat_1(esk4_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),X1))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:34:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S032I
% 0.13/0.41  # and selection function SelectUnlessUniqMax.
% 0.13/0.41  #
% 0.13/0.41  # Preprocessing time       : 0.028 s
% 0.13/0.41  # Presaturation interreduction done
% 0.13/0.41  
% 0.13/0.41  # Proof found!
% 0.13/0.41  # SZS status Theorem
% 0.13/0.41  # SZS output start CNFRefutation
% 0.13/0.41  fof(t191_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,k6_subset_1(k1_relat_1(X2),X1)))=k6_subset_1(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_relat_1)).
% 0.13/0.41  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 0.13/0.41  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.41  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.41  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 0.13/0.41  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.41  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.13/0.41  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.13/0.41  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,k6_subset_1(k1_relat_1(X2),X1)))=k6_subset_1(k1_relat_1(X2),X1))), inference(assume_negation,[status(cth)],[t191_relat_1])).
% 0.13/0.41  fof(c_0_9, plain, ![X25, X26, X27]:(((r2_hidden(X25,X26)|~r2_hidden(X25,k1_relat_1(k7_relat_1(X27,X26)))|~v1_relat_1(X27))&(r2_hidden(X25,k1_relat_1(X27))|~r2_hidden(X25,k1_relat_1(k7_relat_1(X27,X26)))|~v1_relat_1(X27)))&(~r2_hidden(X25,X26)|~r2_hidden(X25,k1_relat_1(X27))|r2_hidden(X25,k1_relat_1(k7_relat_1(X27,X26)))|~v1_relat_1(X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 0.13/0.41  fof(c_0_10, negated_conjecture, (v1_relat_1(esk4_0)&k1_relat_1(k7_relat_1(esk4_0,k6_subset_1(k1_relat_1(esk4_0),esk3_0)))!=k6_subset_1(k1_relat_1(esk4_0),esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.13/0.41  fof(c_0_11, plain, ![X23, X24]:k1_setfam_1(k2_tarski(X23,X24))=k3_xboole_0(X23,X24), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.41  fof(c_0_12, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.41  cnf(c_0_13, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.41  fof(c_0_15, plain, ![X14, X15]:((~r2_hidden(esk2_2(X14,X15),X14)|~r2_hidden(esk2_2(X14,X15),X15)|X14=X15)&(r2_hidden(esk2_2(X14,X15),X14)|r2_hidden(esk2_2(X14,X15),X15)|X14=X15)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.13/0.41  fof(c_0_16, plain, ![X17, X18]:k4_xboole_0(X17,X18)=k5_xboole_0(X17,k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.41  cnf(c_0_17, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.41  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.41  cnf(c_0_19, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(esk4_0,X2)))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.41  cnf(c_0_20, plain, (r2_hidden(esk2_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.41  fof(c_0_21, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.13/0.41  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.41  cnf(c_0_23, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.41  cnf(c_0_24, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,X1))=X2|r2_hidden(esk2_2(k1_relat_1(k7_relat_1(esk4_0,X1)),X2),X2)|r2_hidden(esk2_2(k1_relat_1(k7_relat_1(esk4_0,X1)),X2),X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.41  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.41  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.41  cnf(c_0_27, plain, (X1=X2|~r2_hidden(esk2_2(X1,X2),X1)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.41  cnf(c_0_28, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,X1))=X1|r2_hidden(esk2_2(k1_relat_1(k7_relat_1(esk4_0,X1)),X1),X1)), inference(ef,[status(thm)],[c_0_24])).
% 0.13/0.41  cnf(c_0_29, plain, (r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(X3))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.41  cnf(c_0_30, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X4)))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.41  fof(c_0_31, plain, ![X21, X22]:k6_subset_1(X21,X22)=k4_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.13/0.41  cnf(c_0_32, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,X1))=X1|~r2_hidden(esk2_2(k1_relat_1(k7_relat_1(esk4_0,X1)),X1),k1_relat_1(k7_relat_1(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.41  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,k1_relat_1(k7_relat_1(esk4_0,X2)))|~r2_hidden(X1,k1_relat_1(esk4_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_29, c_0_14])).
% 0.13/0.41  cnf(c_0_34, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k1_enumset1(X2,X2,X3))))), inference(er,[status(thm)],[c_0_30])).
% 0.13/0.41  cnf(c_0_35, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,k6_subset_1(k1_relat_1(esk4_0),esk3_0)))!=k6_subset_1(k1_relat_1(esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.41  cnf(c_0_36, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.41  cnf(c_0_37, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,X1))=X1|~r2_hidden(esk2_2(k1_relat_1(k7_relat_1(esk4_0,X1)),X1),k1_relat_1(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_28])).
% 0.13/0.41  cnf(c_0_38, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))))=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))|r2_hidden(esk2_2(k1_relat_1(k7_relat_1(esk4_0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))))),k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))),X1)), inference(spm,[status(thm)],[c_0_34, c_0_28])).
% 0.13/0.41  cnf(c_0_39, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,k5_xboole_0(k1_relat_1(esk4_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),esk3_0)))))!=k5_xboole_0(k1_relat_1(esk4_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_36]), c_0_26]), c_0_26])).
% 0.13/0.41  cnf(c_0_40, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,k5_xboole_0(k1_relat_1(esk4_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),X1)))))=k5_xboole_0(k1_relat_1(esk4_0),k1_setfam_1(k1_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),X1)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.41  cnf(c_0_41, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40])]), ['proof']).
% 0.13/0.41  # SZS output end CNFRefutation
% 0.13/0.41  # Proof object total steps             : 42
% 0.13/0.41  # Proof object clause steps            : 25
% 0.13/0.41  # Proof object formula steps           : 17
% 0.13/0.41  # Proof object conjectures             : 15
% 0.13/0.41  # Proof object clause conjectures      : 12
% 0.13/0.41  # Proof object formula conjectures     : 3
% 0.13/0.41  # Proof object initial clauses used    : 11
% 0.13/0.41  # Proof object initial formulas used   : 8
% 0.13/0.41  # Proof object generating inferences   : 8
% 0.13/0.41  # Proof object simplifying inferences  : 11
% 0.13/0.41  # Training examples: 0 positive, 0 negative
% 0.13/0.41  # Parsed axioms                        : 8
% 0.13/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.41  # Initial clauses                      : 17
% 0.13/0.41  # Removed in clause preprocessing      : 4
% 0.13/0.41  # Initial clauses in saturation        : 13
% 0.13/0.41  # Processed clauses                    : 420
% 0.13/0.41  # ...of these trivial                  : 10
% 0.13/0.41  # ...subsumed                          : 285
% 0.13/0.41  # ...remaining for further processing  : 125
% 0.13/0.41  # Other redundant clauses eliminated   : 3
% 0.13/0.41  # Clauses deleted for lack of memory   : 0
% 0.13/0.41  # Backward-subsumed                    : 2
% 0.13/0.41  # Backward-rewritten                   : 9
% 0.13/0.41  # Generated clauses                    : 1531
% 0.13/0.41  # ...of the previous two non-trivial   : 1315
% 0.13/0.41  # Contextual simplify-reflections      : 10
% 0.13/0.41  # Paramodulations                      : 1494
% 0.13/0.41  # Factorizations                       : 34
% 0.13/0.41  # Equation resolutions                 : 3
% 0.13/0.41  # Propositional unsat checks           : 0
% 0.13/0.41  #    Propositional check models        : 0
% 0.13/0.41  #    Propositional check unsatisfiable : 0
% 0.13/0.41  #    Propositional clauses             : 0
% 0.13/0.41  #    Propositional clauses after purity: 0
% 0.13/0.41  #    Propositional unsat core size     : 0
% 0.13/0.41  #    Propositional preprocessing time  : 0.000
% 0.13/0.41  #    Propositional encoding time       : 0.000
% 0.13/0.41  #    Propositional solver time         : 0.000
% 0.13/0.41  #    Success case prop preproc time    : 0.000
% 0.13/0.41  #    Success case prop encoding time   : 0.000
% 0.13/0.41  #    Success case prop solver time     : 0.000
% 0.13/0.41  # Current number of processed clauses  : 98
% 0.13/0.41  #    Positive orientable unit clauses  : 7
% 0.13/0.41  #    Positive unorientable unit clauses: 3
% 0.13/0.41  #    Negative unit clauses             : 2
% 0.13/0.41  #    Non-unit-clauses                  : 86
% 0.13/0.41  # Current number of unprocessed clauses: 893
% 0.13/0.41  # ...number of literals in the above   : 2430
% 0.13/0.41  # Current number of archived formulas  : 0
% 0.13/0.41  # Current number of archived clauses   : 28
% 0.13/0.41  # Clause-clause subsumption calls (NU) : 2915
% 0.13/0.41  # Rec. Clause-clause subsumption calls : 1665
% 0.13/0.41  # Non-unit clause-clause subsumptions  : 181
% 0.13/0.41  # Unit Clause-clause subsumption calls : 331
% 0.13/0.41  # Rewrite failures with RHS unbound    : 104
% 0.13/0.41  # BW rewrite match attempts            : 112
% 0.13/0.41  # BW rewrite match successes           : 21
% 0.13/0.41  # Condensation attempts                : 0
% 0.13/0.41  # Condensation successes               : 0
% 0.13/0.41  # Termbank termtop insertions          : 41936
% 0.13/0.41  
% 0.13/0.41  # -------------------------------------------------
% 0.13/0.41  # User time                : 0.063 s
% 0.13/0.41  # System time              : 0.005 s
% 0.13/0.41  # Total time               : 0.068 s
% 0.13/0.41  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
