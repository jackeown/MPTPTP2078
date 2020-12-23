%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:30 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 202 expanded)
%              Number of clauses        :   34 (  89 expanded)
%              Number of leaves         :    8 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  115 ( 390 expanded)
%              Number of equality atoms :   50 ( 217 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t213_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k6_subset_1(k1_relat_1(X2),k1_relat_1(k7_relat_1(X2,X1))) = k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t212_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1))) = k6_subset_1(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k6_subset_1(k1_relat_1(X2),k1_relat_1(k7_relat_1(X2,X1))) = k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1))) ) ),
    inference(assume_negation,[status(cth)],[t213_relat_1])).

fof(c_0_9,plain,(
    ! [X14,X15] : k4_xboole_0(X14,X15) = k5_xboole_0(X14,k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_10,plain,(
    ! [X22,X23] : k1_setfam_1(k2_tarski(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & k6_subset_1(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0))) != k1_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_12,plain,(
    ! [X20,X21] : k6_subset_1(X20,X21) = k4_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_16,negated_conjecture,
    ( k6_subset_1(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0))) != k1_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | k1_relat_1(k6_subset_1(X25,k7_relat_1(X25,X24))) = k6_subset_1(k1_relat_1(X25),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t212_relat_1])])).

fof(c_0_21,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | k1_relat_1(k7_relat_1(X27,X26)) = k3_xboole_0(k1_relat_1(X27),X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_22,negated_conjecture,
    ( k5_xboole_0(k1_relat_1(esk3_0),k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0))))) != k1_relat_1(k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,k7_relat_1(esk3_0,esk2_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17]),c_0_18]),c_0_18])).

cnf(c_0_23,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_19,c_0_14])).

cnf(c_0_24,plain,
    ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X2))) = k6_subset_1(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X18,X19] : k2_tarski(X18,X19) = k2_tarski(X19,X18) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_26,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_3(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)),X1),k1_relat_1(esk3_0))
    | r2_hidden(esk1_3(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)),X1),X1)
    | k5_xboole_0(k1_relat_1(esk3_0),X1) != k1_relat_1(k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,k7_relat_1(esk3_0,esk2_0))))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( k1_relat_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k7_relat_1(X1,X2))))) = k5_xboole_0(k1_relat_1(X1),k1_setfam_1(k2_tarski(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_17]),c_0_17]),c_0_18]),c_0_18])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_26,c_0_14])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k2_tarski(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_27,c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk1_3(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)),X1),k1_relat_1(esk3_0))
    | r2_hidden(esk1_3(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)),X1),X1)
    | k5_xboole_0(k1_relat_1(esk3_0),X1) != k5_xboole_0(k1_relat_1(esk3_0),k1_setfam_1(k2_tarski(esk2_0,k1_relat_1(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])])).

cnf(c_0_36,plain,
    ( k1_setfam_1(k2_tarski(X1,k1_relat_1(X2))) = k1_relat_1(k7_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_30])).

cnf(c_0_37,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_14])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk1_3(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)),X1),k1_relat_1(esk3_0))
    | r2_hidden(esk1_3(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)),X1),X1)
    | k5_xboole_0(k1_relat_1(esk3_0),X1) != k5_xboole_0(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_31])])).

cnf(c_0_41,plain,
    ( X3 = k1_setfam_1(k2_tarski(X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_37,c_0_14])).

cnf(c_0_42,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_38])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk1_3(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)),k1_relat_1(k7_relat_1(esk3_0,esk2_0))),k1_relat_1(k7_relat_1(esk3_0,esk2_0)))
    | r2_hidden(esk1_3(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)),k1_relat_1(k7_relat_1(esk3_0,esk2_0))),k1_relat_1(esk3_0)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_45,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk1_3(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)),k1_relat_1(k7_relat_1(esk3_0,esk2_0))),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_31])])).

cnf(c_0_47,negated_conjecture,
    ( k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)))) = k1_relat_1(k7_relat_1(esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_48,negated_conjecture,
    ( k1_relat_1(k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,k7_relat_1(esk3_0,esk2_0))))) != k5_xboole_0(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_47])).

cnf(c_0_49,negated_conjecture,
    ( k5_xboole_0(k1_relat_1(esk3_0),k1_setfam_1(k2_tarski(esk2_0,k1_relat_1(esk3_0)))) != k5_xboole_0(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_29]),c_0_30]),c_0_31])])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_36]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.77/0.97  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.77/0.97  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.77/0.97  #
% 0.77/0.97  # Preprocessing time       : 0.037 s
% 0.77/0.97  # Presaturation interreduction done
% 0.77/0.97  
% 0.77/0.97  # Proof found!
% 0.77/0.97  # SZS status Theorem
% 0.77/0.97  # SZS output start CNFRefutation
% 0.77/0.97  fof(t213_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>k6_subset_1(k1_relat_1(X2),k1_relat_1(k7_relat_1(X2,X1)))=k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t213_relat_1)).
% 0.77/0.97  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.77/0.97  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.77/0.97  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.77/0.97  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.77/0.97  fof(t212_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)))=k6_subset_1(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 0.77/0.97  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 0.77/0.97  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.77/0.97  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>k6_subset_1(k1_relat_1(X2),k1_relat_1(k7_relat_1(X2,X1)))=k1_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1))))), inference(assume_negation,[status(cth)],[t213_relat_1])).
% 0.77/0.97  fof(c_0_9, plain, ![X14, X15]:k4_xboole_0(X14,X15)=k5_xboole_0(X14,k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.77/0.97  fof(c_0_10, plain, ![X22, X23]:k1_setfam_1(k2_tarski(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.77/0.97  fof(c_0_11, negated_conjecture, (v1_relat_1(esk3_0)&k6_subset_1(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)))!=k1_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.77/0.97  fof(c_0_12, plain, ![X20, X21]:k6_subset_1(X20,X21)=k4_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.77/0.97  cnf(c_0_13, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.77/0.97  cnf(c_0_14, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.77/0.97  fof(c_0_15, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.77/0.97  cnf(c_0_16, negated_conjecture, (k6_subset_1(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)))!=k1_relat_1(k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.77/0.97  cnf(c_0_17, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.77/0.97  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.77/0.97  cnf(c_0_19, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.77/0.97  fof(c_0_20, plain, ![X24, X25]:(~v1_relat_1(X25)|k1_relat_1(k6_subset_1(X25,k7_relat_1(X25,X24)))=k6_subset_1(k1_relat_1(X25),X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t212_relat_1])])).
% 0.77/0.97  fof(c_0_21, plain, ![X26, X27]:(~v1_relat_1(X27)|k1_relat_1(k7_relat_1(X27,X26))=k3_xboole_0(k1_relat_1(X27),X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.77/0.97  cnf(c_0_22, negated_conjecture, (k5_xboole_0(k1_relat_1(esk3_0),k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)))))!=k1_relat_1(k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,k7_relat_1(esk3_0,esk2_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_17]), c_0_18]), c_0_18])).
% 0.77/0.97  cnf(c_0_23, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_19, c_0_14])).
% 0.77/0.97  cnf(c_0_24, plain, (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X2)))=k6_subset_1(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.77/0.97  fof(c_0_25, plain, ![X18, X19]:k2_tarski(X18,X19)=k2_tarski(X19,X18), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.77/0.97  cnf(c_0_26, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.77/0.97  cnf(c_0_27, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.77/0.97  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_3(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)),X1),k1_relat_1(esk3_0))|r2_hidden(esk1_3(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)),X1),X1)|k5_xboole_0(k1_relat_1(esk3_0),X1)!=k1_relat_1(k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,k7_relat_1(esk3_0,esk2_0)))))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.77/0.97  cnf(c_0_29, plain, (k1_relat_1(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k7_relat_1(X1,X2)))))=k5_xboole_0(k1_relat_1(X1),k1_setfam_1(k2_tarski(k1_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_17]), c_0_17]), c_0_18]), c_0_18])).
% 0.77/0.97  cnf(c_0_30, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.77/0.97  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.77/0.97  cnf(c_0_32, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k2_tarski(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_26, c_0_14])).
% 0.77/0.97  cnf(c_0_33, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.77/0.97  cnf(c_0_34, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k2_tarski(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_27, c_0_14])).
% 0.77/0.97  cnf(c_0_35, negated_conjecture, (r2_hidden(esk1_3(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)),X1),k1_relat_1(esk3_0))|r2_hidden(esk1_3(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)),X1),X1)|k5_xboole_0(k1_relat_1(esk3_0),X1)!=k5_xboole_0(k1_relat_1(esk3_0),k1_setfam_1(k2_tarski(esk2_0,k1_relat_1(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])])).
% 0.77/0.97  cnf(c_0_36, plain, (k1_setfam_1(k2_tarski(X1,k1_relat_1(X2)))=k1_relat_1(k7_relat_1(X2,X1))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_32, c_0_30])).
% 0.77/0.97  cnf(c_0_37, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.77/0.97  cnf(c_0_38, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_33, c_0_14])).
% 0.77/0.97  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))), inference(er,[status(thm)],[c_0_34])).
% 0.77/0.97  cnf(c_0_40, negated_conjecture, (r2_hidden(esk1_3(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)),X1),k1_relat_1(esk3_0))|r2_hidden(esk1_3(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)),X1),X1)|k5_xboole_0(k1_relat_1(esk3_0),X1)!=k5_xboole_0(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_31])])).
% 0.77/0.97  cnf(c_0_41, plain, (X3=k1_setfam_1(k2_tarski(X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_37, c_0_14])).
% 0.77/0.97  cnf(c_0_42, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_38])).
% 0.77/0.97  cnf(c_0_43, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3)))), inference(spm,[status(thm)],[c_0_39, c_0_32])).
% 0.77/0.97  cnf(c_0_44, negated_conjecture, (r2_hidden(esk1_3(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)),k1_relat_1(k7_relat_1(esk3_0,esk2_0))),k1_relat_1(k7_relat_1(esk3_0,esk2_0)))|r2_hidden(esk1_3(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)),k1_relat_1(k7_relat_1(esk3_0,esk2_0))),k1_relat_1(esk3_0))), inference(er,[status(thm)],[c_0_40])).
% 0.77/0.97  cnf(c_0_45, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~r2_hidden(esk1_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_42])).
% 0.77/0.97  cnf(c_0_46, negated_conjecture, (r2_hidden(esk1_3(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)),k1_relat_1(k7_relat_1(esk3_0,esk2_0))),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_31])])).
% 0.77/0.97  cnf(c_0_47, negated_conjecture, (k1_setfam_1(k2_tarski(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0))))=k1_relat_1(k7_relat_1(esk3_0,esk2_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.77/0.97  cnf(c_0_48, negated_conjecture, (k1_relat_1(k5_xboole_0(esk3_0,k1_setfam_1(k2_tarski(esk3_0,k7_relat_1(esk3_0,esk2_0)))))!=k5_xboole_0(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)))), inference(rw,[status(thm)],[c_0_22, c_0_47])).
% 0.77/0.97  cnf(c_0_49, negated_conjecture, (k5_xboole_0(k1_relat_1(esk3_0),k1_setfam_1(k2_tarski(esk2_0,k1_relat_1(esk3_0))))!=k5_xboole_0(k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_29]), c_0_30]), c_0_31])])).
% 0.77/0.97  cnf(c_0_50, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_36]), c_0_31])]), ['proof']).
% 0.77/0.97  # SZS output end CNFRefutation
% 0.77/0.97  # Proof object total steps             : 51
% 0.77/0.97  # Proof object clause steps            : 34
% 0.77/0.97  # Proof object formula steps           : 17
% 0.77/0.97  # Proof object conjectures             : 15
% 0.77/0.97  # Proof object clause conjectures      : 12
% 0.77/0.97  # Proof object formula conjectures     : 3
% 0.77/0.97  # Proof object initial clauses used    : 12
% 0.77/0.97  # Proof object initial formulas used   : 8
% 0.77/0.97  # Proof object generating inferences   : 12
% 0.77/0.97  # Proof object simplifying inferences  : 29
% 0.77/0.97  # Training examples: 0 positive, 0 negative
% 0.77/0.97  # Parsed axioms                        : 9
% 0.77/0.97  # Removed by relevancy pruning/SinE    : 0
% 0.77/0.97  # Initial clauses                      : 15
% 0.77/0.97  # Removed in clause preprocessing      : 3
% 0.77/0.97  # Initial clauses in saturation        : 12
% 0.77/0.97  # Processed clauses                    : 1463
% 0.77/0.97  # ...of these trivial                  : 19
% 0.77/0.97  # ...subsumed                          : 858
% 0.77/0.97  # ...remaining for further processing  : 586
% 0.77/0.97  # Other redundant clauses eliminated   : 1517
% 0.77/0.97  # Clauses deleted for lack of memory   : 0
% 0.77/0.97  # Backward-subsumed                    : 24
% 0.77/0.97  # Backward-rewritten                   : 38
% 0.77/0.97  # Generated clauses                    : 33577
% 0.77/0.97  # ...of the previous two non-trivial   : 31107
% 0.77/0.97  # Contextual simplify-reflections      : 32
% 0.77/0.97  # Paramodulations                      : 31830
% 0.77/0.97  # Factorizations                       : 222
% 0.77/0.97  # Equation resolutions                 : 1525
% 0.77/0.97  # Propositional unsat checks           : 0
% 0.77/0.97  #    Propositional check models        : 0
% 0.77/0.97  #    Propositional check unsatisfiable : 0
% 0.77/0.97  #    Propositional clauses             : 0
% 0.77/0.97  #    Propositional clauses after purity: 0
% 0.77/0.97  #    Propositional unsat core size     : 0
% 0.77/0.97  #    Propositional preprocessing time  : 0.000
% 0.77/0.97  #    Propositional encoding time       : 0.000
% 0.77/0.97  #    Propositional solver time         : 0.000
% 0.77/0.97  #    Success case prop preproc time    : 0.000
% 0.77/0.97  #    Success case prop encoding time   : 0.000
% 0.77/0.97  #    Success case prop solver time     : 0.000
% 0.77/0.97  # Current number of processed clauses  : 509
% 0.77/0.97  #    Positive orientable unit clauses  : 18
% 0.77/0.97  #    Positive unorientable unit clauses: 1
% 0.77/0.97  #    Negative unit clauses             : 9
% 0.77/0.97  #    Non-unit-clauses                  : 481
% 0.77/0.97  # Current number of unprocessed clauses: 29589
% 0.77/0.97  # ...number of literals in the above   : 170005
% 0.77/0.97  # Current number of archived formulas  : 0
% 0.77/0.97  # Current number of archived clauses   : 77
% 0.77/0.97  # Clause-clause subsumption calls (NU) : 36348
% 0.77/0.97  # Rec. Clause-clause subsumption calls : 21545
% 0.77/0.97  # Non-unit clause-clause subsumptions  : 905
% 0.77/0.97  # Unit Clause-clause subsumption calls : 703
% 0.77/0.97  # Rewrite failures with RHS unbound    : 0
% 0.77/0.97  # BW rewrite match attempts            : 159
% 0.77/0.97  # BW rewrite match successes           : 20
% 0.77/0.97  # Condensation attempts                : 0
% 0.77/0.97  # Condensation successes               : 0
% 0.77/0.97  # Termbank termtop insertions          : 1178319
% 0.77/0.98  
% 0.77/0.98  # -------------------------------------------------
% 0.77/0.98  # User time                : 0.616 s
% 0.77/0.98  # System time              : 0.019 s
% 0.77/0.98  # Total time               : 0.635 s
% 0.77/0.98  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
