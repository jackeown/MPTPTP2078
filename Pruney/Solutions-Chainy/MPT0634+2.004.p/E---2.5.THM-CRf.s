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
% DateTime   : Thu Dec  3 10:53:19 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 253 expanded)
%              Number of clauses        :   30 ( 105 expanded)
%              Number of leaves         :    8 (  68 expanded)
%              Depth                    :   11
%              Number of atoms          :  120 ( 511 expanded)
%              Number of equality atoms :   39 ( 243 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    inference(assume_negation,[status(cth)],[t37_funct_1])).

fof(c_0_9,plain,(
    ! [X21,X22] : k1_setfam_1(k2_tarski(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_10,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)) != k3_xboole_0(k1_relat_1(esk3_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_12,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,plain,(
    ! [X14,X15] : k2_tarski(X14,X15) = k2_tarski(X15,X14) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_16,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)) != k3_xboole_0(k1_relat_1(esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
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

cnf(c_0_21,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)) != k1_setfam_1(k2_enumset1(k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_13]),c_0_13]),c_0_18]),c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0))) != k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_17]),c_0_18])).

fof(c_0_27,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | k7_relat_1(X27,X26) = k5_relat_1(k6_relat_1(X26),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_28,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_17]),c_0_18])).

cnf(c_0_29,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_30,plain,(
    ! [X23,X24,X25] :
      ( ( r2_hidden(X23,X24)
        | ~ r2_hidden(X23,k1_relat_1(k7_relat_1(X25,X24)))
        | ~ v1_relat_1(X25) )
      & ( r2_hidden(X23,k1_relat_1(X25))
        | ~ r2_hidden(X23,k1_relat_1(k7_relat_1(X25,X24)))
        | ~ v1_relat_1(X25) )
      & ( ~ r2_hidden(X23,X24)
        | ~ r2_hidden(X23,k1_relat_1(X25))
        | r2_hidden(X23,k1_relat_1(k7_relat_1(X25,X24)))
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,k1_relat_1(esk3_0),k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))),k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)))
    | r2_hidden(esk1_3(esk2_0,k1_relat_1(esk3_0),k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))),k1_relat_1(esk3_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_32,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,k1_relat_1(esk3_0),k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))),k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)))
    | r2_hidden(esk1_3(esk2_0,k1_relat_1(esk3_0),k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))),esk2_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_28])])).

cnf(c_0_35,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_17]),c_0_18])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3)))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0))),k1_relat_1(k7_relat_1(esk3_0,esk2_0)))
    | r2_hidden(esk1_3(esk2_0,k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0))),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0))),k1_relat_1(k7_relat_1(esk3_0,esk2_0)))
    | r2_hidden(esk1_3(esk2_0,k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0))),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_32]),c_0_33])])).

cnf(c_0_41,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_setfam_1(k2_enumset1(X3,X3,X3,X4))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk1_3(X3,X4,k1_relat_1(k7_relat_1(X1,X2))),k1_relat_1(X1))
    | ~ r2_hidden(esk1_3(X3,X4,k1_relat_1(k7_relat_1(X1,X2))),X4)
    | ~ r2_hidden(esk1_3(X3,X4,k1_relat_1(k7_relat_1(X1,X2))),X3)
    | ~ r2_hidden(esk1_3(X3,X4,k1_relat_1(k7_relat_1(X1,X2))),X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0))),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_33])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk1_3(esk2_0,k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0))),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_33])])).

cnf(c_0_44,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0))) = k1_relat_1(k7_relat_1(esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_33]),c_0_42]),c_0_43])])).

cnf(c_0_45,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)) != k1_relat_1(k7_relat_1(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_44])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_32]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:48:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.040 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(t37_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_funct_1)).
% 0.21/0.40  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.21/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.40  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.21/0.40  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.21/0.40  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.21/0.40  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 0.21/0.40  fof(c_0_8, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))=k3_xboole_0(k1_relat_1(X2),X1))), inference(assume_negation,[status(cth)],[t37_funct_1])).
% 0.21/0.40  fof(c_0_9, plain, ![X21, X22]:k1_setfam_1(k2_tarski(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.21/0.40  fof(c_0_10, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.40  fof(c_0_11, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))!=k3_xboole_0(k1_relat_1(esk3_0),esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.21/0.40  cnf(c_0_12, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.40  cnf(c_0_13, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.40  fof(c_0_14, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.40  fof(c_0_15, plain, ![X14, X15]:k2_tarski(X14,X15)=k2_tarski(X15,X14), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.21/0.40  cnf(c_0_16, negated_conjecture, (k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))!=k3_xboole_0(k1_relat_1(esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.40  cnf(c_0_17, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.21/0.40  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.40  cnf(c_0_19, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  fof(c_0_20, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.21/0.40  cnf(c_0_21, negated_conjecture, (k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))!=k1_setfam_1(k2_enumset1(k1_relat_1(esk3_0),k1_relat_1(esk3_0),k1_relat_1(esk3_0),esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.21/0.40  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_13]), c_0_13]), c_0_18]), c_0_18])).
% 0.21/0.40  cnf(c_0_23, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.40  cnf(c_0_24, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.40  cnf(c_0_25, negated_conjecture, (k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))!=k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.40  cnf(c_0_26, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_17]), c_0_18])).
% 0.21/0.40  fof(c_0_27, plain, ![X26, X27]:(~v1_relat_1(X27)|k7_relat_1(X27,X26)=k5_relat_1(k6_relat_1(X26),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.21/0.40  cnf(c_0_28, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_17]), c_0_18])).
% 0.21/0.40  cnf(c_0_29, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.40  fof(c_0_30, plain, ![X23, X24, X25]:(((r2_hidden(X23,X24)|~r2_hidden(X23,k1_relat_1(k7_relat_1(X25,X24)))|~v1_relat_1(X25))&(r2_hidden(X23,k1_relat_1(X25))|~r2_hidden(X23,k1_relat_1(k7_relat_1(X25,X24)))|~v1_relat_1(X25)))&(~r2_hidden(X23,X24)|~r2_hidden(X23,k1_relat_1(X25))|r2_hidden(X23,k1_relat_1(k7_relat_1(X25,X24)))|~v1_relat_1(X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 0.21/0.40  cnf(c_0_31, negated_conjecture, (r2_hidden(esk1_3(esk2_0,k1_relat_1(esk3_0),k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))),k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)))|r2_hidden(esk1_3(esk2_0,k1_relat_1(esk3_0),k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))),k1_relat_1(esk3_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26])])).
% 0.21/0.40  cnf(c_0_32, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.40  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.40  cnf(c_0_34, negated_conjecture, (r2_hidden(esk1_3(esk2_0,k1_relat_1(esk3_0),k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))),k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0)))|r2_hidden(esk1_3(esk2_0,k1_relat_1(esk3_0),k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))),esk2_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_28])])).
% 0.21/0.40  cnf(c_0_35, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_17]), c_0_18])).
% 0.21/0.40  cnf(c_0_36, plain, (r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(X3))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.40  cnf(c_0_37, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X3)))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.40  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_3(esk2_0,k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0))),k1_relat_1(k7_relat_1(esk3_0,esk2_0)))|r2_hidden(esk1_3(esk2_0,k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0))),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.21/0.40  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.40  cnf(c_0_40, negated_conjecture, (r2_hidden(esk1_3(esk2_0,k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0))),k1_relat_1(k7_relat_1(esk3_0,esk2_0)))|r2_hidden(esk1_3(esk2_0,k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0))),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_32]), c_0_33])])).
% 0.21/0.40  cnf(c_0_41, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_setfam_1(k2_enumset1(X3,X3,X3,X4))|~v1_relat_1(X1)|~r2_hidden(esk1_3(X3,X4,k1_relat_1(k7_relat_1(X1,X2))),k1_relat_1(X1))|~r2_hidden(esk1_3(X3,X4,k1_relat_1(k7_relat_1(X1,X2))),X4)|~r2_hidden(esk1_3(X3,X4,k1_relat_1(k7_relat_1(X1,X2))),X3)|~r2_hidden(esk1_3(X3,X4,k1_relat_1(k7_relat_1(X1,X2))),X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.40  cnf(c_0_42, negated_conjecture, (r2_hidden(esk1_3(esk2_0,k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0))),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_33])])).
% 0.21/0.40  cnf(c_0_43, negated_conjecture, (r2_hidden(esk1_3(esk2_0,k1_relat_1(esk3_0),k1_relat_1(k7_relat_1(esk3_0,esk2_0))),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_33])])).
% 0.21/0.40  cnf(c_0_44, negated_conjecture, (k1_setfam_1(k2_enumset1(esk2_0,esk2_0,esk2_0,k1_relat_1(esk3_0)))=k1_relat_1(k7_relat_1(esk3_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_33]), c_0_42]), c_0_43])])).
% 0.21/0.40  cnf(c_0_45, negated_conjecture, (k1_relat_1(k5_relat_1(k6_relat_1(esk2_0),esk3_0))!=k1_relat_1(k7_relat_1(esk3_0,esk2_0))), inference(rw,[status(thm)],[c_0_25, c_0_44])).
% 0.21/0.40  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_32]), c_0_33])]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 47
% 0.21/0.40  # Proof object clause steps            : 30
% 0.21/0.40  # Proof object formula steps           : 17
% 0.21/0.40  # Proof object conjectures             : 16
% 0.21/0.40  # Proof object clause conjectures      : 13
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 13
% 0.21/0.40  # Proof object initial formulas used   : 8
% 0.21/0.40  # Proof object generating inferences   : 9
% 0.21/0.40  # Proof object simplifying inferences  : 31
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 8
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 17
% 0.21/0.40  # Removed in clause preprocessing      : 3
% 0.21/0.40  # Initial clauses in saturation        : 14
% 0.21/0.40  # Processed clauses                    : 52
% 0.21/0.40  # ...of these trivial                  : 2
% 0.21/0.40  # ...subsumed                          : 6
% 0.21/0.40  # ...remaining for further processing  : 44
% 0.21/0.40  # Other redundant clauses eliminated   : 11
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 0
% 0.21/0.40  # Backward-rewritten                   : 7
% 0.21/0.40  # Generated clauses                    : 170
% 0.21/0.40  # ...of the previous two non-trivial   : 155
% 0.21/0.40  # Contextual simplify-reflections      : 0
% 0.21/0.40  # Paramodulations                      : 157
% 0.21/0.40  # Factorizations                       : 2
% 0.21/0.40  # Equation resolutions                 : 11
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 20
% 0.21/0.40  #    Positive orientable unit clauses  : 5
% 0.21/0.40  #    Positive unorientable unit clauses: 1
% 0.21/0.40  #    Negative unit clauses             : 1
% 0.21/0.40  #    Non-unit-clauses                  : 13
% 0.21/0.40  # Current number of unprocessed clauses: 130
% 0.21/0.40  # ...number of literals in the above   : 571
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 24
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 102
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 57
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 6
% 0.21/0.40  # Unit Clause-clause subsumption calls : 0
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 13
% 0.21/0.40  # BW rewrite match successes           : 11
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 4637
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.050 s
% 0.21/0.40  # System time              : 0.004 s
% 0.21/0.40  # Total time               : 0.054 s
% 0.21/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
