%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:02 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 209 expanded)
%              Number of clauses        :   32 (  93 expanded)
%              Number of leaves         :   11 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  120 ( 332 expanded)
%              Number of equality atoms :   45 ( 192 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t119_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k8_relat_1(X1,X2)) = k3_xboole_0(k2_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t120_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k2_relat_1(k8_relat_1(X1,X2)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_relat_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(c_0_11,plain,(
    ! [X34,X35] : k1_setfam_1(k2_tarski(X34,X35)) = k3_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_12,plain,(
    ! [X29,X30] : k1_enumset1(X29,X29,X30) = k2_tarski(X29,X30) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | k2_relat_1(k8_relat_1(X36,X37)) = k3_xboole_0(k2_relat_1(X37),X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_relat_1])])).

cnf(c_0_14,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X31,X32,X33] : k2_enumset1(X31,X31,X32,X33) = k1_enumset1(X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X20,X21] : k4_xboole_0(X20,k4_xboole_0(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_18,plain,
    ( k2_relat_1(k8_relat_1(X2,X1)) = k3_xboole_0(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X1,k2_relat_1(X2))
         => k2_relat_1(k8_relat_1(X1,X2)) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t120_relat_1])).

fof(c_0_23,plain,(
    ! [X27,X28] : k2_tarski(X27,X28) = k2_tarski(X28,X27) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_24,plain,
    ( k2_relat_1(k8_relat_1(X2,X1)) = k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_19]),c_0_20])).

fof(c_0_26,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & r1_tarski(esk3_0,k2_relat_1(esk4_0))
    & k2_relat_1(k8_relat_1(esk3_0,esk4_0)) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X22,X23,X24] :
      ( ~ r1_tarski(X22,X23)
      | ~ r1_xboole_0(X23,X24)
      | r1_xboole_0(X22,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_29,plain,
    ( k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X2)) = k2_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_15]),c_0_15]),c_0_20]),c_0_20])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk3_0,k2_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | r1_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_35,negated_conjecture,
    ( k4_xboole_0(k2_relat_1(esk4_0),k4_xboole_0(k2_relat_1(esk4_0),X1)) = k2_relat_1(k8_relat_1(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_31]),c_0_25])).

fof(c_0_37,plain,(
    ! [X25,X26] :
      ( ( ~ r1_xboole_0(X25,X26)
        | k4_xboole_0(X25,X26) = X25 )
      & ( k4_xboole_0(X25,X26) != X25
        | r1_xboole_0(X25,X26) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_38,negated_conjecture,
    ( r1_xboole_0(esk3_0,X1)
    | ~ r1_xboole_0(k2_relat_1(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_41,plain,(
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

cnf(c_0_42,negated_conjecture,
    ( k2_relat_1(k8_relat_1(esk3_0,esk4_0)) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_relat_1(esk4_0))) = k2_relat_1(k8_relat_1(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( r1_xboole_0(esk3_0,X1)
    | r2_hidden(esk2_2(k2_relat_1(esk4_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r1_xboole_0(esk3_0,X1)
    | r2_hidden(esk2_2(k2_relat_1(esk4_0),X1),k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_40])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k2_relat_1(esk4_0))) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(esk3_0,X1) = esk3_0
    | r2_hidden(esk2_2(k2_relat_1(esk4_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( k4_xboole_0(esk3_0,X1) = esk3_0
    | r2_hidden(esk2_2(k2_relat_1(esk4_0),X1),k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_46])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk2_2(k2_relat_1(esk4_0),k4_xboole_0(esk3_0,k2_relat_1(esk4_0))),k4_xboole_0(esk3_0,k2_relat_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk2_2(k2_relat_1(esk4_0),k4_xboole_0(esk3_0,k2_relat_1(esk4_0))),k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:23 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.44  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.20/0.44  # and selection function SelectNegativeLiterals.
% 0.20/0.44  #
% 0.20/0.44  # Preprocessing time       : 0.028 s
% 0.20/0.44  # Presaturation interreduction done
% 0.20/0.44  
% 0.20/0.44  # Proof found!
% 0.20/0.44  # SZS status Theorem
% 0.20/0.44  # SZS output start CNFRefutation
% 0.20/0.44  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.44  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.44  fof(t119_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k8_relat_1(X1,X2))=k3_xboole_0(k2_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 0.20/0.44  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.44  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.44  fof(t120_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k2_relat_1(X2))=>k2_relat_1(k8_relat_1(X1,X2))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_relat_1)).
% 0.20/0.44  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.20/0.44  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.20/0.44  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.44  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.44  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.44  fof(c_0_11, plain, ![X34, X35]:k1_setfam_1(k2_tarski(X34,X35))=k3_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.44  fof(c_0_12, plain, ![X29, X30]:k1_enumset1(X29,X29,X30)=k2_tarski(X29,X30), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.44  fof(c_0_13, plain, ![X36, X37]:(~v1_relat_1(X37)|k2_relat_1(k8_relat_1(X36,X37))=k3_xboole_0(k2_relat_1(X37),X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_relat_1])])).
% 0.20/0.44  cnf(c_0_14, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.44  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.44  fof(c_0_16, plain, ![X31, X32, X33]:k2_enumset1(X31,X31,X32,X33)=k1_enumset1(X31,X32,X33), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.44  fof(c_0_17, plain, ![X20, X21]:k4_xboole_0(X20,k4_xboole_0(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.44  cnf(c_0_18, plain, (k2_relat_1(k8_relat_1(X2,X1))=k3_xboole_0(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.44  cnf(c_0_19, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.44  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.44  cnf(c_0_21, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.44  fof(c_0_22, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k2_relat_1(X2))=>k2_relat_1(k8_relat_1(X1,X2))=X1))), inference(assume_negation,[status(cth)],[t120_relat_1])).
% 0.20/0.44  fof(c_0_23, plain, ![X27, X28]:k2_tarski(X27,X28)=k2_tarski(X28,X27), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.20/0.44  cnf(c_0_24, plain, (k2_relat_1(k8_relat_1(X2,X1))=k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.20/0.44  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_19]), c_0_20])).
% 0.20/0.44  fof(c_0_26, negated_conjecture, (v1_relat_1(esk4_0)&(r1_tarski(esk3_0,k2_relat_1(esk4_0))&k2_relat_1(k8_relat_1(esk3_0,esk4_0))!=esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.20/0.44  cnf(c_0_27, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.44  fof(c_0_28, plain, ![X22, X23, X24]:(~r1_tarski(X22,X23)|~r1_xboole_0(X23,X24)|r1_xboole_0(X22,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.20/0.44  cnf(c_0_29, plain, (k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X2))=k2_relat_1(k8_relat_1(X2,X1))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.44  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.44  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_15]), c_0_15]), c_0_20]), c_0_20])).
% 0.20/0.44  cnf(c_0_32, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.44  cnf(c_0_33, negated_conjecture, (r1_tarski(esk3_0,k2_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.44  fof(c_0_34, plain, ![X14, X15, X17, X18, X19]:(((r2_hidden(esk2_2(X14,X15),X14)|r1_xboole_0(X14,X15))&(r2_hidden(esk2_2(X14,X15),X15)|r1_xboole_0(X14,X15)))&(~r2_hidden(X19,X17)|~r2_hidden(X19,X18)|~r1_xboole_0(X17,X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.44  cnf(c_0_35, negated_conjecture, (k4_xboole_0(k2_relat_1(esk4_0),k4_xboole_0(k2_relat_1(esk4_0),X1))=k2_relat_1(k8_relat_1(X1,esk4_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.44  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_31]), c_0_25])).
% 0.20/0.44  fof(c_0_37, plain, ![X25, X26]:((~r1_xboole_0(X25,X26)|k4_xboole_0(X25,X26)=X25)&(k4_xboole_0(X25,X26)!=X25|r1_xboole_0(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.44  cnf(c_0_38, negated_conjecture, (r1_xboole_0(esk3_0,X1)|~r1_xboole_0(k2_relat_1(esk4_0),X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.44  cnf(c_0_39, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.44  cnf(c_0_40, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.44  fof(c_0_41, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.44  cnf(c_0_42, negated_conjecture, (k2_relat_1(k8_relat_1(esk3_0,esk4_0))!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.44  cnf(c_0_43, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,k2_relat_1(esk4_0)))=k2_relat_1(k8_relat_1(X1,esk4_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.44  cnf(c_0_44, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.44  cnf(c_0_45, negated_conjecture, (r1_xboole_0(esk3_0,X1)|r2_hidden(esk2_2(k2_relat_1(esk4_0),X1),X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.44  cnf(c_0_46, negated_conjecture, (r1_xboole_0(esk3_0,X1)|r2_hidden(esk2_2(k2_relat_1(esk4_0),X1),k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_38, c_0_40])).
% 0.20/0.44  cnf(c_0_47, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.44  cnf(c_0_48, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k2_relat_1(esk4_0)))!=esk3_0), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.44  cnf(c_0_49, negated_conjecture, (k4_xboole_0(esk3_0,X1)=esk3_0|r2_hidden(esk2_2(k2_relat_1(esk4_0),X1),X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.44  cnf(c_0_50, negated_conjecture, (k4_xboole_0(esk3_0,X1)=esk3_0|r2_hidden(esk2_2(k2_relat_1(esk4_0),X1),k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_44, c_0_46])).
% 0.20/0.44  cnf(c_0_51, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_47])).
% 0.20/0.44  cnf(c_0_52, negated_conjecture, (r2_hidden(esk2_2(k2_relat_1(esk4_0),k4_xboole_0(esk3_0,k2_relat_1(esk4_0))),k4_xboole_0(esk3_0,k2_relat_1(esk4_0)))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.44  cnf(c_0_53, negated_conjecture, (r2_hidden(esk2_2(k2_relat_1(esk4_0),k4_xboole_0(esk3_0,k2_relat_1(esk4_0))),k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_48, c_0_50])).
% 0.20/0.44  cnf(c_0_54, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])]), ['proof']).
% 0.20/0.44  # SZS output end CNFRefutation
% 0.20/0.44  # Proof object total steps             : 55
% 0.20/0.44  # Proof object clause steps            : 32
% 0.20/0.44  # Proof object formula steps           : 23
% 0.20/0.44  # Proof object conjectures             : 17
% 0.20/0.44  # Proof object clause conjectures      : 14
% 0.20/0.44  # Proof object formula conjectures     : 3
% 0.20/0.44  # Proof object initial clauses used    : 14
% 0.20/0.44  # Proof object initial formulas used   : 11
% 0.20/0.44  # Proof object generating inferences   : 11
% 0.20/0.44  # Proof object simplifying inferences  : 15
% 0.20/0.44  # Training examples: 0 positive, 0 negative
% 0.20/0.44  # Parsed axioms                        : 11
% 0.20/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.44  # Initial clauses                      : 21
% 0.20/0.44  # Removed in clause preprocessing      : 3
% 0.20/0.44  # Initial clauses in saturation        : 18
% 0.20/0.44  # Processed clauses                    : 238
% 0.20/0.44  # ...of these trivial                  : 19
% 0.20/0.44  # ...subsumed                          : 43
% 0.20/0.44  # ...remaining for further processing  : 176
% 0.20/0.44  # Other redundant clauses eliminated   : 62
% 0.20/0.44  # Clauses deleted for lack of memory   : 0
% 0.20/0.44  # Backward-subsumed                    : 1
% 0.20/0.44  # Backward-rewritten                   : 20
% 0.20/0.44  # Generated clauses                    : 3914
% 0.20/0.44  # ...of the previous two non-trivial   : 3410
% 0.20/0.44  # Contextual simplify-reflections      : 0
% 0.20/0.44  # Paramodulations                      : 3852
% 0.20/0.44  # Factorizations                       : 0
% 0.20/0.44  # Equation resolutions                 : 62
% 0.20/0.44  # Propositional unsat checks           : 0
% 0.20/0.44  #    Propositional check models        : 0
% 0.20/0.44  #    Propositional check unsatisfiable : 0
% 0.20/0.44  #    Propositional clauses             : 0
% 0.20/0.44  #    Propositional clauses after purity: 0
% 0.20/0.44  #    Propositional unsat core size     : 0
% 0.20/0.44  #    Propositional preprocessing time  : 0.000
% 0.20/0.44  #    Propositional encoding time       : 0.000
% 0.20/0.44  #    Propositional solver time         : 0.000
% 0.20/0.44  #    Success case prop preproc time    : 0.000
% 0.20/0.44  #    Success case prop encoding time   : 0.000
% 0.20/0.44  #    Success case prop solver time     : 0.000
% 0.20/0.44  # Current number of processed clauses  : 134
% 0.20/0.44  #    Positive orientable unit clauses  : 24
% 0.20/0.44  #    Positive unorientable unit clauses: 3
% 0.20/0.44  #    Negative unit clauses             : 3
% 0.20/0.44  #    Non-unit-clauses                  : 104
% 0.20/0.44  # Current number of unprocessed clauses: 3161
% 0.20/0.44  # ...number of literals in the above   : 14766
% 0.20/0.44  # Current number of archived formulas  : 0
% 0.20/0.44  # Current number of archived clauses   : 42
% 0.20/0.44  # Clause-clause subsumption calls (NU) : 1266
% 0.20/0.44  # Rec. Clause-clause subsumption calls : 890
% 0.20/0.44  # Non-unit clause-clause subsumptions  : 41
% 0.20/0.44  # Unit Clause-clause subsumption calls : 160
% 0.20/0.44  # Rewrite failures with RHS unbound    : 0
% 0.20/0.44  # BW rewrite match attempts            : 25
% 0.20/0.44  # BW rewrite match successes           : 23
% 0.20/0.44  # Condensation attempts                : 0
% 0.20/0.44  # Condensation successes               : 0
% 0.20/0.44  # Termbank termtop insertions          : 62708
% 0.20/0.44  
% 0.20/0.44  # -------------------------------------------------
% 0.20/0.44  # User time                : 0.086 s
% 0.20/0.44  # System time              : 0.008 s
% 0.20/0.44  # Total time               : 0.095 s
% 0.20/0.44  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
